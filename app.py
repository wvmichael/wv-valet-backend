"""
WeatherValet.ai · Live Valet Verification Backend
==================================================

A small Flask service that turns the "Request Live Valet Verification" button
on the v2.4 ticket UI into actual revenue.

What it does:

    1. Frontend POSTs the plan + tier choice to /api/v1/verification/checkout
    2. Server creates a Stripe Checkout Session with the right price
    3. Customer pays on Stripe's hosted page (no card data ever touches us)
    4. Stripe webhooks /webhooks/stripe with checkout.session.completed
    5. Server marks the request paid, sends customer SMS, notifies meteorologist
    6. Meteorologist receives SMS with pre-synthesized brief + claim link
    7. Customer's "standby" page polls /api/v1/verification/status until done
    8. Meteorologist signs off via /meteorologist/<token>; customer gets the brief

What it deliberately doesn't do (yet):

    - User accounts / login (friction kills conversion at the upsell moment)
    - Recurring billing for the $99/month tier (one-time checkout for v1;
      add Stripe Subscriptions when you actually have repeat customers)
    - Two-way SMS (customer texting back questions; adds a state machine
      that's not worth it for v1)
    - Multi-meteorologist routing (single on-duty meteorologist gets every
      ping; add routing when you have two)
    - Refund flow (Stripe dashboard handles it manually for v1)

Architecture:

    Netlify (static v2.4 HTML/JS)  ──[POST /api/v1/verification/checkout]──▶  This Flask app
                                                                                    │
                                                                                    ├─ creates Stripe Checkout Session
                                                                                    ├─ inserts row in Postgres (status='pending')
                                                                                    └─ returns hosted_url to frontend
                                                                                    
    Customer ──redirected to Stripe──▶  pays  ──redirect──▶  /verification/standby
                                          │
                                          ▼
                                      Stripe webhook ──▶ /webhooks/stripe
                                                              │
                                                              ├─ verifies signature
                                                              ├─ marks Postgres row 'paid'
                                                              ├─ Twilio SMS to customer
                                                              └─ Twilio SMS to meteorologist (with brief + claim link)
                                                              
    Meteorologist ──/meteorologist/<token>──▶ types verdict ──POST──▶ marks 'completed', SMSes customer

Run:

    pip install flask stripe twilio psycopg2-binary
    export STRIPE_SECRET_KEY=sk_test_...
    export STRIPE_WEBHOOK_SECRET=whsec_...
    export TWILIO_ACCOUNT_SID=AC...
    export TWILIO_AUTH_TOKEN=...
    export TWILIO_FROM_NUMBER=+15555550100
    export METEOROLOGIST_PHONE=+15555550101    # Timmy's phone for v1
    export PUBLIC_BASE_URL=https://api.weathervalet.ai   # how Stripe webhooks reach us
    export FRONTEND_BASE_URL=https://weathervalet.ai     # where customers come from
    export DATABASE_URL=postgresql://localhost/wv_valet   # Postgres connection
    python app.py

The frontend changes are in static/upsell.js — they replace the v2.4 modal
behavior with calls to this server. That file is in the same directory.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import os
import secrets
import sys
import time
import urllib.request
import urllib.error
from contextlib import contextmanager
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

# bcrypt for password hashing. Slow hashing is appropriate here because
# passwords have low entropy — users pick guessable values like "fluffy123"
# instead of cryptographically-random 256-bit values. Slow hashing makes
# brute-force attacks computationally expensive even against weak passwords.
# bcrypt is the industry-standard choice; argon2 is also acceptable but
# bcrypt has wider tooling support and more battle-tested deployments.
import bcrypt

# Postgres driver. psycopg2-binary bundles the native libpq library, which
# means we don't need pg_config / libpq-dev on the build system. This is
# the recommended package for Render and other PaaS hosts.
#
# RealDictCursor makes cur.fetchone() and cur.fetchall() return dicts
# keyed by column name (e.g. row['stripe_session_id']), preserving the
# access pattern from the prior sqlite3.Row implementation. Without this,
# rows would come back as tuples and every row access would break.
import psycopg2
import psycopg2.extras

from flask import Flask, abort, jsonify, make_response, redirect, render_template_string, request

# Stripe and Twilio are imported lazily so the file can be inspected without them
try:
    import stripe  # pip install stripe
except ImportError:
    stripe = None  # type: ignore

try:
    from twilio.rest import Client as TwilioClient  # pip install twilio
except ImportError:
    TwilioClient = None  # type: ignore

# Decision Engine — produces the pre-synthesized brief sent to the meteorologist.
# This is the v2.1 module from the previous session; living in PYTHONPATH or
# vendored alongside this file.
try:
    from decision_engine import generate_ticket_decision
except ImportError:
    generate_ticket_decision = None  # type: ignore


# ════════════════════════════════════════════════════════════════════════════
# Configuration
# ════════════════════════════════════════════════════════════════════════════

# All sensitive values come from environment variables. NEVER hard-code keys.
# Stripe test keys start with sk_test_; live keys start with sk_live_.
STRIPE_SECRET_KEY = os.environ.get("STRIPE_SECRET_KEY", "")
STRIPE_WEBHOOK_SECRET = os.environ.get("STRIPE_WEBHOOK_SECRET", "")

TWILIO_ACCOUNT_SID = os.environ.get("TWILIO_ACCOUNT_SID", "")
TWILIO_AUTH_TOKEN = os.environ.get("TWILIO_AUTH_TOKEN", "")
TWILIO_FROM_NUMBER = os.environ.get("TWILIO_FROM_NUMBER", "")  # Twilio number we send from

# The on-duty meteorologist's phone, in E.164 format (+15555550101).
# When you have multiple, swap this for a routing function.
METEOROLOGIST_PHONE = os.environ.get("METEOROLOGIST_PHONE", "")
METEOROLOGIST_NAME = os.environ.get("METEOROLOGIST_NAME", "your meteorologist")

# How Stripe reaches us for webhooks (must be HTTPS in production). Locally,
# use ngrok or stripe-cli to forward webhooks.
PUBLIC_BASE_URL = os.environ.get("PUBLIC_BASE_URL", "http://localhost:8080")

# Where customers came from — used for the success/cancel redirect URLs.
FRONTEND_BASE_URL = os.environ.get("FRONTEND_BASE_URL", "http://localhost:8000")

# Postgres connection URL. Render auto-injects DATABASE_URL when a
# Postgres service is linked to a web service via the Render dashboard.
# The URL format is: postgresql://user:pass@host:port/dbname
#
# Local development fallback: assumes a Postgres instance running on
# localhost. In practice you'd run `docker run -e POSTGRES_PASSWORD=...
# -p 5432:5432 postgres:15` or use Postgres.app on macOS.
#
# Migration from SQLite (May 2026): the prior DB_PATH = "wv_valet.db"
# pattern is replaced because Render's ephemeral filesystem means SQLite
# data doesn't survive deploys. Postgres on Render is durable and
# survives redeploys, making it the right answer for production auth
# and any other persistent state.
DATABASE_URL = os.environ.get("DATABASE_URL", "")

# Defensive URL scheme normalization. Some Render deploy paths (and other
# PaaS hosts) provide DATABASE_URL with the older `postgres://` prefix.
# Modern psycopg2 (2.9+) accepts both schemes via parse_dsn, but other
# tools in the broader ecosystem (SQLAlchemy 1.4+, certain ORMs) explicitly
# reject `postgres://`. Normalizing here means the URL works everywhere
# even if someone adds SQLAlchemy later.
if DATABASE_URL.startswith("postgres://"):
    DATABASE_URL = "postgresql://" + DATABASE_URL[len("postgres://"):]

if not DATABASE_URL:
    # Local dev fallback. If Postgres isn't running locally, the app
    # will fail to start with a clear connection error rather than
    # silently creating an empty SQLite file (which was the prior
    # behavior and could mask configuration mistakes).
    DATABASE_URL = "postgresql://localhost/wv_valet"

# Where the WeatherValet Meteorologist Brief lives — the JSON file the
# Decision Engine reads on every per-ticket call. The /admin/brief form
# writes to this same path, so the moment a meteorologist saves a brief
# it's live in the customer-facing forecast pipeline.
BRIEF_PATH = Path(os.environ.get("WV_BRIEF_PATH", "meteorologist_brief.json"))
BRIEF_SCHEMA_VERSION = "1.1"

# ════════════════════════════════════════════════════════════════════════════
# AI explainer — Gemini (Google Generative Language API)
# ════════════════════════════════════════════════════════════════════════════
#
# Why Gemini specifically: Google's free tier is genuinely free (no card
# required to start), the request rate (~15/min on the free tier as of
# build time) is enough for prototype testing, and the gemini-1.5-flash
# model is fast and cheap. If we outgrow this we swap in a paid tier or
# switch to Claude/OpenAI — the switch is one function in this file.
#
# The key is created at https://aistudio.google.com/app/apikey — that's a
# button-click flow that the human operator runs once, then pastes into
# the GEMINI_API_KEY env var on Render.
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "")
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash")
# The v1 endpoint serves the 2.x family; v1beta is for older/preview models.
# If you point GEMINI_MODEL at a preview model that needs v1beta, also set
# GEMINI_API_VERSION=v1beta in the environment.
GEMINI_API_VERSION = os.environ.get("GEMINI_API_VERSION", "v1")
GEMINI_API_URL = (
    f"https://generativelanguage.googleapis.com/{GEMINI_API_VERSION}/models/"
    f"{GEMINI_MODEL}:generateContent"
)

# ──────────────────────────────────────────────────────────────────────────
# Mailchimp — marketing list / waitlist capture
# ──────────────────────────────────────────────────────────────────────────
# The API key has the data center suffix appended (e.g. "abc123...-us8").
# We split it to derive the API base URL: every Mailchimp account is on
# a specific data center, and the API URL must match.
#
# Endpoint pattern: https://{dc}.api.mailchimp.com/3.0/lists/{audience_id}/members
# Auth: HTTP Basic with username "anystring" and password = API key
#
# Set both env vars on Render:
#   MAILCHIMP_API_KEY = the full API key including -us8 suffix
#   MAILCHIMP_AUDIENCE_ID = the 10-character audience identifier
MAILCHIMP_API_KEY = os.environ.get("MAILCHIMP_API_KEY", "")
MAILCHIMP_AUDIENCE_ID = os.environ.get("MAILCHIMP_AUDIENCE_ID", "")
# Derive the data center from the API key suffix. Default to us8 to match
# our current account; if a future key is on a different DC, this still works.
MAILCHIMP_DC = MAILCHIMP_API_KEY.split("-")[-1] if "-" in MAILCHIMP_API_KEY else "us8"
MAILCHIMP_API_URL = f"https://{MAILCHIMP_DC}.api.mailchimp.com/3.0"

# Which tags are valid. The frontend passes a `source` field (e.g.
# "pricing-pro-single") and we map it to the corresponding Mailchimp tag.
# Tags not in this dict get mapped to "general-interest" as a safe default.
MAILCHIMP_VALID_TAGS = {
    "pricing-hobbyist",
    "pricing-pro-single",
    "pricing-pro-multi",
    "pricing-pro-enterprise",
    "crew-applicant",
    "footer-cta",
    "general-interest",
}

# Pricing tiers. Amounts in cents; Stripe expects integer cents.
TIERS = {
    "single": {
        "name": "Single Verification",
        "price_cents": 1900,  # $19
        "description": "One plan reviewed by a lead meteorologist within 30 minutes.",
    },
    "day_pass": {
        "name": "Day Pass",
        "price_cents": 4900,  # $49
        "description": "Unlimited verifications for 24 hours.",
    },
    "pro_monthly": {
        "name": "Pro Monthly",
        "price_cents": 9900,  # $99
        "description": "Unlimited verifications all month, priority queue.",
        # Note: this is one-time checkout for v1. For real recurring billing,
        # switch to Stripe Subscriptions — see comment in create_checkout_session.
    },
}

# SLA budget for the meteorologist response. Customer-facing copy says
# "usually under 30 minutes." This drives the dashboard's "overdue" flag.
SLA_MINUTES = 30


# ════════════════════════════════════════════════════════════════════════════
# Database — Postgres, durable, multi-process safe
# ════════════════════════════════════════════════════════════════════════════
#
# One table for now (verification_requests) plus an audit log
# (brief_submissions). Columns map directly to the lifecycle of a request:
#
#   pending   → checkout session created, customer hasn't paid yet
#   paid      → Stripe webhook fired, SMSes sent
#   claimed   → meteorologist tapped the claim link in their SMS
#   completed → meteorologist published their verdict, customer notified
#   expired   → customer never paid (Stripe sessions expire after 24h)
#
# The `claim_token` is a per-request secret in the meteorologist's SMS link,
# so we don't need them logged in. It's a 32-char URL-safe random token.
#
# Postgres-vs-SQLite notes for the schema below:
#   - SERIAL replaces INTEGER PRIMARY KEY AUTOINCREMENT. Postgres
#     auto-generates a sequence and returns the value via RETURNING id
#     instead of cur.lastrowid.
#   - BIGINT replaces INTEGER for Unix-timestamp columns. INTEGER (4 bytes)
#     overflows in 2038; BIGINT (8 bytes) is safe through year 292B.
#   - CREATE INDEX IF NOT EXISTS syntax is identical between SQLite and
#     Postgres.
#   - All other column types (TEXT, etc.) are identical.

SCHEMA = """
CREATE TABLE IF NOT EXISTS verification_requests (
    id                  SERIAL PRIMARY KEY,
    created_at          BIGINT NOT NULL,
    updated_at          BIGINT NOT NULL,
    status              TEXT NOT NULL,           -- pending|paid|claimed|completed|expired
    tier                TEXT NOT NULL,           -- single|day_pass|pro_monthly
    price_cents         INTEGER NOT NULL,

    -- Customer (no account, just contact info)
    customer_email      TEXT,
    customer_phone      TEXT,                    -- E.164 format

    -- Plan being reviewed — keep verbatim so the meteorologist sees the user's words
    plan_text           TEXT NOT NULL,
    plan_industry       TEXT,
    plan_location       TEXT,
    plan_window         TEXT,
    ai_brief_markdown   TEXT,                    -- pre-synthesized Decision Engine output
    ai_status_key       TEXT,                    -- 'clear'|'caution'|'risk' from existing rules

    -- Stripe linkage
    stripe_session_id   TEXT UNIQUE,
    stripe_payment_id   TEXT,

    -- Meteorologist workflow
    claim_token         TEXT UNIQUE NOT NULL,    -- per-request secret in the claim URL
    claimed_at          BIGINT,
    completed_at        BIGINT,
    meteorologist_verdict   TEXT,
    meteorologist_notes     TEXT
);
CREATE INDEX IF NOT EXISTS idx_status_created ON verification_requests(status, created_at);
CREATE INDEX IF NOT EXISTS idx_claim_token ON verification_requests(claim_token);
CREATE INDEX IF NOT EXISTS idx_stripe_session ON verification_requests(stripe_session_id);

-- ── Brief submission audit log ──
-- Every POST to /admin/brief writes a row here. Lets the Meteorologist Portal
-- show a real submission history (not just the current state of the brief
-- file), and gives us an audit trail for future accountability + AI training.
-- One row per POST, never updated — append-only by design.
CREATE TABLE IF NOT EXISTS brief_submissions (
    id                  SERIAL PRIMARY KEY,
    submitted_at        BIGINT NOT NULL,         -- Unix timestamp seconds
    meteorologist_name  TEXT NOT NULL,
    region_name         TEXT NOT NULL,
    verdict             TEXT NOT NULL,           -- dry|wet|mixed|stormy|clear
    start_time          TEXT,                    -- "06:00" form input
    end_time            TEXT,                    -- "20:00" form input
    summary             TEXT,                    -- the customer-facing text
    confidence          TEXT,                    -- high|medium|low
    notes               TEXT                     -- internal-only
);
CREATE INDEX IF NOT EXISTS idx_briefs_recent ON brief_submissions(submitted_at DESC);
CREATE INDEX IF NOT EXISTS idx_briefs_meteorologist ON brief_submissions(meteorologist_name, submitted_at DESC);

-- ════════════════════════════════════════════════════════════════════════════
-- Auth tables (added May 2026 — Phase 3 of the auth project)
-- ════════════════════════════════════════════════════════════════════════════
--
-- Magic-link authentication: email-only login, no passwords. The user
-- requests a link, we email them a one-time URL that expires in 15 minutes.
-- Clicking the link creates a session that lasts 30 days absolute, 7 days
-- idle. See AUTH-IMPLEMENTATION-PLAN.pdf for the full design rationale.
--
-- Security design notes for everything below:
--   - Raw tokens / session IDs are NEVER stored. We store SHA-256 hashes.
--     The user receives the raw value (in their email or as a cookie);
--     we compute the hash to look up the row. If the database leaks,
--     the hashes are useless — they can't be reversed to working credentials.
--   - All foreign keys use ON DELETE CASCADE so "delete my account"
--     actually removes everything tied to the user. GDPR-friendly.
--   - The users table uses LOWER(email) indexing so email case doesn't
--     create duplicate accounts (User@x.com and user@x.com are the same).

-- ── Users — one row per real person who can sign in ──
-- Email is the primary login mechanism. Password hash is bcrypt — stores
-- the hashed value of the user's password. Name is collected at first
-- sign-in or pulled from Stripe customer data.
--
-- Auth flow: user submits email + password to /api/v1/auth/login.
-- Server looks up by email, bcrypt-verifies the password against
-- password_hash, creates a session if match.
--
-- For users who don't have a password yet (e.g. legacy accounts from
-- the magic-link prototype, or accounts created via Stripe before
-- their first login), password_hash is NULL. Those users can't log
-- in via password; they need to set one via the password-reset flow
-- (which uses the magic-link infrastructure we kept around for that
-- purpose).
CREATE TABLE IF NOT EXISTS users (
    id              SERIAL PRIMARY KEY,
    email           TEXT UNIQUE NOT NULL,
    password_hash   TEXT,                       -- bcrypt hash; nullable for legacy accounts
    name            TEXT,                       -- nullable; collected after first login
    created_at      BIGINT NOT NULL,
    last_login_at   BIGINT                      -- null until first successful login
);
CREATE INDEX IF NOT EXISTS idx_users_email_lower ON users(LOWER(email));

-- Existing-deploy migration: if the users table was created before
-- password_hash existed, add the column. Postgres makes this idempotent
-- via IF NOT EXISTS (supported since Postgres 9.6).
ALTER TABLE users ADD COLUMN IF NOT EXISTS password_hash TEXT;

-- Soft-delete column — admin "deactivates" a user instead of deleting,
-- so historical reviews/reports keep their authorship. Default true
-- so existing users stay active without an explicit migration value.
ALTER TABLE users ADD COLUMN IF NOT EXISTS is_active BOOLEAN NOT NULL DEFAULT TRUE;

-- Force-password-change flag — when admin creates a user with a temp
-- password, this is set to TRUE. The login flow checks it and requires
-- a password change before allowing access to any workspace.
ALTER TABLE users ADD COLUMN IF NOT EXISTS password_must_change BOOLEAN NOT NULL DEFAULT FALSE;

-- Stripe customer ID — populated when a user signs up via Stripe
-- subscription checkout. Lets us look up the user from any Stripe
-- webhook event (cancellation, payment failure, upgrade) without
-- needing the email round-trip. Nullable because not every user has
-- a Stripe customer (manual admin-created accounts, free-tier users).
-- Indexed for the cancellation webhook's user lookup.
ALTER TABLE users ADD COLUMN IF NOT EXISTS stripe_customer_id TEXT;
CREATE INDEX IF NOT EXISTS idx_users_stripe_customer ON users(stripe_customer_id) WHERE stripe_customer_id IS NOT NULL;

-- ── User roles — many-to-many; a user can hold several roles ──
-- Roles: 'subscriber', 'crew', 'met', 'admin'
-- A subscriber who is also Crew has two rows here.
-- New users are created with zero roles by default; admin grants roles
-- explicitly (or Stripe webhook grants 'subscriber' on payment).
CREATE TABLE IF NOT EXISTS user_roles (
    user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    role            TEXT NOT NULL,              -- subscriber|crew|met|admin
    granted_at      BIGINT NOT NULL,
    PRIMARY KEY (user_id, role)
);
CREATE INDEX IF NOT EXISTS idx_user_roles_user ON user_roles(user_id);

-- ── Magic-link tokens — short-lived single-use credentials ──
-- Lifecycle:
--   1. User submits email to /api/v1/auth/request-magic-link
--   2. Server generates 256-bit token, stores SHA-256 hash here
--   3. Server emails raw token (or logs it via stub) as part of a URL
--   4. User clicks link, frontend hits /api/v1/auth/verify with raw token
--   5. Server hashes the raw token, looks up this row by hash
--   6. If found, not expired, not used: mark used_at, create session
--   7. After 15 minutes the row is dead even if not used
CREATE TABLE IF NOT EXISTS magic_link_tokens (
    token_hash      TEXT PRIMARY KEY,           -- SHA-256 of the raw token, hex
    user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    created_at      BIGINT NOT NULL,
    expires_at      BIGINT NOT NULL,            -- created_at + 900 (15 min)
    used_at         BIGINT,                     -- null until consumed
    ip_requested    TEXT                        -- IP that requested the link; for abuse forensics
);
CREATE INDEX IF NOT EXISTS idx_magic_link_user ON magic_link_tokens(user_id);
CREATE INDEX IF NOT EXISTS idx_magic_link_expires ON magic_link_tokens(expires_at);

-- ── Sessions — long-lived, browser-cookie-backed ──
-- The user's browser holds the raw session ID in an HttpOnly cookie.
-- This table stores its SHA-256 hash. On every request, the server
-- recomputes the hash and looks up the row to confirm the session is
-- valid and find the user.
--
-- Two expiration windows:
--   - expires_at: absolute. 30 days from creation. Session dies regardless.
--   - idle_expires_at: 7 days from last activity. Refreshed on use.
-- This belt-and-suspenders approach means even infrequently-used
-- sessions eventually time out, but active users don't get logged out
-- mid-task.
CREATE TABLE IF NOT EXISTS sessions (
    session_id_hash  TEXT PRIMARY KEY,          -- SHA-256 of the raw session ID, hex
    user_id          INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    created_at       BIGINT NOT NULL,
    expires_at       BIGINT NOT NULL,           -- absolute: created_at + 30 days
    idle_expires_at  BIGINT NOT NULL,           -- idle: last_used + 7 days
    ip_created       TEXT,
    user_agent       TEXT
);
CREATE INDEX IF NOT EXISTS idx_sessions_user ON sessions(user_id);
CREATE INDEX IF NOT EXISTS idx_sessions_expires ON sessions(expires_at);

-- ── Login attempts — append-only audit log for password-based logins ──
-- Both successful and failed attempts get rows here. Two purposes:
--   1. Rate limiting: we count failed attempts per IP in the last 15
--      minutes to throttle brute-force attacks.
--   2. Audit forensics: incident response can ask "when did this email
--      get tried from this IP?"
-- We deliberately do NOT store the attempted password. Even hashed,
-- that would create a target for offline attacks if the table leaked.
-- The email is normalized to lowercase for consistent rate-limit lookups
-- (rate limit applies regardless of email case).
CREATE TABLE IF NOT EXISTS login_attempts (
    id              SERIAL PRIMARY KEY,
    email           TEXT NOT NULL,              -- lowercase
    ip              TEXT NOT NULL,
    succeeded       BOOLEAN NOT NULL,
    attempted_at    BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_login_attempts_ip_time ON login_attempts(ip, attempted_at DESC);
CREATE INDEX IF NOT EXISTS idx_login_attempts_email_time ON login_attempts(email, attempted_at DESC);

-- ── Stripe event ledger — webhook idempotency ──
-- Stripe retries failed webhooks (and sometimes succeeds twice through
-- network glitches). To avoid double-creating users / double-sending
-- emails, we record every event ID we've fully processed. The webhook
-- handler checks this table FIRST; if the event ID is already here,
-- we ack with 200 and skip the work.
--
-- Columns:
--   event_id    — Stripe's "evt_..." identifier, unique per event
--   event_type  — the type field ("checkout.session.completed", etc.)
--   processed_at — when we finished processing it
--   payload_kb  — first 1024 bytes of the JSON, for audit/debugging
--                (not the full payload — webhooks can be ~10KB and we
--                don't want to balloon the DB just for forensics)
CREATE TABLE IF NOT EXISTS stripe_events (
    event_id        TEXT PRIMARY KEY,
    event_type      TEXT NOT NULL,
    processed_at    BIGINT NOT NULL,
    payload_kb      TEXT
);
CREATE INDEX IF NOT EXISTS idx_stripe_events_type ON stripe_events(event_type, processed_at DESC);
"""


@contextmanager
def db():
    """Context-managed Postgres connection with dict row factory and autocommit.

    Returns a connection that:
      - Uses RealDictCursor so cur.fetchone() returns dicts keyed by column
        name (preserving the prior row['column'] access pattern from sqlite3.Row)
      - Has autocommit enabled, matching the prior SQLite behavior where
        every statement was committed immediately. Each call site that
        currently fires a single INSERT/UPDATE relies on this — switching
        to transaction mode would silently drop those writes.
      - Is closed on context exit, freeing the connection for reuse.

    Failure modes:
      - psycopg2.OperationalError: connection refused, DNS failure, wrong
        DATABASE_URL. Surface to caller; do not retry inside this function.
      - psycopg2.errors.UndefinedTable: tables haven't been created yet.
        _ensure_db() should have run init_db() on first request, but if it
        didn't, the caller sees a 500 and a clear error.

    Connection pooling deferred to future optimization. At current volume
    (~100 requests/day), creating a fresh connection per request is wasteful
    but correct. When traffic justifies it, add psycopg2.pool.ThreadedConnectionPool
    or front the database with pgbouncer.
    """
    conn = psycopg2.connect(DATABASE_URL, cursor_factory=psycopg2.extras.RealDictCursor)
    conn.autocommit = True
    try:
        yield conn
    finally:
        conn.close()


def init_db() -> None:
    """Create tables on first boot. Idempotent — safe to call every start.

    Passes the entire SCHEMA as a single multi-statement query to psycopg2.
    This works because:
      - psycopg2 supports multi-statement execute() when no parameter
        binding is used (our SCHEMA has no parameters — it's pure DDL).
      - All statements use CREATE ... IF NOT EXISTS, so the operation
        is idempotent. Running it twice creates nothing on the second run.
      - The Postgres server parses the entire string at once, so semicolons
        inside SQL comments are correctly ignored (a naive Python split()
        on semicolons would not handle this — and earlier comments in our
        SCHEMA do contain semicolons, like 'no roles by default; admin grants'
        which would otherwise break statement splitting).

    Reference: psycopg2 maintainer Federico Di Gregorio confirmed this
    pattern works as long as there are no SELECTs needing result retrieval
    (we have none — DDL only).
    """
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(SCHEMA)


# ════════════════════════════════════════════════════════════════════════════
# Helpers
# ════════════════════════════════════════════════════════════════════════════


def now_ts() -> int:
    """Current Unix timestamp. Seconds, integer. Used for all created_at fields."""
    return int(time.time())


def new_claim_token() -> str:
    """URL-safe 32-char token. Lives in the meteorologist's SMS claim link.
    secrets.token_urlsafe(24) gives ~32 chars of base64. Cryptographically
    random — guessing it is computationally infeasible, which is the auth
    story for v1 (no meteorologist login)."""
    return secrets.token_urlsafe(24)


# ════════════════════════════════════════════════════════════════════════════
# Auth helpers — token generation, hashing, cookie management, stub email
# ════════════════════════════════════════════════════════════════════════════
#
# These functions are the building blocks for the auth routes below.
# Kept together so the security-critical primitives are all in one place
# and easy to audit.
#
# Security design notes:
#   - All tokens generated by secrets.token_urlsafe(32), which gives
#     ~43 chars of cryptographically-random base64 (256 bits of entropy).
#     Guessing one is computationally infeasible (2^256 possibilities).
#   - Tokens and session IDs are hashed with SHA-256 before database
#     storage. The raw value goes to the user (in email or cookie);
#     the hash goes in the database. If the database leaks, the hashes
#     are useless — they can't be reversed to working credentials.
#   - SHA-256 is appropriate here (not bcrypt/argon2) because tokens are
#     random 256-bit values, not user-chosen passwords. Brute-forcing
#     SHA-256 of a 256-bit input is the same difficulty as guessing the
#     input itself, which is already infeasible. The argument for slow
#     hashes only applies when the input has low entropy (passwords).


# Magic link tokens expire 15 minutes after creation. Tight enough that a
# leaked email link can't be replayed long after the user discards it,
# loose enough that "I'll click this in a minute" works in practice.
MAGIC_LINK_TTL_SECONDS = 15 * 60

# Sessions expire 30 days after creation absolutely (regardless of activity).
# This is the upper bound on how long any single session can live.
SESSION_ABSOLUTE_TTL_SECONDS = 30 * 24 * 60 * 60

# Sessions also expire after 7 days of inactivity. Refreshed on each use.
# Belt-and-suspenders alongside the absolute expiration.
SESSION_IDLE_TTL_SECONDS = 7 * 24 * 60 * 60

# Cookie name for the session ID. Prefixed with __Host- in production for
# the strictest browser security (must be Secure, no Domain, path=/).
# In dev (HTTP localhost) we use a non-prefixed name because __Host-
# requires HTTPS.
SESSION_COOKIE_NAME = "wv_session"


def new_secure_token() -> str:
    """Generate a 256-bit cryptographically-random URL-safe token.

    Returns a ~43-character base64 string. Used for both magic link
    tokens (lives 15 minutes in the user's email) and session IDs
    (lives up to 30 days in a browser cookie). 256 bits is the
    industry-standard entropy for security-sensitive random values.

    secrets.token_urlsafe(32) gives 32 random bytes = 256 bits of entropy,
    encoded as URL-safe base64. NOT to be confused with token_urlsafe(24)
    used by new_claim_token() for meteorologist claim URLs — those are
    192-bit tokens, which is fine for non-credential URL secrets but a
    bit short for actual auth tokens.
    """
    return secrets.token_urlsafe(32)


def hash_token(raw_token: str) -> str:
    """SHA-256 hash of a token, returned as hex.

    Used to convert a raw user-facing token (in their email or browser
    cookie) into the form we store in the database. Look up by hash;
    never store the raw token.

    SHA-256 is appropriate here because tokens are random 256-bit
    values, not user-chosen passwords. We don't need slow hashing
    (bcrypt/argon2) — those are for low-entropy inputs.
    """
    return hashlib.sha256(raw_token.encode("utf-8")).hexdigest()


def is_valid_email(email: str) -> bool:
    """Best-effort email format check.

    Not RFC-perfect — that would require thousands of lines for negligible
    benefit. This catches obvious garbage (no @, no domain, too long)
    while accepting essentially any real address. The real validation
    happens when we try to send mail — if the address is malformed, SES
    will reject it, and the user retries.

    Returns True for plausibly-valid addresses, False for clearly invalid.
    """
    if not email or not isinstance(email, str):
        return False
    email = email.strip()
    if len(email) > 254:  # RFC 5321 max
        return False
    if "@" not in email:
        return False
    local, _, domain = email.rpartition("@")
    if not local or not domain:
        return False
    if "." not in domain:
        return False
    return True


def get_client_ip() -> str:
    """Return the IP address of the current request, taking into account
    proxy headers when running behind a load balancer.

    Render terminates TLS at its load balancer and forwards the original
    client IP in X-Forwarded-For. The leftmost value in that header is
    the original client; subsequent values are intermediate proxies.

    Falls back to request.remote_addr if no forwarding header (local dev,
    direct connections). Returns 'unknown' if neither is available.
    """
    forwarded = request.headers.get("X-Forwarded-For", "")
    if forwarded:
        # Take the leftmost (original client) address; strip whitespace.
        return forwarded.split(",")[0].strip()
    return request.remote_addr or "unknown"


def get_user_agent() -> str:
    """Return the User-Agent header of the current request, truncated.

    Browsers send full UA strings of 100-300 characters. We truncate to
    500 to bound the storage size while preserving enough detail to
    identify the browser/OS combination. Defaults to 'unknown' if missing.
    """
    ua = request.headers.get("User-Agent", "unknown")
    return ua[:500]


def _send_magic_link_email(email: str, magic_link_url: str, intent: str = "sign-in") -> bool:
    """Send a magic-link email to the user.

    DELIVERY: Resend (resend.com) via their HTTP API.
    Requires two environment variables on Render:
      RESEND_API_KEY  — server token from resend.com/api-keys
      EMAIL_FROM      — sender address at a verified domain
                        (e.g., noreply@weathervalet.ai)

    If RESEND_API_KEY is not set, falls back to printing the magic link
    to server logs (development/stub mode). This lets local dev and
    early testing continue to work even before Resend is wired up, and
    gives us a clean rollback if Resend has a transient outage.

    The `intent` argument toggles the email subject and body framing.
    All three intents share the same delivery path and visual style;
    only the wording changes:
      "sign-in"        → "Sign in to WeatherValet" (magic-link sign-in)
      "password-reset" → "Reset your WeatherValet password" (forgot password)
      "new-account"    → "Welcome to WeatherValet — set your password"
                         (new subscriber from Stripe webhook)

    Unknown intents fall back to "sign-in" framing.

    Returns True on success (or successful stub print), False on send
    failure. The auth flow does not block on this return value — a
    failed send is logged but doesn't reveal anything to the user
    (which would enable email-enumeration attacks).
    """
    api_key = os.environ.get("RESEND_API_KEY", "").strip()
    from_addr = os.environ.get("EMAIL_FROM", "").strip()

    # Stub fallback — no API key configured, just log the link.
    if not api_key or not from_addr:
        print(
            f"[MAGIC LINK STUB] To: {email}\n"
            f"[MAGIC LINK STUB] Link: {magic_link_url}\n"
            f"[MAGIC LINK STUB] (no RESEND_API_KEY set; logging only)",
            flush=True,
        )
        return True

    # Subject + body adapt based on the intent. The visual style of the
    # email is identical across all intents; only the wording changes.
    # Picking each piece independently (subject/heading/button/body/safety)
    # keeps the copy obvious and prevents accidental cross-wiring when
    # we later add new intents.
    if intent == "new-account":
        subject = "Welcome to WeatherValet \u2014 set your password"
        heading_text = "Welcome to WeatherValet"
        button_text = "Set your password"
        body_text = (
            "Thanks for subscribing. Tap the button below to set your "
            "password and access your account. This link expires in "
            "15 minutes and can only be used once."
        )
        safety_text = (
            "If you didn't sign up for WeatherValet, please reply to this "
            "email so we can look into it \u2014 no charges have been finalized "
            "until your account is activated."
        )
    elif intent == "password-reset":
        subject = "Reset your WeatherValet password"
        heading_text = "Reset your password"
        button_text = "Set a new password"
        body_text = (
            "Tap the button below to set a new password. This link expires "
            "in 15 minutes and can only be used once."
        )
        safety_text = (
            "If you didn't request this password reset, you can safely "
            "ignore this email \u2014 your password won't change."
        )
    else:
        # Default: "sign-in" (magic-link login)
        subject = "Sign in to WeatherValet"
        heading_text = "Sign in to WeatherValet"
        button_text = "Sign in to WeatherValet"
        body_text = (
            "Tap the button below to sign in. This link expires in 15 "
            "minutes and can only be used once."
        )
        safety_text = (
            "If you didn't request this sign-in link, you can safely "
            "ignore this email \u2014 no one can sign in without clicking "
            "the link above."
        )

    html_body = (
        '<div style="font-family: -apple-system, BlinkMacSystemFont, '
        '\'Segoe UI\', Roboto, sans-serif; max-width: 480px; margin: 0 auto; '
        'padding: 24px;">'
        f'<h2 style="color: #0E1116; font-size: 20px; margin: 0 0 16px;">'
        f'{heading_text}</h2>'
        f'<p style="color: rgba(15,17,22,0.75); font-size: 15px; line-height: 1.5;">'
        f'{body_text}</p>'
        f'<p style="margin: 28px 0;"><a href="{magic_link_url}" '
        'style="display: inline-block; background: #4169E1; color: #fff; '
        'padding: 12px 24px; border-radius: 8px; text-decoration: none; '
        f'font-weight: 600;">{button_text}</a></p>'
        '<p style="color: rgba(15,17,22,0.55); font-size: 13px; line-height: 1.5;">'
        'If the button doesn\'t work, copy and paste this link into your browser:'
        f'<br><span style="word-break: break-all;">{magic_link_url}</span></p>'
        '<p style="color: rgba(15,17,22,0.45); font-size: 12px; '
        'margin-top: 32px; border-top: 1px solid rgba(15,17,22,0.08); padding-top: 16px;">'
        f'{safety_text}</p>'
        '</div>'
    )
    text_body = (
        f"{heading_text}\n\n"
        f"{body_text}\n\n"
        f"{magic_link_url}\n\n"
        f"{safety_text}"
    )

    payload = json.dumps({
        "from": from_addr,
        "to": [email],
        "subject": subject,
        "html": html_body,
        "text": text_body,
    }).encode("utf-8")

    req = urllib.request.Request(
        "https://api.resend.com/emails",
        data=payload,
        method="POST",
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            # Cloudflare (sits in front of api.resend.com) sometimes blocks
            # requests with no User-Agent or with Python's default
            # "Python-urllib/3.x" UA as suspicious automation. A real-looking
            # UA gets through without the WAF interception that returns
            # Cloudflare's "error code: 1010".
            "User-Agent": "WeatherValet-Backend/1.0 (+https://weathervalet.ai)",
        },
    )

    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            # Resend returns 200 with a JSON body containing the email ID
            # on success. We don't inspect the body; status code is enough.
            if 200 <= resp.status < 300:
                return True
            print(
                f"[MAGIC LINK SEND] Resend returned status {resp.status} "
                f"for {email}",
                flush=True,
            )
            return False
    except urllib.error.HTTPError as e:
        # Most common: 422 (invalid email), 401 (bad API key), 403
        # (domain not verified). Log the body so we can debug from
        # Render logs without leaking through user-facing errors.
        body = ""
        try:
            body = e.read().decode("utf-8", errors="replace")[:500]
        except Exception:
            pass
        print(
            f"[MAGIC LINK SEND] Resend HTTPError {e.code} for {email}: {body}",
            flush=True,
        )
        return False
    except Exception as e:
        # Network errors, timeouts, etc. We don't want a transient
        # Resend outage to break the auth flow — log it and return False
        # so the calling code can decide what to do.
        print(
            f"[MAGIC LINK SEND] Unexpected error for {email}: {e!r}",
            flush=True,
        )
        return False


def _create_session(user_id: int, conn) -> str:
    """Create a new session for the given user. Returns the RAW session ID
    (the value that goes into the browser cookie).

    Internally:
      1. Generate a 256-bit random session ID
      2. Compute its SHA-256 hash
      3. Insert a sessions row with the hash, user_id, and timestamps
      4. Return the raw session ID for the caller to set as a cookie

    The caller is responsible for setting the cookie. This function
    just creates the database row and returns the value that needs to
    travel to the browser.

    The conn parameter accepts an already-open database connection so
    this function can be called inside an existing transaction (e.g.
    during /auth/verify where we also mark the magic-link token as used).
    """
    raw_session_id = new_secure_token()
    session_hash = hash_token(raw_session_id)
    now = now_ts()

    with conn.cursor() as cur:
        cur.execute(
            """INSERT INTO sessions
               (session_id_hash, user_id, created_at, expires_at,
                idle_expires_at, ip_created, user_agent)
               VALUES (%s, %s, %s, %s, %s, %s, %s)""",
            (
                session_hash,
                user_id,
                now,
                now + SESSION_ABSOLUTE_TTL_SECONDS,
                now + SESSION_IDLE_TTL_SECONDS,
                get_client_ip(),
                get_user_agent(),
            ),
        )

    return raw_session_id


def _set_session_cookie(response, raw_session_id: str):
    """Attach the session cookie to a Flask response with secure flags.

    Cookie flags explained:
      - HttpOnly: JavaScript on the page can't read this cookie. Prevents
        XSS-based session theft (an injected script can't steal the cookie).
      - Secure: only transmitted over HTTPS. Required when SameSite=None.
        Prevents passive interception on hostile networks.
      - SameSite=None: required for cross-site cookies in modern browsers.
        Our frontend (weathervalet.ai) and backend (wv-valet-backend.onrender.com)
        are different sites, so fetch() calls from frontend JS are
        cross-site requests. With SameSite=Lax (the safer default), the
        browser would refuse to send the cookie on these requests. We
        use SameSite=None to allow it, paired with Secure (required by
        browsers for SameSite=None) and HttpOnly (defense against XSS).
        CSRF protection comes from the fetch() API itself — by default
        fetch doesn't send cookies cross-origin unless we explicitly
        opt in with credentials:'include', AND the server returns
        Access-Control-Allow-Credentials:true. So an attacker site
        can't trick a browser into sending our cookie to us.
      - Path=/: cookie is sent for all paths on the domain.
      - Max-Age: cookie expires when the absolute session TTL expires.

    In dev (HTTP localhost) we drop Secure and use SameSite=Lax instead
    because SameSite=None requires Secure. Cross-site auth doesn't work
    in dev anyway because localhost isn't a public origin — you'd test
    by hitting the backend directly or using a tunnel like ngrok.
    """
    is_prod = bool(os.environ.get("PUBLIC_BASE_URL", "").startswith("https://"))
    response.set_cookie(
        SESSION_COOKIE_NAME,
        raw_session_id,
        max_age=SESSION_ABSOLUTE_TTL_SECONDS,
        httponly=True,
        secure=is_prod,
        samesite="None" if is_prod else "Lax",
        path="/",
    )
    return response


def _clear_session_cookie(response):
    """Clear the session cookie. Used on logout.

    Matches the flags used in _set_session_cookie so the browser sees
    the same cookie identity and replaces (rather than additionally
    setting a second cookie at a different scope).
    """
    is_prod = bool(os.environ.get("PUBLIC_BASE_URL", "").startswith("https://"))
    response.set_cookie(
        SESSION_COOKIE_NAME,
        "",
        max_age=0,
        httponly=True,
        secure=is_prod,
        samesite="None" if is_prod else "Lax",
        path="/",
    )
    return response


def _get_or_create_user(email: str, conn) -> int:
    """Look up a user by email (case-insensitive), or create one if missing.

    Returns the user's id (an integer). Used in the magic-link request
    flow: when someone enters an email we've never seen, we create the
    user account silently and email them a link. First-time sign-in
    and returning sign-in look identical from their perspective.

    Case handling: emails are stored as the user typed them but looked
    up case-insensitively via LOWER(email) indexed query. This means
    User@Example.com and user@example.com resolve to the same account,
    which is what real users expect (email addresses are not case-sensitive
    per RFC 5321, even though SMTP servers technically COULD treat them
    that way).
    """
    normalized = email.strip()
    now = now_ts()

    with conn.cursor() as cur:
        # Look up by lowercase email
        cur.execute(
            "SELECT id FROM users WHERE LOWER(email) = LOWER(%s)",
            (normalized,),
        )
        row = cur.fetchone()
        if row:
            return row["id"]

        # Doesn't exist — create the user
        cur.execute(
            """INSERT INTO users (email, created_at)
               VALUES (%s, %s)
               RETURNING id""",
            (normalized, now),
        )
        return cur.fetchone()["id"]


def _check_rate_limit_email(email: str, conn) -> bool:
    """Return True if this email is over its rate limit (request should be blocked).

    Limit: 5 magic-link requests per email per hour. Prevents an attacker
    from spamming a victim's inbox with login emails.

    Counts magic_link_tokens rows tied to this user that were created
    in the last hour. Since the tokens are tied to a user_id (which we
    only know after _get_or_create_user), this check runs AFTER user
    lookup but BEFORE creating a new token.
    """
    one_hour_ago = now_ts() - 3600
    with conn.cursor() as cur:
        cur.execute(
            """SELECT COUNT(*) as n FROM magic_link_tokens t
               JOIN users u ON u.id = t.user_id
               WHERE LOWER(u.email) = LOWER(%s) AND t.created_at >= %s""",
            (email, one_hour_ago),
        )
        row = cur.fetchone()
        return row["n"] >= 5


def _check_rate_limit_ip(ip: str, conn) -> bool:
    """Return True if this IP is over its rate limit (request should be blocked).

    Limit: 20 magic-link requests per IP per hour. Prevents an attacker
    from probing many accounts from a single machine.

    Counts magic_link_tokens rows that recorded this IP in the last hour.
    """
    one_hour_ago = now_ts() - 3600
    with conn.cursor() as cur:
        cur.execute(
            """SELECT COUNT(*) as n FROM magic_link_tokens
               WHERE ip_requested = %s AND created_at >= %s""",
            (ip, one_hour_ago),
        )
        row = cur.fetchone()
        return row["n"] >= 20


# ════════════════════════════════════════════════════════════════════════════
# Password hashing (bcrypt) — for username/password login
# ════════════════════════════════════════════════════════════════════════════
#
# Passwords are bcrypt-hashed before database storage. bcrypt is slow by
# design (configurable via "work factor", which is the cost parameter that
# controls how many rounds of hashing happen). This slowness is the point:
# brute-forcing 1 billion guesses takes ~hours instead of ~seconds.
#
# bcrypt's defaults are appropriate (work factor 12, which takes ~250ms
# to hash on modern hardware). We don't tune this — bcrypt's library
# maintainers update the defaults when hardware gets faster.

# Cost parameter — higher = slower = more secure but slower login.
# 12 is the industry-standard default. Don't change without performance testing.
BCRYPT_COST = 12


def hash_password(plain_password: str) -> str:
    """Hash a plain-text password with bcrypt. Returns the hash as a UTF-8 string.

    The returned hash includes the cost parameter and a random salt, so
    the same plain password produces different hashes on each call. This
    is a feature — it prevents rainbow-table attacks where an attacker
    pre-computes hashes of common passwords.

    Stored in users.password_hash as TEXT. The hash is ~60 characters,
    self-contained (no separate salt column needed).

    bcrypt has a 72-byte limit on the input password — anything longer
    is silently truncated. We don't enforce a max length on the form
    (users CAN type long passwords) but they should know that bcrypt
    only uses the first 72 bytes. In practice, no one types passwords
    over 50 characters, so this isn't a real issue.

    Usage:
        h = hash_password("hunter2")
        # Store h in users.password_hash
    """
    pw_bytes = plain_password.encode("utf-8")
    salt = bcrypt.gensalt(rounds=BCRYPT_COST)
    hashed = bcrypt.hashpw(pw_bytes, salt)
    return hashed.decode("utf-8")


def verify_password(plain_password: str, stored_hash: str) -> bool:
    """Check whether a plain-text password matches a stored bcrypt hash.

    Returns True on match, False otherwise. Constant-time comparison
    against timing attacks (bcrypt.checkpw uses hmac.compare_digest
    internally).

    Returns False (not raises) on any error — corrupt hash, encoding
    issues, etc. Callers should treat "False" as "password doesn't
    match" without distinguishing failure causes.

    Usage:
        if verify_password(submitted_password, user["password_hash"]):
            # Login successful
            ...
    """
    if not stored_hash:
        return False
    try:
        return bcrypt.checkpw(
            plain_password.encode("utf-8"),
            stored_hash.encode("utf-8"),
        )
    except (ValueError, TypeError):
        # Malformed stored hash — treat as no match.
        return False


def _check_rate_limit_login_ip(ip: str, conn) -> bool:
    """Return True if this IP has too many failed login attempts (block).

    Limit: 10 failed logins per IP per 15 minutes. Tighter than the
    magic-link rate limit because login attempts have a clearer
    "guessing" signature — repeated attempts from one IP usually mean
    someone is trying passwords.

    Note: we count from a NEW table (login_attempts) so failed logins
    don't pollute the magic_link_tokens table's rate limit logic.
    See the SCHEMA — login_attempts is added in this same change.
    """
    fifteen_min_ago = now_ts() - (15 * 60)
    with conn.cursor() as cur:
        cur.execute(
            """SELECT COUNT(*) as n FROM login_attempts
               WHERE ip = %s AND succeeded = false AND attempted_at >= %s""",
            (ip, fifteen_min_ago),
        )
        row = cur.fetchone()
        return row["n"] >= 10


def _log_login_attempt(email: str, ip: str, succeeded: bool, conn) -> None:
    """Record a login attempt (success or failure) for audit + rate limiting.

    Both successes and failures are logged. Successes help with audit
    forensics ("when did this user last log in?"). Failures power the
    rate limiter and help detect attack patterns.

    The email is stored lowercase for consistent rate-limit lookups.
    Note we DON'T store the attempted password — that would be a
    security disaster if the table ever leaked.
    """
    with conn.cursor() as cur:
        cur.execute(
            """INSERT INTO login_attempts (email, ip, succeeded, attempted_at)
               VALUES (%s, %s, %s, %s)""",
            (email.lower(), ip, succeeded, now_ts()),
        )


def _get_current_user() -> Optional[dict]:
    """Read the session cookie, validate it, return user info or None.

    Used by /auth/session, /auth/logout, and the require_auth decorator.
    Centralizes session-validation logic so we don't duplicate it across
    every protected endpoint.

    Returns a dict with the same shape as the verify endpoint's `user`
    field plus the roles list, or None if no valid session exists.

    Side effect: on successful validation, the session's idle_expires_at
    is refreshed to now + SESSION_IDLE_TTL_SECONDS. This means active
    users keep their sessions alive; idle users eventually time out.

    Why the side effect: without refreshing on each use, the idle timeout
    would be meaningless. Either we'd never time out (idle expiration
    set once at session creation), or we'd time out everyone after 7
    days regardless of activity. The refresh makes idle expiration
    behave the way users expect.

    Performance note: this writes to the database on every auth-checked
    request. At current scale (~100 req/day) that's negligible. At
    larger scale, batch the refresh (e.g., only refresh if last refresh
    was more than 1 hour ago) or move sessions to a faster store like
    Redis.

    Failure modes:
      - No cookie present: returns None (not an error)
      - Cookie present but no matching session row: returns None
        (could be: session was revoked, session expired and cleaned up,
        or cookie was forged)
      - Session row exists but expired: returns None, leaves the row
        for later cleanup
      - Database unreachable: raises psycopg2.OperationalError to caller
    """
    raw_session_id = request.cookies.get(SESSION_COOKIE_NAME)
    if not raw_session_id:
        return None

    session_hash = hash_token(raw_session_id)
    now = now_ts()

    with db() as conn:
        with conn.cursor() as cur:
            # Join session + user + roles in one query for efficiency
            cur.execute(
                """SELECT s.user_id, s.expires_at, s.idle_expires_at,
                          u.email, u.name, u.is_active
                   FROM sessions s
                   JOIN users u ON u.id = s.user_id
                   WHERE s.session_id_hash = %s""",
                (session_hash,),
            )
            row = cur.fetchone()

        if row is None:
            return None

        # Validate expiration
        if row["expires_at"] < now:
            return None
        if row["idle_expires_at"] < now:
            return None

        # Deactivated-account check (Phase 3). If a user was deactivated
        # mid-session, their session may not have been killed yet (race
        # between deactivation and the next request). Treat the session
        # as invalid here so EVERY authed endpoint (not just login) sees
        # the deactivation immediately. We also delete the session row so
        # subsequent requests short-circuit at the "no matching session"
        # check above.
        if not row.get("is_active", True):
            with conn.cursor() as cur:
                cur.execute(
                    "DELETE FROM sessions WHERE session_id_hash = %s",
                    (session_hash,),
                )
            print(
                f"[auth] session invalidated: deactivated user_id={row['user_id']}",
                flush=True,
            )
            return None

        # Refresh idle expiration (extend by SESSION_IDLE_TTL_SECONDS from now)
        # Only writes if we're actually extending — defensive against rare race
        # where two simultaneous requests both refresh.
        with conn.cursor() as cur:
            cur.execute(
                "UPDATE sessions SET idle_expires_at = %s WHERE session_id_hash = %s",
                (now + SESSION_IDLE_TTL_SECONDS, session_hash),
            )

        # Fetch user's roles
        with conn.cursor() as cur:
            cur.execute(
                "SELECT role FROM user_roles WHERE user_id = %s ORDER BY role",
                (row["user_id"],),
            )
            role_rows = cur.fetchall()

    return {
        "id": row["user_id"],
        "email": row["email"],
        "name": row["name"],
        "roles": [r["role"] for r in role_rows],
    }


def require_auth(view_func):
    """Decorator that ensures the request has a valid session.

    On success: attaches `request.user` (the dict from _get_current_user)
    and calls the wrapped view function.

    On failure: returns 401 JSON. The frontend should handle this by
    showing the sign-in modal.

    Usage:
        @app.get('/api/v1/account/profile')
        @require_auth
        def my_profile():
            return jsonify({'email': request.user['email']})

    Note: this decorator is for API endpoints that return JSON. For
    HTML page routes, you'd want a different pattern that redirects
    to a login page. We don't have HTML page auth in v1 — the admin
    pages still use HTTP Basic auth (separate code path).
    """
    from functools import wraps

    @wraps(view_func)
    def wrapper(*args, **kwargs):
        user = _get_current_user()
        if user is None:
            return jsonify({"ok": False, "error": "not-authenticated"}), 401
        # Stash user on the request object so the view can access it
        request.user = user
        return view_func(*args, **kwargs)

    return wrapper


def require_role(role_name: str):
    """Decorator factory that ensures the user has a specific role.

    Builds on require_auth. After confirming the user is logged in,
    checks their roles list for `role_name`.

    Usage:
        @app.get('/api/v1/met/queue')
        @require_role('met')
        def met_queue():
            ...

    A user with multiple roles (e.g. subscriber + admin) can access
    endpoints gated for either role.

    Returns 401 if not logged in, 403 if logged in without the role.
    Distinguishing these helps the frontend show the right message
    ("please sign in" vs "you don't have access to this").
    """
    from functools import wraps

    def decorator(view_func):
        @wraps(view_func)
        def wrapper(*args, **kwargs):
            user = _get_current_user()
            if user is None:
                return jsonify({"ok": False, "error": "not-authenticated"}), 401
            if role_name not in user["roles"]:
                return jsonify({"ok": False, "error": "forbidden"}), 403
            request.user = user
            return view_func(*args, **kwargs)
        return wrapper
    return decorator


def normalize_phone(raw: Optional[str]) -> Optional[str]:
    """Coerce '317-555-0123' / '(317) 555-0123' / '+13175550123' all to
    +13175550123. v1 assumes US numbers — for international, use the
    `phonenumbers` library and accept a country code from the form."""
    if not raw:
        return None
    digits = "".join(c for c in raw if c.isdigit())
    if len(digits) == 10:
        return "+1" + digits
    if len(digits) == 11 and digits.startswith("1"):
        return "+" + digits
    if raw.startswith("+") and len(digits) >= 10:
        return "+" + digits
    return None  # caller treats None as "invalid number, ask again"


def send_sms(to: str, body: str) -> bool:
    """Fire-and-log SMS via Twilio. Returns True on success.
    Failures are logged but never raised — SMS is best-effort, the request
    record in SQLite is the source of truth."""
    if not (TwilioClient and TWILIO_ACCOUNT_SID and TWILIO_AUTH_TOKEN and TWILIO_FROM_NUMBER):
        # Fallback for local dev — print to stdout so the developer can see the flow
        print(f"[sms-stub] to={to}\n{body}\n", flush=True)
        return True
    try:
        client = TwilioClient(TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN)
        msg = client.messages.create(body=body, from_=TWILIO_FROM_NUMBER, to=to)
        print(f"[sms] sent sid={msg.sid} to={to}", flush=True)
        return True
    except Exception as e:
        # Twilio errors come in many flavors; log the type, never crash the request
        print(f"[sms] FAILED to={to}: {type(e).__name__}: {e}", flush=True)
        return False


# ────────────────────────────────────────────────────────────────────────────
# Meteorologist Brief storage — read/merge/write the JSON file
# ────────────────────────────────────────────────────────────────────────────
#
# Storage model: a single JSON file at BRIEF_PATH. The Decision Engine reads
# it on every per-ticket call. The /admin/brief form writes to it.
#
# Multiple submissions per day MERGE rather than overwrite — a meteorologist
# might post a morning brief for Boone County, then add an afternoon update
# for Marion County, then revise their original Boone County call when new
# data comes in. The merge logic:
#
#   - Same region name + overlapping window → REPLACE the window
#   - Same region name + non-overlapping window → APPEND a new window
#   - New region name → APPEND a new region
#   - generated_at always updates to the latest submission time
#
# Concurrency: writes use atomic rename (write to .tmp, then rename) so a
# concurrent reader either gets the old file or the new file, never half-
# written JSON. Single-process Flask + SQLite WAL means we don't need
# explicit locking for our scale.


def _load_brief_for_edit() -> dict:
    """Load the current brief as a dict, or return a fresh empty structure.
    Never raises — corrupt files become empty briefs (logged to stderr)."""
    if not BRIEF_PATH.exists():
        return {
            "version": BRIEF_SCHEMA_VERSION,
            "generated_at": "",
            "date": datetime.now().strftime("%Y-%m-%d"),
            "meteorologist": "WeatherValet Meteorologist",
            "regions": [],
        }
    try:
        with BRIEF_PATH.open(encoding="utf-8") as f:
            data = json.load(f)
        # Coerce expected keys
        data.setdefault("version", BRIEF_SCHEMA_VERSION)
        data.setdefault("regions", [])
        data.setdefault("date", datetime.now().strftime("%Y-%m-%d"))
        data.setdefault("meteorologist", "WeatherValet Meteorologist")
        return data
    except (json.JSONDecodeError, OSError) as e:
        print(f"[brief] failed to read {BRIEF_PATH}: {e}", file=sys.stderr)
        return {
            "version": BRIEF_SCHEMA_VERSION,
            "generated_at": "",
            "date": datetime.now().strftime("%Y-%m-%d"),
            "meteorologist": "WeatherValet Meteorologist",
            "regions": [],
        }


def _save_brief_atomic(data: dict) -> None:
    """Write the brief to disk via a temp-file-and-rename atomic swap.
    Concurrent readers see the old file until the rename completes."""
    BRIEF_PATH.parent.mkdir(parents=True, exist_ok=True)
    tmp = BRIEF_PATH.with_suffix(BRIEF_PATH.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
        f.write("\n")
    tmp.replace(BRIEF_PATH)


def _merge_window(region: dict, new_window: dict) -> None:
    """In-place merge: if `new_window` overlaps an existing window for this
    region, replace it; otherwise append. Overlap is defined as same start
    OR same end OR fully contained — close enough for the human use case
    (no meteorologist will submit two windows that touch end-to-end and
    expect them merged into one)."""
    new_start = new_window.get("start", "")
    new_end = new_window.get("end", "")
    windows = region.setdefault("windows", [])
    for i, w in enumerate(windows):
        ws, we = w.get("start", ""), w.get("end", "")
        # Same exact bounds → replace
        if ws == new_start and we == new_end:
            windows[i] = new_window
            return
        # Strictly contained → replace the larger one
        if ws <= new_start and new_end <= we and (ws != new_start or new_end != we):
            windows[i] = new_window
            return
    windows.append(new_window)


def merge_brief_submission(submission: dict) -> dict:
    """Apply a single meteorologist submission to the on-disk brief.

    Submission shape (what the form posts):
        {
          "region_name": "Boone County, IN",
          "verdict": "dry",
          "start_time": "06:00",
          "end_time": "20:00",
          "summary": "High pressure ridge holds...",
          "confidence": "high",
          "notes": "HRRR shows scattered cells...",
          "meteorologist_name": "WeatherValet Meteorologist"  # optional
        }

    Returns the merged brief dict (also written to disk).
    """
    brief = _load_brief_for_edit()

    # Update metadata on every save
    brief["version"] = BRIEF_SCHEMA_VERSION
    brief["generated_at"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    brief["date"] = datetime.now().strftime("%Y-%m-%d")
    if submission.get("meteorologist_name"):
        brief["meteorologist"] = submission["meteorologist_name"]

    region_name = (submission.get("region_name") or "").strip()
    if not region_name:
        raise ValueError("region_name is required")

    # Find or create the region
    region = next(
        (r for r in brief["regions"] if r.get("name", "").lower() == region_name.lower()),
        None,
    )
    if region is None:
        region = {"name": region_name, "verdict": "unknown", "windows": [], "notes": ""}
        brief["regions"].append(region)

    # Update region-level fields
    verdict = (submission.get("verdict") or "").strip().lower()
    if verdict in {"dry", "wet", "mixed", "stormy", "clear"}:
        region["verdict"] = verdict

    # Notes are stamped per submission; we keep only the latest
    notes = (submission.get("notes") or "").strip()
    if notes:
        region["notes"] = notes

    # Build the window object and merge it in
    window = {
        "start": (submission.get("start_time") or "").strip(),
        "end": (submission.get("end_time") or "").strip(),
        "summary": (submission.get("summary") or "").strip(),
        "confidence": (submission.get("confidence") or "medium").strip().lower(),
    }
    if window["start"] and window["end"] and window["summary"]:
        _merge_window(region, window)

    _save_brief_atomic(brief)

    # Audit log: append a row to brief_submissions for every save. This is
    # what the Meteorologist Portal reads to show "your recent submissions"
    # — without this, we'd only have the current state of the brief file
    # and couldn't reconstruct who submitted what when.
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO brief_submissions
                       (submitted_at, meteorologist_name, region_name, verdict,
                        start_time, end_time, summary, confidence, notes)
                       VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)""",
                    (
                        now_ts(),
                        submission.get("meteorologist_name") or brief.get("meteorologist", "WeatherValet Meteorologist"),
                        region_name,
                        verdict if verdict in {"dry", "wet", "mixed", "stormy", "clear"} else "unknown",
                        window["start"], window["end"], window["summary"],
                        window["confidence"], submission.get("notes") or "",
                    ),
                )
    except Exception as e:
        # Audit logging is best-effort — never block a save because the
        # log table is unavailable. The brief file is the source of truth
        # for the customer-facing forecast pipeline; the audit log is
        # secondary metadata for the portal.
        print(f"[brief-audit] failed to log submission: {e}", file=sys.stderr)

    return brief


# ════════════════════════════════════════════════════════════════════════════
# Flask app
# ════════════════════════════════════════════════════════════════════════════


app = Flask(__name__)


# ────────────────────────────────────────────────────────────────────────────
# CORS — allow the static frontend to call us across origins.
# The prototype HTML lives on Netlify (or the user's local machine, or
# weathervalet.ai) and POSTs to this Flask backend on a different origin.
# Without CORS headers, the browser blocks the response. We allow our own
# frontend origins explicitly; we DON'T allow `*` because that would let
# any random site abuse our AI quota.
# ────────────────────────────────────────────────────────────────────────────

# Origins that are allowed to talk to this backend. The env var lets us add
# more without code changes — comma-separated. Localhost is included by
# default for local dev and for opening the prototype HTML directly via
# file:// (which sends a "null" Origin header — handled below).
_default_origins = "https://weathervalet.ai,https://www.weathervalet.ai,http://localhost:8000,http://localhost:8080"
ALLOWED_ORIGINS = set(
    o.strip() for o in os.environ.get("WV_ALLOWED_ORIGINS", _default_origins).split(",") if o.strip()
)


@app.after_request
def _add_cors_headers(response):
    """Attach CORS headers to every response when the origin is allowed.

    For most endpoints this is a no-op (Stripe webhooks and HTML pages don't
    need CORS), but for /api/v1/forecast/explain it's required so the
    browser will let our frontend read the response.
    """
    origin = request.headers.get("Origin", "")
    # `null` is what browsers send when the page is loaded via file://.
    # Allow it during prototype testing — remove before production.
    if origin in ALLOWED_ORIGINS or origin == "null":
        response.headers["Access-Control-Allow-Origin"] = origin
        response.headers["Access-Control-Allow-Methods"] = "GET, POST, OPTIONS"
        response.headers["Access-Control-Allow-Headers"] = "Content-Type"
        # Allow the browser to send/receive cookies on cross-origin requests.
        # Required for the auth flow: frontend (weathervalet.ai) calls
        # backend (wv-valet-backend.onrender.com), which sets a session
        # cookie via Set-Cookie. Without this header, the browser silently
        # drops the cookie. Without credentials:'include' on the frontend
        # fetch call, the browser doesn't send the cookie back on
        # subsequent requests.
        response.headers["Access-Control-Allow-Credentials"] = "true"
        response.headers["Access-Control-Max-Age"] = "3600"
        # Vary on Origin so caches don't serve the wrong CORS response
        response.headers["Vary"] = "Origin"
    return response


@app.route("/api/v1/forecast/explain", methods=["OPTIONS"])
def _forecast_explain_preflight():
    """Handle CORS preflight for the forecast endpoint.

    Browsers send OPTIONS before POST when the request has a JSON body.
    Returning 204 with the CORS headers (added by _add_cors_headers above)
    tells the browser the actual POST is allowed.
    """
    return ("", 204)


@app.get("/")
def _health_check():
    """Health check / friendly landing page.

    Render pings this to confirm the service is alive. Anyone who hits
    this URL in a browser sees a brief explanation of what's running here.
    Don't return sensitive details.
    """
    return jsonify({
        "service": "wv-valet-backend",
        "status": "ok",
        "endpoints": [
            "POST /api/v1/forecast/explain",
            "POST /api/v1/verification/checkout",
            "GET /meteorologist/home",
            "GET /admin/dashboard",
        ],
    })


@app.before_request
def _ensure_db():
    """Lazy schema init — runs once. Robust to first-boot and migrations."""
    if not getattr(app, "_db_inited", False):
        init_db()
        app._db_inited = True
        if stripe is not None and STRIPE_SECRET_KEY:
            stripe.api_key = STRIPE_SECRET_KEY


# ════════════════════════════════════════════════════════════════════════════
# AI Forecast Explainer — the secret-sauce paragraph
# ════════════════════════════════════════════════════════════════════════════
#
# This is the heart of WeatherValet's user experience. The frontend sends
# us the user's parsed plan + the resolved weather data; we call Gemini
# with a carefully designed prompt and return a 2-4 sentence paragraph
# that translates the numbers into how the weather will *feel* and *behave*
# for the user's specific activity.
#
# Why a server-side proxy: the Gemini API key is sensitive. If we put it
# in the frontend HTML, anyone who views source can steal it. So the
# frontend asks us; we ask Gemini; we return just the paragraph.
#
# Failure modes & fallbacks:
#   - Gemini API down or slow → return a short, honest fallback paragraph
#     so the ticket still works (the verdict + numbers are still useful)
#   - Gemini returns gibberish → same fallback
#   - Rate limit hit → same fallback
#   - User typed nonsense → still call Gemini; the prompt instructs it
#     to handle gracefully
#
# We do NOT cache responses by plan because every plan is unique and the
# weather data shifts hour by hour. Each call is fresh.
# ────────────────────────────────────────────────────────────────────────────

# Use urllib for the Gemini call — we don't want to add `requests` as a
# dependency just for one HTTP call. urllib is in the Python stdlib.
# (urllib.request and urllib.error are imported at the top of the file.)


# The system prompt is the most important text in this entire file.
# Edit with care. Each instruction is here for a specific reason —
# the comments explain why. When tuning, change one thing at a time
# and re-test the example queries (see test_explain_prompt.py).
EXPLAINER_SYSTEM_PROMPT = """You are WeatherValet, a weather concierge. Someone has handed you the keys to their plan and you're handing them back a clear, friendly answer about what the weather will feel like and how it will behave for their specific activity.

Your job: write a single short paragraph (2-4 sentences) that translates the weather data into how the weather will actually be experienced by this person, doing this specific thing, at this specific time and place. You will also assess whether the conditions actually warrant concern *for this specific activity* (more on that below).

WHAT KIND OF QUERY IS THIS?
The user might give you any of three kinds of input. Read the plan text and respond appropriately:

(1) A PLAN with an activity (most common): "Saturday wedding at 4 PM", "concrete pour Saturday morning", "baseball game tonight". Translate the weather into how it'll feel and behave for that specific activity.

(2) A QUESTION about the weather: "when will the rain stop?", "how windy will it get this evening?", "is the rain going to clear up?". Answer the question directly in the same friendly voice — give them the specific information they asked for. Use the weather data to give a real answer, not a generic paragraph.

(3) A "RIGHT NOW" snapshot: "weather right now", "what's it like outside", "current conditions". Describe what's happening at this moment in plain terms — temperature feel, sky, wind, whether it's raining — and add a brief note about whether anything's about to change in the next hour or two.

In all three cases: same voice, same length (2-4 sentences), same plain English. The only thing that changes is what you're answering.

VOICE
- Conversational, warm, knowledgeable. Like a friend who happens to know weather, sending a thoughtful text message.
- No greetings, no sign-offs, no "Here's what I think" — just the answer.
- Don't restate the verdict (Clear/Caution/Risk) — that's already shown above your paragraph. Don't say "the forecast is..." — be direct.
- Open with the activity by name when there is one. "Your lunch will be comfortable" or "The 4 PM wedding looks workable" — not "Conditions look workable for your plan" (that's a verdict echo, not a forecast). Use the activity word from the user's plan as soon as possible in the opening sentence. If they didn't name a specific activity ("outdoor stuff"), open with the time or place instead — "Saturday afternoon will be..." or "Lebanon will see..."
- Use plain English. "Light breeze" not "8 mph wind." "Comfortable in a t-shirt" not "78°F."
- Use the specific numbers only when they genuinely help (rain timing, dramatic temperature swings, answering questions that ask for numbers).

WHAT TO TALK ABOUT (for plans)
- How the temperature will feel for this specific activity (a baseball game vs. a wedding vs. a concrete pour all feel different at 78°F).
- How the wind, humidity, and sun will affect this person doing this thing.
- Anything practical: layers, sunscreen, water, timing tweaks, gear.
- If the user shared context about why this matters (frustration, history, stakes, "this is my third try"), acknowledge it naturally.

RAIN — BE PRECISE
- If rain is in the time window, say WHEN it starts and stops if possible. "Light rain looks likely from about 4:15 to 5:45" is useful. "40% chance of precipitation" is not.
- If asked WHEN rain will stop and you don't have exact end-time data, give the best estimate from what you have: "Looks like the rain should taper off in the next hour or two" rather than "I don't know."
- If no rain in the window, say so plainly: "No rain to worry about" or omit it.

CRITICAL GUARDRAILS — NEVER VIOLATE
- NEVER invent venue details. You don't know which way a baseball field faces, which side of a building has shade, where the trees are, where the sun will hit at the venue. Don't say "the breeze will be at your back" or "the sun will be in your eyes" or "right field will see drift" — you have no way to know.
- NEVER claim to see radar, satellite, or anything visual you weren't given.
- NEVER make up specific weather events (a thunderstorm, a microburst) that aren't in the data.
- NEVER mention specific landmarks, neighborhoods, or features unless they're in the user's plan text.
- NEVER reference other parts of the page. Don't say "the numbers below show...", "as you can see in the data...", "the tiles have the specifics", or anything that points the reader away from your paragraph. You're writing the only weather content this person reads. Describe weather directly. They can look at the data tiles themselves if they want the numbers.
- If the user's plan is vague ("outdoor stuff at 4 PM"), write a general but useful paragraph. Don't fabricate specifics.

OFF-TOPIC
- If the user's input isn't about weather at all (e.g., they typed "what's the meaning of life"), write a brief polite paragraph saying you're built for weather questions about specific outdoor plans, and suggest they tell you what they're doing, when, and where.
- Never engage with non-weather topics. Never role-play. Never pretend to be anything other than WeatherValet.

LENGTH
- 2-4 sentences. No more. No bullet points. No headers. Just the paragraph.

═══════════════════════════════════════════════════════════════════
ACTIVITY-AWARE VERDICT ASSESSMENT
═══════════════════════════════════════════════════════════════════
The user's ticket already shows a verdict pill (Clear / Caution / Risk) computed by rules. Those rules apply uniformly across all activities — they don't know whether the user is roofing a house or walking into church. Sometimes the rules over-flag a situation as Caution that's actually fine for the specific activity.

Your job in this section: assess whether the rule-based verdict matches reality FOR THIS SPECIFIC ACTIVITY. You can suggest a downgrade in the assessed_verdict field if the activity makes the conditions less concerning than the numbers suggest in isolation.

WHEN TO SUGGEST A DOWNGRADE (Caution → Clear):
- Walking from a parking lot into a building (church, store, restaurant, school)
- Spectating from covered seating
- Indoor events with brief outdoor exposure
- Activities that benefit from breeze (a hot picnic, an outdoor cookout in summer)
- Conditions where the only "concern" is a windier-than-average day with no precipitation, no extreme heat/cold, and no thunderstorms

WHEN TO HOLD THE VERDICT AS-IS (don't downgrade):
- Manual labor outdoors (roofing, concrete, painting, landscaping, construction)
- Drone operation, ballooning, sailing, kite-flying, or anything wind-sensitive
- Outdoor weddings/ceremonies with decorations or veils sensitive to wind
- Sports and physical activities affected by the conditions (cycling, running, golf)
- Photography or filming
- Anything where the user mentioned the weather concern themselves
- Temperature extremes (above 90°F or below 40°F) regardless of activity
- Any precipitation in the window
- Any active NWS alert

NEVER UPGRADE THE VERDICT. If the rules said Clear, you can only suggest Clear. If the rules said Caution, you can suggest Caution or Clear. If the rules said Risk, you can ONLY suggest Risk — never downgrade Risk to Caution or Clear, because Risk is the safety floor. The frontend will reject upgrades; this rule is for your reasoning.

═══════════════════════════════════════════════════════════════════
RESPONSE FORMAT — IMPORTANT
═══════════════════════════════════════════════════════════════════
Respond with TWO things separated by exactly this delimiter on its own line:
---VERDICT---

First, write the paragraph (2-4 sentences as described above).
Then on a new line, write exactly:
---VERDICT---
Then on the next line, write exactly one word: clear, caution, or risk.

Example response:
It'll be a comfortably warm afternoon for the wedding, with mostly clear skies and a gentle breeze. With low humidity, your guests will be quite comfortable, and there's no rain in sight to worry about.
---VERDICT---
clear

Do not write anything else after the verdict word. No explanation, no caveats, just the single word.
"""


def _build_explainer_user_message(payload: dict) -> str:
    """Assemble the user-facing prompt that gets sent alongside the system prompt.

    The payload is what the frontend sent us. We restructure it into a
    clean, predictable shape for the AI — no clever formatting tricks,
    just labeled fields the AI can read at a glance.
    """
    plan = (payload.get("plan") or "").strip() or "(not specified)"
    location = (payload.get("location") or "").strip() or "(not specified)"
    when = (payload.get("when") or "").strip() or "(not specified)"
    verdict = (payload.get("verdict") or "").strip() or "(unknown)"

    # Weather numbers — we only include what we have, and we label them
    # plainly so the AI doesn't have to guess what each value means.
    weather_lines = []
    w = payload.get("weather") or {}
    if "temperature_f" in w:
        weather_lines.append(f"Temperature: {w['temperature_f']}°F")
    if "feels_like_f" in w:
        weather_lines.append(f"Feels like: {w['feels_like_f']}°F")
    if "wind_mph" in w:
        weather_lines.append(f"Wind speed: {w['wind_mph']} mph")
    if "wind_gust_mph" in w:
        weather_lines.append(f"Wind gusts: up to {w['wind_gust_mph']} mph")
    if "humidity_pct" in w:
        weather_lines.append(f"Humidity: {w['humidity_pct']}%")
    if "cloud_cover_pct" in w:
        weather_lines.append(f"Cloud cover: {w['cloud_cover_pct']}%")
    if "precip_probability_pct" in w:
        weather_lines.append(f"Precipitation chance: {w['precip_probability_pct']}%")
    if "precip_amount_in" in w:
        weather_lines.append(f"Expected precipitation: {w['precip_amount_in']} inches")
    if w.get("rain_window"):
        # rain_window is a string like "4:15 PM to 5:45 PM" if rain is in the window
        weather_lines.append(f"Rain timing: {w['rain_window']}")
    weather_block = "\n".join(weather_lines) if weather_lines else "(no weather data provided)"

    return f"""USER'S PLAN
{plan}

WHEN
{when}

WHERE
{location}

RULE-BASED VERDICT (the pill above your paragraph — assess if it matches reality for this activity)
{verdict}

WEATHER DATA
{weather_block}

Write the paragraph (2-4 sentences, plain English, no venue specifics, no greeting or sign-off). Then on a new line, the delimiter ---VERDICT--- and on the next line your assessed verdict (clear, caution, or risk).
"""


def _call_gemini(system_prompt: str, user_message: str, timeout_s: int = 12) -> Optional[str]:
    """Make the actual HTTP call to Gemini and extract the text.

    Returns the generated text, or None on any failure. Failure paths:
      - No API key configured
      - Network error
      - Gemini returns non-200
      - Response shape unexpected (Google occasionally changes it)

    We log the failure mode but don't raise — the caller falls back to
    a hardcoded paragraph so the user always gets *something*.
    """
    if not GEMINI_API_KEY:
        return None

    body = {
        "contents": [
            {"role": "user", "parts": [{"text": user_message}]}
        ],
        "systemInstruction": {
            "parts": [{"text": system_prompt}]
        },
        "generationConfig": {
            "temperature": 0.7,        # warm but not wild — we want consistent voice
            "maxOutputTokens": 800,    # generous headroom; the actual paragraph is short
            "topP": 0.95,
            "candidateCount": 1,
            # Gemini 2.5 family models think internally before producing
            # output, and the thinking counts against maxOutputTokens. For
            # a 2-4 sentence paragraph, we don't need deep reasoning —
            # disable thinking so the entire token budget goes to the
            # actual output. (Older models ignore this field; safe to send.)
            "thinkingConfig": {"thinkingBudget": 0},
        },
        # Gemini's default safety filters are fine for our use case — we're
        # not asking for anything edgy. If they ever block legitimate weather
        # paragraphs, tune these down. For now: defaults.
    }

    url = f"{GEMINI_API_URL}?key={GEMINI_API_KEY}"
    req = urllib.request.Request(
        url,
        data=json.dumps(body).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            raw = resp.read().decode("utf-8")
            data = json.loads(raw)
    except urllib.error.HTTPError as e:
        # 429 = rate limited; 400 = bad request; 5xx = Google's problem.
        # Print to stderr so Render logs capture it for debugging.
        print(f"[gemini] HTTPError {e.code}: {e.read()[:300] if hasattr(e, 'read') else ''}", file=sys.stderr)
        return None
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        print(f"[gemini] network error: {e}", file=sys.stderr)
        return None
    except (ValueError, json.JSONDecodeError) as e:
        print(f"[gemini] bad json: {e}", file=sys.stderr)
        return None

    # Walk the response shape carefully — Google nests deeply.
    try:
        candidates = data.get("candidates") or []
        if not candidates:
            print(f"[gemini] no candidates: {str(data)[:300]}", file=sys.stderr)
            return None
        parts = candidates[0].get("content", {}).get("parts") or []
        if not parts:
            print(f"[gemini] no parts: {str(data)[:300]}", file=sys.stderr)
            return None
        text = parts[0].get("text", "").strip()
        if not text:
            return None
        return text
    except (KeyError, IndexError, TypeError) as e:
        print(f"[gemini] response shape: {e}", file=sys.stderr)
        return None


def _fallback_paragraph(payload: dict) -> str:
    """Honest one-sentence fallback when the AI is unavailable.

    Deliberately simple: we don't try to fake what the AI would say. We
    say "here's the snapshot" and let the verdict pill + numbers below
    do the rest. Better than a broken ticket.
    """
    verdict = (payload.get("verdict") or "").strip().lower()
    if verdict == "clear":
        return "Conditions look workable for your plan. Check the numbers below for the specifics."
    if verdict == "caution":
        return "There are a few things worth watching for your plan. The details are in the numbers below."
    if verdict == "risk":
        return "Conditions are stacked against this one. Take a careful look at the details below before committing."
    return "Here's the snapshot for your plan. The details are below."


# ──────────────────────────────────────────────────────────────────────────
# Mailchimp integration — email capture
# ──────────────────────────────────────────────────────────────────────────

def _call_mailchimp_add_member(email: str, tag: str, timeout_s: int = 10) -> tuple[bool, str]:
    """Add an email to the Mailchimp audience with a tag.

    Returns (success, message) tuple. On failure, message describes what
    went wrong; on success, message is a status indicator.

    Mailchimp's "members" endpoint adds OR updates a contact based on
    email. For new emails, status="subscribed" (no double-opt-in friction
    for our waitlist context). For existing emails, the endpoint returns
    400 with "Member Exists" — we treat that as a soft success (the
    email is in the list, which is what we wanted) and update tags.

    Auth: HTTP Basic. Username can be anything ("anystring" is fine);
    password is the full API key.
    """
    if not MAILCHIMP_API_KEY or not MAILCHIMP_AUDIENCE_ID:
        return (False, "mailchimp not configured")

    # Normalize the tag — fall back to general-interest if unknown
    if tag not in MAILCHIMP_VALID_TAGS:
        tag = "general-interest"

    url = f"{MAILCHIMP_API_URL}/lists/{MAILCHIMP_AUDIENCE_ID}/members"
    body = {
        "email_address": email,
        "status": "subscribed",
        "tags": [tag],
    }

    # HTTP Basic auth header
    import base64
    auth_str = base64.b64encode(f"anystring:{MAILCHIMP_API_KEY}".encode("utf-8")).decode("ascii")

    req = urllib.request.Request(
        url,
        data=json.dumps(body).encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Basic {auth_str}",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as resp:
            resp.read()  # drain the body; we don't need the content on success
            return (True, "added")
    except urllib.error.HTTPError as e:
        # Read the error body to check for "Member Exists" — that's a
        # soft-success: the email was already in the list, no harm done.
        err_body = ""
        try:
            err_body = e.read().decode("utf-8", errors="replace")
        except Exception:
            pass

        if e.code == 400 and "Member Exists" in err_body:
            # Already on the list. Try to update their tags so this
            # capture context is recorded (e.g. they previously joined
            # via crew-applicant and now they hit pricing-pro-single).
            _mailchimp_update_tag(email, tag, timeout_s=timeout_s)
            return (True, "already-subscribed")

        # Other HTTP errors: log and return failure with status
        print(f"[mailchimp] HTTPError {e.code}: {err_body[:300]}", file=sys.stderr)
        return (False, f"mailchimp returned {e.code}")
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        print(f"[mailchimp] network error: {e}", file=sys.stderr)
        return (False, "mailchimp unreachable")
    except Exception as e:
        print(f"[mailchimp] unexpected error: {e}", file=sys.stderr)
        return (False, "mailchimp call failed")


def _mailchimp_update_tag(email: str, tag: str, timeout_s: int = 10) -> None:
    """Update tags on an existing Mailchimp member.

    Used when "Member Exists" is returned from the add call — we still
    want to record this capture context. Failure is soft-logged; we
    never raise.
    """
    # Mailchimp identifies members by MD5 hash of lowercased email
    import hashlib
    member_hash = hashlib.md5(email.lower().encode("utf-8")).hexdigest()
    url = f"{MAILCHIMP_API_URL}/lists/{MAILCHIMP_AUDIENCE_ID}/members/{member_hash}/tags"

    body = {"tags": [{"name": tag, "status": "active"}]}

    import base64
    auth_str = base64.b64encode(f"anystring:{MAILCHIMP_API_KEY}".encode("utf-8")).decode("ascii")

    req = urllib.request.Request(
        url,
        data=json.dumps(body).encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Basic {auth_str}",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_s):
            pass  # 204 No Content on success
    except Exception as e:
        # Soft-log; don't disrupt the capture flow
        print(f"[mailchimp] tag-update failed: {e}", file=sys.stderr)


@app.route("/api/v1/email-capture", methods=["OPTIONS"])
def _email_capture_preflight():
    """CORS preflight for the email capture endpoint.

    Same pattern as _forecast_explain_preflight — browsers send OPTIONS
    before POST when there's a JSON body; we return 204 and the after_request
    hook attaches the CORS headers.
    """
    return ("", 204)


@app.post("/api/v1/email-capture")
def email_capture():
    """Capture an email submission and add it to the Mailchimp audience.

    Expected JSON body:
        {
          "email": "person@example.com",
          "source": "pricing-pro-single" | "crew-applicant" | etc.
        }

    The `source` field tells Mailchimp WHICH CTA brought this email in,
    so we can email different audiences later (e.g. "Pro Single tier is
    now live" goes only to people tagged pricing-pro-single).

    Returns:
        200 with {"ok": true, "status": "added"|"already-subscribed"}
        400 if email is missing or invalid
        503 if Mailchimp is unreachable (frontend can retry)

    NEVER returns Mailchimp's API key or other secrets in any path.
    """
    data = request.get_json(silent=True) or {}
    email = (data.get("email") or "").strip().lower()
    source = (data.get("source") or "general-interest").strip()

    # Basic email validation — Mailchimp will also validate, but rejecting
    # obvious garbage here saves API calls and gives faster feedback.
    if not email or "@" not in email or "." not in email.split("@")[-1]:
        return jsonify({"ok": False, "error": "invalid-email"}), 400

    if len(email) > 254:  # RFC 5321 max
        return jsonify({"ok": False, "error": "email-too-long"}), 400

    ok, status = _call_mailchimp_add_member(email, source)

    if ok:
        return jsonify({"ok": True, "status": status}), 200

    # Mailchimp unreachable or configuration error.
    # 503 = the frontend can retry, this isn't a user error.
    return jsonify({"ok": False, "error": status}), 503


# ════════════════════════════════════════════════════════════════════════════
# Authentication — magic link login, server-side sessions
# ════════════════════════════════════════════════════════════════════════════
#
# Two endpoints for the v1 (request + verify) plus the stub email function
# above. Session/logout/workspaces endpoints come next.
#
# Flow:
#   1. User enters email on the homepage → frontend POSTs to /request-magic-link
#   2. Server emails a one-time link of form: /auth/verify?token=<raw>
#   3. User clicks link → frontend GETs /auth/verify with the token
#   4. Server validates, marks token used, creates session, sets cookie
#   5. User is now logged in; cookie travels with future requests

@app.route("/api/v1/auth/request-magic-link", methods=["OPTIONS"])
def _auth_request_magic_link_preflight():
    """CORS preflight handler — same pattern as the email-capture endpoint."""
    return ("", 204)


@app.post("/api/v1/auth/request-magic-link")
def auth_request_magic_link():
    """Accept an email, send a one-time magic link to it.

    Returns 200 with the same response regardless of whether the email
    matches a real account. This prevents account enumeration — an
    attacker can't probe which emails are registered by watching the
    response.

    Request body:
        {"email": "person@example.com"}

    Returns:
        200 {"ok": true, "message": "If that's a valid email, check your inbox"}
        400 {"ok": false, "error": "invalid-email"}     — malformed
        429 {"ok": false, "error": "rate-limited"}      — too many requests

    Security notes:
      - Magic links expire in 15 minutes (MAGIC_LINK_TTL_SECONDS)
      - Tokens are 256-bit random, SHA-256 hashed before DB storage
      - Rate limited: max 5 requests per email per hour, 20 per IP per hour
      - Stubbed email goes to server logs in dev; real SES in production
    """
    data = request.get_json(silent=True) or {}
    email = (data.get("email") or "").strip()
    # Optional: frontend passes "password-reset" to flag this as a
    # password-reset (not a plain sign-in). The intent is round-tripped
    # into the magic-link URL itself so the frontend knows what to do
    # AFTER verify (just sign in vs. show set-password form).
    # Acceptable values: "sign-in" (default), "password-reset".
    intent = (data.get("intent") or "sign-in").strip()
    if intent not in ("sign-in", "password-reset", "new-account"):
        intent = "sign-in"

    if not is_valid_email(email):
        return jsonify({"ok": False, "error": "invalid-email"}), 400

    client_ip = get_client_ip()

    with db() as conn:
        # Check IP rate limit FIRST, before we even look up the user.
        # An attacker hammering this endpoint with random emails should
        # get blocked at the IP level without us doing user lookups.
        if _check_rate_limit_ip(client_ip, conn):
            print(f"[auth] rate-limit-ip blocked: {client_ip}", flush=True)
            # Return same response as success to avoid leaking that this
            # IP is being rate-limited. The user will see "check your email"
            # but no email arrives. They'll retry; if still blocked, eventually
            # the IP rate-limit window passes.
            return jsonify({
                "ok": True,
                "message": "If that's a valid email, check your inbox",
            }), 200

        # Look up the user (create if missing). After this, user_id is set
        # regardless of whether this was a new signup or returning user.
        # The user account exists either way; only roles differ.
        user_id = _get_or_create_user(email, conn)

        # Now check email rate limit (using user_id we just established)
        if _check_rate_limit_email(email, conn):
            print(f"[auth] rate-limit-email blocked: {email}", flush=True)
            return jsonify({
                "ok": True,
                "message": "If that's a valid email, check your inbox",
            }), 200

        # Generate a fresh token and store its hash
        raw_token = new_secure_token()
        token_hash = hash_token(raw_token)
        now = now_ts()

        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO magic_link_tokens
                   (token_hash, user_id, created_at, expires_at, ip_requested)
                   VALUES (%s, %s, %s, %s, %s)""",
                (token_hash, user_id, now, now + MAGIC_LINK_TTL_SECONDS, client_ip),
            )

    # Build the magic link URL. Uses FRONTEND_BASE_URL so the link points
    # to the static site (weathervalet.ai), not the backend (api.weathervalet.ai).
    # The frontend has a JS handler that detects this URL pattern and calls
    # back to the backend's /api/v1/auth/verify endpoint.
    #
    # URL pattern: /?auth=verify&token=<raw>
    # We use query params on the root path (not /auth/verify path) because
    # the static site doesn't have routing infrastructure to map arbitrary
    # paths to index.html. Future polish: add a Render Static rewrite rule
    # mapping /auth/verify → /index.html, then use the cleaner path-based URL.
    base = os.environ.get("FRONTEND_BASE_URL", "https://weathervalet.ai")
    # URL pattern: /?auth=verify&token=<raw>&intent=<sign-in|password-reset>
    # The intent is what the frontend reads to know whether to show
    # "set new password" form after verify, or just sign the user in.
    magic_link_url = f"{base}/?auth=verify&token={raw_token}&intent={intent}"

    # Send the email (or log it via stub during development)
    _send_magic_link_email(email, magic_link_url, intent=intent)

    # Audit log — record that we issued a link. Useful for debugging
    # ("did the link actually get sent?") and for security forensics.
    print(
        f"[auth] magic-link issued: email={email} user_id={user_id} "
        f"ip={client_ip} expires_in={MAGIC_LINK_TTL_SECONDS}s",
        flush=True,
    )

    return jsonify({
        "ok": True,
        "message": "If that's a valid email, check your inbox",
    }), 200


# ── Password login (primary auth path) ──
@app.route("/api/v1/auth/login", methods=["OPTIONS"])
def _auth_login_preflight():
    """CORS preflight for the login endpoint."""
    return ("", 204)


@app.post("/api/v1/auth/login")
def auth_login():
    """Username/password login — the primary auth path.

    Request body:
        {"email": "person@example.com", "password": "their-password"}

    Returns:
        200 {"ok": true, "user": {...}, "workspaces": [...]}  + session cookie
        400 {"ok": false, "error": "missing-credentials"}
        401 {"ok": false, "error": "invalid-credentials"}
            (same response for "no such user", "wrong password", and
             "user has no password set yet" — prevents enumeration)
        429 {"ok": false, "error": "rate-limited"}

    Security properties:
      - bcrypt password verification (constant-time, slow by design)
      - Generic 401 for all failure modes (no enumeration)
      - Rate limited: 10 failed attempts per IP per 15 min
      - All attempts logged (success + failure) for audit forensics
      - Session cookie uses same flags as magic-link verify path
        (HttpOnly, Secure in prod, SameSite=None for cross-site)

    Sets the same session cookie as /auth/verify. After successful
    login, subsequent /auth/session calls return the user info.
    """
    data = request.get_json(silent=True) or {}
    email = (data.get("email") or "").strip()
    password = data.get("password") or ""

    if not email or not password:
        return jsonify({"ok": False, "error": "missing-credentials"}), 400

    if not is_valid_email(email):
        return jsonify({"ok": False, "error": "invalid-credentials"}), 401

    client_ip = get_client_ip()
    now = now_ts()

    with db() as conn:
        # Rate limit check FIRST — before we do any work that could leak
        # information through timing analysis.
        if _check_rate_limit_login_ip(client_ip, conn):
            print(f"[auth] login rate-limit blocked: ip={client_ip}", flush=True)
            return jsonify({"ok": False, "error": "rate-limited"}), 429

        # Look up the user by lowercase email
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, email, name, password_hash, is_active
                   FROM users WHERE LOWER(email) = LOWER(%s)""",
                (email,),
            )
            user_row = cur.fetchone()

        # Verify password. We do this regardless of whether the user
        # exists, to make timing-based user enumeration harder. If no
        # user, we still call verify_password with a dummy hash so the
        # bcrypt computation runs (~250ms) before we return 401.
        if user_row is None:
            # Dummy bcrypt check to make timing similar to the real path.
            # The hash here is a known-good bcrypt output of "x", so the
            # comparison runs but never matches the real submitted password.
            verify_password(password, "$2b$12$KIXxPfnxJ.dummy.hash.value.for.timing.")
            # Log the failed attempt
            _log_login_attempt(email, client_ip, False, conn)
            print(f"[auth] login failed: no-such-user email={email} ip={client_ip}", flush=True)
            return jsonify({"ok": False, "error": "invalid-credentials"}), 401

        # User exists. Check password.
        stored_hash = user_row["password_hash"]
        if not stored_hash:
            # User exists but has no password set. This happens for
            # legacy accounts (magic-link era) or Stripe-created accounts
            # before the user sets their initial password. They need to
            # use the password-reset flow to set one.
            _log_login_attempt(email, client_ip, False, conn)
            print(f"[auth] login failed: no-password-set user_id={user_row['id']} ip={client_ip}", flush=True)
            return jsonify({"ok": False, "error": "invalid-credentials"}), 401

        if not verify_password(password, stored_hash):
            _log_login_attempt(email, client_ip, False, conn)
            print(f"[auth] login failed: wrong-password user_id={user_row['id']} ip={client_ip}", flush=True)
            return jsonify({"ok": False, "error": "invalid-credentials"}), 401

        # Deactivated-account check. Comes AFTER password verification so
        # an attacker probing for valid emails can't distinguish "wrong
        # password" from "valid password on deactivated account" via timing
        # or response patterns. The user (who actually has the right
        # password) gets a clear error, attackers get the same 401 as any
        # other failure.
        if not user_row.get("is_active", True):
            _log_login_attempt(email, client_ip, False, conn)
            print(
                f"[auth] login blocked: deactivated user_id={user_row['id']} "
                f"email={email} ip={client_ip}",
                flush=True,
            )
            return jsonify({"ok": False, "error": "account-deactivated"}), 403

        # Success — log it, update last_login_at, create session, fetch roles
        _log_login_attempt(email, client_ip, True, conn)
        with conn.cursor() as cur:
            cur.execute(
                "UPDATE users SET last_login_at = %s WHERE id = %s",
                (now, user_row["id"]),
            )
            cur.execute(
                "SELECT role FROM user_roles WHERE user_id = %s ORDER BY role",
                (user_row["id"],),
            )
            role_rows = cur.fetchall()

        # Create the session (inserts a row, returns the raw session ID)
        raw_session_id = _create_session(user_row["id"], conn)

    roles = [r["role"] for r in role_rows]
    workspaces = _roles_to_workspaces(roles)

    response = jsonify({
        "ok": True,
        "user": {
            "id": user_row["id"],
            "email": user_row["email"],
            "name": user_row["name"],
        },
        "workspaces": workspaces,
    })
    _set_session_cookie(response, raw_session_id)

    print(
        f"[auth] login succeeded: user_id={user_row['id']} email={email} "
        f"roles={roles} ip={client_ip}",
        flush=True,
    )

    return response


@app.get("/api/v1/auth/verify")
def auth_verify():
    """Consume a magic link. Token comes from query param.

    Steps:
      1. Read the raw token from the query string
      2. Compute its SHA-256 hash
      3. Look up magic_link_tokens by hash
      4. Verify: not expired, not used
      5. Mark used (set used_at)
      6. Create a new session for the user
      7. Set the session cookie
      8. Return user info + workspaces (frontend decides where to route)

    Returns:
        200 {"ok": true, "user": {...}, "workspaces": [...]}  + session cookie set
        400 {"ok": false, "error": "missing-token"}
        401 {"ok": false, "error": "invalid-token"}            — not found
        410 {"ok": false, "error": "expired-token"}            — past expiry
        410 {"ok": false, "error": "already-used"}             — single-use enforcement

    The frontend uses the workspaces list to route the user:
      - 0 workspaces → "your account isn't set up yet, contact support"
      - 1 workspace  → redirect directly to that workspace
      - 2+ workspaces → show workspace picker modal
    """
    raw_token = request.args.get("token", "").strip()
    if not raw_token:
        return jsonify({"ok": False, "error": "missing-token"}), 400

    token_hash = hash_token(raw_token)
    now = now_ts()

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT t.user_id, t.expires_at, t.used_at,
                          u.email, u.name, u.is_active
                   FROM magic_link_tokens t
                   JOIN users u ON u.id = t.user_id
                   WHERE t.token_hash = %s""",
                (token_hash,),
            )
            row = cur.fetchone()

        if row is None:
            # No matching token. Could be: never issued, already deleted,
            # forged, or someone clicked an old link after the row was
            # cleaned up. We don't distinguish — all return the same error.
            print(f"[auth] verify failed: no token match (hash={token_hash[:8]}...)", flush=True)
            return jsonify({"ok": False, "error": "invalid-token"}), 401

        if row["used_at"] is not None:
            # Token was previously consumed. Magic links are single-use.
            print(f"[auth] verify failed: already-used (user_id={row['user_id']})", flush=True)
            return jsonify({"ok": False, "error": "already-used"}), 410

        if row["expires_at"] < now:
            # Token aged out.
            print(f"[auth] verify failed: expired (user_id={row['user_id']})", flush=True)
            return jsonify({"ok": False, "error": "expired-token"}), 410

        # Deactivated-account check. If the user was deactivated between
        # link issuance and click, refuse the sign-in. We also burn the
        # token (mark used) so an attacker who intercepted the link can't
        # replay it after a potential reactivation. The user can request
        # a fresh link after reactivation.
        if not row.get("is_active", True):
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE magic_link_tokens SET used_at = %s WHERE token_hash = %s",
                    (now, token_hash),
                )
            print(
                f"[auth] verify blocked: deactivated user_id={row['user_id']} "
                f"email={row['email']}",
                flush=True,
            )
            return jsonify({"ok": False, "error": "account-deactivated"}), 403

        # Token is valid. Mark it used and create a session.
        with conn.cursor() as cur:
            cur.execute(
                "UPDATE magic_link_tokens SET used_at = %s WHERE token_hash = %s",
                (now, token_hash),
            )
            # Update user's last_login_at
            cur.execute(
                "UPDATE users SET last_login_at = %s WHERE id = %s",
                (now, row["user_id"]),
            )
            # Fetch user's roles to return to the frontend
            cur.execute(
                "SELECT role FROM user_roles WHERE user_id = %s ORDER BY role",
                (row["user_id"],),
            )
            role_rows = cur.fetchall()

        # Create the session (inserts a row, returns the raw session ID)
        raw_session_id = _create_session(row["user_id"], conn)

    # Build response with user info and workspace list
    roles = [r["role"] for r in role_rows]
    workspaces = _roles_to_workspaces(roles)

    response = jsonify({
        "ok": True,
        "user": {
            "id": row["user_id"],
            "email": row["email"],
            "name": row["name"],
        },
        "workspaces": workspaces,
    })
    _set_session_cookie(response, raw_session_id)

    print(
        f"[auth] verify succeeded: user_id={row['user_id']} email={row['email']} "
        f"roles={roles} ip={get_client_ip()}",
        flush=True,
    )

    return response


# ── Set or change password (used by password-reset flow) ──
@app.route("/api/v1/auth/set-password", methods=["OPTIONS"])
def _auth_set_password_preflight():
    """CORS preflight."""
    return ("", 204)


@app.post("/api/v1/auth/set-password")
def auth_set_password():
    """Set a new password for the currently signed-in user.

    Used as the second step of the password-reset flow:
      1. User clicks magic link in their email
      2. Frontend calls /api/v1/auth/verify → user is now signed in
      3. Frontend shows "Set a new password" form
      4. Frontend POSTs {"new_password": "..."} to THIS endpoint
      5. Backend hashes + stores the password, clears password_must_change
      6. User is now signed in AND has a fresh password

    Authentication: session cookie (the verify step created it). We
    deliberately do NOT require the old password — this endpoint is
    used precisely when the user has forgotten or never set a password.
    A session cookie already proves they hold the magic-link token,
    which was emailed to the verified address; that's the authentication.

    Request body:
        {"new_password": "their-chosen-password"}

    Returns:
        200 {"ok": true}
        400 {"ok": false, "error": "password-too-short"}
        400 {"ok": false, "error": "missing-fields"}
        401 {"ok": false, "error": "not-authenticated"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}
    new_password = (data.get("new_password") or "")

    if not new_password:
        return jsonify({"ok": False, "error": "missing-fields"}), 400

    # Same minimum as the admin set-password endpoint (8 chars). If you
    # want to lift this later, do it in one place: this endpoint plus
    # the admin one. Frontend should enforce it too for UX.
    if len(new_password) < 8:
        return jsonify({"ok": False, "error": "password-too-short"}), 400

    new_hash = hash_password(new_password)
    user_id = user["id"]

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE users
                   SET password_hash = %s,
                       password_must_change = FALSE
                   WHERE id = %s""",
                (new_hash, user_id),
            )

    print(
        f"[auth] set-password succeeded: user_id={user_id} ip={get_client_ip()}",
        flush=True,
    )

    return jsonify({"ok": True}), 200


def _roles_to_workspaces(roles: list) -> list:
    """Convert a list of role names into workspace metadata for the frontend.

    Each workspace dict has:
      role:  the role name (subscriber|crew|met|admin)
      label: the human-readable label shown in the picker
      url:   where to route the user after they pick this workspace

    Note: the URLs here are placeholders for now. Once Phase 4 (frontend
    integration) wires up the actual workspace routes, these point at
    the real auth-gated pages. For v1 they're the same as the prototype
    simulation routes.
    """
    workspace_map = {
        "subscriber": {
            "label": "Subscriber",
            "url": "/portal",
        },
        "crew": {
            "label": "Valet Crew",
            "url": "/crew",
        },
        "met": {
            "label": "Meteorologist",
            "url": "/meteorologist",
        },
        "admin": {
            "label": "Admin",
            "url": "/admin/dashboard",
        },
    }
    workspaces = []
    for role in roles:
        if role in workspace_map:
            workspaces.append({
                "role": role,
                "label": workspace_map[role]["label"],
                "url": workspace_map[role]["url"],
            })
    return workspaces


# ── Session inspection — what the frontend calls on every page load ──
@app.get("/api/v1/auth/session")
def auth_session():
    """Return info about the currently-logged-in user.

    Reads the session cookie, validates it, returns the same shape as
    /auth/verify (user info + workspaces). Or 401 if not logged in.

    Returns:
        200 {"ok": true, "user": {...}, "workspaces": [...]}
        401 {"ok": false, "error": "not-authenticated"}

    This is what the frontend calls on every page load to determine
    whether to show "Sign in" or "Welcome back, [name]". It also
    refreshes the session's idle expiration as a side effect (via
    _get_current_user).

    NOT decorated with @require_auth because we want to return a clean
    401 instead of the decorator's generic 401. Same outcome, different
    code path for clarity.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    workspaces = _roles_to_workspaces(user["roles"])
    return jsonify({
        "ok": True,
        "user": {
            "id": user["id"],
            "email": user["email"],
            "name": user["name"],
        },
        "workspaces": workspaces,
    }), 200


# ── Logout — destroys the current session ──
@app.post("/api/v1/auth/logout")
def auth_logout():
    """Destroy the current session and clear the cookie.

    Returns:
        200 {"ok": true}

    Always returns 200, even if no session existed. We don't reveal
    session state in error responses — an attacker probing the endpoint
    can't tell whether they hit a real session or a forged one.

    Side effects:
      - Deletes the sessions row by hash
      - Clears the wv_session cookie in the response

    A logged-out user can't access protected endpoints until they go
    through the magic-link flow again.
    """
    raw_session_id = request.cookies.get(SESSION_COOKIE_NAME)

    if raw_session_id:
        session_hash = hash_token(raw_session_id)
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    "DELETE FROM sessions WHERE session_id_hash = %s",
                    (session_hash,),
                )

    # Clear the cookie regardless of whether we found a row to delete
    response = jsonify({"ok": True})
    _clear_session_cookie(response)
    return response, 200


@app.post("/admin/set-password")
def admin_set_password():
    """Admin-only endpoint to set a user's password by email.

    This exists to bootstrap auth for testing and admin operations
    BEFORE the Stripe-driven signup flow is built. Once Stripe is
    wired to create accounts (Phase C — separate work item), most
    password setting happens through that flow + a "set your password"
    email. For now this endpoint lets admin manually set passwords.

    Protected by the existing HTTP Basic auth (WV_ADMIN_USER + WV_ADMIN_PASS
    env vars). Same protection as /admin/dashboard.

    Request body (JSON):
        {"email": "person@example.com", "password": "new-password"}

    Returns:
        200 {"ok": true, "user_id": 1}      — password set/updated
        400 {"ok": false, "error": "..."}   — missing field or bad email
        401 — admin auth failed
        404 {"ok": false, "error": "no-such-user"}

    If the user doesn't exist, returns 404 — admin should create the
    user first (or use the magic-link request flow which auto-creates).
    """
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp

    data = request.get_json(silent=True) or {}
    email = (data.get("email") or "").strip()
    password = data.get("password") or ""

    if not email or not password:
        return jsonify({"ok": False, "error": "missing-fields"}), 400

    if not is_valid_email(email):
        return jsonify({"ok": False, "error": "invalid-email"}), 400

    if len(password) < 8:
        return jsonify({"ok": False, "error": "password-too-short"}), 400

    # Hash and store
    new_hash = hash_password(password)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE users SET password_hash = %s
                   WHERE LOWER(email) = LOWER(%s)
                   RETURNING id""",
                (new_hash, email),
            )
            row = cur.fetchone()

    if row is None:
        return jsonify({"ok": False, "error": "no-such-user"}), 404

    print(f"[admin] password set for user_id={row['id']} email={email}", flush=True)
    return jsonify({"ok": True, "user_id": row["id"]}), 200


@app.post("/admin/grant-role")
def admin_grant_role():
    """Admin-only endpoint to grant a role to a user.

    Mirrors /admin/set-password's pattern: HTTP Basic auth (same admin
    credentials), JSON body, returns user_id on success.

    Until Stripe webhook signup grants 'subscriber' automatically, this
    is how subscribers get their role. For 'crew', 'met', and 'admin',
    this is always how roles are granted (no self-service).

    Request body (JSON):
        {"email": "person@example.com", "role": "subscriber"}

    Valid roles: subscriber, crew, met, admin

    Returns:
        200 {"ok": true, "user_id": N, "role": "..."}
        400 {"ok": false, "error": "..."}
        401 — admin auth failed
        404 {"ok": false, "error": "no-such-user"}
        409 {"ok": false, "error": "already-has-role"}
            (user already has this role; nothing to do)

    Idempotent semantics: granting a role twice is treated as a conflict
    (409) rather than a silent success — so admin can detect "I thought
    I already did this" cases. Conflict resolution: if you genuinely
    meant to grant again, this means you didn't.
    """
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp

    data = request.get_json(silent=True) or {}
    email = (data.get("email") or "").strip()
    role = (data.get("role") or "").strip().lower()

    if not email or not role:
        return jsonify({"ok": False, "error": "missing-fields"}), 400

    if role not in ("subscriber", "crew", "met", "admin"):
        return jsonify({"ok": False, "error": "invalid-role"}), 400

    if not is_valid_email(email):
        return jsonify({"ok": False, "error": "invalid-email"}), 400

    with db() as conn:
        # Look up user
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id FROM users WHERE LOWER(email) = LOWER(%s)",
                (email,),
            )
            user_row = cur.fetchone()

        if user_row is None:
            return jsonify({"ok": False, "error": "no-such-user"}), 404

        user_id = user_row["id"]

        # Check if role already exists
        with conn.cursor() as cur:
            cur.execute(
                "SELECT 1 FROM user_roles WHERE user_id = %s AND role = %s",
                (user_id, role),
            )
            existing = cur.fetchone()

        if existing is not None:
            return jsonify({"ok": False, "error": "already-has-role"}), 409

        # Grant the role
        with conn.cursor() as cur:
            cur.execute(
                "INSERT INTO user_roles (user_id, role, granted_at) VALUES (%s, %s, %s)",
                (user_id, role, now_ts()),
            )

    print(f"[admin] role granted: user_id={user_id} email={email} role={role}", flush=True)
    return jsonify({"ok": True, "user_id": user_id, "role": role}), 200


@app.post("/admin/revoke-role")
def admin_revoke_role():
    """Admin-only endpoint to revoke a role from a user.

    Opposite of /admin/grant-role. Removes the user_roles row but does
    NOT delete sessions — the user stays logged in but loses access to
    that workspace's endpoints. They'll see the workspace disappear
    from their picker on next session check.

    Request body (JSON):
        {"email": "person@example.com", "role": "subscriber"}

    Returns:
        200 {"ok": true, "user_id": N, "role": "..."}
        400 {"ok": false, "error": "..."}
        401 — admin auth failed
        404 {"ok": false, "error": "no-such-user"} or "role-not-held"
    """
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp

    data = request.get_json(silent=True) or {}
    email = (data.get("email") or "").strip()
    role = (data.get("role") or "").strip().lower()

    if not email or not role:
        return jsonify({"ok": False, "error": "missing-fields"}), 400

    if not is_valid_email(email):
        return jsonify({"ok": False, "error": "invalid-email"}), 400

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id FROM users WHERE LOWER(email) = LOWER(%s)",
                (email,),
            )
            user_row = cur.fetchone()

        if user_row is None:
            return jsonify({"ok": False, "error": "no-such-user"}), 404

        user_id = user_row["id"]

        with conn.cursor() as cur:
            cur.execute(
                "DELETE FROM user_roles WHERE user_id = %s AND role = %s RETURNING role",
                (user_id, role),
            )
            deleted = cur.fetchone()

        if deleted is None:
            return jsonify({"ok": False, "error": "role-not-held"}), 404

    print(f"[admin] role revoked: user_id={user_id} email={email} role={role}", flush=True)
    return jsonify({"ok": True, "user_id": user_id, "role": role}), 200


@app.post("/api/v1/forecast/explain")
def forecast_explain():
    """Generate the friendly, activity-aware paragraph for a forecast ticket.

    Expected JSON body:
        {
          "plan": "Saturday wedding at 4 PM",
          "location": "Columbus, OH",
          "when": "Saturday May 10, 4:00 PM",
          "verdict": "Clear" | "Caution" | "Risk",
          "weather": {
            "temperature_f": 76,
            "feels_like_f": 76,
            "wind_mph": 6,
            "wind_gust_mph": 9,
            "humidity_pct": 50,
            "cloud_cover_pct": 25,
            "precip_probability_pct": 5,
            "precip_amount_in": 0,
            "rain_window": null    // or "4:15 PM to 5:45 PM" if rain expected
          }
        }

    Returns:
        {"paragraph": "Beautiful afternoon for it..."}
    """
    payload = request.get_json(silent=True) or {}

    # Basic shape validation — we don't want garbage flowing into our prompt
    if not isinstance(payload, dict):
        return jsonify({"error": "invalid payload"}), 400
    plan = payload.get("plan")
    if not isinstance(plan, str) or not plan.strip() or len(plan) > 600:
        # Reject empty, whitespace-only, missing, or absurdly long plans.
        # 600 chars is generous — most plans are <100. A 600+ char "plan"
        # is probably someone testing prompt-injection and we don't pay
        # to call the AI for that.
        return jsonify({"error": "invalid plan"}), 400

    user_message = _build_explainer_user_message(payload)
    raw_response = _call_gemini(EXPLAINER_SYSTEM_PROMPT, user_message)
    used_ai = raw_response is not None

    # Parse the response: paragraph and (optionally) a verdict assessment
    # separated by the ---VERDICT--- delimiter. If the AI didn't follow the
    # format (or we got a fallback), the whole response is the paragraph
    # and we don't suggest any verdict override.
    paragraph = raw_response
    verdict_override = None
    if raw_response and "---VERDICT---" in raw_response:
        parts = raw_response.split("---VERDICT---", 1)
        paragraph = parts[0].strip()
        suggested = parts[1].strip().lower()
        # Take the first word in case the model wrote anything else
        suggested_first_word = suggested.split()[0].rstrip(".,;:!?") if suggested else ""
        if suggested_first_word in ("clear", "caution", "risk"):
            # Apply the downgrade-only safety rule on the SERVER side too,
            # so the frontend doesn't have to know the rule. The frontend
            # can trust whatever verdict_override comes back.
            #
            # Hierarchy: clear < caution < risk
            # Allowed transitions:
            #   rule=caution → AI=clear      ✓ (downgrade)
            #   rule=caution → AI=caution    ✓ (no change)
            #   rule=clear   → AI=clear      ✓ (no change)
            #   rule=risk    → AI=risk       ✓ (no change)
            # Disallowed (the AI suggested an upgrade — silently drop it):
            #   rule=clear   → AI=caution    ✗
            #   rule=clear   → AI=risk       ✗
            #   rule=caution → AI=risk       ✗
            #   rule=risk    → AI=caution    ✗
            #   rule=risk    → AI=clear      ✗ (Risk is the safety floor)
            severity = {"clear": 0, "caution": 1, "risk": 2}
            rule_verdict = (payload.get("verdict") or "").strip().lower()
            rule_level = severity.get(rule_verdict, -1)
            ai_level = severity.get(suggested_first_word, -1)
            # Only honor the override if it's a genuine downgrade from
            # caution to clear. Risk never gets downgraded; clear never
            # gets upgraded; same-level overrides aren't useful to send.
            if rule_level == 1 and ai_level == 0:
                verdict_override = "clear"

    if not paragraph:
        paragraph = _fallback_paragraph(payload)

    response_body = {
        "paragraph": paragraph,
        "source": "ai" if used_ai else "fallback",
    }
    if verdict_override:
        response_body["verdict_override"] = verdict_override
    return jsonify(response_body)


# ────────────────────────────────────────────────────────────────────────────
# Customer flow: create checkout
# ────────────────────────────────────────────────────────────────────────────


@app.post("/api/v1/verification/checkout")
def create_checkout_session():
    """Frontend POSTs the plan + tier choice. We:
       1. Validate the tier.
       2. Run the Decision Engine to get the pre-synthesized brief.
       3. Insert a 'pending' row in SQLite.
       4. Create a Stripe Checkout Session.
       5. Return the hosted_url for the frontend to redirect to.

    Body schema (JSON):
      {
        "tier": "single" | "day_pass" | "pro_monthly",
        "plan_text": "Concrete pour at 10 AM in Lebanon, IN",
        "plan_industry": "concrete",
        "plan_location": "Lebanon, IN",
        "plan_window": "10 AM - 1 PM",
        "ai_status_key": "caution",
        "customer_email": "user@example.com",
        "customer_phone": "317-555-0123",
        "forecast_json": "..."   (optional, pass-through to Decision Engine)
      }
    """
    body = request.get_json(silent=True) or {}
    tier_key = body.get("tier")
    if tier_key not in TIERS:
        return jsonify({"error": "invalid tier"}), 400

    plan_text = (body.get("plan_text") or "").strip()
    if not plan_text:
        return jsonify({"error": "plan_text is required"}), 400

    customer_email = (body.get("customer_email") or "").strip().lower()
    customer_phone = normalize_phone(body.get("customer_phone"))
    if not customer_phone:
        return jsonify({"error": "valid phone number required"}), 400

    tier = TIERS[tier_key]
    claim_token = new_claim_token()

    # Pre-synthesize the brief NOW so the meteorologist sees it the moment
    # they get the SMS. This is the single biggest reason the meteorologist
    # can hit the 30-minute SLA: they don't start from a blank page.
    ai_brief = ""
    if generate_ticket_decision is not None:
        try:
            ai_brief = generate_ticket_decision(
                plan_text,
                forecast_json=body.get("forecast_json"),
            )
        except Exception as e:
            # Decision Engine failures must NEVER block payment — that would
            # mean the customer can't buy if our AI is down. Log and proceed.
            print(f"[decision-engine] failed: {e}", flush=True)
            ai_brief = "(AI brief unavailable — meteorologist starts from raw forecast.)"
    else:
        ai_brief = "(Decision Engine not installed in this deployment.)"

    with db() as conn:
        with conn.cursor() as cur:
            # Use RETURNING id to get the auto-generated primary key. This
            # replaces the prior cur.lastrowid pattern (a SQLite-specific
            # convenience). Postgres requires the RETURNING clause to
            # retrieve auto-generated values from an INSERT.
            cur.execute(
                """INSERT INTO verification_requests
                   (created_at, updated_at, status, tier, price_cents,
                    customer_email, customer_phone,
                    plan_text, plan_industry, plan_location, plan_window,
                    ai_brief_markdown, ai_status_key, claim_token)
                   VALUES (%s, %s, 'pending', %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                   RETURNING id""",
                (now_ts(), now_ts(), tier_key, tier["price_cents"],
                 customer_email, customer_phone,
                 plan_text, body.get("plan_industry"), body.get("plan_location"),
                 body.get("plan_window"),
                 ai_brief, body.get("ai_status_key"), claim_token),
            )
            request_id = cur.fetchone()['id']

    # Create the Stripe Checkout Session.
    # Test mode: use sk_test_... keys; payments are simulated, no real charges.
    # Live mode: use sk_live_... keys after passing Stripe's activation review.
    if stripe is None or not STRIPE_SECRET_KEY:
        # Local dev path: skip Stripe and mark the request as paid immediately.
        # Useful for testing the rest of the flow without setting up Stripe.
        # NEVER deploy this branch — it would let anyone get verifications free.
        if os.environ.get("WV_ALLOW_FAKE_PAYMENT") == "1":
            print(f"[stripe-stub] no API key — marking request {request_id} as paid", flush=True)
            _mark_paid_and_notify(request_id, fake_payment=True)
            return jsonify({
                "request_id": request_id,
                "checkout_url": f"{FRONTEND_BASE_URL}/verification/standby?rid={request_id}",
                "fake": True,
            })
        return jsonify({"error": "Stripe not configured on server"}), 500

    try:
        session = stripe.checkout.Session.create(
            mode="payment",  # one-time. For pro_monthly subscription, use 'subscription'
                             # and pre-create Price IDs in the Stripe dashboard.
            payment_method_types=["card"],
            line_items=[{
                "price_data": {
                    "currency": "usd",
                    "product_data": {
                        "name": tier["name"],
                        "description": tier["description"],
                    },
                    "unit_amount": tier["price_cents"],
                },
                "quantity": 1,
            }],
            customer_email=customer_email or None,
            metadata={
                "wv_request_id": str(request_id),
                "wv_tier": tier_key,
            },
            success_url=f"{FRONTEND_BASE_URL}/verification/standby?rid={request_id}&session={{CHECKOUT_SESSION_ID}}",
            cancel_url=f"{FRONTEND_BASE_URL}/verification/cancelled?rid={request_id}",
        )
    except Exception as e:
        print(f"[stripe] session create failed: {e}", flush=True)
        return jsonify({"error": "payment processor unavailable"}), 502

    # Record the Stripe session id so the webhook can match it back.
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "UPDATE verification_requests SET stripe_session_id = %s, updated_at = %s WHERE id = %s",
                (session.id, now_ts(), request_id),
            )

    return jsonify({
        "request_id": request_id,
        "checkout_url": session.url,
    })


# ────────────────────────────────────────────────────────────────────────────
# Stripe webhook — payment confirmation
# ────────────────────────────────────────────────────────────────────────────


@app.post("/webhooks/stripe")
def stripe_webhook():
    """Stripe POSTs payment events here. We only care about
    `checkout.session.completed`. The signature MUST be verified — without
    it, anyone could POST a fake event and get free verifications.

    Set STRIPE_WEBHOOK_SECRET from your Stripe dashboard:
      Developers → Webhooks → your endpoint → Signing secret"""
    if stripe is None or not STRIPE_WEBHOOK_SECRET:
        return jsonify({"error": "webhooks not configured"}), 500

    payload = request.get_data(as_text=False)
    sig_header = request.headers.get("Stripe-Signature", "")

    try:
        event = stripe.Webhook.construct_event(payload, sig_header, STRIPE_WEBHOOK_SECRET)
    except ValueError:
        # Malformed JSON — likely a probe, not Stripe
        return jsonify({"error": "invalid payload"}), 400
    except stripe.error.SignatureVerificationError:
        # Wrong signature — could be a spoof attempt; never trust it
        return jsonify({"error": "invalid signature"}), 400

    if event["type"] == "checkout.session.completed":
        session = event["data"]["object"]
        request_id = int(session.get("metadata", {}).get("wv_request_id", 0))
        if request_id:
            payment_id = session.get("payment_intent") or session.get("id")
            _mark_paid_and_notify(request_id, payment_id=payment_id)

    # Stripe expects 200 quickly. Other event types we ignore — Stripe is OK
    # with that as long as we acknowledge.
    return jsonify({"received": True})


def _mark_paid_and_notify(request_id: int, *, payment_id: Optional[str] = None,
                          fake_payment: bool = False) -> None:
    """Idempotent: mark a request paid, send customer SMS, ping the meteorologist.

    Idempotency matters because Stripe retries webhooks. If we already moved
    past 'pending', we skip the SMS sends — otherwise customers get duplicate
    texts every time the webhook gets retried."""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM verification_requests WHERE id = %s",
                (request_id,),
            )
            row = cur.fetchone()
            if row is None:
                print(f"[webhook] no row for request_id={request_id}", flush=True)
                return
            if row["status"] != "pending":
                print(f"[webhook] request {request_id} already {row['status']}, skipping notifications", flush=True)
                return
            cur.execute(
                "UPDATE verification_requests SET status='paid', stripe_payment_id=%s, updated_at=%s WHERE id=%s",
                (payment_id, now_ts(), request_id),
            )

    # Customer SMS — the standby promise. Keep it short, warm, time-bounded.
    customer_msg = (
        "WeatherValet: Got it. " + METEOROLOGIST_NAME.split()[0].capitalize()
        + " is reviewing your plan now and we'll text you when the call is ready "
        "(usually under 30 minutes). Reply STOP to opt out."
    )
    send_sms(row["customer_phone"], customer_msg)

    # Meteorologist SMS — the brief + claim link. We send this LAST so the
    # customer has gotten their confirmation before the meteorologist starts.
    if METEOROLOGIST_PHONE:
        claim_url = f"{PUBLIC_BASE_URL}/meteorologist/{row['claim_token']}"
        plan = row["plan_text"][:80] + ("…" if len(row["plan_text"]) > 80 else "")
        loc = row["plan_location"] or "(no location)"
        ai_status = (row["ai_status_key"] or "unknown").upper()
        met_msg = (
            f"WV new request #{request_id} ({row['tier']}): {plan}\n"
            f"Loc: {loc}\n"
            f"AI verdict: {ai_status}\n"
            f"Brief + claim: {claim_url}\n"
            f"30-min SLA. Tap the link."
        )
        send_sms(METEOROLOGIST_PHONE, met_msg)


# ────────────────────────────────────────────────────────────────────────────
# Stripe webhook v2 — subscription signup flow (Phase 4)
# ────────────────────────────────────────────────────────────────────────────
#
# Listens for checkout.session.completed events from Stripe and handles
# the subscription onboarding flow:
#   1. Verify Stripe's HMAC signature against STRIPE_WEBHOOK_SECRET
#   2. Check the event ID against stripe_events table (idempotency)
#   3. If session.mode == 'subscription':
#        a. Find or create the user matching session.customer_details.email
#        b. Grant them the 'subscriber' role (if not already)
#        c. Send them a magic-link email with intent=new-account so
#           they can set their initial password (welcome-framed copy)
#   4. If session.mode == 'payment' (one-time $19 purchase):
#        a. Log it but don't create an account (per product decision —
#           $19 is a transactional purchase, not an account-creation event)
#   5. Record the event in stripe_events
#   6. Return 200
#
# Note: this is the NEW endpoint at /api/v1/stripe/webhook. The older
# /webhooks/stripe route (line ~3076) is left in place for now but has
# no Stripe destination pointing at it. If the $19 verification_requests
# flow is later re-wired, it can either move to this endpoint or keep
# its own — but right now, this is the only live webhook.

def _validate_stripe_signature(payload: bytes, sig_header: str, secret: str,
                                tolerance_seconds: int = 300) -> bool:
    """Validate a Stripe webhook signature using HMAC-SHA256.

    Stripe documents this scheme at:
      https://stripe.com/docs/webhooks/signatures

    The Stripe-Signature header looks like:
      t=1492774577,v1=5257a869e7ecebeda32...

    Where:
      t  = the timestamp when Stripe signed the request (seconds since epoch)
      v1 = the HMAC-SHA256 hex digest of "{t}.{payload}" keyed with our secret

    Validation steps:
      1. Parse the header into t and v1 values
      2. Reject if timestamp is more than `tolerance_seconds` old (default 5min).
         This prevents replay attacks where someone captures a real webhook
         and re-sends it later.
      3. Compute our own HMAC of "{t}.{payload}" and constant-time compare
         against the v1 value.

    Returns True only when the signature is valid AND fresh. Any malformed
    header, missing fields, wrong digest, or stale timestamp → False.

    Constant-time comparison via hmac.compare_digest prevents timing-attack
    leaks where an attacker could narrow in on the secret one byte at a time.
    """
    if not payload or not sig_header or not secret:
        return False

    # Parse header into key=value pairs
    parts = {}
    for chunk in sig_header.split(","):
        chunk = chunk.strip()
        if "=" not in chunk:
            continue
        key, value = chunk.split("=", 1)
        parts.setdefault(key, value)

    timestamp_str = parts.get("t")
    sig_v1 = parts.get("v1")
    if not timestamp_str or not sig_v1:
        return False

    try:
        timestamp = int(timestamp_str)
    except ValueError:
        return False

    # Replay protection — reject anything older than tolerance.
    # now_ts() returns seconds since epoch, same units as Stripe's t.
    if abs(now_ts() - timestamp) > tolerance_seconds:
        print(
            f"[stripe-webhook] signature timestamp out of tolerance: "
            f"t={timestamp} now={now_ts()} delta={abs(now_ts() - timestamp)}s",
            flush=True,
        )
        return False

    # Compute the expected signature. Stripe signs the literal byte sequence
    # "t={timestamp_str}.{raw_payload}" — the timestamp must be the EXACT
    # string from the header (no re-formatting), and the payload must be the
    # raw bytes (no JSON re-serialization).
    signed_payload = f"{timestamp_str}.".encode("utf-8") + payload
    expected_sig = hmac.new(
        secret.encode("utf-8"),
        signed_payload,
        hashlib.sha256,
    ).hexdigest()

    return hmac.compare_digest(expected_sig, sig_v1)


def _stripe_event_already_processed(event_id: str) -> bool:
    """Check if we've already handled this Stripe event ID.

    Stripe retries failed webhooks and occasionally double-sends successful
    ones through network issues. The event_id is unique per event, so we
    use it as the idempotency key. The stripe_events table holds every
    event we've fully processed.

    Returns True if the event was already processed (caller should skip
    work and return 200 to ack), False if it's new.
    """
    if not event_id:
        return False
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT 1 FROM stripe_events WHERE event_id = %s LIMIT 1",
                (event_id,),
            )
            return cur.fetchone() is not None


def _stripe_event_record(event_id: str, event_type: str, payload: bytes) -> None:
    """Record that we've processed a Stripe event.

    Called AFTER the event has been fully handled (account created, email
    sent, etc.). If we crash mid-processing, the row isn't written and
    Stripe's next retry will re-trigger the full flow. This is intentional:
    a partial failure is better re-tried than silently lost.

    payload_kb stores only the first 1024 bytes — enough to audit
    "what kind of event was this" without ballooning the table.
    """
    if not event_id:
        return
    payload_preview = payload[:1024].decode("utf-8", errors="replace") if payload else ""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO stripe_events
                   (event_id, event_type, processed_at, payload_kb)
                   VALUES (%s, %s, %s, %s)
                   ON CONFLICT (event_id) DO NOTHING""",
                (event_id, event_type, now_ts(), payload_preview),
            )


def _grant_subscriber_role(user_id: int, conn) -> bool:
    """Grant the 'subscriber' role to a user. Idempotent — returns True
    only if the role was newly added (False if they already had it).
    Used after a successful subscription webhook.
    """
    with conn.cursor() as cur:
        cur.execute(
            "SELECT 1 FROM user_roles WHERE user_id = %s AND role = %s",
            (user_id, "subscriber"),
        )
        if cur.fetchone() is not None:
            return False
        cur.execute(
            """INSERT INTO user_roles (user_id, role, granted_at)
               VALUES (%s, %s, %s)
               ON CONFLICT DO NOTHING""",
            (user_id, "subscriber", now_ts()),
        )
        return True


def _revoke_subscriber_role(user_id: int, conn) -> bool:
    """Revoke the 'subscriber' role from a user. Idempotent — returns True
    only if the role was actually removed (False if they didn't have it).
    Used by the subscription-cancellation webhook (Phase 1).

    Other roles (admin, crew, met) are untouched — a Met who happened
    to also be a subscriber doesn't lose their Met access when they
    cancel their subscription.
    """
    with conn.cursor() as cur:
        cur.execute(
            "DELETE FROM user_roles WHERE user_id = %s AND role = %s",
            (user_id, "subscriber"),
        )
        return cur.rowcount > 0


def _find_user_for_stripe_customer(stripe_customer_id: str, email_fallback: Optional[str] = None) -> Optional[int]:
    """Look up the user matching a Stripe customer ID.

    Primary lookup: users.stripe_customer_id. Populated for any user
    who subscribed after Phase 2 of the May 14 work.

    Fallback: if no row matches the customer ID AND an email was
    provided (e.g. fetched from Stripe's customer object), look up by
    email. This handles existing subscribers created before Phase 2
    whose stripe_customer_id is still NULL.

    Returns the integer user_id, or None if no match found.
    """
    if not stripe_customer_id and not email_fallback:
        return None

    with db() as conn:
        with conn.cursor() as cur:
            if stripe_customer_id:
                cur.execute(
                    "SELECT id FROM users WHERE stripe_customer_id = %s LIMIT 1",
                    (stripe_customer_id,),
                )
                row = cur.fetchone()
                if row:
                    return row["id"]

            if email_fallback:
                cur.execute(
                    "SELECT id FROM users WHERE LOWER(email) = LOWER(%s) LIMIT 1",
                    (email_fallback.strip(),),
                )
                row = cur.fetchone()
                if row:
                    # Found via email — backfill the customer ID for future lookups
                    if stripe_customer_id:
                        cur.execute(
                            "UPDATE users SET stripe_customer_id = %s WHERE id = %s",
                            (stripe_customer_id, row["id"]),
                        )
                    return row["id"]

    return None


def _fetch_stripe_customer_email(stripe_customer_id: str) -> Optional[str]:
    """Fetch a customer's email from Stripe's API. Used as a fallback when
    a webhook references a customer ID we don't have linked yet.

    Returns the email string, or None if the lookup fails. Uses urllib
    directly (no Stripe SDK dependency).
    """
    if not stripe_customer_id or not STRIPE_SECRET_KEY:
        return None
    try:
        req = urllib.request.Request(
            f"https://api.stripe.com/v1/customers/{stripe_customer_id}",
            method="GET",
            headers={
                "Authorization": f"Bearer {STRIPE_SECRET_KEY}",
                "User-Agent": "WeatherValet-Backend/1.0 (+https://weathervalet.ai)",
            },
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            if 200 <= resp.status < 300:
                body = json.loads(resp.read().decode("utf-8"))
                email = body.get("email")
                if email and isinstance(email, str):
                    return email.strip()
    except Exception as e:
        print(f"[stripe-webhook] customer fetch failed for {stripe_customer_id}: {e!r}", flush=True)
    return None


@app.route("/api/v1/stripe/webhook", methods=["OPTIONS"])
def _stripe_webhook_v2_preflight():
    """CORS preflight. Stripe doesn't send preflights but this route
    being CORS-clean is harmless and matches the codebase pattern."""
    return ("", 204)


@app.post("/api/v1/stripe/webhook")
def stripe_webhook_v2():
    """Stripe POSTs subscription events here.

    Configured at Stripe dashboard → Event destinations:
      URL:    https://wv-valet-backend.onrender.com/api/v1/stripe/webhook
      Events: checkout.session.completed

    Security: STRIPE_WEBHOOK_SECRET must be set on Render. Without it,
    we return 500 (not 200) because a misconfigured webhook is worse
    than a slow webhook — Stripe will retry, and someone will notice.
    """
    if not STRIPE_WEBHOOK_SECRET:
        print("[stripe-webhook] STRIPE_WEBHOOK_SECRET not configured", flush=True)
        return jsonify({"error": "webhook-not-configured"}), 500

    # Read the raw payload bytes. Do NOT use request.get_json() — that
    # parses and re-serializes, which breaks the signature.
    payload = request.get_data(as_text=False)
    sig_header = request.headers.get("Stripe-Signature", "")

    # Signature gate — anything that doesn't validate is rejected before
    # we look at the payload. Could be a probe, a forgery attempt, or a
    # legitimate event with the wrong secret in env vars.
    if not _validate_stripe_signature(payload, sig_header, STRIPE_WEBHOOK_SECRET):
        print(
            f"[stripe-webhook] signature validation failed "
            f"(payload_len={len(payload)} sig_present={bool(sig_header)})",
            flush=True,
        )
        return jsonify({"error": "invalid-signature"}), 400

    # Parse the JSON only after signature validation passed.
    try:
        event = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as e:
        print(f"[stripe-webhook] payload parse error: {e!r}", flush=True)
        return jsonify({"error": "invalid-payload"}), 400

    event_id = event.get("id", "")
    event_type = event.get("type", "")

    # Idempotency check — if we've seen this event ID before, skip.
    if _stripe_event_already_processed(event_id):
        print(f"[stripe-webhook] event {event_id} already processed, skipping", flush=True)
        return jsonify({"received": True, "duplicate": True}), 200

    # Dispatch. Today we handle:
    #   - checkout.session.completed       → subscription signup (Phase 4)
    #   - customer.subscription.deleted    → subscription cancellation (Phase 1)
    # Other event types ack with 200 (so Stripe doesn't retry) but do nothing.
    if event_type not in ("checkout.session.completed", "customer.subscription.deleted"):
        print(f"[stripe-webhook] unhandled event type: {event_type} (id={event_id})", flush=True)
        # Record it anyway so we don't reprocess on retries
        _stripe_event_record(event_id, event_type, payload)
        return jsonify({"received": True, "handled": False}), 200

    # ────────────────────────────────────────────────────────────────
    # checkout.session.completed — subscription signup (or one-time payment)
    # ────────────────────────────────────────────────────────────────
    if event_type == "checkout.session.completed":
        # Extract the checkout session
        session = event.get("data", {}).get("object", {})
        mode = session.get("mode", "")  # 'subscription' | 'payment' | 'setup'
        customer_details = session.get("customer_details") or {}
        email = (customer_details.get("email") or "").strip()
        customer_name = (customer_details.get("name") or "").strip()
        stripe_customer_id = session.get("customer") or ""

        print(
            f"[stripe-webhook] checkout.session.completed received: "
            f"id={event_id} mode={mode} email={email} customer={stripe_customer_id}",
            flush=True,
        )

        if mode == "subscription":
            # Account-creation flow. We need a valid email; without it, we
            # can't create a user or send a welcome link.
            if not email or not is_valid_email(email):
                print(f"[stripe-webhook] subscription mode but invalid email: '{email}'", flush=True)
                _stripe_event_record(event_id, event_type, payload)
                return jsonify({"received": True, "handled": False, "reason": "invalid-email"}), 200

            try:
                with db() as conn:
                    # Find or create the user. _get_or_create_user is idempotent —
                    # if they already exist, returns their id. If not, creates a
                    # new row with no password set.
                    user_id = _get_or_create_user(email, conn)

                    # If we got a name from Stripe and the user doesn't have one
                    # yet, fill it in. Don't overwrite an existing name (the user
                    # may have set their own preferred form).
                    if customer_name:
                        with conn.cursor() as cur:
                            cur.execute(
                                """UPDATE users SET name = %s
                                   WHERE id = %s AND (name IS NULL OR name = '')""",
                                (customer_name, user_id),
                            )

                    # Link the Stripe customer ID to the user (Phase 2). Lets
                    # subsequent webhooks (cancellation, payment failure) look
                    # up the user by customer ID without a Stripe round-trip.
                    # We always overwrite — if a user re-subscribes after a
                    # cancellation, the customer ID may have changed.
                    if stripe_customer_id:
                        with conn.cursor() as cur:
                            cur.execute(
                                "UPDATE users SET stripe_customer_id = %s WHERE id = %s",
                                (stripe_customer_id, user_id),
                            )

                    # Grant subscriber role
                    newly_granted = _grant_subscriber_role(user_id, conn)

                # Send the password-reset email so the new subscriber can set
                # their password and sign in. Reusing the magic-link infra —
                # password-reset and first-time-account-setup are the same flow.
                base = os.environ.get("FRONTEND_BASE_URL", "https://weathervalet.ai")
                raw_token = new_secure_token()
                token_hash = hash_token(raw_token)
                now = now_ts()
                with db() as conn:
                    with conn.cursor() as cur:
                        cur.execute(
                            """INSERT INTO magic_link_tokens
                               (token_hash, user_id, created_at, expires_at, ip_requested)
                               VALUES (%s, %s, %s, %s, %s)""",
                            (token_hash, user_id, now, now + MAGIC_LINK_TTL_SECONDS, "stripe-webhook"),
                        )
                magic_link_url = f"{base}/?auth=verify&token={raw_token}&intent=new-account"
                _send_magic_link_email(email, magic_link_url, intent="new-account")

                print(
                    f"[stripe-webhook] subscription provisioned: "
                    f"user_id={user_id} email={email} newly_granted={newly_granted}",
                    flush=True,
                )

                # Record the event so we don't reprocess on retries
                _stripe_event_record(event_id, event_type, payload)
                return jsonify({"received": True, "handled": True, "user_id": user_id}), 200

            except Exception as e:
                # DB error, email send failure, etc. Don't record the event —
                # Stripe will retry, and the retry has a real chance of working
                # (transient DB issues, Resend hiccups, etc.). Log loudly.
                print(
                    f"[stripe-webhook] FAILED to provision subscription for {email}: {e!r}",
                    flush=True,
                )
                return jsonify({"error": "internal-error"}), 500

        elif mode == "payment":
            # One-time payment ($19 Met-verified review). Per product decision,
            # we do NOT create an account here — the $19 product is transactional
            # only. The existing verification_requests flow (separate webhook,
            # currently inactive) handles its own bookkeeping.
            print(
                f"[stripe-webhook] one-time payment received (no account created): "
                f"email={email} session={session.get('id')}",
                flush=True,
            )
            _stripe_event_record(event_id, event_type, payload)
            return jsonify({"received": True, "handled": True, "mode": "payment"}), 200

        else:
            # 'setup' mode or anything else we don't handle. Ack so Stripe
            # doesn't retry, but log so we notice if a new mode appears.
            print(f"[stripe-webhook] unhandled mode: '{mode}' (id={event_id})", flush=True)
            _stripe_event_record(event_id, event_type, payload)
            return jsonify({"received": True, "handled": False, "mode": mode}), 200

    # ────────────────────────────────────────────────────────────────
    # customer.subscription.deleted — subscription cancellation (Phase 1)
    # ────────────────────────────────────────────────────────────────
    if event_type == "customer.subscription.deleted":
        # For this event, data.object is the Subscription, not a checkout
        # session. The key fields we care about:
        #   - customer: the Stripe customer ID
        #   - status: should be 'canceled' but we don't gate on it
        subscription = event.get("data", {}).get("object", {})
        stripe_customer_id = subscription.get("customer") or ""
        sub_status = subscription.get("status", "")

        print(
            f"[stripe-webhook] customer.subscription.deleted received: "
            f"id={event_id} customer={stripe_customer_id} status={sub_status}",
            flush=True,
        )

        if not stripe_customer_id:
            # Malformed event with no customer ID — nothing we can do.
            _stripe_event_record(event_id, event_type, payload)
            return jsonify({"received": True, "handled": False, "reason": "no-customer-id"}), 200

        try:
            # Find the user. Try the customer ID first; if that misses (legacy
            # subscribers from before Phase 2 may not have it linked), fetch
            # the email from Stripe's customer API and try by email.
            user_id = _find_user_for_stripe_customer(stripe_customer_id)
            if user_id is None:
                email = _fetch_stripe_customer_email(stripe_customer_id)
                if email:
                    user_id = _find_user_for_stripe_customer(stripe_customer_id, email_fallback=email)

            if user_id is None:
                # No matching user. Record the event so we don't reprocess,
                # but don't 500 — the subscription is genuinely cancelled at
                # Stripe regardless, and us not having the user just means
                # we have nothing local to revoke.
                print(
                    f"[stripe-webhook] cancellation event for unknown customer "
                    f"{stripe_customer_id} (no matching user)",
                    flush=True,
                )
                _stripe_event_record(event_id, event_type, payload)
                return jsonify({"received": True, "handled": False, "reason": "no-matching-user"}), 200

            # Revoke the subscriber role. Other roles (admin, crew, met) stay.
            # Note: we do NOT kill their sessions or deactivate the account.
            # If they're also a Crew member or Met, they keep that access.
            # A subscriber-only user simply loses their subscriber workspace
            # the next time the frontend re-fetches /auth/session.
            with db() as conn:
                revoked = _revoke_subscriber_role(user_id, conn)

            print(
                f"[stripe-webhook] subscription revoked: "
                f"user_id={user_id} revoked={revoked} customer={stripe_customer_id}",
                flush=True,
            )
            _stripe_event_record(event_id, event_type, payload)
            return jsonify({"received": True, "handled": True, "user_id": user_id, "revoked": revoked}), 200

        except Exception as e:
            # Don't record the event — Stripe will retry, transient errors
            # may resolve themselves.
            print(
                f"[stripe-webhook] FAILED to process cancellation "
                f"for {stripe_customer_id}: {e!r}",
                flush=True,
            )
            return jsonify({"error": "internal-error"}), 500

    # Defensive: unhandled event type at end of dispatch. Shouldn't be
    # reachable given the early-return at the top, but keeps the function
    # type-clean.
    _stripe_event_record(event_id, event_type, payload)
    return jsonify({"received": True, "handled": False}), 200


# ────────────────────────────────────────────────────────────────────────────
# Customer status polling
# ────────────────────────────────────────────────────────────────────────────


@app.get("/api/v1/verification/status")
def status():
    """Customer's standby page polls this every few seconds.
    We expose the minimum the standby UI needs — never the claim_token, never
    the meteorologist's phone."""
    request_id = request.args.get("rid", type=int)
    if not request_id:
        return jsonify({"error": "rid required"}), 400
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, status, created_at, claimed_at, completed_at,
                          meteorologist_verdict, meteorologist_notes
                   FROM verification_requests WHERE id = %s""",
                (request_id,),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"error": "not found"}), 404

    return jsonify({
        "request_id": row["id"],
        "status": row["status"],
        "created_at": row["created_at"],
        "claimed_at": row["claimed_at"],
        "completed_at": row["completed_at"],
        "verdict": row["meteorologist_verdict"] if row["status"] == "completed" else None,
        "notes": row["meteorologist_notes"] if row["status"] == "completed" else None,
        "elapsed_minutes": (now_ts() - row["created_at"]) // 60,
    })


# ────────────────────────────────────────────────────────────────────────────
# Meteorologist flow
# ────────────────────────────────────────────────────────────────────────────


@app.get("/meteorologist/home")
def meteorologist_home():
    """The Meteorologist Portal — what a meteorologist sees when they log in.

    This is a clean, simple landing page: prominent Submit Daily Brief button
    at the top, then a list of their recent submissions below. Mobile-first.

    Auth model for v1: same HTTP Basic credentials as the operator dashboard.
    The portal is a meteorologist-shaped view onto the same admin data, not
    a separate auth domain. When v2 adds per-meteorologist accounts, this
    route filters submissions by the logged-in meteorologist's name; v1
    shows all submissions because there's only one meteorologist on duty.

    Note: this static path /meteorologist/home is registered before Flask's
    wildcard /meteorologist/<claim_token> route. Flask resolves static paths
    before dynamic ones, so 'home' won't be misinterpreted as a claim token.
    """
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp

    # Pull the most recent submissions for the activity feed. We cap at 20
    # rows because that's what fits comfortably on a phone screen without
    # paging. If a meteorologist needs deeper history, they can drill into
    # the brief file directly via the Submit Brief form (which shows
    # all current regions in its dropdown).
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT id, submitted_at, meteorologist_name, region_name,
                              verdict, start_time, end_time, summary, confidence
                       FROM brief_submissions
                       ORDER BY submitted_at DESC
                       LIMIT 20"""
                )
                rows = cur.fetchall()
    except (psycopg2.OperationalError, psycopg2.errors.UndefinedTable):
        # Table might not exist yet on a fresh boot — _ensure_db hasn't run
        # for this process, or the database is unreachable. Treat as empty.
        # The Postgres-specific UndefinedTable is the closest analog to
        # SQLite's OperationalError "no such table".
        rows = []

    # Decorate each row with a relative-time label so the meteorologist
    # can see "2 minutes ago", "today at 9:14 AM", "yesterday at 3 PM" etc.
    now = now_ts()
    submissions = []
    for r in rows:
        ts = r["submitted_at"]
        delta = now - ts
        if delta < 60:
            relative = "just now"
        elif delta < 3600:
            relative = f"{delta // 60} min ago"
        elif delta < 86400:
            # Today — show local clock time
            local_dt = datetime.fromtimestamp(ts)
            relative = "today at " + local_dt.strftime("%-I:%M %p").lower()
        elif delta < 86400 * 2:
            local_dt = datetime.fromtimestamp(ts)
            relative = "yesterday at " + local_dt.strftime("%-I:%M %p").lower()
        else:
            local_dt = datetime.fromtimestamp(ts)
            relative = local_dt.strftime("%b %-d at %-I:%M %p").lower()

        submissions.append({
            "id": r["id"],
            "region": r["region_name"],
            "verdict": r["verdict"],
            "start_time": r["start_time"] or "",
            "end_time": r["end_time"] or "",
            "summary": r["summary"] or "",
            "confidence": r["confidence"] or "",
            "relative": relative,
            "meteorologist": r["meteorologist_name"],
        })

    # Also show today's submission count as a small at-a-glance metric
    midnight = int(datetime.now().replace(
        hour=0, minute=0, second=0, microsecond=0
    ).timestamp())
    submissions_today = sum(1 for s in rows if s["submitted_at"] >= midnight)

    return render_template_string(
        METEOROLOGIST_PORTAL_TEMPLATE,
        submissions=submissions,
        submissions_today=submissions_today,
    )


@app.get("/meteorologist/<claim_token>")
def meteorologist_view(claim_token: str):
    """Meteorologist taps the link in their SMS and lands here.
    Auth is the token itself — it's a 32-char URL-safe random secret in
    a private SMS, so possession proves authorization. For v1 this is fine;
    for v2 add a meteorologist account system."""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM verification_requests WHERE claim_token = %s",
                (claim_token,),
            )
            row = cur.fetchone()
    if not row:
        abort(404)

    if row["status"] == "paid":
        # First view — mark it claimed so the dashboard shows accountability.
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE verification_requests SET status='claimed', claimed_at=%s, updated_at=%s WHERE id=%s",
                    (now_ts(), now_ts(), row["id"]),
                )

    return render_template_string(METEOROLOGIST_TEMPLATE, row=dict(row),
                                  sla_minutes=SLA_MINUTES, now=now_ts())


@app.post("/meteorologist/<claim_token>/complete")
def meteorologist_complete(claim_token: str):
    """Meteorologist submits their verdict. We mark completed and SMS customer."""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM verification_requests WHERE claim_token = %s",
                (claim_token,),
            )
            row = cur.fetchone()
    if not row:
        abort(404)
    if row["status"] == "completed":
        # Idempotent — meteorologist double-submitted, just show them the page
        return redirect(f"/meteorologist/{claim_token}")

    verdict = (request.form.get("verdict") or "").strip()
    notes = (request.form.get("notes") or "").strip()
    if not verdict:
        abort(400)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE verification_requests
                   SET status='completed', completed_at=%s, updated_at=%s,
                       meteorologist_verdict=%s, meteorologist_notes=%s
                   WHERE id=%s""",
                (now_ts(), now_ts(), verdict, notes, row["id"]),
            )

    # Customer SMS — verdict ready. We don't dump the full text into SMS
    # because that gets unwieldy; we link them back to the standby page
    # which will now show the verdict.
    customer_msg = (
        f"WeatherValet: Your meteorologist's call is ready. "
        f"{verdict[:120]}{'…' if len(verdict) > 120 else ''} "
        f"View full brief: {FRONTEND_BASE_URL}/verification/standby?rid={row['id']}"
    )
    send_sms(row["customer_phone"], customer_msg)

    return redirect(f"/meteorologist/{claim_token}")


# ────────────────────────────────────────────────────────────────────────────
# Tiny operator dashboard (admin) — see everything that's happening
# ────────────────────────────────────────────────────────────────────────────


def _admin_auth():
    """Shared HTTP Basic Auth for all /admin/* routes. Returns None when
    auth passes, or a Flask response when it doesn't.

    If WV_ADMIN_USER / WV_ADMIN_PASS aren't set, auth is skipped. That's
    convenient for local dev but ALWAYS set them in production — the
    dashboard exposes customer phone numbers and revenue data."""
    admin_user = os.environ.get("WV_ADMIN_USER")
    admin_pass = os.environ.get("WV_ADMIN_PASS")
    if not (admin_user and admin_pass):
        return None
    auth = request.authorization
    if not auth or auth.username != admin_user or auth.password != admin_pass:
        return ("Auth required", 401, {"WWW-Authenticate": 'Basic realm="WV Admin"'})
    return None


def _classify_meteorologist_verdict(verdict_text: str) -> str:
    """Bin a free-text meteorologist verdict into {clear, caution, risk} so we
    can compare it against the AI's verdict. Imperfect — meteorologists write
    nuanced prose — but correct enough to be a useful operational signal.

    Strategy: scan for explicit risk/caution keywords first (because a verdict
    that says 'mostly clear but watch the wind' is really a Caution call),
    then fall back to clear keywords, then default to caution.

    The dashboard shows the raw verdict alongside this classification so a
    human can sanity-check when something looks off."""
    if not verdict_text:
        return "unknown"
    t = verdict_text.lower()

    # Risk keywords — anything implying re-plan, cancel, severe weather, stop work
    risk_words = (
        "re-plan", "replan", "reschedule", "cancel", "do not", "don't",
        "stop work", "stop-work", "unsafe", "dangerous", "severe", "tornado",
        "hail", "lightning risk", "lightning expected",
        "storms expected", "storms developing", "thunderstorm",
        "rain expected during", "rain during your", "wet conditions",
    )
    if any(w in t for w in risk_words):
        return "risk"

    # Caution keywords — watch this, monitor, possible, marginal, borderline
    caution_words = (
        "watch", "monitor", "marginal", "borderline", "uncertain",
        "scattered", "possible", "have a backup", "backup plan",
        "secure your", "windy", "breezy", "gusts", "shower",
        "may want to", "consider delaying", "consider rescheduling",
        "be ready", "keep an eye",
    )
    if any(w in t for w in caution_words):
        return "caution"

    # Clear keywords — go ahead, looks good, all clear, dry, fine
    clear_words = (
        "looks good", "all clear", "go ahead", "good to go",
        "you're clear", "youre clear", "no concerns", "all dry",
        "dry window", "clear window", "fine for", "trust the valet",
        "clear all day", "clear through", "we're clear", "were clear",
    )
    if any(w in t for w in clear_words):
        return "clear"

    # Defensive default — if we can't classify, it's safer to call it caution
    # than risk (avoids over-counting disagreements with AI=clear) or clear
    # (avoids under-counting disagreements with AI=risk).
    return "caution"


@app.get("/admin/queue")
def admin_queue():
    """The original simple queue view. Kept for backwards compatibility —
    /admin/dashboard is the richer version with summary stats."""
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, created_at, status, tier, customer_phone,
                          plan_text, plan_location, ai_status_key,
                          claimed_at, completed_at
                   FROM verification_requests
                   WHERE created_at > %s
                   ORDER BY created_at DESC LIMIT 100""",
                (now_ts() - 86400 * 7,),
            )
            rows = cur.fetchall()
            cur.execute(
                """SELECT status, COUNT(*) as n FROM verification_requests
                   WHERE created_at > %s GROUP BY status""",
                (now_ts() - 86400 * 7,),
            )
            counts = cur.fetchall()
    return render_template_string(
        ADMIN_TEMPLATE,
        rows=[dict(r) for r in rows],
        counts={r["status"]: r["n"] for r in counts},
        sla_minutes=SLA_MINUTES, now=now_ts(),
    )


@app.get("/admin/dashboard")
def admin_dashboard():
    """The operator dashboard — today's tickets, summary stats, AI-vs-human
    disagreement rate. This is what Timmy and the team look at to know
    what's happening right now.

    Today is defined as 'since local midnight' from the server's perspective.
    For US deployments we use the server clock; if you're running this in
    a UTC container but operating in EST, set the TZ env var on the
    container to America/New_York."""
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp

    # Compute "today" as the start of the current local day. We use the
    # server's local time — set TZ=America/Indianapolis on your container
    # for the founding territory.
    import datetime as _dt
    midnight = int(_dt.datetime.now().replace(
        hour=0, minute=0, second=0, microsecond=0
    ).timestamp())

    with db() as conn:
        with conn.cursor() as cur:
            # Today's tickets, ordered with most recent first
            cur.execute(
                """SELECT id, created_at, status, tier, price_cents,
                          customer_phone, plan_text, plan_location,
                          ai_status_key, claimed_at, completed_at,
                          meteorologist_verdict
                   FROM verification_requests
                   WHERE created_at >= %s
                   ORDER BY created_at DESC""",
                (midnight,),
            )
            today_rows = cur.fetchall()

            # Summary counts — today only
            # Total tickets includes everything created today regardless of
            # whether payment cleared; pending/completed counts are subsets.
            total_today = len(today_rows)
            pending_count = sum(
                1 for r in today_rows if r["status"] in ("pending", "paid", "claimed")
            )
            completed_count = sum(1 for r in today_rows if r["status"] == "completed")
            expired_count = sum(1 for r in today_rows if r["status"] == "expired")

            # Revenue today — only count requests that actually paid (paid + later)
            revenue_cents = sum(
                r["price_cents"] for r in today_rows
                if r["status"] in ("paid", "claimed", "completed")
            )

            # Overdue count — requests past SLA that haven't completed
            now = now_ts()
            overdue_count = sum(
                1 for r in today_rows
                if r["status"] in ("pending", "paid", "claimed")
                and (now - r["created_at"]) // 60 >= SLA_MINUTES
            )

            # AI vs Human disagreement — across ALL completed requests in the
            # last 30 days, not just today, because the daily volume is small
            # and the metric is noisy on tiny samples. We surface "today's"
            # numbers in the per-row table; the headline rate is over time.
            cur.execute(
                """SELECT ai_status_key, meteorologist_verdict
                   FROM verification_requests
                   WHERE status = 'completed'
                     AND created_at >= %s
                     AND ai_status_key IS NOT NULL
                     AND meteorologist_verdict IS NOT NULL""",
                (now - 86400 * 30,),
            )
            completed_history = cur.fetchall()

    # Walk completed history and classify each meteorologist verdict
    total_compared = 0
    disagreements = 0
    disagree_breakdown = {"clear→risk": 0, "clear→caution": 0,
                          "caution→clear": 0, "caution→risk": 0,
                          "risk→clear": 0, "risk→caution": 0}
    for row in completed_history:
        ai = row["ai_status_key"]
        human = _classify_meteorologist_verdict(row["meteorologist_verdict"])
        if ai not in ("clear", "caution", "risk") or human == "unknown":
            continue
        total_compared += 1
        if ai != human:
            disagreements += 1
            key = f"{ai}→{human}"
            if key in disagree_breakdown:
                disagree_breakdown[key] += 1

    disagreement_rate = (disagreements / total_compared) if total_compared else 0.0

    # Per-row decoration for the today table
    rows_decorated = []
    for row in today_rows:
        d = dict(row)
        d["elapsed_min"] = (now - row["created_at"]) // 60
        d["overdue"] = (
            row["status"] in ("pending", "paid", "claimed")
            and d["elapsed_min"] >= SLA_MINUTES
        )
        d["is_paid_request"] = row["status"] in ("paid", "claimed", "completed")
        # Per-row disagreement flag for completed rows
        if row["status"] == "completed" and row["meteorologist_verdict"]:
            human = _classify_meteorologist_verdict(row["meteorologist_verdict"])
            d["human_classification"] = human
            d["is_disagreement"] = (
                row["ai_status_key"] in ("clear", "caution", "risk")
                and human in ("clear", "caution", "risk")
                and row["ai_status_key"] != human
            )
        else:
            d["human_classification"] = None
            d["is_disagreement"] = False
        # Truncate plan text for the table without losing the location
        d["plan_short"] = (row["plan_text"][:60] + "…") if len(row["plan_text"]) > 60 else row["plan_text"]
        rows_decorated.append(d)

    return render_template_string(
        DASHBOARD_TEMPLATE,
        rows=rows_decorated,
        total_today=total_today,
        pending_count=pending_count,
        completed_count=completed_count,
        expired_count=expired_count,
        overdue_count=overdue_count,
        revenue_cents=revenue_cents,
        disagreement_rate=disagreement_rate,
        disagreement_total=total_compared,
        disagreement_count=disagreements,
        disagree_breakdown=disagree_breakdown,
        sla_minutes=SLA_MINUTES,
        now=now,
    )


@app.get("/admin/brief")
def admin_brief_form():
    """Render the Submit Daily Brief form. Pre-populates the region dropdown
    from regions already in the brief, so meteorologists can quickly add an
    update to an existing region without retyping the name."""
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp

    current = _load_brief_for_edit()

    # Build a list of "your existing regions" for quick re-selection. Each
    # entry shows the region's current verdict + freshness so the meteorologist
    # can see at a glance what's already on file.
    existing_regions = []
    for r in current.get("regions", []):
        existing_regions.append({
            "name": r.get("name", ""),
            "verdict": r.get("verdict", "unknown"),
            "windows": len(r.get("windows", [])),
        })

    # Optional ?region=Boone County, IN query param to preselect
    preselect = request.args.get("region", "")
    saved = request.args.get("saved") == "1"

    return render_template_string(
        BRIEF_FORM_TEMPLATE,
        existing_regions=existing_regions,
        preselect=preselect,
        saved=saved,
        meteorologist_default=current.get("meteorologist", "WeatherValet Meteorologist"),
        last_generated_at=current.get("generated_at", ""),
    )


@app.post("/admin/brief")
def admin_brief_submit():
    """Handle the form POST. Merges the submission into the on-disk JSON
    brief and redirects back to the form with ?saved=1 for the success flash."""
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp

    submission = {
        "region_name": request.form.get("region_name", "").strip(),
        "verdict": request.form.get("verdict", "").strip(),
        "start_time": request.form.get("start_time", "").strip(),
        "end_time": request.form.get("end_time", "").strip(),
        "summary": request.form.get("summary", "").strip(),
        "confidence": request.form.get("confidence", "medium").strip(),
        "notes": request.form.get("notes", "").strip(),
        "meteorologist_name": request.form.get("meteorologist_name", "").strip(),
    }

    # Custom region — when the meteorologist picks "Other / new region" from
    # the dropdown, the actual name comes from a separate text input.
    if submission["region_name"] == "__new__":
        submission["region_name"] = request.form.get("region_name_new", "").strip()

    if not submission["region_name"]:
        return render_template_string(
            BRIEF_FORM_TEMPLATE,
            existing_regions=[],
            preselect="",
            saved=False,
            error="Please choose or type a region name.",
            meteorologist_default=submission.get("meteorologist_name", "WeatherValet Meteorologist"),
            last_generated_at="",
        ), 400

    try:
        merge_brief_submission(submission)
    except ValueError as e:
        return render_template_string(
            BRIEF_FORM_TEMPLATE,
            existing_regions=[],
            preselect="",
            saved=False,
            error=str(e),
            meteorologist_default=submission.get("meteorologist_name", "WeatherValet Meteorologist"),
            last_generated_at="",
        ), 400

    # Redirect-after-POST so a refresh doesn't resubmit. ?saved=1 triggers
    # the success flash, region= preselects the region the user just edited
    # (so adding a second window for the same region is one click away).
    return redirect(
        f"/admin/brief?saved=1&region={request.form.get('region_name', '')}"
    )


@app.get("/healthz")
def healthz():
    """Liveness probe — useful for container orchestrators."""
    return jsonify({"ok": True, "ts": now_ts()})


# ════════════════════════════════════════════════════════════════════════════
# Templates — minimal HTML, brand voice intact
# ════════════════════════════════════════════════════════════════════════════
#
# These are intentionally simple. The meteorologist page only needs to be
# usable on a phone (Timmy will tap his SMS link from his pocket). The admin
# page is a glance-able status board.

METEOROLOGIST_TEMPLATE = """\
<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>WV Verification #{{ row.id }}</title>
<style>
  body { font-family: system-ui, -apple-system, sans-serif; max-width: 720px;
         margin: 0 auto; padding: 16px; color: #0E1116; }
  h1 { font-size: 18px; margin: 0 0 4px; }
  .meta { color: #555; font-size: 13px; margin-bottom: 16px; }
  .ai-brief { background: #f5f6f8; border-radius: 8px; padding: 12px;
              white-space: pre-wrap; font-size: 13px; line-height: 1.5;
              margin: 12px 0; max-height: 320px; overflow: auto; }
  .plan { background: #fff; border: 1px solid rgba(15,17,22,0.10);
          border-radius: 8px; padding: 12px; margin: 12px 0; }
  .plan strong { color: #4169E1; }
  textarea, input { width: 100%; padding: 10px; font: inherit;
                    border: 1px solid #ccc; border-radius: 6px; margin: 4px 0; }
  textarea { min-height: 80px; }
  button { background: #4169E1; color: #fff; padding: 12px 16px;
           border: none; border-radius: 8px; font-weight: 600; font-size: 15px;
           width: 100%; cursor: pointer; margin-top: 8px; }
  .completed { background: #d1f4dd; padding: 16px; border-radius: 8px;
               border-left: 4px solid #12A150; margin: 12px 0; }
  .pill { display: inline-block; padding: 2px 8px; border-radius: 999px;
          font-size: 11px; font-weight: 700; letter-spacing: 0.6px;
          text-transform: uppercase; }
  .pill-clear { background: #d1f4dd; color: #0a6e35; }
  .pill-caution { background: #fff0c6; color: #8a5a0a; }
  .pill-risk { background: #fcd9d6; color: #9b2823; }
</style></head><body>

<h1>Verification Request #{{ row.id }}</h1>
<div class="meta">
  Tier: <strong>{{ row.tier }}</strong> · ${{ '%.2f' % (row.price_cents / 100) }} ·
  Status: <span class="pill pill-{{ row.ai_status_key or 'caution' }}">{{ row.status }}</span> ·
  {% set elapsed = (now - row.created_at) // 60 %}
  Elapsed: {{ elapsed }} min{% if elapsed >= sla_minutes %} ⚠️ overdue{% endif %}
</div>

<div class="plan">
  <div><strong>Plan:</strong> {{ row.plan_text }}</div>
  {% if row.plan_location %}<div><strong>Location:</strong> {{ row.plan_location }}</div>{% endif %}
  {% if row.plan_window %}<div><strong>Window:</strong> {{ row.plan_window }}</div>{% endif %}
  <div><strong>AI verdict:</strong>
    <span class="pill pill-{{ row.ai_status_key or 'caution' }}">{{ row.ai_status_key or 'unknown' }}</span></div>
</div>

<details open>
  <summary><strong>AI pre-synthesized brief</strong></summary>
  <div class="ai-brief">{{ row.ai_brief_markdown }}</div>
</details>

{% if row.status == 'completed' %}
  <div class="completed">
    <strong>Completed.</strong> Customer has been notified via SMS.
    <p style="white-space:pre-wrap">{{ row.meteorologist_verdict }}</p>
    {% if row.meteorologist_notes %}
      <p style="font-size:12px;color:#555;white-space:pre-wrap">Notes: {{ row.meteorologist_notes }}</p>
    {% endif %}
  </div>
{% else %}
  <form method="POST" action="/meteorologist/{{ row.claim_token }}/complete">
    <label><strong>Your verdict</strong> (this is what the customer sees first)</label>
    <textarea name="verdict" required placeholder="Window looks good. Hold the pour for the morning to dodge the afternoon line. Trust the Valet."></textarea>
    <label><strong>Internal notes</strong> (not shown to customer)</label>
    <textarea name="notes" placeholder="HRRR vs RAP disagreement on convection timing; went with HRRR."></textarea>
    <button type="submit">Submit Verdict</button>
  </form>
{% endif %}

</body></html>
"""

ADMIN_TEMPLATE = """\
<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>WV Valet Admin</title>
<style>
  body { font-family: system-ui, sans-serif; max-width: 1100px; margin: 16px auto;
         padding: 0 16px; color: #0E1116; }
  h1 { font-size: 22px; }
  .counts { display: flex; gap: 12px; margin: 16px 0; flex-wrap: wrap; }
  .count { background: #f5f6f8; padding: 10px 16px; border-radius: 8px; }
  .count strong { font-size: 22px; display: block; }
  table { width: 100%; border-collapse: collapse; font-size: 13px; }
  th, td { padding: 8px; text-align: left; border-bottom: 1px solid #eee; }
  th { background: #f5f6f8; font-weight: 600; }
  tr.overdue { background: #fef0ec; }
  .pill { display: inline-block; padding: 2px 6px; border-radius: 999px;
          font-size: 10px; font-weight: 700; }
  .pending { background: #f0f0f0; color: #666; }
  .paid { background: #cee9ff; color: #1d4d8c; }
  .claimed { background: #fff0c6; color: #8a5a0a; }
  .completed { background: #d1f4dd; color: #0a6e35; }
  .expired { background: #fcd9d6; color: #9b2823; }
</style></head><body>

<h1>WeatherValet Verification Queue</h1>
<div class="counts">
  {% for label in ['pending','paid','claimed','completed','expired'] %}
    <div class="count"><strong>{{ counts.get(label, 0) }}</strong>{{ label }}</div>
  {% endfor %}
</div>

<table>
<thead><tr><th>#</th><th>Created</th><th>Status</th><th>Tier</th><th>Plan</th>
<th>Phone</th><th>Elapsed</th><th></th></tr></thead>
<tbody>
{% for r in rows %}
  {% set elapsed = (now - r.created_at) // 60 %}
  {% set overdue = r.status not in ('completed','expired') and elapsed >= sla_minutes %}
  <tr {% if overdue %}class="overdue"{% endif %}>
    <td>{{ r.id }}</td>
    <td>{{ r.created_at | int }}</td>
    <td><span class="pill {{ r.status }}">{{ r.status }}</span></td>
    <td>{{ r.tier }}</td>
    <td>{{ r.plan_text[:80] }}{% if r.plan_text|length > 80 %}…{% endif %}<br>
        <small>{{ r.plan_location or '' }}</small></td>
    <td>{{ r.customer_phone }}</td>
    <td>{{ elapsed }}m{% if overdue %} ⚠️{% endif %}</td>
    <td>{% if r.status in ('paid','claimed') %}
      <a href="/admin/jump/{{ r.id }}">open</a>{% endif %}</td>
  </tr>
{% endfor %}
</tbody></table>

</body></html>
"""


# Operator dashboard — the richer view at /admin/dashboard. Functional, not
# fancy. Server-rendered. No JS dependencies. Reload the page to refresh.
DASHBOARD_TEMPLATE = """\
<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>WeatherValet · Operator Dashboard</title>
<style>
  body { font-family: system-ui, -apple-system, sans-serif;
         max-width: 1180px; margin: 0 auto; padding: 24px 16px;
         color: #0E1116; background: #fafbfc; }
  h1 { font-size: 24px; margin: 0 0 4px; }
  .subhead { color: #555; font-size: 14px; margin-bottom: 24px; }
  /* Top nav with prominent CTA */
  .hud-nav {
    display: flex; align-items: center; justify-content: space-between;
    gap: 16px; flex-wrap: wrap;
    margin: 8px 0 24px;
  }
  .hud-nav-meta { color: #555; font-size: 13px; }
  .hud-nav-meta a { color: #4169E1; text-decoration: none; }
  .hud-nav-cta {
    display: inline-flex; align-items: center; gap: 8px;
    padding: 10px 16px;
    background: #4169E1;
    color: #fff;
    text-decoration: none;
    font-size: 14px; font-weight: 600;
    border-radius: 10px;
    box-shadow: 0 4px 12px rgba(65,105,225,0.20);
    transition: all 120ms ease;
  }
  .hud-nav-cta:hover {
    box-shadow: 0 6px 16px rgba(65,105,225,0.28);
    transform: translateY(-1px);
  }
  .subhead a { color: #4169E1; text-decoration: none; }

  /* Summary cards row */
  .cards { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr));
           gap: 12px; margin: 0 0 24px; }
  .card { background: #fff; padding: 16px 18px; border-radius: 10px;
          border: 1px solid rgba(15,17,22,0.08); }
  .card .label { font-size: 11px; font-weight: 700; letter-spacing: 1.4px;
                 text-transform: uppercase; color: rgba(15,17,22,0.55);
                 margin-bottom: 6px; }
  .card .value { font-size: 28px; font-weight: 700; line-height: 1; }
  .card .sub { font-size: 12px; color: rgba(15,17,22,0.55); margin-top: 4px; }
  .card.alert { background: #fef0ec; border-color: rgba(194,52,43,0.30); }
  .card.alert .value { color: #9b2823; }
  .card.alert .label { color: #9b2823; }
  .card.good { background: #ecf9f0; border-color: rgba(18,161,80,0.30); }
  .card.good .value { color: #0a6e35; }

  /* Disagreement panel — second row of summary */
  .disagreement {
    background: #fff; padding: 16px 18px; border-radius: 10px;
    border: 1px solid rgba(15,17,22,0.08); margin-bottom: 24px;
  }
  .disagreement-head { display: flex; justify-content: space-between;
                       align-items: baseline; margin-bottom: 8px; }
  .disagreement-rate { font-size: 22px; font-weight: 700; }
  .disagreement-detail { font-size: 12px; color: rgba(15,17,22,0.55); }
  .disagreement-breakdown { font-family: 'JetBrains Mono', monospace;
                            font-size: 11px; color: rgba(15,17,22,0.65);
                            display: flex; gap: 14px; flex-wrap: wrap; }
  .disagreement-breakdown span { white-space: nowrap; }

  /* Today's tickets table */
  h2 { font-size: 16px; margin: 24px 0 8px; }
  table { width: 100%; border-collapse: collapse; font-size: 13px;
          background: #fff; border-radius: 10px; overflow: hidden;
          box-shadow: 0 1px 2px rgba(15,17,22,0.04); }
  th { background: #f5f6f8; padding: 10px 8px; text-align: left;
       font-weight: 600; font-size: 11px; letter-spacing: 1.0px;
       text-transform: uppercase; color: rgba(15,17,22,0.55);
       border-bottom: 1px solid rgba(15,17,22,0.08); }
  td { padding: 10px 8px; border-bottom: 1px solid rgba(15,17,22,0.05);
       vertical-align: top; }
  tr:last-child td { border-bottom: none; }

  /* Highlight Live Valet rows (paid + onward) — these are the moneymakers */
  tr.lv-paid { background: rgba(65,105,225,0.04); }
  tr.lv-paid td:first-child { border-left: 3px solid #4169E1; padding-left: 6px; }

  /* Overdue rows pop red */
  tr.overdue { background: #fef0ec; }
  tr.overdue td:first-child { border-left: 3px solid #C2342B; padding-left: 6px; }

  /* Disagreement highlight on completed rows */
  tr.disagree { background: #fff7e8; }
  tr.disagree td:first-child { border-left: 3px solid #E8A400; padding-left: 6px; }

  .pill { display: inline-block; padding: 2px 8px; border-radius: 999px;
          font-size: 10px; font-weight: 700; letter-spacing: 0.6px;
          text-transform: uppercase; }
  .pill-pending { background: #f0f0f0; color: #666; }
  .pill-paid { background: #cee9ff; color: #1d4d8c; }
  .pill-claimed { background: #fff0c6; color: #8a5a0a; }
  .pill-completed { background: #d1f4dd; color: #0a6e35; }
  .pill-expired { background: #fcd9d6; color: #9b2823; }

  .verdict-pill { display: inline-block; padding: 1px 6px; border-radius: 4px;
                  font-size: 10px; font-weight: 700; }
  .v-clear { background: #d1f4dd; color: #0a6e35; }
  .v-caution { background: #fff0c6; color: #8a5a0a; }
  .v-risk { background: #fcd9d6; color: #9b2823; }
  .v-arrow { color: rgba(15,17,22,0.45); margin: 0 4px; }

  .legend { font-size: 11px; color: rgba(15,17,22,0.55); margin: 12px 0;
            display: flex; gap: 16px; flex-wrap: wrap; }
  .legend-swatch { display: inline-block; width: 8px; height: 8px;
                   border-radius: 2px; margin-right: 4px; vertical-align: middle; }

  .empty { padding: 40px 16px; text-align: center; color: rgba(15,17,22,0.55);
           background: #fff; border-radius: 10px; }
  a.btn { color: #4169E1; text-decoration: none; font-size: 12px;
          font-weight: 600; }
  a.btn:hover { text-decoration: underline; }
</style></head><body>

<h1>WeatherValet · Operator Dashboard</h1>
<div class="hud-nav">
  <div class="hud-nav-meta">Today's queue · refresh page to update · <a href="/admin/queue">simple queue view</a></div>
  <a href="/admin/brief" class="hud-nav-cta">
    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" width="16" height="16">
      <path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/>
      <polyline points="14 2 14 8 20 8"/>
      <line x1="12" y1="18" x2="12" y2="12"/>
      <line x1="9" y1="15" x2="15" y2="15"/>
    </svg>
    Submit Daily Brief
  </a>
</div>

<!-- ── Summary cards ── -->
<div class="cards">
  <div class="card">
    <div class="label">Today</div>
    <div class="value">{{ total_today }}</div>
    <div class="sub">tickets created</div>
  </div>
  <div class="card{% if pending_count > 0 %} alert{% endif %}">
    <div class="label">In flight</div>
    <div class="value">{{ pending_count }}</div>
    <div class="sub">pending · paid · claimed</div>
  </div>
  <div class="card{% if completed_count > 0 %} good{% endif %}">
    <div class="label">Completed</div>
    <div class="value">{{ completed_count }}</div>
    <div class="sub">verdict delivered</div>
  </div>
  <div class="card{% if overdue_count > 0 %} alert{% endif %}">
    <div class="label">Overdue</div>
    <div class="value">{{ overdue_count }}</div>
    <div class="sub">past {{ sla_minutes }}min SLA</div>
  </div>
  <div class="card{% if revenue_cents > 0 %} good{% endif %}">
    <div class="label">Revenue today</div>
    <div class="value">${{ '%.2f' % (revenue_cents / 100) }}</div>
    <div class="sub">paid + completed</div>
  </div>
</div>

<!-- ── AI vs Human disagreement panel ── -->
<div class="disagreement">
  <div class="disagreement-head">
    <strong>AI vs Human verdict — last 30 days</strong>
    <span class="disagreement-rate">
      {% if disagreement_total > 0 %}
        {{ '%.0f' % (disagreement_rate * 100) }}% disagree
      {% else %}
        — no data yet
      {% endif %}
    </span>
  </div>
  <div class="disagreement-detail">
    {% if disagreement_total > 0 %}
      {{ disagreement_count }} of {{ disagreement_total }} completed verifications had a meteorologist verdict that disagreed with the AI's call.
    {% else %}
      No completed verifications in the last 30 days yet. Disagreement rate appears once meteorologists start submitting verdicts.
    {% endif %}
  </div>
  {% if disagreement_total > 0 %}
    <div class="disagreement-breakdown" style="margin-top: 8px;">
      {% for label, count in disagree_breakdown.items() %}
        {% if count > 0 %}<span>{{ label }}: {{ count }}</span>{% endif %}
      {% endfor %}
    </div>
  {% endif %}
</div>

<!-- ── Today's tickets table ── -->
<h2>Today's tickets</h2>
<div class="legend">
  <span><span class="legend-swatch" style="background:#4169E1"></span>Live Valet (paid)</span>
  <span><span class="legend-swatch" style="background:#C2342B"></span>Overdue</span>
  <span><span class="legend-swatch" style="background:#E8A400"></span>AI/human disagreement</span>
</div>

{% if rows %}
<table>
  <thead><tr>
    <th>#</th>
    <th>Created</th>
    <th>Status</th>
    <th>Tier</th>
    <th>Plan / Location</th>
    <th>Phone</th>
    <th>Elapsed</th>
    <th>AI → Human</th>
    <th></th>
  </tr></thead>
  <tbody>
  {% for r in rows %}
    {% set classes = [] %}
    {% if r.is_paid_request %}{% set _ = classes.append('lv-paid') %}{% endif %}
    {% if r.overdue %}{% set _ = classes.append('overdue') %}{% endif %}
    {% if r.is_disagreement %}{% set _ = classes.append('disagree') %}{% endif %}
    <tr {% if classes %}class="{{ classes | join(' ') }}"{% endif %}>
      <td>{{ r.id }}</td>
      <td>{{ r.created_at | int }}<br>
          <small style="color:#999;font-family:'JetBrains Mono',monospace">
            {{ ((now - r.created_at) // 60) }}m ago
          </small></td>
      <td><span class="pill pill-{{ r.status }}">{{ r.status }}</span></td>
      <td>{{ r.tier }}<br><small>${{ '%.0f' % (r.price_cents / 100) }}</small></td>
      <td>{{ r.plan_short }}<br>
          <small style="color:#666">{{ r.plan_location or '—' }}</small></td>
      <td><small style="font-family:'JetBrains Mono',monospace">{{ r.customer_phone or '—' }}</small></td>
      <td>
        {{ r.elapsed_min }}m
        {% if r.overdue %}<span style="color:#C2342B">⚠️</span>{% endif %}
      </td>
      <td>
        {% if r.ai_status_key %}
          <span class="verdict-pill v-{{ r.ai_status_key }}">{{ r.ai_status_key }}</span>
        {% else %}—{% endif %}
        {% if r.human_classification %}
          <span class="v-arrow">→</span>
          <span class="verdict-pill v-{{ r.human_classification }}">{{ r.human_classification }}</span>
        {% endif %}
      </td>
      <td>
        {% if r.status in ('paid','claimed') %}
          <a class="btn" href="/admin/jump/{{ r.id }}">open →</a>
        {% elif r.status == 'completed' %}
          <a class="btn" href="/admin/jump/{{ r.id }}">view</a>
        {% endif %}
      </td>
    </tr>
  {% endfor %}
  </tbody>
</table>
{% else %}
  <div class="empty">No tickets yet today.</div>
{% endif %}

</body></html>
"""


# Submit Daily Brief form — the meteorologist-facing tool. Mobile-first:
# single column, large touch targets, native iOS/Android time pickers,
# big tappable verdict and confidence selectors, an obvious primary action.
# The whole point is that a meteorologist standing in the field can post
# an update in 30 seconds without thinking about JSON or schemas.


# Meteorologist Portal — the home page a meteorologist sees when they log in.
# Two things only: a prominent Submit Daily Brief button at the top, and a
# scannable list of recent submissions below it. Calm, mobile-first, no
# operator-grade summary cards or queue tables (that's the operator's job
# at /admin/dashboard, not the meteorologist's). The portal speaks to one
# person doing one thing: publishing weather calls.
METEOROLOGIST_PORTAL_TEMPLATE = """\
<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Meteorologist Portal · WeatherValet</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Fraunces:wght@400;500;600;700&family=Inter:wght@400;500;600;700&family=JetBrains+Mono:wght@500;700&display=swap" rel="stylesheet">
<style>
  :root {
    --rb: #4169E1; --ink: #0E1116;
    --muted: rgba(15,17,22,0.55);
    --line: rgba(15,17,22,0.08);
    --bg: #fafbfc;
    --tap: 48px;
  }
  *, *::before, *::after { box-sizing: border-box; }
  body {
    font-family: 'Inter', -apple-system, system-ui, sans-serif;
    background: var(--bg);
    color: var(--ink);
    margin: 0;
    -webkit-font-smoothing: antialiased;
    padding: 0 0 32px;
  }

  /* ── Header — quiet, grounding ── */
  .portal-head {
    background: #fff;
    border-bottom: 1px solid var(--line);
    padding: 16px;
  }
  .portal-eyebrow {
    font-family: 'JetBrains Mono', monospace;
    font-size: 10px;
    font-weight: 700;
    letter-spacing: 1.6px;
    text-transform: uppercase;
    color: var(--rb);
    margin-bottom: 4px;
  }
  .portal-title {
    font-family: 'Fraunces', Georgia, serif;
    font-size: 22px;
    font-weight: 600;
    margin: 0;
    letter-spacing: -0.2px;
  }
  .portal-greeting {
    font-size: 13px;
    color: var(--muted);
    margin: 4px 0 0;
  }

  .container {
    max-width: 580px;
    margin: 0 auto;
    padding: 16px;
  }

  /* ── The big primary action — this is the page's reason to exist ── */
  .primary-action {
    display: flex;
    flex-direction: column;
    align-items: center;
    justify-content: center;
    gap: 10px;
    width: 100%;
    min-height: 120px;
    padding: 24px 20px;
    background: var(--rb);
    color: #fff;
    border: none;
    border-radius: 18px;
    text-decoration: none;
    text-align: center;
    cursor: pointer;
    box-shadow: 0 12px 32px rgba(65,105,225,0.30);
    transition: transform 80ms ease, box-shadow 120ms ease;
    -webkit-tap-highlight-color: transparent;
  }
  .primary-action:hover {
    box-shadow: 0 16px 36px rgba(65,105,225,0.38);
    transform: translateY(-1px);
  }
  .primary-action:active {
    transform: translateY(0) scale(0.99);
  }
  .primary-icon {
    width: 36px;
    height: 36px;
    color: rgba(255,255,255,0.95);
  }
  .primary-label {
    font-family: 'Inter', system-ui, sans-serif;
    font-size: 18px;
    font-weight: 700;
    letter-spacing: 0.2px;
  }
  .primary-sub {
    font-size: 13px;
    font-weight: 500;
    color: rgba(255,255,255,0.80);
  }

  /* ── At-a-glance counter (today's submissions) ── */
  .meta-row {
    display: flex;
    align-items: center;
    justify-content: space-between;
    margin: 28px 4px 14px;
  }
  .section-label {
    font-family: 'JetBrains Mono', monospace;
    font-size: 11px;
    font-weight: 700;
    letter-spacing: 1.6px;
    text-transform: uppercase;
    color: var(--muted);
  }
  .today-count {
    font-family: 'JetBrains Mono', monospace;
    font-size: 11px;
    color: var(--muted);
  }
  .today-count strong {
    color: var(--ink);
    font-weight: 700;
  }

  /* ── Recent submission cards ── */
  .submission-list {
    display: flex;
    flex-direction: column;
    gap: 10px;
    list-style: none;
    padding: 0;
    margin: 0;
  }
  .submission {
    background: #fff;
    border: 1px solid var(--line);
    border-radius: 14px;
    padding: 14px 16px;
    transition: border-color 120ms ease;
  }
  .submission:hover {
    border-color: rgba(65,105,225,0.20);
  }
  .submission-head {
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 10px;
    margin-bottom: 6px;
  }
  .submission-region {
    font-weight: 600;
    font-size: 15px;
    color: var(--ink);
  }
  .submission-time {
    font-family: 'JetBrains Mono', monospace;
    font-size: 10px;
    color: var(--muted);
    letter-spacing: 0.4px;
    flex-shrink: 0;
    text-transform: lowercase;
  }
  .submission-meta {
    display: flex;
    align-items: center;
    gap: 8px;
    flex-wrap: wrap;
    font-size: 12px;
    color: var(--muted);
  }
  .submission-summary {
    margin: 8px 0 0;
    font-size: 13px;
    line-height: 1.5;
    color: rgba(15,17,22,0.75);
  }

  /* ── Verdict pills (color-coded) ── */
  .verdict-pill {
    display: inline-flex;
    align-items: center;
    gap: 4px;
    padding: 2px 10px;
    border-radius: 999px;
    font-size: 11px;
    font-weight: 700;
    letter-spacing: 0.4px;
    text-transform: capitalize;
  }
  .verdict-dry { background: rgba(18,161,80,0.10); color: #0a6e35; }
  .verdict-wet { background: rgba(37,102,214,0.10); color: #1d4d8c; }
  .verdict-mixed { background: rgba(232,164,0,0.12); color: #8a5a0a; }
  .verdict-stormy { background: rgba(194,52,43,0.10); color: #9b2823; }
  .verdict-clear { background: rgba(18,161,80,0.10); color: #0a6e35; }
  .verdict-unknown { background: rgba(15,17,22,0.06); color: var(--muted); }

  .window-label {
    font-family: 'JetBrains Mono', monospace;
    font-size: 11px;
    color: var(--muted);
  }
  .confidence-tag {
    font-family: 'JetBrains Mono', monospace;
    font-size: 10px;
    color: var(--muted);
    text-transform: uppercase;
    letter-spacing: 0.6px;
  }

  /* ── Empty state ── */
  .empty-state {
    text-align: center;
    padding: 40px 20px;
    background: #fff;
    border: 1.5px dashed var(--line);
    border-radius: 14px;
  }
  .empty-state svg {
    width: 36px;
    height: 36px;
    color: var(--muted);
    opacity: 0.5;
    margin-bottom: 8px;
  }
  .empty-state-text {
    color: var(--muted);
    font-size: 14px;
    line-height: 1.5;
  }

  .footer-link {
    margin-top: 28px;
    text-align: center;
  }
  .footer-link a {
    font-size: 12px;
    color: var(--muted);
    text-decoration: none;
    border-bottom: 1px dotted rgba(15,17,22,0.20);
    padding-bottom: 1px;
  }
  .footer-link a:hover {
    color: var(--rb);
    border-bottom-color: var(--rb);
  }

  /* ── Mobile tweaks ── */
  @media (max-width: 480px) {
    .portal-title { font-size: 19px; }
    .primary-action { min-height: 110px; padding: 20px 16px; }
    .primary-label { font-size: 16px; }
    .container { padding: 12px; }
  }
</style>
</head><body>

<header class="portal-head">
  <div style="max-width:580px;margin:0 auto">
    <div class="portal-eyebrow">Meteorologist Portal</div>
    <h1 class="portal-title">Welcome back.</h1>
    <p class="portal-greeting">Publish the day's call when you're ready.</p>
  </div>
</header>

<main class="container">

  <!-- ── The primary action — large, prominent, unmissable ── -->
  <a href="/admin/brief" class="primary-action">
    <svg class="primary-icon" viewBox="0 0 24 24" fill="none" stroke="currentColor"
         stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
      <path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/>
      <polyline points="14 2 14 8 20 8"/>
      <line x1="12" y1="18" x2="12" y2="12"/>
      <line x1="9" y1="15" x2="15" y2="15"/>
    </svg>
    <span class="primary-label">Submit Daily Brief</span>
    <span class="primary-sub">Update your call for any region · takes 30 seconds</span>
  </a>

  <!-- ── Recent submissions ── -->
  <div class="meta-row">
    <span class="section-label">Recent submissions</span>
    <span class="today-count">
      {% if submissions_today > 0 %}
        <strong>{{ submissions_today }}</strong> today
      {% else %}
        none today yet
      {% endif %}
    </span>
  </div>

  {% if submissions %}
  <ul class="submission-list">
    {% for s in submissions %}
    <li class="submission">
      <div class="submission-head">
        <span class="submission-region">{{ s.region }}</span>
        <span class="submission-time">{{ s.relative }}</span>
      </div>
      <div class="submission-meta">
        <span class="verdict-pill verdict-{{ s.verdict }}">{{ s.verdict }}</span>
        {% if s.start_time and s.end_time %}
          <span class="window-label">{{ s.start_time }}&ndash;{{ s.end_time }}</span>
        {% endif %}
        {% if s.confidence %}
          <span class="confidence-tag">{{ s.confidence }} conf.</span>
        {% endif %}
      </div>
      {% if s.summary %}
        <p class="submission-summary">{{ s.summary[:140] }}{% if s.summary|length > 140 %}…{% endif %}</p>
      {% endif %}
    </li>
    {% endfor %}
  </ul>
  {% else %}
  <div class="empty-state">
    <svg viewBox="0 0 24 24" fill="none" stroke="currentColor"
         stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round">
      <path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/>
      <polyline points="14 2 14 8 20 8"/>
    </svg>
    <p class="empty-state-text">
      No briefs submitted yet.<br>
      Tap <strong>Submit Daily Brief</strong> above to publish your first call.
    </p>
  </div>
  {% endif %}

  <div class="footer-link">
    <a href="/admin/dashboard">Operator Dashboard &rarr;</a>
  </div>

</main>

</body></html>
"""


# Submit Daily Brief form — the meteorologist-facing tool. Mobile-first:
# single column, large touch targets, native iOS/Android time pickers,
# big tappable verdict and confidence selectors, an obvious primary action.
# The whole point is that a meteorologist standing in the field can post
# an update in 30 seconds without thinking about JSON or schemas.
BRIEF_FORM_TEMPLATE = """\
<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Submit Daily Brief · WeatherValet</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Fraunces:wght@400;500;600;700&family=Inter:wght@400;500;600;700&family=JetBrains+Mono:wght@500;700&display=swap" rel="stylesheet">
<style>
  :root {
    --rb: #4169E1; --ink: #0E1116;
    --muted: rgba(15,17,22,0.55);
    --line: rgba(15,17,22,0.08);
    --bg: #fafbfc;
    --tap: 48px;  /* minimum touch target */
  }
  *, *::before, *::after { box-sizing: border-box; }
  body {
    font-family: 'Inter', -apple-system, system-ui, sans-serif;
    background: var(--bg);
    color: var(--ink);
    margin: 0;
    -webkit-font-smoothing: antialiased;
    padding: 0 0 80px;
  }

  /* ── Top nav (also serves as the HUD breadcrumb) ── */
  .nav {
    position: sticky; top: 0; z-index: 10;
    background: #fff;
    border-bottom: 1px solid var(--line);
    padding: 12px 16px;
    display: flex; align-items: center; gap: 12px;
  }
  .nav-back {
    color: var(--rb); text-decoration: none;
    font-size: 13px; font-weight: 600;
    display: inline-flex; align-items: center; gap: 4px;
    min-height: var(--tap); min-width: var(--tap);
    margin-left: -8px; padding: 0 8px;
  }
  .nav-title {
    font-family: 'Fraunces', Georgia, serif;
    font-size: 18px; font-weight: 600;
    margin: 0; flex: 1;
  }
  .nav-meta {
    font-size: 11px; font-family: 'JetBrains Mono', monospace;
    color: var(--muted); letter-spacing: 0.4px;
  }

  .container {
    max-width: 580px;
    margin: 0 auto;
    padding: 16px;
  }

  /* ── Success flash ── */
  .flash-success {
    background: #d1f4dd; border-left: 4px solid #12A150;
    padding: 14px 16px; border-radius: 10px;
    margin: 16px 0; font-size: 14px;
    display: flex; align-items: flex-start; gap: 10px;
  }
  .flash-success svg { flex-shrink: 0; color: #0a6e35; margin-top: 2px; }
  .flash-success strong { color: #0a6e35; }
  .flash-error {
    background: #fcd9d6; border-left: 4px solid #C2342B;
    padding: 14px 16px; border-radius: 10px;
    margin: 16px 0; font-size: 14px; color: #9b2823;
  }

  /* ── Form sections ── */
  .section { margin: 24px 0; }
  .section-label {
    font-family: 'JetBrains Mono', monospace;
    font-size: 11px; font-weight: 700;
    letter-spacing: 1.6px; text-transform: uppercase;
    color: var(--muted); margin-bottom: 10px;
  }
  .helper {
    font-size: 12px; color: var(--muted);
    margin: 6px 0 0; line-height: 1.5;
  }

  /* ── Inputs (large touch targets) ── */
  .input, .select, .textarea {
    width: 100%;
    min-height: var(--tap);
    padding: 12px 14px;
    border: 1.5px solid var(--line);
    border-radius: 12px;
    background: #fff;
    font: inherit; font-size: 16px;  /* 16px prevents iOS zoom-on-focus */
    color: var(--ink);
    transition: border-color 120ms ease;
  }
  .input:focus, .select:focus, .textarea:focus {
    outline: none;
    border-color: var(--rb);
    box-shadow: 0 0 0 3px rgba(65,105,225,0.15);
  }
  .textarea { min-height: 96px; resize: vertical; line-height: 1.5; }
  .select { appearance: none; -webkit-appearance: none;
    background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='%230E1116' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M6 9l6 6 6-6'/%3E%3C/svg%3E");
    background-repeat: no-repeat; background-position: right 14px center;
    background-size: 18px; padding-right: 42px;
  }

  /* ── Time-window pair: side-by-side on wide phones, stacks on narrow ── */
  .time-pair {
    display: grid;
    grid-template-columns: 1fr auto 1fr;
    gap: 8px;
    align-items: center;
  }
  .time-pair .input { font-family: 'JetBrains Mono', monospace; font-size: 16px; }
  .time-arrow { color: var(--muted); }

  /* ── Tappable choice buttons (verdict, confidence) ── */
  .choice-group {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(120px, 1fr));
    gap: 8px;
  }
  .choice {
    position: relative;
    min-height: var(--tap);
    padding: 12px 8px;
    border: 1.5px solid var(--line);
    border-radius: 12px;
    background: #fff;
    cursor: pointer;
    text-align: center;
    transition: all 120ms ease;
    font-size: 14px; font-weight: 600;
    color: var(--ink);
    -webkit-tap-highlight-color: transparent;
  }
  .choice input { position: absolute; opacity: 0; pointer-events: none; }
  .choice:hover { border-color: rgba(65,105,225,0.30); }
  .choice:has(input:checked) {
    border-color: var(--rb);
    background: rgba(65,105,225,0.06);
    box-shadow: 0 0 0 3px rgba(65,105,225,0.10);
  }
  .choice-emoji {
    display: block; font-size: 22px; margin-bottom: 4px;
    line-height: 1;
  }

  /* Verdict-specific colors when selected */
  .choice[data-verdict="dry"]:has(input:checked) {
    border-color: #12A150;
    background: rgba(18,161,80,0.07);
    box-shadow: 0 0 0 3px rgba(18,161,80,0.10);
  }
  .choice[data-verdict="dry"]:has(input:checked) .choice-label { color: #0a6e35; }
  .choice[data-verdict="wet"]:has(input:checked) {
    border-color: #2566D6;
    background: rgba(37,102,214,0.07);
    box-shadow: 0 0 0 3px rgba(37,102,214,0.10);
  }
  .choice[data-verdict="wet"]:has(input:checked) .choice-label { color: #1d4d8c; }
  .choice[data-verdict="mixed"]:has(input:checked) {
    border-color: #E8A400;
    background: rgba(232,164,0,0.07);
    box-shadow: 0 0 0 3px rgba(232,164,0,0.10);
  }
  .choice[data-verdict="mixed"]:has(input:checked) .choice-label { color: #8a5a0a; }
  .choice[data-verdict="stormy"]:has(input:checked) {
    border-color: #C2342B;
    background: rgba(194,52,43,0.07);
    box-shadow: 0 0 0 3px rgba(194,52,43,0.10);
  }
  .choice[data-verdict="stormy"]:has(input:checked) .choice-label { color: #9b2823; }

  /* ── Existing-regions hint chips ── */
  .existing-regions {
    margin: 8px 0 0;
    display: flex; flex-wrap: wrap; gap: 6px;
  }
  .region-chip {
    font-size: 12px; padding: 4px 10px;
    border-radius: 999px;
    background: rgba(65,105,225,0.06);
    color: var(--rb);
    border: none; cursor: pointer;
    font-family: inherit;
    -webkit-tap-highlight-color: transparent;
  }
  .region-chip:hover { background: rgba(65,105,225,0.12); }
  .region-chip-meta {
    font-family: 'JetBrains Mono', monospace;
    font-size: 10px; color: var(--muted); margin-left: 4px;
  }

  /* ── Custom region input (revealed when "new region" is selected) ── */
  .new-region-row { margin-top: 8px; display: none; }
  .new-region-row.is-visible { display: block; }

  /* ── Save button — the obvious primary action ── */
  .save-bar {
    position: sticky; bottom: 0;
    margin-top: 32px;
    padding: 16px;
    background: linear-gradient(180deg, transparent, var(--bg) 30%);
  }
  .save-button {
    width: 100%;
    min-height: 56px;
    background: var(--rb);
    color: #fff;
    border: none;
    border-radius: 14px;
    font-family: 'Inter', system-ui, sans-serif;
    font-weight: 700;
    font-size: 16px;
    letter-spacing: 0.2px;
    cursor: pointer;
    box-shadow: 0 8px 24px rgba(65,105,225,0.25);
    transition: transform 80ms ease, box-shadow 120ms ease;
    display: flex; align-items: center; justify-content: center; gap: 8px;
    -webkit-tap-highlight-color: transparent;
  }
  .save-button:hover {
    box-shadow: 0 12px 28px rgba(65,105,225,0.32);
  }
  .save-button:active {
    transform: scale(0.98);
  }
  .save-button svg { width: 18px; height: 18px; }

  /* ── Mobile tweaks ── */
  @media (max-width: 480px) {
    .nav-title { font-size: 16px; }
    .container { padding: 12px; }
    .choice-group {
      grid-template-columns: repeat(2, 1fr);
    }
    .time-pair { grid-template-columns: 1fr; gap: 6px; }
    .time-arrow { display: none; }
  }
</style>
</head><body>

<nav class="nav">
  <a href="/meteorologist/home" class="nav-back">
    <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor"
         stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round">
      <path d="M15 18l-6-6 6-6"/>
    </svg>
  </a>
  <h1 class="nav-title">Submit Daily Brief</h1>
  {% if last_generated_at %}
    <span class="nav-meta">last update {{ last_generated_at[:16].replace('T', ' ') }}</span>
  {% endif %}
</nav>

<div class="container">

  {% if saved %}
  <div class="flash-success">
    <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor"
         stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round">
      <path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/><path d="M22 4 12 14.01l-3-3"/>
    </svg>
    <div>
      <strong>Brief saved.</strong> The Decision Engine is using your new call on every customer ticket from this point forward.
    </div>
  </div>
  {% endif %}

  {% if error %}
  <div class="flash-error">{{ error }}</div>
  {% endif %}

  <form method="POST" action="/admin/brief" novalidate>

    <!-- ── Region ── -->
    <div class="section">
      <label class="section-label" for="region_name">Region</label>
      <select class="select" name="region_name" id="region_name" required onchange="onRegionChange(this)">
        <option value="">Select a region…</option>
        {% for r in existing_regions %}
          <option value="{{ r.name }}" {% if r.name == preselect %}selected{% endif %}>
            {{ r.name }} ({{ r.windows }} window{{ 's' if r.windows != 1 else '' }} on file)
          </option>
        {% endfor %}
        <option value="__new__">+ Add a new region…</option>
      </select>
      <div class="new-region-row" id="new-region-row">
        <input type="text" class="input" name="region_name_new"
               placeholder="e.g. Boone County, IN"
               autocomplete="off"
               style="margin-top:8px">
        <p class="helper">Format: <em>County, State</em>. The Decision Engine matches plans like &ldquo;Lebanon, IN&rdquo; to &ldquo;Boone County, IN&rdquo; via a built-in city map.</p>
      </div>
      <p class="helper">Pick an existing region to update, or create a new one.</p>
    </div>

    <!-- ── Time window ── -->
    <div class="section">
      <span class="section-label">Time window today</span>
      <div class="time-pair">
        <input type="time" class="input" name="start_time" value="06:00" required>
        <span class="time-arrow">→</span>
        <input type="time" class="input" name="end_time" value="20:00" required>
      </div>
      <p class="helper">When does this call apply? Leave the defaults for an all-day brief.</p>
    </div>

    <!-- ── Verdict ── -->
    <div class="section">
      <span class="section-label">Verdict</span>
      <div class="choice-group">
        <label class="choice" data-verdict="dry">
          <input type="radio" name="verdict" value="dry" required>
          <span class="choice-emoji">☀️</span>
          <span class="choice-label">Dry</span>
        </label>
        <label class="choice" data-verdict="wet">
          <input type="radio" name="verdict" value="wet">
          <span class="choice-emoji">🌧</span>
          <span class="choice-label">Wet</span>
        </label>
        <label class="choice" data-verdict="mixed">
          <input type="radio" name="verdict" value="mixed">
          <span class="choice-emoji">⛅</span>
          <span class="choice-label">Mixed</span>
        </label>
        <label class="choice" data-verdict="stormy">
          <input type="radio" name="verdict" value="stormy">
          <span class="choice-emoji">⛈</span>
          <span class="choice-label">Stormy</span>
        </label>
      </div>
    </div>

    <!-- ── Summary ── -->
    <div class="section">
      <label class="section-label" for="summary">What's happening</label>
      <textarea class="textarea" name="summary" id="summary" required
                placeholder="High pressure ridge holds through the day. Light NW breeze 6-10 mph. Mostly sunny with a few high cirrus by late afternoon."></textarea>
      <p class="helper">A few sentences a contractor or event planner can act on. This is what the AI uses to override its own model when conditions are clear.</p>
    </div>

    <!-- ── Confidence ── -->
    <div class="section">
      <span class="section-label">Confidence</span>
      <div class="choice-group">
        <label class="choice">
          <input type="radio" name="confidence" value="high" required>
          <span class="choice-label">High</span>
        </label>
        <label class="choice">
          <input type="radio" name="confidence" value="medium" checked>
          <span class="choice-label">Medium</span>
        </label>
        <label class="choice">
          <input type="radio" name="confidence" value="low">
          <span class="choice-label">Low</span>
        </label>
      </div>
      <p class="helper">High = trust this call over the AI. Low = AI weighs models more heavily.</p>
    </div>

    <!-- ── Internal notes (optional) ── -->
    <div class="section">
      <label class="section-label" for="notes">Internal notes <span style="font-weight:400;text-transform:none;letter-spacing:0">(optional, not customer-facing)</span></label>
      <textarea class="textarea" name="notes" id="notes"
                placeholder="HRRR vs RAP timing disagreement on convection development; went with HRRR (better skill in this region)."></textarea>
    </div>

    <!-- ── Meteorologist name (advanced, hidden by default) ── -->
    <details class="section" style="margin-top:8px">
      <summary style="font-size:12px;color:var(--muted);cursor:pointer;padding:8px 0">Advanced</summary>
      <div style="margin-top:8px">
        <label class="section-label" for="meteorologist_name">Your name (for the brief)</label>
        <input type="text" class="input" name="meteorologist_name" id="meteorologist_name"
               value="{{ meteorologist_default }}" placeholder="WeatherValet Meteorologist">
      </div>
    </details>

    <!-- ── Save ── -->
    <div class="save-bar">
      <button type="submit" class="save-button">
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor"
             stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round">
          <path d="M19 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11l5 5v11a2 2 0 0 1-2 2z"/>
          <polyline points="17 21 17 13 7 13 7 21"/>
          <polyline points="7 3 7 8 15 8"/>
        </svg>
        Save Brief
      </button>
    </div>

  </form>

</div>

<script>
  // Show the "new region" text input when the user picks the special option.
  // Also handle the case where the user picked an existing region from the
  // chip list — we want to focus the dropdown so it's obvious what changed.
  function onRegionChange(sel) {
    var newRow = document.getElementById('new-region-row');
    var newInput = newRow.querySelector('input');
    if (sel.value === '__new__') {
      newRow.classList.add('is-visible');
      newInput.required = true;
      newInput.focus();
    } else {
      newRow.classList.remove('is-visible');
      newInput.required = false;
    }
  }
  // Run once on load in case the form was reposted with __new__ selected
  onRegionChange(document.getElementById('region_name'));
</script>

</body></html>
"""


@app.get("/admin/jump/<int:request_id>")
def admin_jump(request_id):
    """Admin shortcut — jump from the queue dashboard into the meteorologist
    view for a given request, without needing the SMS link."""
    auth_resp = _admin_auth()
    if auth_resp is not None:
        return auth_resp
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT claim_token FROM verification_requests WHERE id = %s",
                (request_id,),
            )
            row = cur.fetchone()
    if not row:
        abort(404)
    return redirect(f"/meteorologist/{row['claim_token']}")


# ════════════════════════════════════════════════════════════════════════════
# Main
# ════════════════════════════════════════════════════════════════════════════


# ════════════════════════════════════════════════════════════════════
# Admin · Team management endpoints (Phase 4 Chunk 2)
# ════════════════════════════════════════════════════════════════════
# These power the Team tab in the admin Command Center. Session-auth
# gated via @require_role('admin') — caller must be signed in AND have
# the 'admin' role. The older /admin/* HTTP-Basic routes stay around
# as a bootstrap mechanism (you can still curl /admin/set-password etc.
# if your admin user gets locked out).
#
# Uses the existing `db()` context manager. Connections autocommit,
# so no explicit commit/rollback is needed. Row factory is
# RealDictCursor, so cur.fetchone() returns dicts keyed by column name.


def _generate_temp_password():
    """Generate a memorable but secure temp password for new users.
    Pattern: three short English words + two digits, e.g. "river-storm-cedar-42".
    Easier to share verbally than a random string; still high-entropy enough
    that brute force is impractical within the time before the user is
    required to change it on first login (forced via password_must_change).
    """
    import secrets
    words = [
        "storm", "river", "cedar", "quiet", "amber", "north", "calm",
        "flint", "dune", "marsh", "pine", "vivid", "swift", "bright",
        "creek", "ridge", "valley", "meadow", "harbor", "ember",
    ]
    w1 = secrets.choice(words)
    w2 = secrets.choice([w for w in words if w != w1])
    w3 = secrets.choice([w for w in words if w not in (w1, w2)])
    digits = secrets.randbelow(90) + 10  # 10-99
    return f"{w1}-{w2}-{w3}-{digits}"


def _serialize_user_for_admin(row):
    """Shape a users row (dict, since RealDictCursor) + roles list into
    the JSON shape the frontend Team panel expects. `row` is expected
    to have: id, email, name, created_at, last_login_at, is_active, roles.
    """
    import time as _time
    import datetime as _datetime

    last_login_at = row.get("last_login_at")
    if last_login_at:
        delta = int(_time.time()) - int(last_login_at)
        if delta < 60:
            last_login_str = "just now"
        elif delta < 3600:
            last_login_str = f"{delta // 60} min ago"
        elif delta < 86400:
            last_login_str = f"{delta // 3600}h ago"
        elif delta < 86400 * 7:
            last_login_str = f"{delta // 86400}d ago"
        else:
            last_login_str = _datetime.datetime.utcfromtimestamp(last_login_at).strftime("%b %d")
    else:
        last_login_str = "Never"

    roles = row.get("roles") or []
    # Pick highest-priority role for the frontend's single-role-per-row display.
    # Matches workspace-router precedence (admin > met > crew > subscriber).
    role_priority = ["admin", "met", "crew", "subscriber"]
    primary_role = next((r for r in role_priority if r in roles), None)
    # Frontend uses 'meteorologist' for display; backend stores 'met'.
    if primary_role == "met":
        primary_role = "meteorologist"

    return {
        "id": f"u_{row['id']}",
        "user_id": row["id"],
        "name": row.get("name") or "",
        "email": row["email"],
        "role": primary_role or "subscriber",
        "all_roles": roles,
        "last_login": last_login_str,
        "is_active": bool(row.get("is_active", True)),
    }


@app.get("/api/v1/admin/users")
@require_role("admin")
def admin_list_users():
    """List all users with their roles. Returns active and inactive both;
    the frontend handles visual grey-out for inactive ones."""
    with db() as conn:
        cur = conn.cursor()
        cur.execute("""
            SELECT u.id, u.email, u.name, u.created_at, u.last_login_at, u.is_active,
                   ARRAY_REMOVE(ARRAY_AGG(ur.role ORDER BY ur.role), NULL) AS roles
            FROM users u
            LEFT JOIN user_roles ur ON ur.user_id = u.id
            GROUP BY u.id
            ORDER BY u.is_active DESC, u.created_at DESC
        """)
        rows = cur.fetchall()

    members = [_serialize_user_for_admin(row) for row in rows]
    return jsonify({"ok": True, "members": members})


@app.post("/api/v1/admin/users")
@require_role("admin")
def admin_create_user():
    """Create a new user with a temp password and grant their role.
    Returns the new user + the temp password (the ONLY time the password
    is ever returned in plaintext). The user is created with
    password_must_change=TRUE so they'll be forced to change it on
    first login.

    Request body: {"name": "...", "email": "...", "role": "meteorologist|crew|admin"}
    """
    import time as _time
    import bcrypt as _bcrypt

    data = request.get_json(silent=True) or {}
    name = (data.get("name") or "").strip()
    email = (data.get("email") or "").strip().lower()
    role_input = (data.get("role") or "").strip().lower()

    if not name:
        return jsonify({"ok": False, "error": "missing-name"}), 400
    if not email or not is_valid_email(email):
        return jsonify({"ok": False, "error": "invalid-email"}), 400

    # Frontend uses 'meteorologist'; backend stores 'met'.
    role_map = {"meteorologist": "met", "met": "met", "crew": "crew",
                "admin": "admin", "subscriber": "subscriber"}
    role = role_map.get(role_input)
    if not role:
        return jsonify({"ok": False, "error": "invalid-role"}), 400

    temp_password = _generate_temp_password()
    password_hash = _bcrypt.hashpw(temp_password.encode("utf-8"),
                                   _bcrypt.gensalt(rounds=12)).decode("utf-8")
    now = int(_time.time())

    try:
        with db() as conn:
            cur = conn.cursor()
            # Check for existing user (case-insensitive on email)
            cur.execute("SELECT id FROM users WHERE LOWER(email) = LOWER(%s)", (email,))
            if cur.fetchone():
                return jsonify({"ok": False, "error": "email-already-exists"}), 409

            # Insert user
            cur.execute("""
                INSERT INTO users (email, password_hash, name, created_at, is_active, password_must_change)
                VALUES (%s, %s, %s, %s, TRUE, TRUE)
                RETURNING id
            """, (email, password_hash, name, now))
            new_user_id = cur.fetchone()["id"]

            # Grant role
            cur.execute("""
                INSERT INTO user_roles (user_id, role, granted_at)
                VALUES (%s, %s, %s)
            """, (new_user_id, role, now))

            # Fetch back the freshly-created user for a consistent response shape
            cur.execute("""
                SELECT u.id, u.email, u.name, u.created_at, u.last_login_at, u.is_active,
                       ARRAY_REMOVE(ARRAY_AGG(ur.role ORDER BY ur.role), NULL) AS roles
                FROM users u
                LEFT JOIN user_roles ur ON ur.user_id = u.id
                WHERE u.id = %s
                GROUP BY u.id
            """, (new_user_id,))
            row = cur.fetchone()
    except Exception as e:
        print(f"[admin_create_user] failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "create-failed"}), 500

    return jsonify({
        "ok": True,
        "member": _serialize_user_for_admin(row),
        "temp_password": temp_password,
    })


@app.patch("/api/v1/admin/users/<int:user_id>")
@require_role("admin")
def admin_update_user(user_id):
    """Edit name/email/role/active. Optionally reset password (returns
    new temp_password in response, sets password_must_change=TRUE).

    Request body keys (all optional): name, email, role, is_active, reset_password
    """
    import time as _time
    import bcrypt as _bcrypt

    data = request.get_json(silent=True) or {}
    name = data.get("name")
    email = data.get("email")
    role_input = data.get("role")
    reset_password = bool(data.get("reset_password"))
    is_active = data.get("is_active")

    temp_password = None

    try:
        with db() as conn:
            cur = conn.cursor()

            # Verify user exists
            cur.execute("SELECT id FROM users WHERE id = %s", (user_id,))
            if not cur.fetchone():
                return jsonify({"ok": False, "error": "no-such-user"}), 404

            # Build dynamic UPDATE for the users table
            updates = []
            params = []

            if name is not None:
                name_clean = name.strip()
                if not name_clean:
                    return jsonify({"ok": False, "error": "missing-name"}), 400
                updates.append("name = %s")
                params.append(name_clean)

            if email is not None:
                email_clean = email.strip().lower()
                if not is_valid_email(email_clean):
                    return jsonify({"ok": False, "error": "invalid-email"}), 400
                cur.execute("SELECT id FROM users WHERE LOWER(email) = LOWER(%s) AND id != %s",
                            (email_clean, user_id))
                if cur.fetchone():
                    return jsonify({"ok": False, "error": "email-already-exists"}), 409
                updates.append("email = %s")
                params.append(email_clean)

            if is_active is not None:
                updates.append("is_active = %s")
                params.append(bool(is_active))

            if reset_password:
                temp_password = _generate_temp_password()
                password_hash = _bcrypt.hashpw(temp_password.encode("utf-8"),
                                               _bcrypt.gensalt(rounds=12)).decode("utf-8")
                updates.append("password_hash = %s")
                params.append(password_hash)
                updates.append("password_must_change = TRUE")  # literal, no param

            if updates:
                params.append(user_id)
                cur.execute(f"UPDATE users SET {', '.join(updates)} WHERE id = %s", params)

            # Replace role if provided. Conservative single-primary-role model:
            # remove all existing roles and add the new one. (For a richer
            # multi-role UI we'd add a separate roles-management endpoint.)
            if role_input is not None:
                role_map = {"meteorologist": "met", "met": "met", "crew": "crew",
                            "admin": "admin", "subscriber": "subscriber"}
                new_role = role_map.get(role_input.strip().lower())
                if not new_role:
                    return jsonify({"ok": False, "error": "invalid-role"}), 400
                cur.execute("DELETE FROM user_roles WHERE user_id = %s", (user_id,))
                cur.execute(
                    "INSERT INTO user_roles (user_id, role, granted_at) VALUES (%s, %s, %s)",
                    (user_id, new_role, int(_time.time())),
                )

            # If password was reset, also kill any active sessions so the
            # user is forced to re-auth with the new temp password.
            if reset_password:
                cur.execute("DELETE FROM sessions WHERE user_id = %s", (user_id,))

            # Return the refreshed user
            cur.execute("""
                SELECT u.id, u.email, u.name, u.created_at, u.last_login_at, u.is_active,
                       ARRAY_REMOVE(ARRAY_AGG(ur.role ORDER BY ur.role), NULL) AS roles
                FROM users u
                LEFT JOIN user_roles ur ON ur.user_id = u.id
                WHERE u.id = %s
                GROUP BY u.id
            """, (user_id,))
            row = cur.fetchone()
    except Exception as e:
        print(f"[admin_update_user] failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "update-failed"}), 500

    response = {"ok": True, "member": _serialize_user_for_admin(row)}
    if temp_password:
        response["temp_password"] = temp_password
    return jsonify(response)


@app.delete("/api/v1/admin/users/<int:user_id>")
@require_role("admin")
def admin_deactivate_user(user_id):
    """Soft-delete a user — sets is_active=FALSE. Historical work stays
    in the record under their authorship; they just can't sign in anymore.
    Reactivation is via PATCH with is_active=true. Also destroys any
    active sessions so the user is logged out immediately.
    """
    try:
        with db() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id FROM users WHERE id = %s", (user_id,))
            if not cur.fetchone():
                return jsonify({"ok": False, "error": "no-such-user"}), 404
            cur.execute("UPDATE users SET is_active = FALSE WHERE id = %s", (user_id,))
            cur.execute("DELETE FROM sessions WHERE user_id = %s", (user_id,))
    except Exception as e:
        print(f"[admin_deactivate_user] failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "deactivate-failed"}), 500

    return jsonify({"ok": True})


# ── Multi-role helpers (additive — don't replace existing roles) ──
# The PATCH /api/v1/admin/users/<id> endpoint replaces ALL roles when
# 'role' is in the payload. That's the conservative single-primary-role
# model. These two endpoints are additive — useful for admins testing
# multiple workspaces, or for upgrading a subscriber to also have crew
# without losing their subscriber role.

@app.route("/api/v1/admin/users/<int:user_id>/roles", methods=["OPTIONS"])
def _admin_user_roles_preflight(user_id):
    return ("", 204)


@app.post("/api/v1/admin/users/<int:user_id>/roles")
@require_role("admin")
def admin_add_user_role(user_id):
    """Add a role to a user WITHOUT removing their existing roles.

    Request body: {"role": "meteorologist|crew|admin|subscriber"}

    Idempotent — adding a role the user already has is a no-op and
    returns 200 with the unchanged role list.
    """
    import time as _time

    data = request.get_json(silent=True) or {}
    role_input = (data.get("role") or "").strip().lower()
    role_map = {"meteorologist": "met", "met": "met", "crew": "crew",
                "admin": "admin", "subscriber": "subscriber"}
    role = role_map.get(role_input)
    if not role:
        return jsonify({"ok": False, "error": "invalid-role"}), 400

    try:
        with db() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id FROM users WHERE id = %s", (user_id,))
            if not cur.fetchone():
                return jsonify({"ok": False, "error": "no-such-user"}), 404

            # ON CONFLICT DO NOTHING — idempotent
            cur.execute(
                """INSERT INTO user_roles (user_id, role, granted_at)
                   VALUES (%s, %s, %s)
                   ON CONFLICT DO NOTHING""",
                (user_id, role, int(_time.time())),
            )

            # Return fresh user shape
            cur.execute("""
                SELECT u.id, u.email, u.name, u.created_at, u.last_login_at, u.is_active,
                       ARRAY_REMOVE(ARRAY_AGG(ur.role ORDER BY ur.role), NULL) AS roles
                FROM users u
                LEFT JOIN user_roles ur ON ur.user_id = u.id
                WHERE u.id = %s
                GROUP BY u.id
            """, (user_id,))
            row = cur.fetchone()
    except Exception as e:
        print(f"[admin_add_user_role] failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "add-role-failed"}), 500

    return jsonify({"ok": True, "member": _serialize_user_for_admin(row)})


@app.route("/api/v1/admin/users/<int:user_id>/roles/<role>", methods=["OPTIONS"])
def _admin_user_role_remove_preflight(user_id, role):
    return ("", 204)


@app.delete("/api/v1/admin/users/<int:user_id>/roles/<role>")
@require_role("admin")
def admin_remove_user_role(user_id, role):
    """Remove a single role from a user, leaving their other roles intact.

    The role path param uses the backend's internal names: met, crew,
    admin, subscriber. (Frontend may convert meteorologist→met before
    calling.)

    If removing the role would leave the user with zero roles, we still
    allow it — the frontend can show that user as "no workspaces" and
    they'll see the account-pending screen on next login. This matches
    the semantics of the create-user endpoint (which can't create a
    user without granting at least one role, but a user CAN end up with
    zero roles via this endpoint).
    """
    role_map = {"meteorologist": "met", "met": "met", "crew": "crew",
                "admin": "admin", "subscriber": "subscriber"}
    role_clean = role_map.get(role.strip().lower())
    if not role_clean:
        return jsonify({"ok": False, "error": "invalid-role"}), 400

    try:
        with db() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id FROM users WHERE id = %s", (user_id,))
            if not cur.fetchone():
                return jsonify({"ok": False, "error": "no-such-user"}), 404

            cur.execute(
                "DELETE FROM user_roles WHERE user_id = %s AND role = %s",
                (user_id, role_clean),
            )

            cur.execute("""
                SELECT u.id, u.email, u.name, u.created_at, u.last_login_at, u.is_active,
                       ARRAY_REMOVE(ARRAY_AGG(ur.role ORDER BY ur.role), NULL) AS roles
                FROM users u
                LEFT JOIN user_roles ur ON ur.user_id = u.id
                WHERE u.id = %s
                GROUP BY u.id
            """, (user_id,))
            row = cur.fetchone()
    except Exception as e:
        print(f"[admin_remove_user_role] failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "remove-role-failed"}), 500

    return jsonify({"ok": True, "member": _serialize_user_for_admin(row)})


if __name__ == "__main__":
    init_db()
    port = int(os.environ.get("PORT", 8080))
    debug = os.environ.get("FLASK_DEBUG") == "1"
    app.run(host="0.0.0.0", port=port, debug=debug)
