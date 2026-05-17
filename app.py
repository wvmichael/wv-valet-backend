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
import html as _html_module
import json
import os
import re
import secrets
import sys
import time
import urllib.request
import urllib.error
import urllib.parse
import threading
from contextlib import contextmanager
from dataclasses import dataclass, asdict
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
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

# ── Stripe Price IDs for subscription tiers (Phase 10 C2) ──
# Each Stripe Product has a separate monthly and yearly price; for the
# May 24 launch we only sell monthly. Annual toggle ships later.
#
# These Price IDs are TEST MODE. When we flip to live mode, the Price
# IDs change (Stripe regenerates them per environment) — set new env
# vars or replace these values when the live products are created.
#
# Pro Enterprise is intentionally absent — it's a custom-quoted tier
# sold via a "Talk to us" email handoff, not self-serve Stripe Checkout.
TIER_PRICE_MAP = {
    "hobbyist":   os.environ.get("STRIPE_PRICE_HOBBYIST_MONTHLY",
                                 "price_1TVyScGeHM6pFDnVjhT3r2o2"),
    "pro_single": os.environ.get("STRIPE_PRICE_PRO_SINGLE_MONTHLY",
                                 "price_1TVyYuGeHM6pFDnVJRHGYjT7"),
    "pro_multi":  os.environ.get("STRIPE_PRICE_PRO_MULTI_MONTHLY",
                                 "price_1TVycGGeHM6pFDnVjIHuTMQR"),
}

# Reverse lookup: Price ID → tier key. Used by webhook to know which
# tier was purchased from the line_items in checkout.session.completed.
TIER_BY_PRICE_ID = {v: k for k, v in TIER_PRICE_MAP.items()}

# ─── $99 Starter Month coupon (sales funnel entry point) ───
#
# This is the coupon ID for the Stripe coupon that drops Pro Single's
# first month from $400 to $99. Created in the Stripe dashboard with:
#   - Coupon ID: STARTER99
#   - Type: Amount off
#   - Amount: $301.00 USD
#   - Duration: Once (applies to first invoice only)
#   - Redemption limit: 1 per customer (prevents repeat use)
#   - Applies to: Pro Single price ID only
#
# We pass coupon=STARTER99 into Stripe Checkout for /starter signups.
# Stripe automatically applies the $301 discount to the first month,
# then bills at $400 for every subsequent month until the customer
# cancels.
STARTER_COUPON_ID = os.environ.get("STRIPE_STARTER_COUPON_ID", "STARTER99")

TWILIO_ACCOUNT_SID = os.environ.get("TWILIO_ACCOUNT_SID", "")
TWILIO_AUTH_TOKEN = os.environ.get("TWILIO_AUTH_TOKEN", "")
TWILIO_FROM_NUMBER = os.environ.get("TWILIO_FROM_NUMBER", "")  # Twilio number we send from

# Rosie's dedicated Twilio number. Separate from the main WV number so:
#   - Mets recognize "this is Rosie" by the From: number
#   - Inbound SMS to this number routes to /api/v1/rosie/sms (Rosie chat),
#     not to the customer support inbox
#   - Falls back to TWILIO_FROM_NUMBER if not set, so existing single-number
#     deploys still work (Rosie just shares the main number).
ROSIE_TWILIO_NUMBER = os.environ.get("ROSIE_TWILIO_NUMBER", "")

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
    meteorologist_notes     TEXT,
    -- Tip system (Phase 10 — Met tips)
    completed_by_user_id    INTEGER REFERENCES users(id) ON DELETE SET NULL,
    completed_by_name       TEXT,                -- snapshot — Met can leave, tip still attributes
    customer_review_token   TEXT UNIQUE          -- token-authed review/tip page URL
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

-- ── Subscription tier (Phase 10 Chunk C2) ──
-- Which tier the user is currently subscribed to. Set by the
-- subscription-checkout webhook handler when checkout completes.
-- Null = no active subscription (free user).
-- Values: 'hobbyist' | 'pro_single' | 'pro_multi' | 'pro_enterprise'
ALTER TABLE users ADD COLUMN IF NOT EXISTS subscription_tier TEXT;

-- ── Phone number (Phase 10 Item #3) ──
-- E.164 format ("+15555550101"). Used for daily brief SMS delivery
-- and threshold alerts. Collected during subscriber signup (via Stripe
-- Checkout's phone collection, or via the portal). Nullable — many
-- subscribers may prefer email-only.
ALTER TABLE users ADD COLUMN IF NOT EXISTS phone TEXT;

-- ── Crew home base (Phase 10 Item #6) ──
-- For users with the 'crew' role: their primary geographic location,
-- used to target mission SMS deliveries by polygon. Set at registration
-- and editable from the Crew Profile screen.
--
-- Design note: we use a static home base rather than live geolocation
-- tracking for both privacy and simplicity. Crew members are inherently
-- local — a Lebanon Crew member is in Lebanon. If they travel, they
-- wouldn't respond to a Boone County mission anyway. Live tracking can
-- be added later as an opt-in enhancement.
--
-- crew_active toggles whether this Crew member gets mission SMS at all.
-- Used for "I'm out of town this week, hold my pages" without losing
-- their account. Default TRUE — opt-in by default.
ALTER TABLE users ADD COLUMN IF NOT EXISTS crew_home_lat DOUBLE PRECISION;
ALTER TABLE users ADD COLUMN IF NOT EXISTS crew_home_lng DOUBLE PRECISION;
ALTER TABLE users ADD COLUMN IF NOT EXISTS crew_home_label TEXT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS crew_active BOOLEAN NOT NULL DEFAULT TRUE;

-- Phase 10 Met welcome card: tracks whether the Met has dismissed the
-- first-login welcome card in their workspace. NULL = hasn't seen/dismissed
-- yet (show the card); timestamp = already dismissed (hide).
ALTER TABLE users ADD COLUMN IF NOT EXISTS met_onboarded_at BIGINT;

-- Phase 10 timezone support: every user has a timezone (IANA name like
-- "America/Indiana/Indianapolis"). Used by the brief scheduler to deliver
-- in the subscriber's local time, not UTC. Defaults to Indianapolis
-- since that's our launch market; auto-detected from primary saved
-- location's lat/lng on save.
ALTER TABLE users ADD COLUMN IF NOT EXISTS timezone TEXT NOT NULL DEFAULT 'America/Indiana/Indianapolis';

-- Phase 10 Met tips: track which Met completed each verification + a
-- customer-facing token for the review/tip page (separate from Met's
-- claim_token so we can give customers a URL that doesn't expose
-- Met-only paths).
ALTER TABLE verification_requests ADD COLUMN IF NOT EXISTS completed_by_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL;
ALTER TABLE verification_requests ADD COLUMN IF NOT EXISTS completed_by_name TEXT;
ALTER TABLE verification_requests ADD COLUMN IF NOT EXISTS customer_review_token TEXT UNIQUE;

-- ── Scheduled messages (Phase 10 — Met scheduling) ──
-- One table for Daily Brief / Pro Brief / Crew Post scheduling.
-- The scheduler tick (60s) sweeps for pending items where
-- scheduled_for_ms <= now and fires them.
--
-- type values:
--   'daily_brief'  — county-wide regional brief (DailyBrief tab)
--   'pro_brief'    — per-subscriber Pro tier brief (PrBriefs tab)
--   'crew_post'    — Crew feed post (Send to Crew feed modal)
--
-- content_payload holds whatever the firing logic needs:
--   daily_brief: { body, counties[], mode, state, ... }
--   pro_brief:   { draft_id, final_body, final_verdict }
--   crew_post:   { body, pin_lat, pin_lng, ... }
--
-- status flow:
--   'pending'   — waiting for scheduled time
--   'sent'      — fired successfully
--   'cancelled' — Met cancelled it before firing
--   'failed'    — fire attempt threw an error (see fire_error)
--
-- Scheduling rule: scheduled_for_ms is computed in UTC at submission
-- time. The Met's UI shows the time in their chosen timezone, but the
-- DB stores UTC so the scheduler doesn't need TZ logic at fire time.
CREATE TABLE IF NOT EXISTS scheduled_messages (
    id              SERIAL PRIMARY KEY,
    type            TEXT NOT NULL,             -- 'daily_brief' | 'pro_brief' | 'crew_post'
    scheduled_for_ms BIGINT NOT NULL,
    scheduled_tz    TEXT,                       -- IANA name for display ("America/New_York")
    scheduled_by_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    scheduled_by_name TEXT,                     -- snapshot
    status          TEXT NOT NULL DEFAULT 'pending',
    content_payload TEXT NOT NULL,              -- JSON-encoded
    target_audience TEXT,                       -- JSON: counties[], subscriber_user_id, etc
    fired_at        BIGINT,
    fire_error      TEXT,
    created_at      BIGINT NOT NULL,
    updated_at      BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_sched_msg_pending
    ON scheduled_messages(status, scheduled_for_ms ASC)
    WHERE status = 'pending';
CREATE INDEX IF NOT EXISTS idx_sched_msg_by_user
    ON scheduled_messages(scheduled_by_user_id, created_at DESC);

-- ── Sales reps & commission attribution (Starter Month sales funnel) ──
--
-- Salespeople pitch the $99 Starter Month and earn 20% of the actual
-- subscription cash received for 6 months from each customer's signup.
--
-- Structure:
--   sales_reps          — one row per active rep (Brian, Seattle, etc.)
--   sales_attributions  — one row per customer signup; locked at signup
--
-- The "rep_slug" is the URL-safe identifier used in /starter?rep=brian
-- queries. It's also the field that gets stored in sales_attributions.
-- We deliberately don't FK from sales_attributions.rep_slug to
-- sales_reps.slug — if a rep leaves and is deleted, attributions remain
-- intact and admin can still see the historical record.
CREATE TABLE IF NOT EXISTS sales_reps (
    id              SERIAL PRIMARY KEY,
    slug            TEXT NOT NULL UNIQUE,     -- 'brian', 'seattle1', etc.
    name            TEXT NOT NULL,
    email           TEXT,
    phone           TEXT,
    commission_start_date BIGINT,             -- Date rep started (informational)
    is_active       BOOLEAN NOT NULL DEFAULT TRUE,
    created_at      BIGINT NOT NULL,
    updated_at      BIGINT NOT NULL
);

-- Commission attribution. Locked at signup; never modified.
-- One row per (user_id) — a user can only have one source attribution.
-- If rep_slug is NULL or 'organic', no commission is earned.
CREATE TABLE IF NOT EXISTS sales_attributions (
    user_id         INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    rep_slug        TEXT,                     -- NULL or 'organic' = no commission
    signed_up_at    BIGINT NOT NULL,          -- starts the 6-month window
    starter_used    BOOLEAN NOT NULL DEFAULT FALSE,   -- did they use STARTER99?
    locked          BOOLEAN NOT NULL DEFAULT TRUE     -- always TRUE; reserved
);
CREATE INDEX IF NOT EXISTS idx_sales_attrib_rep
    ON sales_attributions(rep_slug, signed_up_at DESC);

-- ── Custom mission templates (F-X2) ──
--
-- Built-in templates live in the frontend (CREW_MISSIONS dict in index.html).
-- Mets can create CUSTOM templates that go on top of the built-ins.
-- They appear in the deploy modal alongside the built-ins.
--
-- Severe templates need admin sign-off (status='pending-approval').
-- Routine templates go straight to status='approved' (Mets are trained).
CREATE TABLE IF NOT EXISTS mission_templates_user (
    id              SERIAL PRIMARY KEY,
    slug            TEXT NOT NULL UNIQUE,         -- 'wind-gust-check-1', auto-generated
    template_name   TEXT NOT NULL,                -- short display name
    eyebrow         TEXT,                         -- short context above headline
    btn_headline    TEXT NOT NULL,                -- main button text Mets see
    prompt          TEXT NOT NULL,                -- the SMS sent to Crew
    answer_options  TEXT,                         -- JSON: [{id, label}, ...] or null for free-text
    mode            TEXT NOT NULL DEFAULT 'routine',  -- 'routine' | 'severe'
    icon            TEXT DEFAULT 'eye',           -- icon key
    status          TEXT NOT NULL DEFAULT 'approved',  -- 'approved' | 'pending-approval' | 'rejected'
    created_by_user_id INTEGER REFERENCES users(id),
    created_by_name TEXT,
    approved_by_user_id INTEGER REFERENCES users(id),
    approved_at     BIGINT,
    rejection_reason TEXT,
    use_count       INTEGER NOT NULL DEFAULT 0,   -- track usefulness
    created_at      BIGINT NOT NULL,
    updated_at      BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_mtu_status
    ON mission_templates_user(status);


-- ──────────────────────────────────────────────────────────────────────
-- Coverage scheduler (Phase 11, May 17)
-- ──────────────────────────────────────────────────────────────────────
-- Mets sign up to cover (1) Pro subscriber daily briefs and (2) the
-- Review Pool (national $19 reviews). The system tracks:
--   - Primary Met assignment per Pro subscriber (admin-set)
--   - Daily brief delivery time preference per subscriber
--   - Recurring weekly schedule per Met
--   - One-off shift claims (cover for someone)
--   - Real-time "available right now" via login heartbeat
--
-- Hobbyists are NOT in this system — their AI-only briefs need no Met.


-- Coverage assignments per subscriber (Pro tiers only).
-- Hobbyist subscribers don't get a row here. One row per Pro subscriber.
CREATE TABLE IF NOT EXISTS subscriber_coverage (
    user_id              INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    primary_met_id       INTEGER REFERENCES users(id) ON DELETE SET NULL,
    backup_met_id        INTEGER REFERENCES users(id) ON DELETE SET NULL,
    daily_brief_time     TEXT NOT NULL DEFAULT '07:00',  -- HH:MM 24h, subscriber's local
    daily_brief_timezone TEXT NOT NULL DEFAULT 'America/New_York',
    next_br_due          BIGINT,                          -- ms epoch; quarterly/monthly review
    notes                TEXT,
    updated_at           BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_subcov_primary ON subscriber_coverage(primary_met_id);
CREATE INDEX IF NOT EXISTS idx_subcov_backup  ON subscriber_coverage(backup_met_id);


-- Met recurring weekly schedule. One row per Met per day of week per scope.
-- scope_kind: 'subscriber' (covers a specific Pro subscriber's brief)
--             'subscriber_set' (covers all of another Met's subscribers — "I'm covering Chris's KS today")
--             'review_pool' (covers the national $19 reviews)
--
-- day_of_week: 0=Sun, 1=Mon, ... 6=Sat
--
-- Mets create + edit their own rows. A Met can claim shifts for any day,
-- including covering for another Met's "subscriber_set".
CREATE TABLE IF NOT EXISTS met_recurring_shifts (
    id                   SERIAL PRIMARY KEY,
    met_user_id          INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    day_of_week          INTEGER NOT NULL CHECK (day_of_week >= 0 AND day_of_week <= 6),
    scope_kind           TEXT NOT NULL CHECK (scope_kind IN ('subscriber','subscriber_set','review_pool')),
    -- For 'subscriber' scope: which subscriber this covers
    subscriber_user_id   INTEGER REFERENCES users(id) ON DELETE CASCADE,
    -- For 'subscriber_set' scope: whose subscribers this covers (e.g. Chris's whole KS)
    set_owner_met_id     INTEGER REFERENCES users(id) ON DELETE CASCADE,
    -- 'review_pool' uses neither subscriber_user_id nor set_owner_met_id.
    created_at           BIGINT NOT NULL,
    UNIQUE (met_user_id, day_of_week, scope_kind, subscriber_user_id, set_owner_met_id)
);
CREATE INDEX IF NOT EXISTS idx_mrs_met ON met_recurring_shifts(met_user_id);
CREATE INDEX IF NOT EXISTS idx_mrs_day ON met_recurring_shifts(day_of_week);
CREATE INDEX IF NOT EXISTS idx_mrs_subscriber ON met_recurring_shifts(subscriber_user_id);
CREATE INDEX IF NOT EXISTS idx_mrs_setowner ON met_recurring_shifts(set_owner_met_id);


-- One-off shift overrides for a specific date (NOT a recurring day-of-week).
-- Used when:
--   - A Met drops a shift for one day ("I can't do Tuesday this week")
--   - A Met picks up a shift another Met dropped
--   - A new Pro subscriber's first day needs coverage that wasn't in the recurring set
--
-- shift_date is the actual calendar date in YYYY-MM-DD format (subscriber's TZ
-- for subscriber shifts, US Eastern for review_pool).
CREATE TABLE IF NOT EXISTS met_shift_overrides (
    id                   SERIAL PRIMARY KEY,
    -- met_user_id meaning depends on override_kind:
    --   'drop'   : the Met who is dropping this shift (excluded from coverage)
    --   'claim'  : the Met picking up the shift
    --   'assign' : the Met being assigned by admin
    -- In all CURRENT code paths this is non-null. Schema allows NULL for
    -- backward-compat with rows created before May 17 (early test data
    -- where drop stored NULL); the resolver explicitly skips rows with
    -- met_user_id IS NULL to avoid the "one Met's drop blocks everyone"
    -- bug those legacy rows would otherwise cause.
    met_user_id          INTEGER REFERENCES users(id) ON DELETE CASCADE,
    shift_date           TEXT NOT NULL,                                    -- YYYY-MM-DD
    scope_kind           TEXT NOT NULL CHECK (scope_kind IN ('subscriber','subscriber_set','review_pool')),
    subscriber_user_id   INTEGER REFERENCES users(id) ON DELETE CASCADE,
    set_owner_met_id     INTEGER REFERENCES users(id) ON DELETE CASCADE,
    override_kind        TEXT NOT NULL CHECK (override_kind IN ('drop','claim','assign')),
    created_at           BIGINT NOT NULL,
    notes                TEXT
);
CREATE INDEX IF NOT EXISTS idx_mso_date ON met_shift_overrides(shift_date);
CREATE INDEX IF NOT EXISTS idx_mso_met ON met_shift_overrides(met_user_id);
CREATE INDEX IF NOT EXISTS idx_mso_subscriber ON met_shift_overrides(subscriber_user_id);


-- Met "available right now" heartbeat.
-- The frontend pings this every 60 seconds while a Met has the workspace open.
-- Admin dashboard reads this to show who's actually around (vs scheduled).
-- For Review Pool routing, the SMS dispatcher picks from Mets with recent
-- heartbeat AND a review_pool shift active today.
CREATE TABLE IF NOT EXISTS met_heartbeat (
    met_user_id          INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    last_seen_at         BIGINT NOT NULL,
    user_agent           TEXT
);


-- Brief task tracking. One row per (subscriber, date) for Pro subscribers.
-- Created at midnight (UTC) by a cron job for each active Pro subscriber.
-- assigned_met_id resolves at creation time from:
--   1. shift override for this date+subscriber (if any)
--   2. recurring shift for this day-of-week+subscriber (if any)
--   3. recurring "subscriber_set" shift covering this subscriber's primary Met
--   4. subscriber_coverage.primary_met_id (fallback)
-- If all four fail, assigned_met_id is null and the task is a GAP.
CREATE TABLE IF NOT EXISTS daily_brief_tasks (
    id                   SERIAL PRIMARY KEY,
    subscriber_user_id   INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    task_date            TEXT NOT NULL,                                    -- YYYY-MM-DD subscriber TZ
    assigned_met_id      INTEGER REFERENCES users(id) ON DELETE SET NULL,
    due_at_ms            BIGINT NOT NULL,                                  -- absolute deadline UTC
    status               TEXT NOT NULL DEFAULT 'pending'
                           CHECK (status IN ('pending','in_progress','sent','overdue','cancelled')),
    started_at_ms        BIGINT,
    sent_at_ms           BIGINT,
    escalated_at_ms      BIGINT,                                           -- when first SMS fired
    escalated_admin_at_ms BIGINT,                                          -- when admin SMS fired
    notes                TEXT,
    UNIQUE (subscriber_user_id, task_date)
);
CREATE INDEX IF NOT EXISTS idx_dbt_date ON daily_brief_tasks(task_date);
CREATE INDEX IF NOT EXISTS idx_dbt_assigned ON daily_brief_tasks(assigned_met_id, status);
CREATE INDEX IF NOT EXISTS idx_dbt_due ON daily_brief_tasks(status, due_at_ms);


-- ──────────────────────────────────────────────────────────────────────
-- Storm Shelter activations (Met-pay event, $25 per activation)
-- ──────────────────────────────────────────────────────────────────────
-- When NWS issues a tornado/severe-thunderstorm warning that affects
-- one or more Pro subscribers, a Met can "open" a Storm Shelter
-- activation — meaning they're actively monitoring the situation and
-- ready to push updates to affected subscribers. They earn $25 once
-- the activation closes (either Met closes it manually or the NWS
-- warning expires and cron auto-closes).
--
-- One activation per (Met, region) at a time. The region is a
-- free-text label the Met enters (e.g. "Central Kansas" or "Boone
-- County, IN") — we don't yet pin it to a strict geography. Tracking
-- evolves with usage.
CREATE TABLE IF NOT EXISTS storm_shelter_activations (
    id                  SERIAL PRIMARY KEY,
    met_user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    region_label        TEXT NOT NULL,
    nws_event           TEXT,                 -- the triggering NWS event name (snapshot)
    affected_count      INTEGER,              -- Pro subscribers in scope (snapshot at open)
    opened_at_ms        BIGINT NOT NULL,
    closed_at_ms        BIGINT,
    close_reason        TEXT,                 -- 'manual'|'warning_expired'|'admin_closed'
    payout_cents        INTEGER NOT NULL DEFAULT 2500,
    notes               TEXT
);
CREATE INDEX IF NOT EXISTS idx_ssa_met ON storm_shelter_activations(met_user_id);
CREATE INDEX IF NOT EXISTS idx_ssa_open ON storm_shelter_activations(met_user_id, closed_at_ms);
CREATE INDEX IF NOT EXISTS idx_ssa_closed ON storm_shelter_activations(closed_at_ms);


-- ──────────────────────────────────────────────────────────────────────
-- Rosie — Met team AI assistant (Phase 1, May 17, 2026)
-- ──────────────────────────────────────────────────────────────────────
-- Rosie is an AI assistant for the Met team. She helps Mets with
-- schedule, earnings, brief tasks, how-to questions, and reminders.
-- She has tiered permissions and reports up to Michael (CEO).
-- See ROSIE_SYSTEM_PROMPT in code for her full charter.


-- One conversation per (Met, channel). 'channel' is one of:
-- 'web' (in-workspace chat), 'sms' (text), 'discord' (chat command).
-- Each Met has up to 3 conversations (one per channel). Memory is
-- shared across channels via cross-conversation context lookup,
-- but the conversation row itself is per-channel for clarity.
CREATE TABLE IF NOT EXISTS rosie_conversations (
    id              SERIAL PRIMARY KEY,
    met_user_id     INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    channel         TEXT NOT NULL CHECK (channel IN ('web','sms','discord')),
    created_at_ms   BIGINT NOT NULL,
    last_msg_at_ms  BIGINT NOT NULL,
    UNIQUE (met_user_id, channel)
);
CREATE INDEX IF NOT EXISTS idx_rosie_conv_met ON rosie_conversations(met_user_id);


-- Each message in a Rosie conversation.
-- role: 'user' (Met), 'assistant' (Rosie), 'tool' (Rosie's tool call result)
-- For memory cap: we keep last ~20 turns per conversation. Older
-- turns get summarized into a single 'system' message marked as summary.
CREATE TABLE IF NOT EXISTS rosie_messages (
    id                  SERIAL PRIMARY KEY,
    conversation_id     INTEGER NOT NULL REFERENCES rosie_conversations(id) ON DELETE CASCADE,
    role                TEXT NOT NULL CHECK (role IN ('user','assistant','tool','system')),
    content             TEXT NOT NULL,
    -- For tool messages: which tool was called (e.g. 'get_my_schedule')
    tool_name           TEXT,
    -- For tool messages: the args the tool was called with (JSON)
    tool_args           TEXT,
    -- Token cost tracking (input + output combined)
    tokens_used         INTEGER,
    created_at_ms       BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_rosie_msg_conv ON rosie_messages(conversation_id, created_at_ms);


-- Audit log: every Rosie action that touched data or sent a message.
-- This is queryable by Michael to see what Rosie has been doing.
-- More verbose than rosie_messages — captures every tool result,
-- whether the action was permitted, refusal reasons, etc.
CREATE TABLE IF NOT EXISTS rosie_audit_log (
    id              SERIAL PRIMARY KEY,
    met_user_id     INTEGER REFERENCES users(id) ON DELETE SET NULL,
    channel         TEXT,                       -- web|sms|discord
    action          TEXT NOT NULL,              -- short verb: 'sent_sms', 'updated_schedule', 'refused'
    detail          TEXT,                       -- human-readable description
    tier            INTEGER,                    -- 1|2|3 (permission tier)
    approved_by     INTEGER REFERENCES users(id) ON DELETE SET NULL,
    success         BOOLEAN NOT NULL DEFAULT TRUE,
    created_at_ms   BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_rosie_audit_met ON rosie_audit_log(met_user_id, created_at_ms DESC);
CREATE INDEX IF NOT EXISTS idx_rosie_audit_action ON rosie_audit_log(action, created_at_ms DESC);


-- Reminders Rosie schedules on behalf of Mets.
-- Cron job (in the main scheduler loop) fires reminders when due.
CREATE TABLE IF NOT EXISTS rosie_reminders (
    id              SERIAL PRIMARY KEY,
    met_user_id     INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    remind_at_ms    BIGINT NOT NULL,
    message         TEXT NOT NULL,
    -- Channel to send via when firing: 'sms' or 'web' (web posts to chat)
    channel         TEXT NOT NULL DEFAULT 'sms' CHECK (channel IN ('sms','web')),
    fired_at_ms     BIGINT,                     -- when the reminder actually fired
    cancelled_at_ms BIGINT,                     -- if cancelled before firing
    created_at_ms   BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_rosie_remind_due ON rosie_reminders(remind_at_ms)
    WHERE fired_at_ms IS NULL AND cancelled_at_ms IS NULL;
CREATE INDEX IF NOT EXISTS idx_rosie_remind_met ON rosie_reminders(met_user_id, remind_at_ms);


-- Knowledge base — short Q&A docs Rosie searches when a Met asks
-- "how do I X" or "what's the policy on Y". Seeded with the initial
-- KB content via a one-time migration on first deploy. Admins can
-- add/edit through a future admin UI; for now updates happen via SQL.
CREATE TABLE IF NOT EXISTS rosie_kb_docs (
    id              SERIAL PRIMARY KEY,
    title           TEXT NOT NULL,
    -- Comma-separated tags Rosie can match against ("brief,pro,send")
    tags            TEXT NOT NULL DEFAULT '',
    content         TEXT NOT NULL,
    -- 'active' or 'archived' — archived docs aren't searched
    status          TEXT NOT NULL DEFAULT 'active' CHECK (status IN ('active','archived')),
    created_at_ms   BIGINT NOT NULL,
    updated_at_ms   BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_rosie_kb_status ON rosie_kb_docs(status);


-- Daily cost cap tracking. Each Met has a hard $1/day API limit.
-- This table tracks tokens used per (met, day) so we can refuse
-- service when the cap is hit.
-- Day key is 'YYYY-MM-DD' in US Eastern (resets at midnight ET).
CREATE TABLE IF NOT EXISTS rosie_daily_usage (
    met_user_id     INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    usage_date      TEXT NOT NULL,              -- YYYY-MM-DD in ET
    tokens_used     INTEGER NOT NULL DEFAULT 0,
    cost_cents      INTEGER NOT NULL DEFAULT 0,
    PRIMARY KEY (met_user_id, usage_date)
);






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

-- ── Crew field-notebook entries (confessionals) ──
-- Private notes a Crew member writes after completing a mission.
-- Visible only to the author (and optionally the platform if the
-- "quoteable" flag is set, in which case future Met briefs may pull
-- from them). Schema mirrors the frontend client_id pattern so the
-- frontend can keep its existing id format ("c-<base36-timestamp>").
--
-- Phase 4a (May 14): replace localStorage with real persistence.
CREATE TABLE IF NOT EXISTS confessionals (
    id              TEXT PRIMARY KEY,            -- client-generated, e.g. "c-l8x7y2"
    user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    text            TEXT NOT NULL,
    quoteable       BOOLEAN NOT NULL DEFAULT FALSE,
    mission_id      TEXT,                        -- nullable; the mission that prompted it
    mission_label   TEXT,                        -- nullable; human-readable label
    answer_label    TEXT,                        -- nullable; what the Crew answered
    created_at      BIGINT NOT NULL              -- ms since epoch
);
CREATE INDEX IF NOT EXISTS idx_confessionals_user ON confessionals(user_id, created_at DESC);

-- ── Report verifies (Phase 5a) ──
-- Records each (user, report) verification pair. Used to:
--   - Aggregate per-report "X people verified this" counts
--   - Prevent a user from double-verifying the same report
--   - Enforce the 5-minute un-verify window (delete row if recent)
--
-- Composite primary key on (user_id, report_id) gives us idempotency
-- for free: a duplicate POST does nothing instead of creating duplicates.
-- report_id is a TEXT column because the frontend uses string IDs
-- like 'r-1737' that may not all be numeric.
CREATE TABLE IF NOT EXISTS report_verifies (
    user_id       INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    report_id     TEXT NOT NULL,
    created_at    BIGINT NOT NULL,
    PRIMARY KEY (user_id, report_id)
);
CREATE INDEX IF NOT EXISTS idx_verifies_report ON report_verifies(report_id);
CREATE INDEX IF NOT EXISTS idx_verifies_user ON report_verifies(user_id, created_at DESC);

-- ── Met posts (Phase 6a) ──
-- Posts the meteorologist publishes to the Crew feed. Three lifecycle
-- states tracked via the `status` column:
--   'live'      — currently visible on Crew surfaces
--   'scheduled' — published-to-the-future; promoted to 'live' when the
--                 scheduled_for timestamp passes (frontend timer)
--   'cancelled' — scheduled post the Met cancelled before promotion;
--                 kept for audit, never shown on Crew surfaces
--
-- The id column uses the frontend's own ID format ("met-post-<ts>-<rand>")
-- so the frontend can keep generating IDs client-side without round-trips.
-- author_id ties the post to the Met who wrote it (REFERENCES users).
-- Lat/lng are nullable for posts without a map location.
--
-- Times: submitted_at and scheduled_for are ms-since-epoch BIGINTs, same
-- pattern as confessionals + verifies. The frontend converts to ISO
-- strings as needed for display.
CREATE TABLE IF NOT EXISTS met_posts (
    id              TEXT PRIMARY KEY,
    author_id       INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    text            TEXT NOT NULL,
    author_name     TEXT,                -- snapshot of name at publish time
    author_initials TEXT,                -- snapshot of initials (e.g. "MR")
    lat             DOUBLE PRECISION,    -- nullable
    lng             DOUBLE PRECISION,    -- nullable
    status          TEXT NOT NULL,       -- 'live' | 'scheduled' | 'cancelled'
    submitted_at    BIGINT,              -- ms since epoch; null for scheduled
    scheduled_for   BIGINT,              -- ms since epoch; null for live
    cancelled_at    BIGINT,              -- ms since epoch; null unless cancelled
    verified        INTEGER NOT NULL DEFAULT 0,
    created_at      BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_met_posts_status ON met_posts(status);
CREATE INDEX IF NOT EXISTS idx_met_posts_author ON met_posts(author_id, created_at DESC);
CREATE INDEX IF NOT EXISTS idx_met_posts_scheduled ON met_posts(scheduled_for) WHERE status = 'scheduled';

-- ── Met follow-up messages (Phase 7) ──
-- Audit trail of messages a meteorologist sends to a customer outside
-- of the original brief — e.g. "the forecast just changed, here's a
-- revised call." Lets Met history show "you've messaged this customer
-- 3 times" and gives us records for billing/compliance.
--
-- request_id is nullable because in the prototype phase, follow-ups can
-- be sent from mock-data rows that don't have a real verification_requests
-- ID yet. When the history surface is wired to real data, request_id
-- becomes mandatory.
--
-- delivery_status: 'sent' = Twilio accepted, 'stubbed' = no Twilio creds
-- (dev mode), 'failed' = Twilio error, 'queued' = mid-flight.
CREATE TABLE IF NOT EXISTS met_messages (
    id              SERIAL PRIMARY KEY,
    met_user_id     INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    request_id      INTEGER REFERENCES verification_requests(id) ON DELETE SET NULL,
    customer_phone  TEXT,                -- E.164 if known; null if mock-data send
    customer_label  TEXT,                -- "Patel Construction" for display in Met history
    body            TEXT NOT NULL,
    delivery_status TEXT NOT NULL,       -- 'sent' | 'stubbed' | 'failed' | 'queued'
    twilio_sid      TEXT,                -- nullable; only set on real Twilio sends
    sent_at         BIGINT NOT NULL      -- ms since epoch
);
CREATE INDEX IF NOT EXISTS idx_met_messages_request ON met_messages(request_id, sent_at DESC);
CREATE INDEX IF NOT EXISTS idx_met_messages_met ON met_messages(met_user_id, sent_at DESC);

-- ── Subscriber portal: saved locations (Phase 10) ──
-- A subscriber's "home base" location(s) for their daily brief and
-- threshold alerts. Hobbyist tier gets 1 location; Pro tiers get 1-5
-- depending on plan. lat/lng are floats; label is a free-form name
-- like "Home — Lebanon, IN" or "Job site #3".
--
-- The `is_primary` boolean designates which location drives the daily
-- brief and shows on the portal's main identity card. Exactly one
-- location per user is primary; toggling another to primary unsets
-- the prior one (handled in the PATCH endpoint).
CREATE TABLE IF NOT EXISTS saved_locations (
    id              SERIAL PRIMARY KEY,
    user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    label           TEXT NOT NULL,
    address_text    TEXT,                  -- "Lebanon, IN" or full address
    lat             DOUBLE PRECISION NOT NULL,
    lng             DOUBLE PRECISION NOT NULL,
    county          TEXT,                  -- "Boone County" if known
    is_primary      BOOLEAN NOT NULL DEFAULT FALSE,
    created_at      BIGINT NOT NULL,
    updated_at      BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_saved_locations_user ON saved_locations(user_id, is_primary DESC);

-- ── Subscriber portal: brief delivery preferences (Phase 10) ──
-- One row per user. Created on first read with sensible defaults if
-- missing. Tracks when/how the subscriber wants their daily brief.
--
-- Channels are stored as an ordered comma-separated string for
-- simplicity: "sms,email" means SMS first, fall back to email.
-- Quiet hours stored as HH:MM strings to avoid timezone issues at
-- the DB layer; conversion happens in the cron worker that sends.
CREATE TABLE IF NOT EXISTS brief_preferences (
    user_id              INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    morning_enabled      BOOLEAN NOT NULL DEFAULT TRUE,
    morning_window_start TEXT NOT NULL DEFAULT '05:30',  -- HH:MM local
    morning_window_end   TEXT NOT NULL DEFAULT '07:00',
    evening_enabled      BOOLEAN NOT NULL DEFAULT FALSE,
    evening_window_start TEXT,                            -- nullable when evening off
    evening_window_end   TEXT,
    quiet_start          TEXT NOT NULL DEFAULT '21:00',
    quiet_end            TEXT NOT NULL DEFAULT '05:00',
    channels             TEXT NOT NULL DEFAULT 'sms,email',  -- comma-separated ordered list
    updated_at           BIGINT NOT NULL
);

-- ── Subscriber portal: threshold alerts (Phase 10) ──
-- Custom alert rules a subscriber sets up. e.g. "tell me when wind
-- exceeds 25 mph at my saved location." Each alert is independent.
--
-- metric: 'wind' | 'temp_low' | 'temp_high' | 'precip_chance' | 'humidity'
-- comparator: 'gt' | 'lt' | 'gte' | 'lte' | 'eq'
-- threshold_value: the number to compare against
-- units: 'mph' | 'F' | 'C' | 'pct' — display-only, doesn't affect logic
-- channels: same comma-separated channel list as brief_preferences
-- enabled: false = silenced without deleting
CREATE TABLE IF NOT EXISTS threshold_alerts (
    id              SERIAL PRIMARY KEY,
    user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    metric          TEXT NOT NULL,
    comparator      TEXT NOT NULL,
    threshold_value DOUBLE PRECISION NOT NULL,
    units           TEXT NOT NULL,
    channels        TEXT NOT NULL DEFAULT 'sms,email',
    enabled         BOOLEAN NOT NULL DEFAULT TRUE,
    created_at      BIGINT NOT NULL,
    updated_at      BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_threshold_alerts_user ON threshold_alerts(user_id, enabled);

-- ── Subscriber portal: brief history (Phase 10) ──
-- A log of every brief delivered to a subscriber. Source of truth for
-- the portal's "Brief history" section. brief_type distinguishes
-- routine daily briefs from severe-weather pushes.
--
-- delivery_status tracks Twilio/email status so the portal can show
-- "delivered" vs "failed" honestly.
CREATE TABLE IF NOT EXISTS brief_history (
    id              SERIAL PRIMARY KEY,
    user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    brief_type      TEXT NOT NULL,       -- 'morning' | 'evening' | 'severe' | 'threshold'
    delivered_at    BIGINT NOT NULL,     -- ms since epoch
    verdict         TEXT,                -- 'clear' | 'caution' | 'risk' | null
    snippet         TEXT,                -- first ~140 chars of the brief
    full_body       TEXT,                -- the entire brief text
    delivery_status TEXT NOT NULL,       -- 'sent' | 'stubbed' | 'failed'
    channels_used   TEXT,                -- 'sms' or 'email' or both
    is_met_touched  BOOLEAN NOT NULL DEFAULT FALSE,  -- Pro tier: Met-reviewed
    met_name        TEXT                 -- snapshot of the Met's name if touched
);
CREATE INDEX IF NOT EXISTS idx_brief_history_user ON brief_history(user_id, delivered_at DESC);

-- ── Mission deployments (Phase 10 Item #4) ──
-- One row per mission fired (or queued for approval) by a Met.
-- A "mission" is a directed prompt sent to Crew members in a polygon
-- target area — e.g. "Look at the flag at Lebanon HS — how is it
-- behaving?" The mission template defines the format; the deployment
-- records the specific firing.
--
-- status field:
--   'fired'             — sent to Crew immediately (normal mission)
--   'pending-approval'  — severe mission, awaiting admin sign-off
--   'completed'         — all Crew have responded (or auto-closed)
--   'cancelled'         — admin rejected or Met cancelled
--
-- polygon_geojson stores the targeting polygon as a JSON string. Empty
-- means "all Crew in coverage area." Useful for re-firing the same
-- target later, plus for auditing.
--
-- audience_estimate is the number of Crew matched at fire time. Stored
-- as a snapshot because Crew availability shifts; the historical number
-- is what's useful (not "Crew currently in this polygon").
CREATE TABLE IF NOT EXISTS mission_deployments (
    id                  SERIAL PRIMARY KEY,
    fired_at            BIGINT NOT NULL,
    fired_by_user_id    INTEGER REFERENCES users(id) ON DELETE SET NULL,
    fired_by_name       TEXT,                    -- snapshot of name at fire time
    template_id         TEXT NOT NULL,           -- 'flag-check' | 'visibility-check' | etc
    template_name       TEXT NOT NULL,           -- human label, snapshot
    prompt              TEXT NOT NULL,
    polygon_geojson     TEXT,                    -- JSON string of GeoJSON Feature; NULL = "all Crew"
    polygon_label       TEXT,                    -- "Boone County, IN" or "Indianapolis venue"
    is_severe           BOOLEAN NOT NULL DEFAULT FALSE,
    status              TEXT NOT NULL DEFAULT 'fired',
    audience_estimate   INTEGER NOT NULL DEFAULT 0,
    crew_responded      INTEGER NOT NULL DEFAULT 0,
    crew_cited          INTEGER NOT NULL DEFAULT 0,
    completed_at        BIGINT,
    approved_by_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    approved_at         BIGINT
);
CREATE INDEX IF NOT EXISTS idx_mission_deployments_fired_by
    ON mission_deployments(fired_by_user_id, fired_at DESC);
CREATE INDEX IF NOT EXISTS idx_mission_deployments_status
    ON mission_deployments(status, fired_at DESC);

-- ── Mission notifications (Phase 10 Item #5) ──
-- One row per Crew member notified per mission. Created when a mission
-- fires; updated when the Crew member responds (tap link in SMS, submit
-- their observation). Drives the "X of Y responded" counter on the
-- mission deployment.
--
-- delivery_status:
--   'sent'     — Twilio accepted the message
--   'stubbed'  — no Twilio configured (dev/test mode)
--   'failed'   — Twilio rejected (bad number, opt-out, etc.)
--
-- responded_at is NULL until Crew taps the link. response_text is what
-- they sent back (typed observation, photo URL, etc.). cited is whether
-- the Met used the response in their brief (filled later by Met action).
CREATE TABLE IF NOT EXISTS mission_notifications (
    id              SERIAL PRIMARY KEY,
    mission_id      INTEGER NOT NULL REFERENCES mission_deployments(id) ON DELETE CASCADE,
    crew_user_id    INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    sent_at         BIGINT NOT NULL,
    delivery_status TEXT NOT NULL,
    twilio_sid      TEXT,
    response_token  TEXT UNIQUE NOT NULL,    -- short URL secret for the response page
    responded_at    BIGINT,
    response_text   TEXT,
    cited           BOOLEAN NOT NULL DEFAULT FALSE
);
CREATE INDEX IF NOT EXISTS idx_mission_notifications_mission
    ON mission_notifications(mission_id);
CREATE INDEX IF NOT EXISTS idx_mission_notifications_crew
    ON mission_notifications(crew_user_id, sent_at DESC);
CREATE INDEX IF NOT EXISTS idx_mission_notifications_token
    ON mission_notifications(response_token);

-- ── Admin audit log (Phase 10 Admin Tools) ──
-- Every admin action writes a row. Lets the admin screen show a real
-- audit trail and gives us accountability for sensitive actions like
-- approving Crew, deactivating users, issuing refunds. Never deleted —
-- this is the source of truth for "who did what when."
--
-- action examples:
--   'crew.approve'     — approved a pending Crew application
--   'crew.reject'      — rejected a pending Crew application
--   'user.deactivate'  — soft-deleted a user
--   'user.reactivate'  — restored a deactivated user
--   'payment.refund'   — refunded a Stripe charge
--   'mission.approve'  — approved a severe mission (already audited
--                        via approved_by_user_id; logged here too for
--                        unified audit-trail browsing)
--
-- target_type + target_id let us link to whatever was acted on:
--   ('crew_application', 42) → application 42 was approved
--   ('user', 17)             → user 17 was deactivated
--   ('verification_request', 8) → review 8 was refunded
--
-- details_json holds free-form context as a JSON string (reason for
-- rejection, refund amount, etc.). The admin reviewing the audit log
-- can decode it.
CREATE TABLE IF NOT EXISTS admin_audit_log (
    id              SERIAL PRIMARY KEY,
    actor_user_id   INTEGER REFERENCES users(id) ON DELETE SET NULL,
    actor_name      TEXT,                    -- snapshot at action time
    action          TEXT NOT NULL,
    target_type     TEXT,
    target_id       INTEGER,
    details_json    TEXT,
    created_at      BIGINT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_admin_audit_created
    ON admin_audit_log(created_at DESC);
CREATE INDEX IF NOT EXISTS idx_admin_audit_actor
    ON admin_audit_log(actor_user_id, created_at DESC);

-- ── Crew applications (Phase 10 Admin Tools) ──
-- Submitted by the Crew register form. Pending status until an admin
-- approves (creates the user + grants 'crew' role + sets home base) or
-- rejects (records rejection reason).
--
-- We DON'T create a user row at apply time — applicants haven't been
-- vetted yet. Only on approval does a user row appear. This keeps the
-- users table clean (only actual members) and avoids the awkward "you
-- have an account but no role" state during the approval wait.
--
-- email is UNIQUE so accidental double-submissions update the existing
-- row rather than creating two pending applications.
--
-- status values:
--   'pending'  — submitted, waiting on admin review
--   'approved' — admin approved; user row + role created
--   'rejected' — admin rejected; rejection_reason populated
CREATE TABLE IF NOT EXISTS crew_applications (
    id                  SERIAL PRIMARY KEY,
    created_at          BIGINT NOT NULL,
    updated_at          BIGINT NOT NULL,
    status              TEXT NOT NULL DEFAULT 'pending',
    name                TEXT NOT NULL,
    handle              TEXT,
    email               TEXT UNIQUE NOT NULL,
    phone               TEXT,
    county              TEXT,
    mission_interests   TEXT,        -- comma-separated keys: storms,hail,wind,rain,winter,general
    hours               TEXT,        -- all|weekdays-day|weekdays-evening|weekends|custom
    notify              TEXT,        -- sms|email|both
    reviewed_at         BIGINT,
    reviewed_by_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    rejection_reason    TEXT,
    created_user_id     INTEGER REFERENCES users(id) ON DELETE SET NULL
);
CREATE INDEX IF NOT EXISTS idx_crew_applications_status
    ON crew_applications(status, created_at DESC);

-- ── Pro brief drafts (Phase 10 Item #3 Chunk B) ──
-- When the daily-brief scheduler ticks and matches a Pro-tier subscriber,
-- it generates an AI draft and inserts a row here for Met review. The Met
-- workspace surfaces pending drafts; the Met edits and presses "Send"
-- which moves the brief to brief_history and dispatches it.
--
-- status:
--   'pending-review' — scheduler created it, awaiting Met
--   'claimed'        — Met opened it (claimed_at set)
--   'sent'           — Met sent it (sent_at set, brief_history row created)
--   'expired'        — outside the user's window, never reviewed
--
-- ai_* fields are the scheduler's initial output. met_* fields are the
-- Met's edited version (defaulted to ai_* if Met didn't touch them).
-- final_body is what actually went out — captured at send time so we
-- have an exact record even if met_body is later edited (which it
-- shouldn't be after send, but defense in depth).
CREATE TABLE IF NOT EXISTS pro_brief_drafts (
    id              SERIAL PRIMARY KEY,
    user_id         INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    brief_type      TEXT NOT NULL,           -- 'morning' (more later)
    created_at      BIGINT NOT NULL,
    window_end_at   BIGINT NOT NULL,         -- after this, the draft is too late to send
    status          TEXT NOT NULL DEFAULT 'pending-review',

    -- Snapshot of subscriber context at scheduler time
    user_tier       TEXT,                    -- pro_single|pro_multi|pro_enterprise
    location_label  TEXT,
    location_lat    DOUBLE PRECISION,
    location_lng    DOUBLE PRECISION,
    channels        TEXT,                    -- comma-sep snapshot

    -- AI draft (scheduler-generated)
    ai_verdict      TEXT,                    -- clear|caution|risk
    ai_snippet      TEXT,
    ai_body         TEXT,

    -- Met-edited version (defaults to AI version)
    met_verdict     TEXT,
    met_snippet     TEXT,
    met_body        TEXT,
    met_notes       TEXT,                    -- internal Met notes (NOT sent)

    -- Claim + send
    claimed_at      BIGINT,
    claimed_by_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    sent_at         BIGINT,
    sent_by_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    sent_by_name    TEXT,
    final_verdict   TEXT,
    final_body      TEXT,
    history_id      INTEGER REFERENCES brief_history(id) ON DELETE SET NULL
);
CREATE INDEX IF NOT EXISTS idx_pro_brief_drafts_status
    ON pro_brief_drafts(status, created_at DESC);
CREATE INDEX IF NOT EXISTS idx_pro_brief_drafts_user
    ON pro_brief_drafts(user_id, created_at DESC);

-- ── NWS severe alert pages (Phase 10 Item #7) ──
-- One row per NWS alert that affected at least one Pro subscriber.
-- Created by the scheduler when polling NWS detects a new alert whose
-- polygon contains a subscriber's primary location. Triggers an SMS to
-- the on-duty Met with a link to /?nws-page=<token>.
--
-- Dedupe: NWS alert IDs are stable (like "urn:oid:2.49.0.1.840.0.abc123").
-- We index on nws_alert_id and skip insertion if we've already paged
-- for that alert. If the alert is updated (new polygon, severity bump),
-- we'd need a separate flow — out of scope for v1.
--
-- status:
--   'paged'      — SMS sent to Met, awaiting their review
--   'confirmed'  — Met opened the page and decided to alert subscribers
--   'dismissed'  — Met reviewed and decided not to alert (false alarm /
--                  already-known / out-of-scope)
--   'expired'    — alert window passed without Met action
CREATE TABLE IF NOT EXISTS nws_alert_pages (
    id              SERIAL PRIMARY KEY,
    created_at      BIGINT NOT NULL,
    nws_alert_id    TEXT UNIQUE NOT NULL,
    event           TEXT NOT NULL,           -- "Tornado Warning", etc.
    severity        TEXT,                    -- NWS severity field
    headline        TEXT,
    description     TEXT,
    instruction     TEXT,
    area_desc       TEXT,
    polygon_geojson TEXT,
    expires_at      BIGINT,
    response_token  TEXT UNIQUE NOT NULL,
    status          TEXT NOT NULL DEFAULT 'paged',
    affected_user_ids TEXT,                  -- comma-separated user ids matching the polygon
    met_paged_phone TEXT,                    -- which Met phone we paged
    reviewed_at     BIGINT,
    reviewed_by_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    reviewed_by_name TEXT,
    subscriber_message TEXT,                 -- what the Met sent to subscribers
    subscribers_notified INTEGER DEFAULT 0
);
CREATE INDEX IF NOT EXISTS idx_nws_alert_pages_status
    ON nws_alert_pages(status, created_at DESC);
CREATE INDEX IF NOT EXISTS idx_nws_alert_pages_token
    ON nws_alert_pages(response_token);

-- ── Pro Threads (Phase 10 — Met<>Subscriber DMs) ──
-- One thread per subscriber, holding their conversation with the Met
-- team. Simpler than per-topic threading: subscribers see one continuous
-- conversation; Mets see a queue of threads to attend to.
--
-- last_message_at + last_message_preview let the Met queue render fast
-- without joining to messages on every list call. Updated whenever a
-- new message is inserted.
--
-- unread_for_met / unread_for_subscriber counters bump on the other
-- side's writes and decrement when "mark as read" fires.
CREATE TABLE IF NOT EXISTS pro_threads (
    id                  SERIAL PRIMARY KEY,
    subscriber_user_id  INTEGER NOT NULL UNIQUE REFERENCES users(id) ON DELETE CASCADE,
    created_at          BIGINT NOT NULL,
    last_message_at     BIGINT,
    last_message_preview TEXT,
    last_message_from   TEXT,                 -- 'subscriber' | 'met'
    unread_for_met      INTEGER NOT NULL DEFAULT 0,
    unread_for_subscriber INTEGER NOT NULL DEFAULT 0
);
CREATE INDEX IF NOT EXISTS idx_pro_threads_subscriber
    ON pro_threads(subscriber_user_id);
CREATE INDEX IF NOT EXISTS idx_pro_threads_last_message
    ON pro_threads(last_message_at DESC NULLS LAST);

-- ── Pro Thread Messages ──
-- One row per message. sender_role identifies who sent it ('subscriber'
-- or 'met'). sender_user_id is the actual user — useful for Met audit
-- (which Met responded?). Body is plain text (no markdown for v1).
CREATE TABLE IF NOT EXISTS pro_thread_messages (
    id              SERIAL PRIMARY KEY,
    thread_id       INTEGER NOT NULL REFERENCES pro_threads(id) ON DELETE CASCADE,
    created_at      BIGINT NOT NULL,
    sender_role     TEXT NOT NULL,            -- 'subscriber' | 'met'
    sender_user_id  INTEGER REFERENCES users(id) ON DELETE SET NULL,
    sender_name     TEXT,                     -- snapshot
    body            TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_pro_thread_messages_thread
    ON pro_thread_messages(thread_id, created_at ASC);

-- ── Met tips (Phase 10 — Customer tips for $19 review Met) ──
-- After a Met delivers a $19 verification, the customer can tip the Met
-- via a "like" button on the delivered-review page. All money flows
-- through WeatherValet's Stripe account; Mets see tip earnings in their
-- workspace and get paid via payroll on payday.
--
-- Two payment paths:
--   1. Logged-in subscriber → off-session charge to saved payment method
--      (one-tap, no redirect)
--   2. Non-subscriber (paid $19, no account) → Stripe Checkout session
--      (full payment form, redirect back to thank-you)
--
-- status:
--   'pending'   — Checkout session created, customer hasn't paid yet
--   'completed' — Stripe charge succeeded
--   'failed'    — Stripe charge failed (insufficient funds, card declined)
--
-- Linking: every tip references the verification_request that originated
-- it, plus the Met user (snapshot at tip time — Met can leave the team
-- later, but the tip is still theirs).
CREATE TABLE IF NOT EXISTS met_tips (
    id              SERIAL PRIMARY KEY,
    created_at      BIGINT NOT NULL,
    verification_request_id INTEGER REFERENCES verification_requests(id) ON DELETE SET NULL,
    met_user_id     INTEGER REFERENCES users(id) ON DELETE SET NULL,
    met_name        TEXT,                          -- snapshot
    customer_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL,  -- null for anon
    customer_email  TEXT,                          -- snapshot
    customer_phone  TEXT,                          -- snapshot
    amount_cents    INTEGER NOT NULL,
    status          TEXT NOT NULL DEFAULT 'pending',
    stripe_payment_intent_id TEXT,
    stripe_session_id        TEXT,
    completed_at    BIGINT,
    note            TEXT                           -- optional customer thank-you note
);
CREATE INDEX IF NOT EXISTS idx_met_tips_met
    ON met_tips(met_user_id, created_at DESC);
CREATE INDEX IF NOT EXISTS idx_met_tips_verification
    ON met_tips(verification_request_id);
CREATE INDEX IF NOT EXISTS idx_met_tips_session
    ON met_tips(stripe_session_id);
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
    # Seed Rosie's knowledge base on first deploy. Idempotent — only
    # inserts if the table is empty.
    try:
        _rosie_seed_kb()
    except Exception as e:
        print(f"[rosie-kb] seed at init failed: {e}", flush=True)


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


def _email_shell(content_html: str, preheader: str = "") -> str:
    """Wraps content HTML in a consistent branded shell — header with
    WeatherValet wordmark, footer with company info and support link.
    All transactional emails (magic links, briefs, alerts) use this so
    they feel like part of the same product.

    `preheader` is hidden preview text that email clients show in inbox
    list views (right after the subject). Keep under 100 chars. Most
    email clients (Gmail, Apple Mail, Outlook) render this between the
    subject and body when previewing.
    """
    preheader_block = (
        '<div style="display:none;font-size:1px;color:#fff;'
        'line-height:1px;max-height:0;max-width:0;opacity:0;overflow:hidden;'
        'mso-hide:all;">' + preheader + '</div>'
    ) if preheader else ''

    return (
        '<!DOCTYPE html>'
        '<html><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        '<title>WeatherValet</title>'
        '</head>'
        '<body style="margin:0;padding:0;background:#F4F5F7;'
        'font-family:-apple-system,BlinkMacSystemFont,\'Segoe UI\',Roboto,sans-serif;'
        'color:#0E1116;">'
        + preheader_block +
        '<table role="presentation" cellpadding="0" cellspacing="0" '
        'width="100%" style="background:#F4F5F7;">'
        '<tr><td align="center" style="padding:32px 16px;">'

        # Outer card
        '<table role="presentation" cellpadding="0" cellspacing="0" '
        'width="100%" style="max-width:560px;background:#fff;'
        'border-radius:14px;overflow:hidden;'
        'box-shadow:0 1px 3px rgba(15,17,22,0.06);">'

        # Header bar with brand
        '<tr><td style="padding:22px 28px 18px;border-bottom:1px solid #ECEEF1;">'
        '<table role="presentation" cellpadding="0" cellspacing="0" width="100%">'
        '<tr>'
        '<td align="left" style="font-size:18px;font-weight:700;color:#0E1116;'
        'letter-spacing:-0.01em;">'
        '<span style="display:inline-block;width:10px;height:10px;background:#2E4FB8;'
        'border-radius:50%;margin-right:8px;vertical-align:middle;"></span>'
        'WeatherValet'
        '</td>'
        '<td align="right" style="font-size:11px;color:#8B8F96;'
        'text-transform:uppercase;letter-spacing:0.08em;font-weight:600;">'
        'Decision-grade weather'
        '</td>'
        '</tr></table>'
        '</td></tr>'

        # Content
        '<tr><td style="padding:28px;font-size:15px;line-height:1.55;'
        'color:#0E1116;">'
        + content_html +
        '</td></tr>'

        # Footer
        '<tr><td style="padding:20px 28px;background:#FAFBFC;'
        'border-top:1px solid #ECEEF1;font-size:11.5px;color:#8B8F96;'
        'line-height:1.5;">'
        'WeatherValet \u00b7 Indianapolis, IN<br>'
        'Questions? Reply to this email and a human will read it.<br>'
        '<a href="https://weathervalet.ai" '
        'style="color:#2E4FB8;text-decoration:none;">weathervalet.ai</a>'
        '</td></tr>'

        '</table>'
        '</td></tr></table>'
        '</body></html>'
    )


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

    html_body_inner = (
        f'<h1 style="color:#0E1116;font-size:22px;margin:0 0 14px;'
        f'font-weight:600;letter-spacing:-0.01em;">{heading_text}</h1>'
        f'<p style="color:#3D4148;font-size:15px;line-height:1.6;margin:0 0 24px;">'
        f'{body_text}</p>'
        f'<p style="margin:0 0 28px;"><a href="{magic_link_url}" '
        'style="display:inline-block;background:#2E4FB8;color:#fff;'
        'padding:13px 28px;border-radius:8px;text-decoration:none;'
        f'font-weight:600;font-size:15px;">{button_text}</a></p>'
        '<p style="color:#6B7280;font-size:12.5px;line-height:1.5;margin:0 0 20px;">'
        'If the button doesn\'t work, copy and paste this link into your browser:'
        f'<br><span style="word-break:break-all;color:#2E4FB8;">{magic_link_url}</span></p>'
        '<p style="color:#8B8F96;font-size:12px;line-height:1.5;margin:24px 0 0;'
        'padding-top:18px;border-top:1px solid #ECEEF1;">'
        f'{safety_text}</p>'
    )
    preheader_text = body_text[:90] + "..." if len(body_text) > 90 else body_text
    html_body = _email_shell(html_body_inner, preheader=preheader_text)

    text_body = (
        f"{heading_text}\n\n"
        f"{body_text}\n\n"
        f"{magic_link_url}\n\n"
        f"{safety_text}\n\n"
        f"---\n"
        f"WeatherValet \u00b7 Indianapolis, IN\n"
        f"weathervalet.ai"
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


def send_sms_from(to: str, body: str, from_number: str) -> bool:
    """SMS variant that lets the caller specify the From: number.

    Used by Rosie so her texts come from her own Twilio number (and replies
    route to her webhook). Falls back to TWILIO_FROM_NUMBER if from_number
    is empty — keeps single-number deploys working.
    """
    sender = from_number or TWILIO_FROM_NUMBER
    if not (TwilioClient and TWILIO_ACCOUNT_SID and TWILIO_AUTH_TOKEN and sender):
        print(f"[sms-stub] from={sender or '(none)'} to={to}\n{body}\n", flush=True)
        return True
    try:
        client = TwilioClient(TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN)
        msg = client.messages.create(body=body, from_=sender, to=to)
        print(f"[sms] sent sid={msg.sid} from={sender} to={to}", flush=True)
        return True
    except Exception as e:
        print(f"[sms] FAILED from={sender} to={to}: {type(e).__name__}: {e}", flush=True)
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
        response.headers["Access-Control-Allow-Methods"] = "GET, POST, PATCH, DELETE, OPTIONS"
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


@app.after_request
def _add_security_headers(response):
    """Set security headers on every backend response.

    These defend against clickjacking, MIME-sniffing XSS, protocol
    downgrade attacks, and referrer leakage. They're cheap (one header
    per response, no DB calls) and turn the security-headers grade
    from F to A.

    Headers set:
      - Strict-Transport-Security: force HTTPS for 1 year + subdomains.
        After a browser sees this once, it refuses to connect to the
        site over HTTP. Defense against downgrade attacks.
      - X-Content-Type-Options: nosniff. Browsers must respect the
        Content-Type header we send instead of guessing. Defense
        against MIME-confusion XSS.
      - X-Frame-Options: DENY. The site can't be embedded in an iframe
        anywhere. Defense against clickjacking.
      - Referrer-Policy: strict-origin-when-cross-origin. When users
        click a link to an external site, only the origin (not the
        full URL with query params) is sent as referrer. Defense
        against URL-based info leakage.
      - Permissions-Policy: deny browser features we don't use.
        Reduces attack surface if a future XSS bug gets in.
      - X-XSS-Protection: 0. Modern browsers ignore this, but legacy
        ones can misbehave with the old reflective-XSS filter — better
        to disable it explicitly than leave them guessing.

    NOT set here (intentionally):
      - Content-Security-Policy. CSP is powerful but breaks pages if
        misconfigured (blocks inline scripts/styles that legitimately
        exist). Our index.html has many inline styles and scripts.
        Setting CSP requires a careful audit of every inline use, or
        switching to nonces. That's a separate work item. For now,
        the other headers cover most of CSP's value.
    """
    # Skip for non-HTTPS in case anything still serves on http (Render is
    # always HTTPS, so this is belt-and-suspenders only)
    response.headers["Strict-Transport-Security"] = "max-age=31536000; includeSubDomains"
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    # Disable browser features we don't use, reducing attack surface
    response.headers["Permissions-Policy"] = (
        "accelerometer=(), camera=(), geolocation=(self), "
        "gyroscope=(), magnetometer=(), microphone=(), "
        "payment=(self), usb=(), interest-cohort=()"
    )
    response.headers["X-XSS-Protection"] = "0"
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
# F-X3 (May 17): Polish writing — grammar + spelling check for Mets
# ────────────────────────────────────────────────────────────────────────────
# Mets write Pro Briefs under time pressure. A quick AI pass catches
# typos, grammar slips, and unclear phrasing before the brief goes out.
# Not a heavy-handed rewriter — flagging issues with one-line fixes,
# leaving the Met in control.


POLISH_SYSTEM_PROMPT = """You are a copy-editor for a meteorologist writing
a weather brief for a paying customer. The Met writes under time pressure
and wants a quick proofread.

Find issues in their draft. Focus on:
  - Spelling errors and typos
  - Grammar mistakes (subject/verb agreement, wrong tense, etc.)
  - Run-on or fragment sentences
  - Confusing or unclear phrasing
  - Missing punctuation that hurts readability

Do NOT:
  - Rewrite for "tone" or "voice" — the Met's voice is intentional
  - Suggest stylistic preferences (e.g., serial commas, hyphens vs em-dashes)
  - Restructure paragraphs
  - Change meaning
  - Add new information

Return a JSON array of issues. Each issue is an object with:
  - "original": the exact phrase from the text that has an issue (5-25 words)
  - "suggestion": the corrected version (same length range)
  - "reason": one short phrase explaining the issue (e.g. "typo", "grammar", "unclear")

Return ONLY the JSON array. No prose, no markdown, no explanation. If the
text has no issues, return [].

Limit to 5 issues max — prioritize the most important. If a sentence has
multiple issues, fix all of them in a single suggestion."""


def _call_gemini_polish(body_text: str) -> list:
    """Run Gemini polish pass. Returns list of {original, suggestion, reason}.
    Empty list on success-with-no-issues OR on any failure (best effort)."""
    if not body_text or not body_text.strip():
        return []
    if len(body_text) > 6000:
        body_text = body_text[:6000]

    raw = _call_gemini(POLISH_SYSTEM_PROMPT, body_text, timeout_s=15)
    if not raw:
        return []

    # Strip code fences if Gemini ignored the "no markdown" instruction
    cleaned = raw.strip()
    if cleaned.startswith("```"):
        # ```json\n[...]\n```  or  ```\n[...]\n```
        first_newline = cleaned.find("\n")
        if first_newline > 0:
            cleaned = cleaned[first_newline+1:]
        if cleaned.endswith("```"):
            cleaned = cleaned[:-3]
        cleaned = cleaned.strip()

    try:
        parsed = json.loads(cleaned)
    except Exception as e:
        print(f"[polish] could not parse Gemini JSON: {e!r} raw[:200]={cleaned[:200]}", flush=True)
        return []

    if not isinstance(parsed, list):
        return []

    # Validate + sanitize each issue
    out = []
    for item in parsed[:8]:  # extra safety cap
        if not isinstance(item, dict):
            continue
        orig = (item.get("original") or "").strip()
        sugg = (item.get("suggestion") or "").strip()
        reason = (item.get("reason") or "").strip()
        if not orig or not sugg or orig == sugg:
            continue
        # Make sure original is actually in the body text — Gemini sometimes
        # paraphrases. If it's not a verbatim substring, we can't apply the
        # fix safely, so skip.
        if orig not in body_text:
            # Try a permissive match (lowercase, collapsed whitespace)
            norm_body = " ".join(body_text.lower().split())
            norm_orig = " ".join(orig.lower().split())
            if norm_orig not in norm_body:
                continue
        out.append({
            "original": orig[:200],
            "suggestion": sugg[:200],
            "reason": reason[:60] or "polish"
        })
    return out


@app.route("/api/v1/met/polish-text", methods=["OPTIONS"])
def _met_polish_preflight():
    return ("", 204)


@app.post("/api/v1/met/polish-text")
def met_polish_text():
    """Run a polish pass over a chunk of text. Met-only endpoint.

    Body: { text: "..." }
    Returns: { ok: true, suggestions: [{original, suggestion, reason}, ...] }
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    text = (data.get("text") or "").strip()
    if not text:
        return jsonify({"ok": True, "suggestions": []})
    if len(text) < 20:
        # Too short to bother — also avoids weird outputs on stub headlines
        return jsonify({"ok": True, "suggestions": []})

    try:
        suggestions = _call_gemini_polish(text)
    except Exception as e:
        print(f"[polish] unexpected error: {e!r}", flush=True)
        suggestions = []

    return jsonify({"ok": True, "suggestions": suggestions})


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

    Also clears subscription_tier on the users row (Phase 10 C2) so
    /api/v1/me/subscription correctly reports the user as free.
    """
    with conn.cursor() as cur:
        cur.execute(
            "DELETE FROM user_roles WHERE user_id = %s AND role = %s",
            (user_id, "subscriber"),
        )
        removed = cur.rowcount > 0
        cur.execute(
            "UPDATE users SET subscription_tier = NULL WHERE id = %s",
            (user_id,),
        )
        return removed


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
        customer_phone = (customer_details.get("phone") or "").strip()
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

                    # Phase 10 Item #3: capture phone from Stripe if collected.
                    # We always overwrite — Stripe is the source of truth for
                    # billing/contact info, and the customer just confirmed it.
                    if customer_phone:
                        with conn.cursor() as cur:
                            cur.execute(
                                "UPDATE users SET phone = %s WHERE id = %s",
                                (customer_phone, user_id),
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

                    # Phase 10 C2: capture the subscription tier. We set
                    # the tier key in checkout session metadata when creating
                    # the session. If for some reason metadata is missing,
                    # we fall back to "hobbyist" (cheapest tier — most
                    # forgiving fallback) and log loudly.
                    session_metadata = session.get("metadata") or {}
                    tier_key = (session_metadata.get("wv_tier") or "").strip()
                    if tier_key not in ("hobbyist", "pro_single", "pro_multi"):
                        print(
                            f"[stripe-webhook] missing/invalid wv_tier in metadata "
                            f"(got '{tier_key}') — defaulting to hobbyist",
                            flush=True,
                        )
                        tier_key = "hobbyist"
                    with conn.cursor() as cur:
                        cur.execute(
                            "UPDATE users SET subscription_tier = %s WHERE id = %s",
                            (tier_key, user_id),
                        )

                    # Grant subscriber role
                    newly_granted = _grant_subscriber_role(user_id, conn)

                    # ── Sales rep attribution (locked at signup) ──
                    # Capture rep slug + starter flag from metadata. Once
                    # written, never modified — prevents commission disputes.
                    # If the user has an existing attribution row (came back
                    # after cancelling), DO NOT overwrite — that original
                    # rep already collected their 6 months. The new
                    # subscription becomes a fresh attribution as 'organic'.
                    sess_rep_raw = (session_metadata.get("wv_rep") or "").strip().lower()
                    sess_starter = (session_metadata.get("wv_starter") or "") == "1"
                    rep_slug = "".join(c for c in sess_rep_raw if c.isalnum() or c == "_")[:40] or None
                    signup_ms = int(time.time() * 1000)
                    try:
                        with conn.cursor() as cur:
                            cur.execute(
                                """INSERT INTO sales_attributions
                                   (user_id, rep_slug, signed_up_at, starter_used, locked)
                                   VALUES (%s, %s, %s, %s, TRUE)
                                   ON CONFLICT (user_id) DO NOTHING""",
                                (user_id, rep_slug or "organic", signup_ms, sess_starter),
                            )
                        print(
                            f"[stripe-webhook] attribution: user_id={user_id} "
                            f"rep={rep_slug or 'organic'} starter={sess_starter}",
                            flush=True,
                        )
                    except Exception as e:
                        # Attribution failure shouldn't break the signup —
                        # log it loudly and move on.
                        print(f"[stripe-webhook] attribution write failed: {e!r}", flush=True)

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
            # One-time payment ($19 Met-verified review). Phase 10 Item #2:
            # this is now wired to the verification_requests flow. Stripe
            # session metadata carries wv_request_id (set when we created
            # the checkout session); we use it to find the matching request
            # row and call _mark_paid_and_notify which:
            #   - marks the request 'paid' (idempotent)
            #   - SMSes the customer their standby confirmation
            #   - SMSes the meteorologist with the claim link + AI brief
            session_metadata = session.get("metadata") or {}

            # Phase 10 Met tips: tip-mode checkout? Routed by metadata.
            # wv_tip_for_review is the verification_request_id, not a tip_id —
            # we look up by stripe_session_id (which we stored at tip creation).
            tip_review_id = session_metadata.get("wv_tip_for_review")
            if tip_review_id:
                session_id = session.get("id")
                payment_intent = session.get("payment_intent")
                now_ms = int(time.time() * 1000)
                try:
                    with db() as conn:
                        with conn.cursor() as cur:
                            cur.execute(
                                """UPDATE met_tips
                                   SET status = 'completed', completed_at = %s,
                                       stripe_payment_intent_id = %s
                                   WHERE stripe_session_id = %s AND status = 'pending'
                                   RETURNING id, met_user_id, amount_cents""",
                                (now_ms, payment_intent, session_id),
                            )
                            updated = cur.fetchone()
                    if updated:
                        print(
                            f"[stripe-webhook] met tip completed tip_id={updated['id']} "
                            f"met={updated['met_user_id']} amount=${updated['amount_cents']/100:.2f}",
                            flush=True,
                        )
                    else:
                        print(
                            f"[stripe-webhook] met tip session not found or already completed: {session_id}",
                            flush=True,
                        )
                except Exception as e:
                    print(f"[stripe-webhook] FAILED to complete met tip session={session_id}: {e!r}", flush=True)
                    return jsonify({"error": "internal-error"}), 500
                _stripe_event_record(event_id, event_type, payload)
                return jsonify({"received": True, "handled": True, "mode": "payment", "type": "met-tip"}), 200

            try:
                request_id = int(session_metadata.get("wv_request_id", 0))
            except (ValueError, TypeError):
                request_id = 0
            if request_id:
                payment_id = session.get("payment_intent") or session.get("id")
                try:
                    _mark_paid_and_notify(request_id, payment_id=payment_id)
                    print(
                        f"[stripe-webhook] one-time payment processed: "
                        f"request_id={request_id} session={session.get('id')}",
                        flush=True,
                    )
                except Exception as e:
                    # Don't record the event — let Stripe retry. _mark_paid_and_notify
                    # is idempotent so retries are safe.
                    print(
                        f"[stripe-webhook] FAILED to process payment for "
                        f"request_id={request_id}: {e!r}",
                        flush=True,
                    )
                    return jsonify({"error": "internal-error"}), 500
            else:
                # No request_id in metadata — log and ack so Stripe doesn't retry.
                # Could happen if a test event is fired manually from the Stripe
                # dashboard without our metadata.
                print(
                    f"[stripe-webhook] payment mode but no wv_request_id in metadata: "
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
    """Meteorologist submits their verdict. We mark completed and SMS customer.

    Accepts EITHER:
      - form-encoded (verdict, notes) — legacy HTML view at /meteorologist/<token>
      - JSON body {"verdict": "...", "notes": "..."} — Met workspace (Item #2)

    When called with JSON (Item #2), returns JSON. Otherwise redirects
    back to the meteorologist page like before.
    """
    is_json = (request.is_json or
               request.headers.get("Accept", "").startswith("application/json"))

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM verification_requests WHERE claim_token = %s",
                (claim_token,),
            )
            row = cur.fetchone()
    if not row:
        if is_json:
            return jsonify({"ok": False, "error": "not-found"}), 404
        abort(404)
    if row["status"] == "completed":
        # Idempotent — meteorologist double-submitted, just respond OK
        if is_json:
            return jsonify({"ok": True, "already_completed": True})
        return redirect(f"/meteorologist/{claim_token}")

    # Pull verdict + notes from form OR JSON body
    if request.is_json:
        body = request.get_json(silent=True) or {}
        verdict = (body.get("verdict") or "").strip()
        notes = (body.get("notes") or "").strip()
    else:
        verdict = (request.form.get("verdict") or "").strip()
        notes = (request.form.get("notes") or "").strip()
    if not verdict:
        if is_json:
            return jsonify({"ok": False, "error": "verdict-required"}), 400
        abort(400)

    # Phase 10 Met tips: snapshot the Met's user_id + name on completion
    # so we can attribute future tips to them. If no logged-in user
    # (legacy claim-link flow), these stay null and the tip link won't
    # know who to credit — that's acceptable for the rare legacy path.
    actor = _get_current_user()
    completed_by_user_id = actor["id"] if actor else None
    completed_by_name = (
        (actor.get("name") if actor else None)
        or (actor.get("email") if actor else None)
        or "Your meteorologist"
    )

    # Generate the customer review token (separate from claim_token —
    # this is what we share with the customer in the delivered-review SMS).
    customer_review_token = new_secure_token()

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE verification_requests
                   SET status='completed', completed_at=%s, updated_at=%s,
                       meteorologist_verdict=%s, meteorologist_notes=%s,
                       completed_by_user_id=%s, completed_by_name=%s,
                       customer_review_token=%s
                   WHERE id=%s""",
                (now_ts(), now_ts(), verdict, notes,
                 completed_by_user_id, completed_by_name,
                 customer_review_token, row["id"]),
            )

    # Customer SMS — verdict ready. We link to the customer review page
    # which shows the verdict + a "thank your meteorologist" tip button.
    customer_msg = (
        f"WeatherValet: Your meteorologist's call is ready. "
        f"{verdict[:120]}{'…' if len(verdict) > 120 else ''} "
        f"View full brief + thank {completed_by_name}: "
        f"{FRONTEND_BASE_URL}/?review={customer_review_token}"
    )
    send_sms(row["customer_phone"], customer_msg)

    if is_json:
        return jsonify({
            "ok": True,
            "request_id": row["id"],
            "verdict_sent_to": row["customer_phone"],
        })
    return redirect(f"/meteorologist/{claim_token}")


# ────────────────────────────────────────────────────────────────────────────
# Tiny operator dashboard (admin) — see everything that's happening
# ────────────────────────────────────────────────────────────────────────────


def _admin_auth():
    """Shared HTTP Basic Auth for all /admin/* routes. Returns None when
    auth passes, or a Flask response when it doesn't.

    SECURITY: if WV_ADMIN_USER / WV_ADMIN_PASS aren't set, this function
    FAILS CLOSED (returns 503). Previously this silently allowed access,
    which was a footgun: forget to set env vars on a new deploy and the
    entire admin surface becomes public. Local dev should set these env
    vars too (.env file or shell exports), same as production. There is
    no longer a 'just for dev' bypass."""
    admin_user = os.environ.get("WV_ADMIN_USER")
    admin_pass = os.environ.get("WV_ADMIN_PASS")
    if not (admin_user and admin_pass):
        # Fail closed. If you see this in production, set WV_ADMIN_USER
        # and WV_ADMIN_PASS env vars and redeploy.
        return (
            "Admin auth is not configured. Set WV_ADMIN_USER and WV_ADMIN_PASS env vars.",
            503,
            {"Content-Type": "text/plain"},
        )
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

    # Fire welcome email with temp password. Background-threaded so a
    # slow Resend response doesn't block the create response.
    role_labels = {"met": "Meteorologist", "crew": "Valet Crew",
                   "admin": "Admin", "subscriber": "Subscriber"}
    role_label = role_labels.get(role, role.title())
    try:
        def _send_create_email():
            try:
                _send_welcome_email_with_temp_password(
                    email=email,
                    name=name,
                    temp_password=temp_password,
                    role_label=role_label,
                )
            except Exception as e:
                print(f"[admin_create_user] welcome email send failed: {e!r}", flush=True)
        threading.Thread(target=_send_create_email, daemon=True).start()
    except Exception as e:
        print(f"[admin_create_user] welcome email setup failed: {e!r}", flush=True)

    return jsonify({
        "ok": True,
        "member": _serialize_user_for_admin(row),
        "temp_password": temp_password,
    })


@app.route("/api/v1/admin/users/<int:user_id>", methods=["OPTIONS"])
def _admin_users_single_preflight(user_id):
    return ("", 204)


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

    # If password was reset, fire the welcome email with the new temp.
    # Background-threaded so a slow Resend response doesn't block the
    # PATCH response (which can cause browser network-error timeouts).
    if reset_password and temp_password and row:
        try:
            roles_list = row.get("roles") or []
            primary_role = roles_list[0] if roles_list else "subscriber"
            role_labels = {"met": "Meteorologist", "crew": "Valet Crew",
                          "admin": "Admin", "subscriber": "Subscriber"}
            role_label = role_labels.get(primary_role, "Team Member")
            target_email = row.get("email")
            target_name = row.get("name") or ""

            def _send_in_background():
                try:
                    _send_welcome_email_with_temp_password(
                        email=target_email,
                        name=target_name,
                        temp_password=temp_password,
                        role_label=role_label,
                    )
                except Exception as e:
                    print(f"[admin_update_user] reset email send failed: {e!r}", flush=True)

            threading.Thread(target=_send_in_background, daemon=True).start()
        except Exception as e:
            print(f"[admin_update_user] reset email setup failed: {e!r}", flush=True)

    # Phase 10 Admin Chunk B: audit-log significant changes. We log
    # deactivation/reactivation explicitly (most sensitive); password
    # resets and role changes are also recorded.
    try:
        actor = getattr(request, "user", None) or _get_current_user()
        if actor:
            actor_name = actor.get("name") or actor.get("email") or "admin"
            actor_id = actor.get("id")
            if is_active is not None:
                action = "user.deactivate" if not is_active else "user.reactivate"
                _audit_log(
                    actor_user_id=actor_id, actor_name=actor_name,
                    action=action, target_type="user", target_id=user_id,
                    details={"target_email": row.get("email") if row else None},
                )
            if reset_password:
                _audit_log(
                    actor_user_id=actor_id, actor_name=actor_name,
                    action="user.password_reset",
                    target_type="user", target_id=user_id,
                    details={"target_email": row.get("email") if row else None},
                )
            if role_input is not None:
                _audit_log(
                    actor_user_id=actor_id, actor_name=actor_name,
                    action="user.role_change",
                    target_type="user", target_id=user_id,
                    details={
                        "target_email": row.get("email") if row else None,
                        "new_role": role_input,
                    },
                )
    except Exception as e:
        print(f"[admin_update_user] audit log failed: {e}", flush=True)

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


# ════════════════════════════════════════════════════════════════════
# Crew confessionals (Phase 4a — May 14)
# ════════════════════════════════════════════════════════════════════
#
# Replaces localStorage-only persistence of Field Notebook entries.
# Each row belongs to a specific user (Crew member); only they can
# read or write their own confessionals.
#
# Endpoints:
#   GET  /api/v1/confessionals      — list current user's confessionals
#   POST /api/v1/confessionals      — create a new confessional
#   DELETE /api/v1/confessionals/<id> — delete (within 1 hour of creation)
#
# Auth: session cookie required. No public access.

@app.route("/api/v1/confessionals", methods=["OPTIONS"])
def _confessionals_preflight():
    return ("", 204)


@app.get("/api/v1/confessionals")
def confessionals_list():
    """Return the current user's confessionals, newest first.

    Returns:
        200 {"ok": true, "confessionals": [...]}
        401 {"ok": false, "error": "not-authenticated"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, text, quoteable, mission_id, mission_label,
                          answer_label, created_at
                   FROM confessionals
                   WHERE user_id = %s
                   ORDER BY created_at DESC""",
                (user["id"],),
            )
            rows = cur.fetchall()

    # Map to the same shape the frontend was using under localStorage,
    # so we can swap fetch for localStorage with minimal frontend code change.
    items = [
        {
            "id": r["id"],
            "text": r["text"],
            "quoteable": bool(r["quoteable"]),
            "missionId": r["mission_id"],
            "missionLabel": r["mission_label"],
            "answerLabel": r["answer_label"],
            # Frontend's localStorage stored ISO strings as `timestamp`.
            # We stored ms-since-epoch in the DB; convert back to ISO so
            # the frontend's existing date formatting still works.
            "timestamp": datetime.fromtimestamp(r["created_at"] / 1000, tz=timezone.utc).isoformat(),
        }
        for r in rows
    ]
    return jsonify({"ok": True, "confessionals": items})


@app.post("/api/v1/confessionals")
def confessionals_create():
    """Create a new confessional for the current user.

    Request body:
        {
          "id": "c-l8x7y2",              # client-generated, optional
          "text": "...",                 # required, non-empty after trim
          "quoteable": false,            # optional, defaults to false
          "missionId": "flag-check",     # optional
          "missionLabel": "Flag check",  # optional
          "answerLabel": "Calm"          # optional
        }

    Returns:
        200 {"ok": true, "confessional": {...}}
        400 {"ok": false, "error": "missing-text"}
        401 {"ok": false, "error": "not-authenticated"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}
    text = (data.get("text") or "").strip()
    if not text:
        return jsonify({"ok": False, "error": "missing-text"}), 400

    # Sanity cap on length to prevent abuse (matches the frontend's
    # ~600 char soft limit). Keep slack room for unicode counts.
    if len(text) > 4000:
        text = text[:4000]

    # Use client-supplied id if present (preserves the c-<base36> format
    # the frontend has been using), else generate one server-side.
    entry_id = (data.get("id") or "").strip()
    if not entry_id:
        entry_id = "c-" + secrets.token_hex(6)

    quoteable = bool(data.get("quoteable", False))
    mission_id = (data.get("missionId") or "").strip() or None
    mission_label = (data.get("missionLabel") or "").strip() or None
    answer_label = (data.get("answerLabel") or "").strip() or None
    # Store created_at in ms since epoch (matches frontend Date.now() semantics)
    created_at_ms = int(time.time() * 1000)

    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO confessionals
                       (id, user_id, text, quoteable, mission_id, mission_label,
                        answer_label, created_at)
                       VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                       ON CONFLICT (id) DO NOTHING""",
                    (entry_id, user["id"], text, quoteable, mission_id,
                     mission_label, answer_label, created_at_ms),
                )
    except Exception as e:
        print(f"[confessionals_create] failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "create-failed"}), 500

    return jsonify({"ok": True, "confessional": {
        "id": entry_id,
        "text": text,
        "quoteable": quoteable,
        "missionId": mission_id,
        "missionLabel": mission_label,
        "answerLabel": answer_label,
        "timestamp": datetime.fromtimestamp(created_at_ms / 1000, tz=timezone.utc).isoformat(),
    }})


@app.route("/api/v1/confessionals/<entry_id>", methods=["OPTIONS"])
def _confessionals_delete_preflight(entry_id):
    return ("", 204)


@app.delete("/api/v1/confessionals/<entry_id>")
def confessionals_delete(entry_id):
    """Delete a confessional. Only allowed within 1 hour of creation —
    after that the entry is "set in stone" by design (it's a journal
    entry, not a chat message). This matches the product spec where
    confessionals are editable for a short window after writing.

    Returns:
        200 {"ok": true}
        401 {"ok": false, "error": "not-authenticated"}
        404 {"ok": false, "error": "not-found"}
        403 {"ok": false, "error": "edit-window-closed"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    now_ms = int(time.time() * 1000)
    edit_window_ms = 60 * 60 * 1000  # 1 hour

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT user_id, created_at FROM confessionals WHERE id = %s",
                (entry_id,),
            )
            row = cur.fetchone()

            if row is None or row["user_id"] != user["id"]:
                # Either no such entry, or it belongs to a different user.
                # Don't distinguish — same 404 either way (no info leak).
                return jsonify({"ok": False, "error": "not-found"}), 404

            if now_ms - row["created_at"] > edit_window_ms:
                return jsonify({"ok": False, "error": "edit-window-closed"}), 403

            cur.execute("DELETE FROM confessionals WHERE id = %s", (entry_id,))

    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Report verifies (Phase 5a — May 14)
# ════════════════════════════════════════════════════════════════════
#
# Replaces localStorage-only persistence of "I see it too" verifies.
# Each row is one (user, report) pair. Composite primary key gives us
# idempotency: a duplicate POST does nothing instead of creating a
# duplicate row.
#
# Endpoints:
#   GET    /api/v1/verifies                    — list current user's verifies
#   POST   /api/v1/verifies                    — verify a report
#   DELETE /api/v1/verifies/<report_id>        — un-verify (within 5 min)
#
# Auth: session cookie required.
#
# Token/profile economics (the +2 tokens, the verificationsCount stat,
# the renderFeed bump) all stay client-side for now. Backend just
# persists the verify pair so it's shared across devices.

UNVERIFY_WINDOW_MS = 5 * 60 * 1000  # 5 minutes — matches frontend constant


@app.route("/api/v1/verifies", methods=["OPTIONS"])
def _verifies_preflight():
    return ("", 204)


@app.get("/api/v1/verifies")
def verifies_list():
    """Return the current user's verifies as a list of {report_id, created_at}.

    The frontend uses this to rebuild its in-memory Set on page load,
    replacing the previous localStorage rehydration step.

    Returns:
        200 {"ok": true, "verifies": [{"report_id": "...", "created_at": 12345}, ...]}
        401 {"ok": false, "error": "not-authenticated"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT report_id, created_at FROM report_verifies
                   WHERE user_id = %s
                   ORDER BY created_at DESC""",
                (user["id"],),
            )
            rows = cur.fetchall()

    verifies = [
        {"report_id": r["report_id"], "created_at": r["created_at"]}
        for r in rows
    ]
    return jsonify({"ok": True, "verifies": verifies})


@app.post("/api/v1/verifies")
def verifies_create():
    """Verify a report.

    Request body:
        {"report_id": "r-1737"}

    Idempotent — verifying an already-verified report returns 200 with
    the existing row's created_at. The frontend can treat any 200 as
    "the verify is recorded" regardless of whether it's new.

    Returns:
        200 {"ok": true, "verify": {"report_id": "...", "created_at": 12345}}
        400 {"ok": false, "error": "missing-report-id"}
        401 {"ok": false, "error": "not-authenticated"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}
    report_id = (data.get("report_id") or "").strip()
    if not report_id:
        return jsonify({"ok": False, "error": "missing-report-id"}), 400

    now_ms = int(time.time() * 1000)

    try:
        with db() as conn:
            with conn.cursor() as cur:
                # ON CONFLICT DO NOTHING — duplicate verifies are silently
                # idempotent. We then fetch whatever row exists (whether
                # the one we just tried to insert, or a pre-existing one).
                cur.execute(
                    """INSERT INTO report_verifies (user_id, report_id, created_at)
                       VALUES (%s, %s, %s)
                       ON CONFLICT (user_id, report_id) DO NOTHING""",
                    (user["id"], report_id, now_ms),
                )
                cur.execute(
                    """SELECT created_at FROM report_verifies
                       WHERE user_id = %s AND report_id = %s""",
                    (user["id"], report_id),
                )
                row = cur.fetchone()
    except Exception as e:
        print(f"[verifies_create] failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "create-failed"}), 500

    return jsonify({"ok": True, "verify": {
        "report_id": report_id,
        "created_at": row["created_at"] if row else now_ms,
    }})


@app.route("/api/v1/verifies/<report_id>", methods=["OPTIONS"])
def _verifies_delete_preflight(report_id):
    return ("", 204)


@app.delete("/api/v1/verifies/<report_id>")
def verifies_delete(report_id):
    """Un-verify a report. Only allowed within UNVERIFY_WINDOW_MS (5 min)
    of the verify. After that window, the row is part of the historical
    record and can't be removed.

    Returns:
        200 {"ok": true}
        401 {"ok": false, "error": "not-authenticated"}
        404 {"ok": false, "error": "not-found"}
        403 {"ok": false, "error": "unverify-window-closed"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    now_ms = int(time.time() * 1000)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT created_at FROM report_verifies
                   WHERE user_id = %s AND report_id = %s""",
                (user["id"], report_id),
            )
            row = cur.fetchone()

            if row is None:
                return jsonify({"ok": False, "error": "not-found"}), 404

            if now_ms - row["created_at"] > UNVERIFY_WINDOW_MS:
                return jsonify({"ok": False, "error": "unverify-window-closed"}), 403

            cur.execute(
                """DELETE FROM report_verifies
                   WHERE user_id = %s AND report_id = %s""",
                (user["id"], report_id),
            )

    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Met posts (Phase 6a — May 14)
# ════════════════════════════════════════════════════════════════════
#
# Replaces localStorage-only persistence of meteorologist posts to the
# Crew feed. Three lifecycle states (live/scheduled/cancelled). Posts
# stay in the table forever — cancelled and consumed-from-scheduled
# posts aren't deleted, just status-flipped, so we have a history.
#
# Endpoints:
#   GET    /api/v1/met-posts                   — list (all statuses)
#   POST   /api/v1/met-posts                   — create new post (live OR scheduled)
#   PATCH  /api/v1/met-posts/<id>              — update fields (scheduled only)
#   DELETE /api/v1/met-posts/<id>              — cancel (scheduled only; sets status='cancelled')
#
# Auth: session cookie required. Currently any authed user can read all
# posts (because Crew need to see them); only the author or an admin
# can create/update/cancel.
#
# Note on promotion (scheduled → live): the FRONTEND timer handles this
# (Chunk 6c-2 in index.html). When a Met has the workspace open and the
# scheduled time passes, the frontend calls PATCH to flip status='live'
# and set submitted_at. If no Met is watching, the post stays 'scheduled'
# in the DB; the next Met to open the workspace promotes it (slightly
# late). For v1 scale (1-2 Mets), this is acceptable.

def _serialize_met_post(row):
    """Convert a DB row to the shape the frontend uses.

    Frontend keys match exactly so the GET /api/v1/met-posts response
    can drop straight into the in-memory MET_POSTS array.
    """
    return {
        "id":              row["id"],
        "text":            row["text"],
        "author":          row["author_name"] or "",
        "authorInitials":  row["author_initials"] or "",
        "isMetPost":       True,
        "lat":             row["lat"],
        "lng":             row["lng"],
        "status":          row["status"],
        "verified":        row["verified"],
        # ISO strings — frontend uses these for display + Date math
        "submittedAt":     datetime.fromtimestamp(row["submitted_at"] / 1000, tz=timezone.utc).isoformat()
                              if row["submitted_at"] else None,
        "scheduledFor":    datetime.fromtimestamp(row["scheduled_for"] / 1000, tz=timezone.utc).isoformat()
                              if row["scheduled_for"] else None,
        "cancelledAt":     datetime.fromtimestamp(row["cancelled_at"] / 1000, tz=timezone.utc).isoformat()
                              if row["cancelled_at"] else None,
    }


@app.route("/api/v1/met-posts", methods=["OPTIONS"])
def _met_posts_preflight():
    return ("", 204)


@app.get("/api/v1/met-posts")
def met_posts_list():
    """Return all met posts (live, scheduled, and cancelled) sorted with
    newest at the top.

    Crew surfaces filter by status='live' client-side. The Met workspace
    surfaces filter by status='scheduled' for the queue panel. Returning
    everything in one call simplifies the frontend's cache logic.

    Returns:
        200 {"ok": true, "posts": [{...}, ...]}
        401 {"ok": false, "error": "not-authenticated"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, text, author_name, author_initials, lat, lng,
                          status, submitted_at, scheduled_for, cancelled_at,
                          verified, created_at
                   FROM met_posts
                   ORDER BY created_at DESC"""
            )
            rows = cur.fetchall()

    posts = [_serialize_met_post(r) for r in rows]
    return jsonify({"ok": True, "posts": posts})


@app.post("/api/v1/met-posts")
def met_posts_create():
    """Create a new Met post.

    Request body:
        {
          "id": "met-post-1234567-456",         # client-generated
          "text": "Cell weakening over...",     # required
          "lat": 39.8,                           # optional
          "lng": -86.2,                          # optional
          "status": "live" | "scheduled",        # required
          "scheduledFor": "2026-05-14T15:00:00Z" # required if scheduled
        }

    Returns:
        200 {"ok": true, "post": {...}}
        400 {"ok": false, "error": "missing-text" | "invalid-status" | "missing-scheduled-time"}
        401 {"ok": false, "error": "not-authenticated"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}
    text = (data.get("text") or "").strip()
    if not text:
        return jsonify({"ok": False, "error": "missing-text"}), 400
    if len(text) > 4000:
        text = text[:4000]

    status = (data.get("status") or "").strip()
    if status not in ("live", "scheduled"):
        return jsonify({"ok": False, "error": "invalid-status"}), 400

    # ID is client-generated to match the frontend's existing format.
    # Fall back to a server ID if none supplied (defensive).
    post_id = (data.get("id") or "").strip()
    if not post_id:
        post_id = "met-post-" + str(int(time.time() * 1000)) + "-" + secrets.token_hex(2)

    lat = data.get("lat")
    lng = data.get("lng")
    # Allow numeric or string-ified numbers; nulls pass through.
    try:
        lat = float(lat) if lat is not None else None
        lng = float(lng) if lng is not None else None
    except (ValueError, TypeError):
        lat = lng = None

    now_ms = int(time.time() * 1000)

    submitted_at = None
    scheduled_for = None

    if status == "live":
        submitted_at = now_ms
    else:  # scheduled
        scheduled_for_iso = (data.get("scheduledFor") or "").strip()
        if not scheduled_for_iso:
            return jsonify({"ok": False, "error": "missing-scheduled-time"}), 400
        try:
            # Accept ISO 8601 with or without Z. Python's fromisoformat is
            # strict but tolerant if we strip the trailing Z.
            iso = scheduled_for_iso.rstrip("Z")
            if iso.endswith("+00:00"):
                iso = iso[:-6]
            scheduled_dt = datetime.fromisoformat(iso)
            # Treat naive datetimes as UTC (matches frontend behavior)
            if scheduled_dt.tzinfo is None:
                scheduled_dt = scheduled_dt.replace(tzinfo=timezone.utc)
            scheduled_for = int(scheduled_dt.timestamp() * 1000)
        except (ValueError, TypeError) as e:
            print(f"[met_posts_create] bad scheduledFor: {scheduled_for_iso!r}: {e}", flush=True)
            return jsonify({"ok": False, "error": "invalid-scheduled-time"}), 400

    # Snapshot author info at publish time so the post displays correctly
    # even if the user later changes their name.
    author_name = (user.get("name") or "").strip() or "Meteorologist"
    parts = author_name.split()
    author_initials = "".join(p[0] for p in parts).upper()[:2] or "MT"

    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO met_posts
                       (id, author_id, text, author_name, author_initials,
                        lat, lng, status, submitted_at, scheduled_for,
                        verified, created_at)
                       VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, 0, %s)
                       ON CONFLICT (id) DO NOTHING""",
                    (post_id, user["id"], text, author_name, author_initials,
                     lat, lng, status, submitted_at, scheduled_for, now_ms),
                )
                cur.execute(
                    """SELECT id, text, author_name, author_initials, lat, lng,
                              status, submitted_at, scheduled_for, cancelled_at,
                              verified, created_at
                       FROM met_posts WHERE id = %s""",
                    (post_id,),
                )
                row = cur.fetchone()
    except Exception as e:
        print(f"[met_posts_create] failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "create-failed"}), 500

    if row is None:
        return jsonify({"ok": False, "error": "create-failed"}), 500
    return jsonify({"ok": True, "post": _serialize_met_post(row)})


@app.route("/api/v1/met-posts/<post_id>", methods=["OPTIONS"])
def _met_posts_id_preflight(post_id):
    return ("", 204)


@app.patch("/api/v1/met-posts/<post_id>")
def met_posts_update(post_id):
    """Update a Met post. Used in two scenarios:

    1. Edit a scheduled post (Met changes their mind before promotion)
       Allowed fields: text, lat, lng, scheduledFor
    2. Promote a scheduled post to live (frontend timer; status flip)
       Allowed fields: status='live', submittedAt

    The PATCH semantics: only the fields the caller sends are updated.
    Other fields stay as-is.

    Authorization: only the author or an admin can update. Returns 403
    if a non-author non-admin tries. (Note: in the current simple model,
    anyone with the met role could in principle update anyone's post —
    but the author check keeps it tight even within a small team.)

    Returns:
        200 {"ok": true, "post": {...}}
        401 {"ok": false, "error": "not-authenticated"}
        403 {"ok": false, "error": "forbidden"}
        404 {"ok": false, "error": "not-found"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}

    # Build update SET clauses dynamically based on which fields are present.
    set_clauses = []
    params = []

    if "text" in data:
        text = (data.get("text") or "").strip()
        if not text:
            return jsonify({"ok": False, "error": "missing-text"}), 400
        if len(text) > 4000:
            text = text[:4000]
        set_clauses.append("text = %s")
        params.append(text)

    if "lat" in data:
        try:
            lat = float(data["lat"]) if data["lat"] is not None else None
            set_clauses.append("lat = %s")
            params.append(lat)
        except (ValueError, TypeError):
            pass

    if "lng" in data:
        try:
            lng = float(data["lng"]) if data["lng"] is not None else None
            set_clauses.append("lng = %s")
            params.append(lng)
        except (ValueError, TypeError):
            pass

    if "scheduledFor" in data:
        if data["scheduledFor"]:
            try:
                iso = data["scheduledFor"].rstrip("Z")
                if iso.endswith("+00:00"):
                    iso = iso[:-6]
                dt = datetime.fromisoformat(iso)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                set_clauses.append("scheduled_for = %s")
                params.append(int(dt.timestamp() * 1000))
            except (ValueError, TypeError):
                return jsonify({"ok": False, "error": "invalid-scheduled-time"}), 400
        else:
            set_clauses.append("scheduled_for = NULL")

    if "status" in data:
        status = (data.get("status") or "").strip()
        if status not in ("live", "scheduled", "cancelled"):
            return jsonify({"ok": False, "error": "invalid-status"}), 400
        set_clauses.append("status = %s")
        params.append(status)
        # If promoting to live, set submitted_at to now (the promotion
        # timer's "the scheduled moment is now" semantics).
        if status == "live" and "submittedAt" not in data:
            set_clauses.append("submitted_at = %s")
            params.append(int(time.time() * 1000))

    if "submittedAt" in data and data["submittedAt"]:
        try:
            iso = data["submittedAt"].rstrip("Z")
            if iso.endswith("+00:00"):
                iso = iso[:-6]
            dt = datetime.fromisoformat(iso)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            set_clauses.append("submitted_at = %s")
            params.append(int(dt.timestamp() * 1000))
        except (ValueError, TypeError):
            pass

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-fields-to-update"}), 400

    # Authorization: only author or admin.
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT author_id FROM met_posts WHERE id = %s",
                (post_id,),
            )
            existing = cur.fetchone()
            if existing is None:
                return jsonify({"ok": False, "error": "not-found"}), 404

            is_admin = "admin" in (user.get("roles") or [])
            if existing["author_id"] != user["id"] and not is_admin:
                return jsonify({"ok": False, "error": "forbidden"}), 403

            params.append(post_id)
            cur.execute(
                f"UPDATE met_posts SET {', '.join(set_clauses)} WHERE id = %s",
                tuple(params),
            )

            cur.execute(
                """SELECT id, text, author_name, author_initials, lat, lng,
                          status, submitted_at, scheduled_for, cancelled_at,
                          verified, created_at
                   FROM met_posts WHERE id = %s""",
                (post_id,),
            )
            row = cur.fetchone()

    return jsonify({"ok": True, "post": _serialize_met_post(row)})


@app.delete("/api/v1/met-posts/<post_id>")
def met_posts_cancel(post_id):
    """Cancel a scheduled Met post. Sets status='cancelled' and records
    the cancellation timestamp. Does NOT remove the row — we keep
    cancelled posts for audit history.

    Live posts cannot be cancelled — they're already published. The
    frontend never offers a "cancel" button on a live post.

    Returns:
        200 {"ok": true}
        401 {"ok": false, "error": "not-authenticated"}
        403 {"ok": false, "error": "forbidden" | "cannot-cancel-live"}
        404 {"ok": false, "error": "not-found"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT author_id, status FROM met_posts WHERE id = %s",
                (post_id,),
            )
            row = cur.fetchone()

            if row is None:
                return jsonify({"ok": False, "error": "not-found"}), 404

            is_admin = "admin" in (user.get("roles") or [])
            if row["author_id"] != user["id"] and not is_admin:
                return jsonify({"ok": False, "error": "forbidden"}), 403

            if row["status"] == "live":
                return jsonify({"ok": False, "error": "cannot-cancel-live"}), 403

            if row["status"] == "cancelled":
                # Idempotent — already cancelled
                return jsonify({"ok": True})

            cur.execute(
                """UPDATE met_posts
                   SET status = 'cancelled', cancelled_at = %s
                   WHERE id = %s""",
                (int(time.time() * 1000), post_id),
            )

    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Met follow-up messages (Phase 7 — May 14)
# ════════════════════════════════════════════════════════════════════
#
# Lets a meteorologist send a follow-up SMS to a customer when the
# forecast changes after the original brief was delivered.
#
# Endpoints:
#   POST /api/v1/met/messages          — send a follow-up
#   GET  /api/v1/met/messages?...      — list messages, optional request_id filter
#
# Auth: requires the met or admin role.

@app.route("/api/v1/met/messages", methods=["OPTIONS"])
def _met_messages_preflight():
    return ("", 204)


@app.post("/api/v1/met/messages")
def met_messages_send():
    """Send a follow-up SMS to a verification customer.

    Request body:
        {
          "request_id": 42,              # optional — links to verification_requests
          "customer_phone": "+15551234", # optional — required if no request_id
          "customer_label": "Patel Co",  # display label for the Met history row
          "body": "Storm has shifted..."  # required, the message text
        }

    If request_id is provided AND that request has a customer_phone, we use
    that phone (the request_id phone is authoritative). If no request_id is
    provided but customer_phone is, we use the phone directly — this is the
    path for mock-data rows in the prototype Met history.

    Returns:
        200 {"ok": true, "message_id": 7, "delivery_status": "sent"}
        400 {"ok": false, "error": "..."}
        401 {"ok": false, "error": "not-authenticated"}
        403 {"ok": false, "error": "forbidden"}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    body = (data.get("body") or "").strip()
    if not body:
        return jsonify({"ok": False, "error": "missing-body"}), 400
    if len(body) > 1600:
        # Twilio caps SMS at ~1600 chars before segmenting heavily
        body = body[:1600]

    request_id = data.get("request_id")
    try:
        request_id = int(request_id) if request_id else None
    except (ValueError, TypeError):
        request_id = None

    customer_phone = (data.get("customer_phone") or "").strip() or None
    customer_label = (data.get("customer_label") or "").strip() or None

    # If request_id provided, look up phone + label from the request record.
    # The request record's phone is authoritative when present.
    if request_id is not None:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    "SELECT customer_phone, plan_text FROM verification_requests WHERE id = %s",
                    (request_id,),
                )
                req_row = cur.fetchone()
        if req_row:
            if req_row.get("customer_phone"):
                customer_phone = req_row["customer_phone"]
            if not customer_label and req_row.get("plan_text"):
                # Use the first ~40 chars of plan_text as a fallback label
                customer_label = req_row["plan_text"][:40]

    # Determine delivery path. If we have a real phone, attempt Twilio.
    # If not, we still record the message but mark it stubbed — the Met
    # gets feedback that the action happened.
    delivery_status = "stubbed"
    twilio_sid = None
    if customer_phone:
        # send_sms returns True on real send OR stub-fallback; we can't
        # distinguish the two from its return value. Use the env vars
        # directly to decide what delivery_status to record.
        sent = send_sms(customer_phone, body)
        if sent and TWILIO_ACCOUNT_SID and TWILIO_AUTH_TOKEN and TWILIO_FROM_NUMBER and TwilioClient:
            delivery_status = "sent"
            # Note: we don't currently extract the SID from send_sms — it
            # logs to stdout. A future enhancement would have send_sms
            # return the SID. For now, the stdout log is the trail.
        elif sent:
            delivery_status = "stubbed"
        else:
            delivery_status = "failed"

    now_ms = int(time.time() * 1000)

    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO met_messages
                       (met_user_id, request_id, customer_phone, customer_label,
                        body, delivery_status, twilio_sid, sent_at)
                       VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                       RETURNING id""",
                    (user["id"], request_id, customer_phone, customer_label,
                     body, delivery_status, twilio_sid, now_ms),
                )
                msg_id = cur.fetchone()["id"]
    except Exception as e:
        print(f"[met_messages_send] DB write failed: {type(e).__name__}: {e}", flush=True)
        return jsonify({"ok": False, "error": "log-write-failed"}), 500

    print(
        f"[met-message] sent: id={msg_id} met_user={user['id']} "
        f"to={customer_phone or '(none)'} status={delivery_status} "
        f"label={customer_label!r}",
        flush=True,
    )

    return jsonify({
        "ok": True,
        "message_id": msg_id,
        "delivery_status": delivery_status,
        "sent_at": now_ms,
    })


@app.get("/api/v1/met/messages")
def met_messages_list():
    """List Met follow-up messages.

    Query params:
        request_id  — optional, filter to messages for one request
        met_only    — optional ('1' or 'true'), filter to current Met's sends

    Returns:
        200 {"ok": true, "messages": [...]}
        401 / 403 as elsewhere
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    request_id_filter = request.args.get("request_id")
    met_only = request.args.get("met_only", "").lower() in ("1", "true", "yes")

    sql = """SELECT id, met_user_id, request_id, customer_phone, customer_label,
                    body, delivery_status, twilio_sid, sent_at
             FROM met_messages WHERE 1=1"""
    params = []
    if request_id_filter:
        try:
            sql += " AND request_id = %s"
            params.append(int(request_id_filter))
        except (ValueError, TypeError):
            pass
    if met_only:
        sql += " AND met_user_id = %s"
        params.append(user["id"])
    sql += " ORDER BY sent_at DESC LIMIT 200"

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(sql, tuple(params))
            rows = cur.fetchall()

    messages = [
        {
            "id": r["id"],
            "met_user_id": r["met_user_id"],
            "request_id": r["request_id"],
            "customer_phone": r["customer_phone"],
            "customer_label": r["customer_label"],
            "body": r["body"],
            "delivery_status": r["delivery_status"],
            "twilio_sid": r["twilio_sid"],
            "sent_at": r["sent_at"],
        }
        for r in rows
    ]
    return jsonify({"ok": True, "messages": messages})


# ════════════════════════════════════════════════════════════════════
# Subscriber portal endpoints (Phase 10 — May 14)
# ════════════════════════════════════════════════════════════════════
#
# Read-only endpoints for the subscriber portal's identity card, saved
# locations, brief preferences, threshold alerts, and brief history.
# Edit/POST/PATCH endpoints come in Chunk B.
#
# Auth: session cookie required. Any signed-in user can read their own
# data; we don't expose another user's portal.

@app.route("/api/v1/me/subscription", methods=["OPTIONS"])
def _me_subscription_preflight():
    return ("", 204)


@app.get("/api/v1/me/subscription")
def me_subscription():
    """Return the current user's subscription summary for the portal
    identity card.

    Pulls from the users table (created_at, is_active) and joins with
    Stripe metadata if a customer record exists. For users without a
    Stripe customer (free tier), returns plan='free' with no renewal.

    Returns:
        200 {
          "ok": true,
          "plan": "free" | "hobbyist" | "pro_single" | "pro_multi" | "pro_enterprise",
          "plan_display": "Hobbyist" | "Pro Single" | ...,
          "price_display": "$30 / month" | "Free" | ...,
          "next_billing_at": ms-since-epoch | null,
          "member_since": ms-since-epoch,
          "is_active": true,
          "stripe_customer_id": "cus_..." | null
        }
        401 not authenticated
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, created_at, is_active, stripe_customer_id,
                          subscription_tier
                   FROM users WHERE id = %s""",
                (user["id"],),
            )
            row = cur.fetchone()

    if row is None:
        return jsonify({"ok": False, "error": "user-not-found"}), 404

    # Determine plan tier. Prefer the stored subscription_tier (set by
    # the webhook on successful checkout). Falls back to "hobbyist" for
    # legacy subscribers (granted role before C2 shipped the column),
    # and "free" for everyone else.
    roles = user.get("roles") or []
    tier_key = row.get("subscription_tier")
    has_subscriber_role = "subscriber" in roles

    TIER_DISPLAY = {
        "hobbyist":   ("hobbyist",   "Hobbyist",       "$30 / month"),
        "pro_single": ("pro_single", "Pro Single",     "$400 / month"),
        "pro_multi":  ("pro_multi",  "Pro Multi",      "$1,200 / month"),
        "pro_enterprise": ("pro_enterprise", "Pro Enterprise", "Custom"),
    }

    if tier_key and tier_key in TIER_DISPLAY:
        plan, plan_display, price_display = TIER_DISPLAY[tier_key]
    elif has_subscriber_role:
        # Legacy: role granted before tier was tracked. Default to Hobbyist
        # since pre-C2 only Hobbyist signups existed.
        plan, plan_display, price_display = TIER_DISPLAY["hobbyist"]
    else:
        plan, plan_display, price_display = "free", "Free", "Free"

    # Next billing date: we don't have it stored locally yet. Chunk C
    # will query Stripe for the actual subscription period_end. For now,
    # estimate as one month from member_since modulo current date — that
    # gives the portal a realistic-looking renewal without lying about
    # data we don't have. NULL for free users.
    next_billing_at = None
    if plan != "free":
        # Naive: today + ~28 days, anchored to member-since day-of-month.
        # When Stripe is wired, replace this entire block with the real
        # subscription.current_period_end timestamp.
        try:
            since_dt = datetime.fromtimestamp(row["created_at"] / 1000, tz=timezone.utc)
            now_dt = datetime.now(timezone.utc)
            # Find next monthly anniversary of created_at
            target_day = since_dt.day
            year, month = now_dt.year, now_dt.month
            # Try this month first; if past, move to next.
            try:
                candidate = now_dt.replace(day=min(target_day, 28))
            except ValueError:
                candidate = now_dt.replace(day=28)
            if candidate <= now_dt:
                if month == 12:
                    candidate = candidate.replace(year=year + 1, month=1)
                else:
                    candidate = candidate.replace(month=month + 1)
            next_billing_at = int(candidate.timestamp() * 1000)
        except Exception:
            next_billing_at = None

    # Starter Month detection (sales funnel). If the user signed up
    # via /starter (starter_used=TRUE) and it's been less than 30 days
    # since signup, they're in their starter window.
    is_starter_month = False
    starter_renews_ms = None
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    "SELECT signed_up_at, starter_used FROM sales_attributions WHERE user_id = %s",
                    (user["id"],),
                )
                attrib = cur.fetchone()
        if attrib and attrib.get("starter_used"):
            signed_at = attrib["signed_up_at"]
            now_ms_check = int(time.time() * 1000)
            # 30 days = 30 * 24 * 3600 * 1000 = 2,592,000,000 ms
            if (now_ms_check - signed_at) < 30 * 24 * 3600 * 1000:
                is_starter_month = True
                starter_renews_ms = signed_at + 30 * 24 * 3600 * 1000
    except Exception as e:
        print(f"[subscription] starter check failed: {e}", flush=True)

    return jsonify({
        "ok": True,
        "plan": plan,
        "plan_display": plan_display,
        "price_display": price_display,
        "next_billing_at": next_billing_at,
        "member_since": row["created_at"],
        "is_active": row["is_active"] if "is_active" in row else True,
        "stripe_customer_id": row.get("stripe_customer_id"),
        "is_starter_month": is_starter_month,
        "starter_renews_at": starter_renews_ms,
    })


@app.route("/api/v1/me/saved-locations", methods=["OPTIONS"])
def _me_saved_locations_preflight():
    return ("", 204)


@app.get("/api/v1/me/saved-locations")
def me_saved_locations_list():
    """List the current user's saved locations, primary first.

    Returns:
        200 {"ok": true, "locations": [...]}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, label, address_text, lat, lng, county, is_primary,
                          created_at, updated_at
                   FROM saved_locations
                   WHERE user_id = %s
                   ORDER BY is_primary DESC, created_at ASC""",
                (user["id"],),
            )
            rows = cur.fetchall()

    locations = [
        {
            "id": r["id"],
            "label": r["label"],
            "address_text": r["address_text"],
            "lat": r["lat"],
            "lng": r["lng"],
            "county": r["county"],
            "is_primary": r["is_primary"],
            "created_at": r["created_at"],
            "updated_at": r["updated_at"],
        }
        for r in rows
    ]
    return jsonify({"ok": True, "locations": locations})


@app.route("/api/v1/me/brief-preferences", methods=["OPTIONS"])
def _me_brief_preferences_preflight():
    return ("", 204)


@app.get("/api/v1/me/brief-preferences")
def me_brief_preferences():
    """Return the current user's brief delivery preferences.

    Auto-creates a row with sensible defaults on first read so the
    portal always has something to display.

    Returns:
        200 {"ok": true, "preferences": {...}}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    now_ms = int(time.time() * 1000)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT user_id, morning_enabled, morning_window_start,
                          morning_window_end, evening_enabled,
                          evening_window_start, evening_window_end,
                          quiet_start, quiet_end, channels, updated_at
                   FROM brief_preferences WHERE user_id = %s""",
                (user["id"],),
            )
            row = cur.fetchone()

            if row is None:
                # Insert default row
                cur.execute(
                    """INSERT INTO brief_preferences (user_id, updated_at)
                       VALUES (%s, %s)
                       ON CONFLICT (user_id) DO NOTHING
                       RETURNING user_id, morning_enabled, morning_window_start,
                                 morning_window_end, evening_enabled,
                                 evening_window_start, evening_window_end,
                                 quiet_start, quiet_end, channels, updated_at""",
                    (user["id"], now_ms),
                )
                row = cur.fetchone()
                # Fallback: in case ON CONFLICT happened (race), re-fetch
                if row is None:
                    cur.execute(
                        """SELECT user_id, morning_enabled, morning_window_start,
                                  morning_window_end, evening_enabled,
                                  evening_window_start, evening_window_end,
                                  quiet_start, quiet_end, channels, updated_at
                           FROM brief_preferences WHERE user_id = %s""",
                        (user["id"],),
                    )
                    row = cur.fetchone()

    if row is None:
        return jsonify({"ok": False, "error": "preferences-unavailable"}), 500

    return jsonify({
        "ok": True,
        "preferences": {
            "morning_enabled":      row["morning_enabled"],
            "morning_window_start": row["morning_window_start"],
            "morning_window_end":   row["morning_window_end"],
            "evening_enabled":      row["evening_enabled"],
            "evening_window_start": row["evening_window_start"],
            "evening_window_end":   row["evening_window_end"],
            "quiet_start":          row["quiet_start"],
            "quiet_end":            row["quiet_end"],
            "channels":             [c for c in (row["channels"] or "").split(",") if c],
            "updated_at":           row["updated_at"],
        },
    })


@app.route("/api/v1/me/threshold-alerts", methods=["OPTIONS"])
def _me_threshold_alerts_preflight():
    return ("", 204)


@app.get("/api/v1/me/threshold-alerts")
def me_threshold_alerts_list():
    """List the current user's threshold alerts, most recent first.

    Returns:
        200 {"ok": true, "alerts": [...]}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, metric, comparator, threshold_value, units,
                          channels, enabled, created_at, updated_at
                   FROM threshold_alerts
                   WHERE user_id = %s
                   ORDER BY created_at DESC""",
                (user["id"],),
            )
            rows = cur.fetchall()

    alerts = [
        {
            "id": r["id"],
            "metric": r["metric"],
            "comparator": r["comparator"],
            "threshold_value": r["threshold_value"],
            "units": r["units"],
            "channels": [c for c in (r["channels"] or "").split(",") if c],
            "enabled": r["enabled"],
            "created_at": r["created_at"],
            "updated_at": r["updated_at"],
        }
        for r in rows
    ]
    return jsonify({"ok": True, "alerts": alerts})


@app.route("/api/v1/me/brief-history", methods=["OPTIONS"])
def _me_brief_history_preflight():
    return ("", 204)


@app.get("/api/v1/me/brief-history")
def me_brief_history():
    """List the current user's brief history (last 30 entries).

    Returns:
        200 {"ok": true, "history": [...]}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, brief_type, delivered_at, verdict, snippet,
                          full_body, delivery_status, channels_used,
                          is_met_touched, met_name
                   FROM brief_history
                   WHERE user_id = %s
                   ORDER BY delivered_at DESC
                   LIMIT 30""",
                (user["id"],),
            )
            rows = cur.fetchall()

    history = [
        {
            "id": r["id"],
            "brief_type": r["brief_type"],
            "delivered_at": r["delivered_at"],
            "verdict": r["verdict"],
            "snippet": r["snippet"],
            "full_body": r["full_body"],
            "delivery_status": r["delivery_status"],
            "channels_used": r["channels_used"],
            "is_met_touched": r["is_met_touched"],
            "met_name": r["met_name"],
        }
        for r in rows
    ]
    return jsonify({"ok": True, "history": history})


# ════════════════════════════════════════════════════════════════════
# Subscriber portal — write endpoints (Phase 10 Chunk B1)
# ════════════════════════════════════════════════════════════════════
#
# PATCH brief preferences, plus CRUD for threshold alerts.
# Saved-location writes come in Chunk B2 (needs geocoding helper).

@app.patch("/api/v1/me/brief-preferences")
def me_brief_preferences_update():
    """Patch the current user's brief delivery preferences.

    Accepts a partial body — only the fields present in the request
    are updated. The rest stay as-is. Returns the full updated row.

    Validates time strings as HH:MM and channels as a list of allowed
    values ('sms', 'email', 'push'). Rejects unknown fields silently.

    Request body (all optional):
        {
          "morning_enabled": true,
          "morning_window_start": "05:30",
          "morning_window_end":   "07:00",
          "evening_enabled": false,
          "evening_window_start": "17:30",
          "evening_window_end":   "18:30",
          "quiet_start": "21:00",
          "quiet_end":   "05:00",
          "channels": ["sms", "email"]
        }

    Returns:
        200 {"ok": true, "preferences": {...}}  (full updated row)
        400 {"ok": false, "error": "invalid-..."}
        401 not authenticated
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}
    now_ms = int(time.time() * 1000)

    # Validate time strings as HH:MM (00-23 : 00-59)
    def _valid_time(s):
        if not isinstance(s, str): return False
        if len(s) != 5 or s[2] != ':': return False
        try:
            h, m = int(s[:2]), int(s[3:])
            return 0 <= h <= 23 and 0 <= m <= 59
        except (ValueError, TypeError):
            return False

    # Build dynamic SET clause from present fields
    set_clauses = []
    params = []

    if "morning_enabled" in data:
        set_clauses.append("morning_enabled = %s")
        params.append(bool(data["morning_enabled"]))

    if "morning_window_start" in data:
        if not _valid_time(data["morning_window_start"]):
            return jsonify({"ok": False, "error": "invalid-morning-start"}), 400
        set_clauses.append("morning_window_start = %s")
        params.append(data["morning_window_start"])

    if "morning_window_end" in data:
        if not _valid_time(data["morning_window_end"]):
            return jsonify({"ok": False, "error": "invalid-morning-end"}), 400
        set_clauses.append("morning_window_end = %s")
        params.append(data["morning_window_end"])

    if "evening_enabled" in data:
        set_clauses.append("evening_enabled = %s")
        params.append(bool(data["evening_enabled"]))

    if "evening_window_start" in data:
        v = data["evening_window_start"]
        if v is None or v == "":
            set_clauses.append("evening_window_start = NULL")
        elif _valid_time(v):
            set_clauses.append("evening_window_start = %s")
            params.append(v)
        else:
            return jsonify({"ok": False, "error": "invalid-evening-start"}), 400

    if "evening_window_end" in data:
        v = data["evening_window_end"]
        if v is None or v == "":
            set_clauses.append("evening_window_end = NULL")
        elif _valid_time(v):
            set_clauses.append("evening_window_end = %s")
            params.append(v)
        else:
            return jsonify({"ok": False, "error": "invalid-evening-end"}), 400

    if "quiet_start" in data:
        if not _valid_time(data["quiet_start"]):
            return jsonify({"ok": False, "error": "invalid-quiet-start"}), 400
        set_clauses.append("quiet_start = %s")
        params.append(data["quiet_start"])

    if "quiet_end" in data:
        if not _valid_time(data["quiet_end"]):
            return jsonify({"ok": False, "error": "invalid-quiet-end"}), 400
        set_clauses.append("quiet_end = %s")
        params.append(data["quiet_end"])

    if "channels" in data:
        ch = data["channels"]
        if not isinstance(ch, list):
            return jsonify({"ok": False, "error": "invalid-channels"}), 400
        ALLOWED = {"sms", "email", "push"}
        clean = [c for c in ch if isinstance(c, str) and c in ALLOWED]
        if not clean:
            return jsonify({"ok": False, "error": "no-valid-channels"}), 400
        set_clauses.append("channels = %s")
        params.append(",".join(clean))

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-fields-to-update"}), 400

    # Always bump updated_at
    set_clauses.append("updated_at = %s")
    params.append(now_ms)

    # Ensure row exists first (auto-create with defaults), then update
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO brief_preferences (user_id, updated_at)
                   VALUES (%s, %s)
                   ON CONFLICT (user_id) DO NOTHING""",
                (user["id"], now_ms),
            )
            params.append(user["id"])
            cur.execute(
                f"UPDATE brief_preferences SET {', '.join(set_clauses)} "
                f"WHERE user_id = %s",
                tuple(params),
            )
            cur.execute(
                """SELECT user_id, morning_enabled, morning_window_start,
                          morning_window_end, evening_enabled,
                          evening_window_start, evening_window_end,
                          quiet_start, quiet_end, channels, updated_at
                   FROM brief_preferences WHERE user_id = %s""",
                (user["id"],),
            )
            row = cur.fetchone()

    return jsonify({
        "ok": True,
        "preferences": {
            "morning_enabled":      row["morning_enabled"],
            "morning_window_start": row["morning_window_start"],
            "morning_window_end":   row["morning_window_end"],
            "evening_enabled":      row["evening_enabled"],
            "evening_window_start": row["evening_window_start"],
            "evening_window_end":   row["evening_window_end"],
            "quiet_start":          row["quiet_start"],
            "quiet_end":            row["quiet_end"],
            "channels":             [c for c in (row["channels"] or "").split(",") if c],
            "updated_at":           row["updated_at"],
        },
    })


@app.post("/api/v1/me/threshold-alerts")
def me_threshold_alerts_create():
    """Create a new threshold alert for the current user.

    Request body:
        {
          "metric": "wind" | "temp_low" | "temp_high" | "precip_chance" | "humidity",
          "comparator": "gt" | "lt" | "gte" | "lte" | "eq",
          "threshold_value": 25,
          "units": "mph" | "F" | "C" | "pct",
          "channels": ["sms", "email"],   (optional, defaults to ["sms","email"])
          "enabled": true                  (optional, defaults to true)
        }

    Returns:
        200 {"ok": true, "alert": {...}}
        400 invalid field
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}

    ALLOWED_METRICS = {"wind", "temp_low", "temp_high", "precip_chance", "humidity"}
    ALLOWED_COMPS = {"gt", "lt", "gte", "lte", "eq"}
    ALLOWED_UNITS = {"mph", "F", "C", "pct"}
    ALLOWED_CHANNELS = {"sms", "email", "push"}

    metric = (data.get("metric") or "").strip()
    if metric not in ALLOWED_METRICS:
        return jsonify({"ok": False, "error": "invalid-metric"}), 400

    comparator = (data.get("comparator") or "").strip()
    if comparator not in ALLOWED_COMPS:
        return jsonify({"ok": False, "error": "invalid-comparator"}), 400

    try:
        threshold_value = float(data.get("threshold_value"))
    except (ValueError, TypeError):
        return jsonify({"ok": False, "error": "invalid-threshold-value"}), 400

    units = (data.get("units") or "").strip()
    if units not in ALLOWED_UNITS:
        return jsonify({"ok": False, "error": "invalid-units"}), 400

    channels_raw = data.get("channels") or ["sms", "email"]
    if not isinstance(channels_raw, list):
        return jsonify({"ok": False, "error": "invalid-channels"}), 400
    channels = [c for c in channels_raw if isinstance(c, str) and c in ALLOWED_CHANNELS]
    if not channels:
        return jsonify({"ok": False, "error": "no-valid-channels"}), 400

    enabled = bool(data.get("enabled", True))
    now_ms = int(time.time() * 1000)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO threshold_alerts
                   (user_id, metric, comparator, threshold_value, units,
                    channels, enabled, created_at, updated_at)
                   VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                   RETURNING id, metric, comparator, threshold_value, units,
                             channels, enabled, created_at, updated_at""",
                (user["id"], metric, comparator, threshold_value, units,
                 ",".join(channels), enabled, now_ms, now_ms),
            )
            row = cur.fetchone()

    return jsonify({
        "ok": True,
        "alert": {
            "id": row["id"],
            "metric": row["metric"],
            "comparator": row["comparator"],
            "threshold_value": row["threshold_value"],
            "units": row["units"],
            "channels": [c for c in (row["channels"] or "").split(",") if c],
            "enabled": row["enabled"],
            "created_at": row["created_at"],
            "updated_at": row["updated_at"],
        },
    })


@app.route("/api/v1/me/threshold-alerts/<int:alert_id>", methods=["OPTIONS"])
def _me_threshold_alert_id_preflight(alert_id):
    return ("", 204)


@app.patch("/api/v1/me/threshold-alerts/<int:alert_id>")
def me_threshold_alerts_update(alert_id):
    """Update an existing threshold alert.

    Same field validation as create. All fields optional (partial update).
    Only the alert's owner can update it.

    Returns:
        200 {"ok": true, "alert": {...}}
        404 alert not found or not owned by current user
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}

    ALLOWED_METRICS = {"wind", "temp_low", "temp_high", "precip_chance", "humidity"}
    ALLOWED_COMPS = {"gt", "lt", "gte", "lte", "eq"}
    ALLOWED_UNITS = {"mph", "F", "C", "pct"}
    ALLOWED_CHANNELS = {"sms", "email", "push"}

    set_clauses = []
    params = []

    if "metric" in data:
        if data["metric"] not in ALLOWED_METRICS:
            return jsonify({"ok": False, "error": "invalid-metric"}), 400
        set_clauses.append("metric = %s")
        params.append(data["metric"])

    if "comparator" in data:
        if data["comparator"] not in ALLOWED_COMPS:
            return jsonify({"ok": False, "error": "invalid-comparator"}), 400
        set_clauses.append("comparator = %s")
        params.append(data["comparator"])

    if "threshold_value" in data:
        try:
            v = float(data["threshold_value"])
            set_clauses.append("threshold_value = %s")
            params.append(v)
        except (ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-threshold-value"}), 400

    if "units" in data:
        if data["units"] not in ALLOWED_UNITS:
            return jsonify({"ok": False, "error": "invalid-units"}), 400
        set_clauses.append("units = %s")
        params.append(data["units"])

    if "channels" in data:
        ch = data["channels"]
        if not isinstance(ch, list):
            return jsonify({"ok": False, "error": "invalid-channels"}), 400
        clean = [c for c in ch if isinstance(c, str) and c in ALLOWED_CHANNELS]
        if not clean:
            return jsonify({"ok": False, "error": "no-valid-channels"}), 400
        set_clauses.append("channels = %s")
        params.append(",".join(clean))

    if "enabled" in data:
        set_clauses.append("enabled = %s")
        params.append(bool(data["enabled"]))

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-fields-to-update"}), 400

    set_clauses.append("updated_at = %s")
    now_ms = int(time.time() * 1000)
    params.append(now_ms)

    with db() as conn:
        with conn.cursor() as cur:
            # Verify ownership first
            cur.execute(
                "SELECT user_id FROM threshold_alerts WHERE id = %s",
                (alert_id,),
            )
            existing = cur.fetchone()
            if existing is None or existing["user_id"] != user["id"]:
                return jsonify({"ok": False, "error": "not-found"}), 404

            params.extend([alert_id, user["id"]])
            cur.execute(
                f"UPDATE threshold_alerts SET {', '.join(set_clauses)} "
                f"WHERE id = %s AND user_id = %s",
                tuple(params),
            )
            cur.execute(
                """SELECT id, metric, comparator, threshold_value, units,
                          channels, enabled, created_at, updated_at
                   FROM threshold_alerts WHERE id = %s""",
                (alert_id,),
            )
            row = cur.fetchone()

    return jsonify({
        "ok": True,
        "alert": {
            "id": row["id"],
            "metric": row["metric"],
            "comparator": row["comparator"],
            "threshold_value": row["threshold_value"],
            "units": row["units"],
            "channels": [c for c in (row["channels"] or "").split(",") if c],
            "enabled": row["enabled"],
            "created_at": row["created_at"],
            "updated_at": row["updated_at"],
        },
    })


@app.delete("/api/v1/me/threshold-alerts/<int:alert_id>")
def me_threshold_alerts_delete(alert_id):
    """Delete a threshold alert. Only the owner can delete.

    Returns:
        200 {"ok": true}
        404 not found or not owned
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT user_id FROM threshold_alerts WHERE id = %s",
                (alert_id,),
            )
            row = cur.fetchone()
            if row is None or row["user_id"] != user["id"]:
                return jsonify({"ok": False, "error": "not-found"}), 404

            cur.execute(
                "DELETE FROM threshold_alerts WHERE id = %s AND user_id = %s",
                (alert_id, user["id"]),
            )

    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Saved locations — write endpoints (Phase 10 Chunk B2)
# ════════════════════════════════════════════════════════════════════
#
# CRUD for the subscriber's saved location(s) + a geocoding helper that
# turns a free-form address string into lat/lng using Open-Meteo's free
# geocoding API. The helper is also exposed as its own endpoint so the
# frontend's "Look up" button can show the resolved location before the
# user commits to saving it.

def _geocode_address(query: str) -> Optional[dict]:
    """Look up a free-form address string using Open-Meteo's geocoding API.

    No API key required, no rate-limit signup. Returns the first result
    or None if no match. Result shape:
        {
          "lat": float,
          "lng": float,
          "name": "Lebanon",
          "admin1": "Indiana",       # state
          "admin2": "Boone County",   # county
          "country": "United States"
        }

    Network failures return None silently — caller treats it as "no match"
    and asks the user to drop a pin manually.
    """
    if not query or not isinstance(query, str):
        return None
    q = query.strip()
    if not q:
        return None

    try:
        # URL-encode the query
        from urllib.parse import quote
        url = (
            "https://geocoding-api.open-meteo.com/v1/search"
            f"?name={quote(q)}&count=1&language=en&format=json"
        )
        req = urllib.request.Request(url, headers={"User-Agent": "weathervalet/1.0"})
        with urllib.request.urlopen(req, timeout=4) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except (urllib.error.URLError, ValueError, TimeoutError) as e:
        print(f"[GEOCODE] failed for '{q[:80]}': {e}", flush=True)
        return None
    except Exception as e:
        print(f"[GEOCODE] unexpected error for '{q[:80]}': {e}", flush=True)
        return None

    results = (data or {}).get("results") or []
    if not results:
        return None

    r = results[0]
    return {
        "lat": float(r.get("latitude")),
        "lng": float(r.get("longitude")),
        "name": r.get("name") or q,
        "admin1": r.get("admin1") or "",   # state
        "admin2": r.get("admin2") or "",   # county
        "country": r.get("country") or "",
    }


@app.route("/api/v1/geocode", methods=["OPTIONS"])
def _geocode_preflight():
    return ("", 204)


@app.get("/api/v1/geocode")
def geocode_lookup():
    """Geocode a free-form address string.

    Query params:
        q  — the address string ("Lebanon, IN" or "1600 Pennsylvania Ave")

    Returns:
        200 {"ok": true, "result": {...}}   match found
        200 {"ok": true, "result": null}    no match (treat as user error)
        400 missing q
        401 not authenticated (we keep this auth-only to avoid being a
            free geocoder for the internet)
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    q = (request.args.get("q") or "").strip()
    if not q:
        return jsonify({"ok": False, "error": "missing-query"}), 400

    result = _geocode_address(q)
    return jsonify({"ok": True, "result": result})


@app.post("/api/v1/me/saved-locations")
def me_saved_locations_create():
    """Create a new saved location for the current user.

    Two input shapes are accepted:
      A) {"address_text": "Lebanon, IN", "label": "Home"}
         — backend geocodes to get lat/lng
      B) {"address_text": "Lebanon, IN", "label": "Home",
          "lat": 40.0481, "lng": -86.4694, "county": "Boone County"}
         — frontend already has coords (e.g. after pin-drop), backend trusts them

    `is_primary` defaults to TRUE if this is the user's first location.
    If `is_primary` is explicitly TRUE and another location exists, the
    other one is automatically unset (exactly-one-primary invariant).

    Returns:
        200 {"ok": true, "location": {...}}
        400 invalid input or geocoding failure
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}

    label = (data.get("label") or "").strip()
    if not label:
        # Auto-generate a label from address_text if not supplied
        label = (data.get("address_text") or "Saved location").strip()[:80]
    if len(label) > 120:
        label = label[:120]

    address_text = (data.get("address_text") or "").strip() or None

    # If lat/lng provided, trust them. Otherwise geocode.
    lat = data.get("lat")
    lng = data.get("lng")
    county = (data.get("county") or "").strip() or None

    if lat is None or lng is None:
        # Need to geocode from address_text
        if not address_text:
            return jsonify({"ok": False, "error": "no-location-data"}), 400
        geo = _geocode_address(address_text)
        if not geo:
            return jsonify({"ok": False, "error": "geocoding-failed"}), 400
        lat = geo["lat"]
        lng = geo["lng"]
        if not county:
            county = geo.get("admin2") or None
    else:
        try:
            lat = float(lat)
            lng = float(lng)
        except (ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-coords"}), 400
        # Sanity check — somewhere on Earth
        if not (-90 <= lat <= 90 and -180 <= lng <= 180):
            return jsonify({"ok": False, "error": "invalid-coords"}), 400

    now_ms = int(time.time() * 1000)
    requested_primary = bool(data.get("is_primary", False))

    with db() as conn:
        with conn.cursor() as cur:
            # If user has no existing locations, force is_primary=TRUE
            cur.execute(
                "SELECT COUNT(*) AS n FROM saved_locations WHERE user_id = %s",
                (user["id"],),
            )
            row = cur.fetchone()
            existing_count = row["n"] if row else 0
            is_primary = requested_primary or (existing_count == 0)

            # If setting primary, unset any existing primary first
            if is_primary and existing_count > 0:
                cur.execute(
                    "UPDATE saved_locations SET is_primary = FALSE, updated_at = %s "
                    "WHERE user_id = %s AND is_primary = TRUE",
                    (now_ms, user["id"]),
                )

            cur.execute(
                """INSERT INTO saved_locations
                   (user_id, label, address_text, lat, lng, county, is_primary,
                    created_at, updated_at)
                   VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                   RETURNING id, label, address_text, lat, lng, county,
                             is_primary, created_at, updated_at""",
                (user["id"], label, address_text, lat, lng, county, is_primary,
                 now_ms, now_ms),
            )
            new_row = cur.fetchone()

            # Phase 10 timezone foundation: if this is becoming the
            # user's primary location, update their timezone too.
            # Brief scheduler uses this to deliver at 7 AM subscriber-
            # local instead of 7 AM UTC.
            if is_primary:
                detected_tz = _timezone_for_latlng(lat, lng)
                cur.execute(
                    "UPDATE users SET timezone = %s WHERE id = %s",
                    (detected_tz, user["id"]),
                )

    return jsonify({
        "ok": True,
        "location": {
            "id": new_row["id"],
            "label": new_row["label"],
            "address_text": new_row["address_text"],
            "lat": new_row["lat"],
            "lng": new_row["lng"],
            "county": new_row["county"],
            "is_primary": new_row["is_primary"],
            "created_at": new_row["created_at"],
            "updated_at": new_row["updated_at"],
        },
    })


@app.route("/api/v1/me/saved-locations/<int:loc_id>", methods=["OPTIONS"])
def _me_saved_location_id_preflight(loc_id):
    return ("", 204)


@app.patch("/api/v1/me/saved-locations/<int:loc_id>")
def me_saved_locations_update(loc_id):
    """Update an existing saved location. Owner-only.

    Same field-validation rules as create. Re-geocoding is NOT automatic —
    if the address_text changes but no new lat/lng is supplied, we keep
    the existing lat/lng (user must do a fresh geocode + pin-drop to move).

    Setting is_primary=true unsets any other primary location for this user.

    Returns:
        200 {"ok": true, "location": {...}}
        404 not found or not owned
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}
    now_ms = int(time.time() * 1000)

    set_clauses = []
    params = []

    if "label" in data:
        label = (data["label"] or "").strip()
        if not label or len(label) > 120:
            return jsonify({"ok": False, "error": "invalid-label"}), 400
        set_clauses.append("label = %s")
        params.append(label)

    if "address_text" in data:
        addr = (data["address_text"] or "").strip()
        set_clauses.append("address_text = %s")
        params.append(addr or None)

    if "lat" in data or "lng" in data:
        # If either coord is in the body, both must be present and valid
        try:
            lat = float(data["lat"])
            lng = float(data["lng"])
        except (KeyError, ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-coords"}), 400
        if not (-90 <= lat <= 90 and -180 <= lng <= 180):
            return jsonify({"ok": False, "error": "invalid-coords"}), 400
        set_clauses.append("lat = %s")
        params.append(lat)
        set_clauses.append("lng = %s")
        params.append(lng)

    if "county" in data:
        set_clauses.append("county = %s")
        params.append((data["county"] or "").strip() or None)

    requested_primary = data.get("is_primary")
    if requested_primary is not None:
        set_clauses.append("is_primary = %s")
        params.append(bool(requested_primary))

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-fields-to-update"}), 400

    set_clauses.append("updated_at = %s")
    params.append(now_ms)

    with db() as conn:
        with conn.cursor() as cur:
            # Verify ownership
            cur.execute(
                "SELECT user_id FROM saved_locations WHERE id = %s",
                (loc_id,),
            )
            existing = cur.fetchone()
            if existing is None or existing["user_id"] != user["id"]:
                return jsonify({"ok": False, "error": "not-found"}), 404

            # If toggling this location to primary, unset others first
            if requested_primary is True:
                cur.execute(
                    "UPDATE saved_locations SET is_primary = FALSE, updated_at = %s "
                    "WHERE user_id = %s AND is_primary = TRUE AND id != %s",
                    (now_ms, user["id"], loc_id),
                )

            params.extend([loc_id, user["id"]])
            cur.execute(
                f"UPDATE saved_locations SET {', '.join(set_clauses)} "
                f"WHERE id = %s AND user_id = %s",
                tuple(params),
            )
            cur.execute(
                """SELECT id, label, address_text, lat, lng, county, is_primary,
                          created_at, updated_at
                   FROM saved_locations WHERE id = %s""",
                (loc_id,),
            )
            row = cur.fetchone()

    return jsonify({
        "ok": True,
        "location": {
            "id": row["id"],
            "label": row["label"],
            "address_text": row["address_text"],
            "lat": row["lat"],
            "lng": row["lng"],
            "county": row["county"],
            "is_primary": row["is_primary"],
            "created_at": row["created_at"],
            "updated_at": row["updated_at"],
        },
    })


@app.delete("/api/v1/me/saved-locations/<int:loc_id>")
def me_saved_locations_delete(loc_id):
    """Delete a saved location. Owner-only.

    If the deleted location was primary AND another location exists,
    the most recently created location is promoted to primary so the
    invariant (subscriber always has a primary location when they have
    any locations) holds.

    Returns:
        200 {"ok": true}
        404 not found or not owned
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    now_ms = int(time.time() * 1000)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT user_id, is_primary FROM saved_locations WHERE id = %s",
                (loc_id,),
            )
            row = cur.fetchone()
            if row is None or row["user_id"] != user["id"]:
                return jsonify({"ok": False, "error": "not-found"}), 404

            was_primary = row["is_primary"]

            cur.execute(
                "DELETE FROM saved_locations WHERE id = %s AND user_id = %s",
                (loc_id, user["id"]),
            )

            # If we removed the primary, promote the newest remaining location
            if was_primary:
                cur.execute(
                    """SELECT id FROM saved_locations
                       WHERE user_id = %s
                       ORDER BY created_at DESC LIMIT 1""",
                    (user["id"],),
                )
                successor = cur.fetchone()
                if successor:
                    cur.execute(
                        "UPDATE saved_locations SET is_primary = TRUE, updated_at = %s "
                        "WHERE id = %s",
                        (now_ms, successor["id"]),
                    )

    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Subscription signup via Stripe Checkout (Phase 10 Chunk C2)
# ════════════════════════════════════════════════════════════════════
#
# Creates a Stripe Checkout Session in 'subscription' mode for the chosen
# tier. Returns the checkout URL; the frontend redirects to it.
#
# On successful checkout, Stripe fires checkout.session.completed →
# the existing webhook (see stripe_webhook_v1) handles user creation,
# subscriber role grant, tier capture, and welcome magic link.
#
# Anonymous checkout is supported (option B from the May 14 plan):
# the user need NOT be signed in. Stripe collects their email at
# checkout; the webhook finds-or-creates the user from that email.
# For signed-in users, we pre-fill the email so the existing user gets
# their subscription linked correctly.

@app.route("/api/v1/subscribe", methods=["OPTIONS"])
def _subscribe_preflight():
    return ("", 204)


@app.post("/api/v1/subscribe")
def subscribe_create_checkout():
    """Create a Stripe Checkout Session for a subscription tier.

    Request body:
        {
          "tier": "hobbyist" | "pro_single" | "pro_multi",
          "starter": true,            // optional — apply STARTER99 coupon
          "rep": "brian"              // optional — sales rep attribution
        }

    Returns:
        200 {"ok": true, "url": "https://checkout.stripe.com/c/pay/..."}
        400 invalid tier
        503 Stripe not configured
    """
    if stripe is None or not STRIPE_SECRET_KEY:
        return jsonify({"ok": False, "error": "stripe-not-configured"}), 503

    data = request.get_json(silent=True) or {}
    tier_key = (data.get("tier") or "").strip()
    if tier_key not in TIER_PRICE_MAP:
        return jsonify({"ok": False, "error": "invalid-tier"}), 400

    price_id = TIER_PRICE_MAP[tier_key]

    # Starter Month — only applies to pro_single
    use_starter = bool(data.get("starter")) and tier_key == "pro_single"

    # Sales rep attribution — slug only, must be alphanumeric+underscore
    rep_slug_raw = (data.get("rep") or "").strip().lower()
    rep_slug = "".join(c for c in rep_slug_raw if c.isalnum() or c == "_")[:40]
    if not rep_slug:
        rep_slug = None

    # If the requester is signed in, pre-fill their email and link to
    # their existing Stripe customer if one exists. If they're cold
    # (anonymous on pricing page), Stripe collects the email at checkout.
    customer_email = None
    existing_stripe_customer = None
    user = _get_current_user()
    if user:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    "SELECT email, stripe_customer_id FROM users WHERE id = %s",
                    (user["id"],),
                )
                row = cur.fetchone()
        if row:
            customer_email = row.get("email")
            existing_stripe_customer = row.get("stripe_customer_id")

    # Build the success/cancel URLs. We send them back to the home page
    # with a query flag so the frontend knows to celebrate or apologize.
    success_url = f"{FRONTEND_BASE_URL}/?subscribed=1&tier={tier_key}&session={{CHECKOUT_SESSION_ID}}"
    if use_starter:
        success_url += "&starter=1"
    cancel_url = f"{FRONTEND_BASE_URL}/?subscribe_cancelled=1&tier={tier_key}"

    # Build the Checkout Session params. If we have an existing Stripe
    # customer (this user previously subscribed and cancelled, for
    # example), pass `customer=` instead of `customer_email=` so the new
    # subscription is linked to the same customer record.
    metadata = {"wv_tier": tier_key}
    if use_starter:
        metadata["wv_starter"] = "1"
    if rep_slug:
        metadata["wv_rep"] = rep_slug

    session_params = {
        "mode": "subscription",
        "payment_method_types": ["card"],
        "line_items": [{"price": price_id, "quantity": 1}],
        "metadata": metadata,
        # Also attach the tier to the subscription itself, so we can
        # read it back later via subscription metadata if needed.
        "subscription_data": {
            "metadata": metadata.copy(),
        },
        "success_url": success_url,
        "cancel_url": cancel_url,
        "allow_promotion_codes": True,
        # Phase 10 Item #3: collect phone number at checkout so daily
        # briefs and threshold alerts can be sent by SMS without an
        # extra portal step. Stripe surfaces this as an optional field.
        "phone_number_collection": {"enabled": True},
    }
    # Apply STARTER99 coupon for Starter Month signups.
    # Stripe duration:'once' handles the auto-rollover to full price.
    if use_starter:
        session_params["discounts"] = [{"coupon": STARTER_COUPON_ID}]
        # allow_promotion_codes can't coexist with discounts on Stripe Checkout
        session_params.pop("allow_promotion_codes", None)

    if existing_stripe_customer:
        session_params["customer"] = existing_stripe_customer
    elif customer_email:
        session_params["customer_email"] = customer_email
    # else: Stripe collects email at checkout (anonymous flow)

    try:
        session = stripe.checkout.Session.create(**session_params)
    except Exception as e:
        print(f"[subscribe] checkout session create failed: {e}", flush=True)
        return jsonify({
            "ok": False,
            "error": "stripe-error",
            "message": "Couldn't start checkout. Please try again.",
        }), 500

    return jsonify({"ok": True, "url": session.url})


# ════════════════════════════════════════════════════════════════════
# Stripe Customer Portal session (Phase 10 Chunk C1)
# ════════════════════════════════════════════════════════════════════
#
# Creates a Stripe billing portal session for the current user and
# returns the URL the frontend should redirect to. Stripe hosts the
# portal UI — they handle plan changes, cancellation, payment method
# updates, and invoice history. On exit, the user is redirected back
# to our subscriber portal.
#
# Pre-requisites for this to work in production:
#   1. STRIPE_SECRET_KEY set in env (already configured)
#   2. The user must have a stripe_customer_id (set when they signed
#      up via checkout — populated by the existing webhook handler)
#   3. The Stripe Customer Portal must be CONFIGURED in the Stripe
#      Dashboard → Settings → Billing → Customer portal. Enable the
#      features you want customers to self-serve (cancel, change plan,
#      update payment method). Both Test Mode and Live Mode have
#      separate configs — set up both.

@app.route("/api/v1/me/stripe-portal-session", methods=["OPTIONS"])
def _me_stripe_portal_preflight():
    return ("", 204)


@app.post("/api/v1/me/stripe-portal-session")
def me_stripe_portal_session():
    """Create a Stripe billing portal session for the current user.

    Returns:
        200 {"ok": true, "url": "https://billing.stripe.com/p/session/..."}
        400 {"ok": false, "error": "no-stripe-customer"}  user has no Stripe
            customer record (likely a free user or pre-Stripe-launch user)
        401 not authenticated
        500 Stripe API error
        503 Stripe not configured on server
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    if stripe is None or not STRIPE_SECRET_KEY:
        return jsonify({"ok": False, "error": "stripe-not-configured"}), 503

    # Pull the user's stripe_customer_id from the DB. Phase 2 populated
    # this field via webhook when the user first paid; if it's NULL,
    # they have no Stripe customer record and can't open a portal.
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT stripe_customer_id FROM users WHERE id = %s",
                (user["id"],),
            )
            row = cur.fetchone()

    stripe_customer_id = row.get("stripe_customer_id") if row else None
    if not stripe_customer_id:
        return jsonify({
            "ok": False,
            "error": "no-stripe-customer",
            "message": "No active subscription found. Subscribe to a plan to access billing settings.",
        }), 400

    # Return-URL: where Stripe sends them after they're done. We send
    # them back to the subscriber portal so they pick up right where
    # they left off.
    return_url = f"{FRONTEND_BASE_URL}/?portal=back"

    try:
        session = stripe.billing_portal.Session.create(
            customer=stripe_customer_id,
            return_url=return_url,
        )
    except Exception as e:
        # Stripe SDK throws stripe.error.* exceptions; we catch broadly
        # to avoid leaking implementation details to the client.
        print(f"[stripe-portal] session create failed for user={user['id']}: {e}", flush=True)
        return jsonify({
            "ok": False,
            "error": "stripe-error",
            "message": "Couldn't open billing portal. Please try again or contact support.",
        }), 500

    return jsonify({"ok": True, "url": session.url})


# ════════════════════════════════════════════════════════════════════
# Met queue — pending verification_requests for Met workspace (Item #2)
# ════════════════════════════════════════════════════════════════════
#
# The Met workspace's Review Queue tab is currently rendered from a
# hardcoded MET_QUEUE_MOCK array. To make it real, the frontend calls
# this endpoint on workspace entry; if there ARE real paid requests,
# they take priority. Mock rows can still be shown alongside (or below)
# for demo continuity, controlled by the frontend.
#
# Auth: requires the 'met' role. Subscribers and crew can't see the
# queue.

@app.route("/api/v1/met/queue", methods=["OPTIONS"])
def _met_queue_preflight():
    return ("", 204)


@app.get("/api/v1/met/queue")
def met_queue_list():
    """List paid-but-unclaimed verification requests for the Met queue.

    Returns rows in 'paid' status (paid for, waiting for a Met to pick
    them up) plus rows in 'claimed' status that the current Met has
    claimed but not yet submitted. Other Mets' claimed rows are hidden.

    Returns:
        200 {"ok": true, "requests": [...]}
        401 not authenticated
        403 not a Met
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            # 'paid' rows are unclaimed; show all. 'claimed' rows belong
            # to a specific Met (claimed_at, but we don't yet track WHICH
            # Met claimed it — for now show all claimed rows so a Met can
            # pick back up after switching devices). When we add a
            # claimed_by_user_id column we can filter properly.
            cur.execute(
                """SELECT id, created_at, updated_at, status, tier, price_cents,
                          customer_email, customer_phone, plan_text, plan_industry,
                          plan_location, plan_window, ai_brief_markdown, ai_status_key,
                          claim_token, claimed_at
                   FROM verification_requests
                   WHERE status IN ('paid', 'claimed')
                   ORDER BY
                     CASE WHEN status = 'paid' THEN 0 ELSE 1 END,
                     created_at ASC
                   LIMIT 50""",
            )
            rows = cur.fetchall()

    now = now_ts()
    requests_out = [
        {
            "id": r["id"],
            "tier": r["tier"],
            "tier_label": _format_tier_label(r["tier"]),
            "status": r["status"],
            "price_cents": r["price_cents"],
            "customer_email": r["customer_email"],
            "customer_phone": r["customer_phone"],
            "plan_text": r["plan_text"],
            "plan_industry": r["plan_industry"],
            "plan_location": r["plan_location"],
            "plan_window": r["plan_window"],
            "ai_brief_markdown": r["ai_brief_markdown"],
            "ai_status_key": r["ai_status_key"],
            "claim_token": r["claim_token"],
            "claimed_at": r["claimed_at"],
            "created_at": r["created_at"],
            "paid_minutes_ago": max(0, (now - r["created_at"]) // 60),
        }
        for r in rows
    ]
    return jsonify({"ok": True, "requests": requests_out})


def _format_tier_label(tier_key: str) -> str:
    """Convert a verification tier key to a user-facing label."""
    return {
        "single": "Single",
        "day_pass": "Day Pass",
        "pro_monthly": "Pro",
    }.get(tier_key, tier_key.title())


# ════════════════════════════════════════════════════════════════════
# Admin audit log (Phase 10 Admin Tools)
# ════════════════════════════════════════════════════════════════════

def _audit_log(actor_user_id: Optional[int], actor_name: Optional[str],
               action: str, target_type: Optional[str] = None,
               target_id: Optional[int] = None,
               details: Optional[dict] = None) -> None:
    """Write a row to admin_audit_log. Best-effort — failures are logged
    but never raised, since auditing must not block the real action.

    Pass `details` as a dict; we serialize it to JSON. Keep payloads
    small (under a few KB) — this isn't event storage, it's a
    "what changed" trail.
    """
    try:
        details_json = json.dumps(details) if details is not None else None
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO admin_audit_log
                       (actor_user_id, actor_name, action,
                        target_type, target_id, details_json, created_at)
                       VALUES (%s, %s, %s, %s, %s, %s, %s)""",
                    (actor_user_id, actor_name, action,
                     target_type, target_id, details_json,
                     int(time.time() * 1000)),
                )
    except Exception as e:
        print(f"[audit] log write failed action={action}: {e!r}", flush=True)


def _require_admin():
    """Helper: returns (user, error_response). If error_response is not
    None, the caller should return it immediately. Otherwise `user` is
    the authenticated admin user dict.

    Used as a one-liner gate in admin endpoints:
        user, err = _require_admin()
        if err: return err
    """
    user = _get_current_user()
    if user is None:
        return (None, (jsonify({"ok": False, "error": "not-authenticated"}), 401))
    roles = user.get("roles") or []
    if "admin" not in roles:
        return (None, (jsonify({"ok": False, "error": "forbidden"}), 403))
    return (user, None)


# ════════════════════════════════════════════════════════════════════
# User profile updates (Phase 10 Item #3 — supporting infra)
# ════════════════════════════════════════════════════════════════════
#
# Lets a signed-in user update their own name + phone. Used by the
# subscriber portal so users who didn't supply phone at Stripe checkout
# can still enable SMS delivery for their daily brief.

@app.route("/api/v1/me/profile", methods=["OPTIONS"])
def _me_profile_preflight():
    return ("", 204)


@app.get("/api/v1/me/profile")
def me_profile_get():
    """Return the current user's basic profile (name, email, phone).

    Also returns Met-specific onboarding state: `met_onboarded_at` is
    null until the Met dismisses the workspace welcome card.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id, email, name, phone, met_onboarded_at FROM users WHERE id = %s",
                (user["id"],),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "user-not-found"}), 404
    return jsonify({
        "ok": True,
        "profile": {
            "email": row["email"],
            "name": row.get("name") or "",
            "phone": row.get("phone") or "",
            "met_onboarded_at": row.get("met_onboarded_at"),
        },
    })


@app.patch("/api/v1/me/profile")
def me_profile_update():
    """Update the current user's name and/or phone.

    Accepts:
      {
        "name": "Jane Smith",     (optional)
        "phone": "+15551234567"   (optional, must be E.164 if present)
      }

    Phone is normalized lightly — leading whitespace stripped and
    bare 10-digit US numbers ("3175551234") get a "+1" prefix. Anything
    else is rejected (we'd rather refuse than silently send to the
    wrong number).
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}
    set_clauses = []
    params = []

    if "name" in data:
        name = (data["name"] or "").strip()
        if len(name) > 200:
            return jsonify({"ok": False, "error": "name-too-long"}), 400
        set_clauses.append("name = %s")
        params.append(name or None)

    if "phone" in data:
        phone_raw = (data["phone"] or "").strip()
        if phone_raw == "":
            # Empty string = clear the phone
            set_clauses.append("phone = NULL")
        else:
            # Try to normalize. We accept:
            #   "+15551234567" — already E.164
            #   "5551234567"   — bare US 10-digit, prepend "+1"
            #   "(555) 123-4567" or "555-123-4567" — strip and prepend "+1"
            digits_only = "".join(c for c in phone_raw if c.isdigit())
            if phone_raw.startswith("+") and 8 <= len(digits_only) <= 15:
                phone_norm = "+" + digits_only
            elif len(digits_only) == 10:
                phone_norm = "+1" + digits_only
            elif len(digits_only) == 11 and digits_only.startswith("1"):
                phone_norm = "+" + digits_only
            else:
                return jsonify({"ok": False, "error": "invalid-phone"}), 400
            set_clauses.append("phone = %s")
            params.append(phone_norm)

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-fields-to-update"}), 400

    params.append(user["id"])
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                f"UPDATE users SET {', '.join(set_clauses)} WHERE id = %s",
                tuple(params),
            )
            cur.execute(
                "SELECT email, name, phone FROM users WHERE id = %s",
                (user["id"],),
            )
            row = cur.fetchone()

    return jsonify({
        "ok": True,
        "profile": {
            "email": row["email"],
            "name": row.get("name") or "",
            "phone": row.get("phone") or "",
        },
    })


@app.route("/api/v1/me/met-onboarding-dismiss", methods=["OPTIONS"])
def _me_met_onboarding_dismiss_preflight():
    return ("", 204)


@app.post("/api/v1/me/met-onboarding-dismiss")
def me_met_onboarding_dismiss():
    """Met dismissed the workspace welcome card. Stamps met_onboarded_at
    so the card never shows again for this user. Idempotent — calling
    twice has no extra effect.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE users
                   SET met_onboarded_at = COALESCE(met_onboarded_at, %s)
                   WHERE id = %s""",
                (now_ms, user["id"]),
            )
    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Crew location (Phase 10 Item #6)
# ════════════════════════════════════════════════════════════════════
#
# Crew members have a "home base" location used to target mission SMS
# by polygon. Set at Crew registration or via the Crew Profile screen.
# Requires the crew role to read/write.

@app.route("/api/v1/me/crew-location", methods=["OPTIONS"])
def _me_crew_location_preflight():
    return ("", 204)


@app.get("/api/v1/me/crew-location")
def me_crew_location_get():
    """Return the current user's Crew home base (lat/lng/label) and
    active toggle. Returns 403 if user isn't a Crew member."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "crew" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT crew_home_lat, crew_home_lng, crew_home_label,
                          crew_active
                   FROM users WHERE id = %s""",
                (user["id"],),
            )
            row = cur.fetchone()

    return jsonify({
        "ok": True,
        "crew_location": {
            "lat": row.get("crew_home_lat"),
            "lng": row.get("crew_home_lng"),
            "label": row.get("crew_home_label") or "",
            "active": row.get("crew_active") if row.get("crew_active") is not None else True,
        }
    })


@app.patch("/api/v1/me/crew-location")
def me_crew_location_update():
    """Update the current user's Crew home base.

    Accepts:
      {
        "lat": 40.0481,        (optional)
        "lng": -86.4694,       (optional, but if lat present must also be)
        "label": "Lebanon, IN" (optional human label)
        "active": true         (optional toggle)
      }

    Returns:
        200 {"ok": true, "crew_location": {...}}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "crew" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    set_clauses = []
    params = []

    if "lat" in data or "lng" in data:
        try:
            lat = float(data["lat"])
            lng = float(data["lng"])
        except (KeyError, ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-coords"}), 400
        if not (-90 <= lat <= 90 and -180 <= lng <= 180):
            return jsonify({"ok": False, "error": "invalid-coords"}), 400
        set_clauses.append("crew_home_lat = %s")
        params.append(lat)
        set_clauses.append("crew_home_lng = %s")
        params.append(lng)

    if "label" in data:
        label = (data["label"] or "").strip()
        if len(label) > 200:
            return jsonify({"ok": False, "error": "label-too-long"}), 400
        set_clauses.append("crew_home_label = %s")
        params.append(label or None)

    if "active" in data:
        set_clauses.append("crew_active = %s")
        params.append(bool(data["active"]))

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-fields-to-update"}), 400

    params.append(user["id"])
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                f"UPDATE users SET {', '.join(set_clauses)} WHERE id = %s",
                tuple(params),
            )
            cur.execute(
                """SELECT crew_home_lat, crew_home_lng, crew_home_label, crew_active
                   FROM users WHERE id = %s""",
                (user["id"],),
            )
            row = cur.fetchone()

    return jsonify({
        "ok": True,
        "crew_location": {
            "lat": row.get("crew_home_lat"),
            "lng": row.get("crew_home_lng"),
            "label": row.get("crew_home_label") or "",
            "active": row.get("crew_active") if row.get("crew_active") is not None else True,
        }
    })


# ════════════════════════════════════════════════════════════════════
# Severe weather status for current user (Storm Shelter auto-trigger)
# ════════════════════════════════════════════════════════════════════
#
# Returns the most severe NWS alert tier currently active for the user's
# primary saved location. Frontend polls this every 60 seconds when
# signed in; if the response flips to 'warning' or 'watch', the Storm
# Shelter UI auto-activates.
#
# Returns 200 even when there's no alert (status='clear') so the
# frontend can rely on the response shape. Anonymous users (no signed-in
# session, no saved location) get 'no-location' — frontend treats that
# as "don't auto-trigger; manual only".

@app.route("/api/v1/me/severe-weather-status", methods=["OPTIONS"])
def _me_severe_weather_preflight():
    return ("", 204)


# In-memory cache for NWS active alerts: avoid hammering api.weather.gov
# 60-second-per-user (could be N polls × M users). One fetch per 60s
# serves all callers. Cached for 60s.
_NWS_ALERTS_CACHE = {"data": None, "fetched_at": 0}
_NWS_ALERTS_CACHE_LOCK = threading.Lock()


def _get_cached_nws_alerts() -> list:
    """Return the latest active NWS alerts list, fetching at most once
    per 60 seconds across all callers."""
    with _NWS_ALERTS_CACHE_LOCK:
        now = time.time()
        if _NWS_ALERTS_CACHE["data"] is not None and \
           (now - _NWS_ALERTS_CACHE["fetched_at"]) < 60:
            return _NWS_ALERTS_CACHE["data"]
    # Fetch outside the lock so concurrent callers don't all serialize
    fresh = _fetch_active_nws_alerts()
    with _NWS_ALERTS_CACHE_LOCK:
        _NWS_ALERTS_CACHE["data"] = fresh
        _NWS_ALERTS_CACHE["fetched_at"] = time.time()
    return fresh


def _alert_tier_rank(event: str) -> int:
    """Higher number = more severe. Used to pick the worst active alert.
    Tornado Warning beats Severe Thunderstorm Warning beats Flash Flood
    Warning beats their respective Watches."""
    event_lower = (event or "").lower()
    if "tornado warning" in event_lower: return 100
    if "tornado watch" in event_lower: return 60
    if "severe thunderstorm warning" in event_lower: return 80
    if "severe thunderstorm watch" in event_lower: return 55
    if "flash flood warning" in event_lower: return 75
    if "flood warning" in event_lower: return 70
    return 10  # any other alert we somehow got


def _event_to_shelter_tier(event: str) -> str:
    """Map NWS event name → Storm Shelter tier key."""
    event_lower = (event or "").lower()
    if "warning" in event_lower:
        return "warning"
    if "watch" in event_lower:
        return "watch"
    return "clear"


@app.get("/api/v1/me/severe-weather-status")
def me_severe_weather_status():
    """Get current severe-weather tier for the signed-in user's primary location.

    Returns:
        {"ok": true, "status": "warning"|"watch"|"clear"|"no-location",
         "event": "Tornado Warning",  (when active)
         "headline": "...",
         "area_desc": "...",
         "expires_at": <ms timestamp>,
         "location_label": "Lebanon, IN"}
    """
    user = _get_current_user()
    if user is None:
        # Don't 401 — frontend handles this cleanly without auth.
        # Anonymous users just don't get auto-trigger.
        return jsonify({"ok": True, "status": "no-location"})

    # Find their primary saved location
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT label, lat, lng FROM saved_locations
                   WHERE user_id = %s AND is_primary = TRUE
                   LIMIT 1""",
                (user["id"],),
            )
            row = cur.fetchone()

    if not row or row.get("lat") is None or row.get("lng") is None:
        return jsonify({"ok": True, "status": "no-location"})

    user_lat = float(row["lat"])
    user_lng = float(row["lng"])
    user_location_label = row.get("label") or ""

    # Fetch alerts (cached for 60s)
    alerts = _get_cached_nws_alerts()

    # Find the worst alert whose polygon contains the user's location
    worst = None
    worst_rank = 0
    for alert in alerts:
        geom = alert.get("geometry")
        if not geom:
            continue
        try:
            geom_str = json.dumps(geom)
            if not _point_in_polygon_geojson(user_lat, user_lng, geom_str):
                continue
        except Exception:
            continue
        rank = _alert_tier_rank(alert.get("event", ""))
        if rank > worst_rank:
            worst_rank = rank
            worst = alert

    if not worst:
        return jsonify({
            "ok": True,
            "status": "clear",
            "location_label": user_location_label,
        })

    return jsonify({
        "ok": True,
        "status": _event_to_shelter_tier(worst.get("event", "")),
        "event": worst.get("event"),
        "headline": worst.get("headline"),
        "area_desc": worst.get("area_desc"),
        "expires_at": worst.get("expires_at"),
        "location_label": user_location_label,
    })


# ════════════════════════════════════════════════════════════════════
# Daily brief delivery (Item #3 — Chunk 3A)
# ════════════════════════════════════════════════════════════════════
#
# Subscribers set their brief preferences (morning_window_start/end,
# channels, location) in the portal. This module:
#   1. Runs a background scheduler thread that checks every 60 seconds
#   2. For each subscriber whose preferences match the current time AND
#      who has NOT already received their brief today, fetch forecast,
#      generate AI brief, send via channels, record in brief_history.
#   3. Skips Pro-tier subscribers (Chunk 3B handles Met-touched briefs).
#
# Threading notes:
#   - The scheduler runs in a daemon thread spawned at first request.
#   - One scheduler instance per Python process. Render runs a single
#     gunicorn worker (default for our service) so we get exactly one.
#   - If the process restarts mid-day, the scheduler picks back up.
#   - Idempotency via brief_history: we check "did we send today already?"
#     before each send, so even multiple workers wouldn't double-send.

_BRIEF_SCHEDULER_STARTED = False
_BRIEF_SCHEDULER_LOCK = threading.Lock()


def _fetch_forecast(lat: float, lng: float) -> Optional[dict]:
    """Fetch a forecast from Open-Meteo for the given lat/lng.

    Returns a dict with the day's high/low, hourly precipitation,
    wind, and overall conditions; or None on failure. Used by the
    brief generator — no user is present so we hit the API directly
    from the backend (unlike ticket forecasts which the frontend fetches).
    """
    try:
        url = (
            "https://api.open-meteo.com/v1/forecast"
            f"?latitude={lat}&longitude={lng}"
            "&hourly=temperature_2m,precipitation_probability,windspeed_10m,weathercode"
            "&daily=temperature_2m_max,temperature_2m_min,precipitation_sum,"
            "windspeed_10m_max,weathercode,sunrise,sunset"
            "&temperature_unit=fahrenheit&windspeed_unit=mph"
            "&precipitation_unit=inch&timezone=auto&forecast_days=1"
        )
        req = urllib.request.Request(url, headers={"User-Agent": "weathervalet/1.0"})
        with urllib.request.urlopen(req, timeout=6) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        print(f"[brief-forecast] fetch failed for ({lat},{lng}): {e}", flush=True)
        return None


def _weather_code_label(code: int) -> str:
    """Open-Meteo WMO weather code → short human label."""
    if code == 0: return "Clear"
    if code in (1, 2): return "Mostly clear"
    if code == 3: return "Overcast"
    if code in (45, 48): return "Fog"
    if code in (51, 53, 55): return "Drizzle"
    if code in (61, 63, 65): return "Rain"
    if code in (66, 67): return "Freezing rain"
    if code in (71, 73, 75, 77): return "Snow"
    if code in (80, 81, 82): return "Rain showers"
    if code in (85, 86): return "Snow showers"
    if code in (95, 96, 99): return "Thunderstorms"
    return "Mixed conditions"


def _generate_ai_brief(location_label: str, forecast: dict) -> tuple[str, str, str]:
    """Generate a daily brief paragraph.

    Returns (verdict, snippet, full_body):
      verdict — "clear" | "caution" | "risk"
      snippet — first ~140 chars suitable for SMS preview / portal card
      full_body — the full 2-4 sentence brief

    For now this is a rules-based generator that reads the day's
    high/low/precip/wind from the forecast and writes a deterministic
    summary. Future: swap to Gemini/Decision Engine for richer prose.
    """
    if not forecast or "daily" not in forecast:
        body = f"Your morning brief for {location_label}: forecast unavailable right now. We'll retry on the next interval."
        return ("caution", body[:140], body)

    daily = forecast["daily"]
    high = (daily.get("temperature_2m_max") or [None])[0]
    low = (daily.get("temperature_2m_min") or [None])[0]
    precip = (daily.get("precipitation_sum") or [0])[0] or 0
    wind = (daily.get("windspeed_10m_max") or [0])[0] or 0
    code = (daily.get("weathercode") or [0])[0] or 0
    conditions = _weather_code_label(int(code))

    # Verdict logic — conservative thresholds suitable for a "should I
    # do my outdoor thing today" brief
    if precip >= 0.5 or wind >= 30 or code in (95, 96, 99):
        verdict = "risk"
    elif precip >= 0.1 or wind >= 20 or code in (51, 53, 55, 61, 63, 65, 80, 81):
        verdict = "caution"
    else:
        verdict = "clear"

    # Compose the brief — 2-3 sentences that read naturally
    parts = []
    parts.append(f"Good morning. Your {location_label} brief:")
    parts.append(f"{conditions}, high {int(high) if high else '?'}°F, low {int(low) if low else '?'}°F.")
    if precip >= 0.05:
        parts.append(f"Expect {precip:.2f}\" of precipitation through the day.")
    if wind >= 15:
        parts.append(f"Winds gusting to {int(wind)} mph at peak.")
    if verdict == "clear":
        parts.append("Solid day for outdoor plans.")
    elif verdict == "caution":
        parts.append("Plan around the weather, but you can work today.")
    else:
        parts.append("Heads up — conditions are unfavorable for sensitive outdoor work.")

    full_body = " ".join(parts)
    snippet = full_body[:140]
    return (verdict, snippet, full_body)


def _html_escape(s):
    """Escape user-supplied strings for safe inclusion in HTML email."""
    return _html_module.escape(str(s or ""), quote=True)


def _send_welcome_email_with_temp_password(email: str, name: str,
                                            temp_password: str,
                                            role_label: str) -> bool:
    """Welcome email sent when admin creates a new Met/Crew/Admin account.
    Includes a one-time temp password and instructions to change it on
    first sign-in.

    role_label is the human-readable role (e.g. "Meteorologist", "Valet
    Crew", "Admin") — appears in the email body.

    Returns True on send success (or stub-mode print), False on send fail.
    """
    api_key = os.environ.get("RESEND_API_KEY", "").strip()
    from_addr = os.environ.get("EMAIL_FROM", "").strip()
    # Subject — avoid "Welcome" + "password" combos that trip spam filters.
    # Mention the role so the recipient knows it's expected.
    subject = f"Your WeatherValet {role_label} account is ready"

    # Stub fallback if Resend isn't configured (dev mode)
    if not api_key or not from_addr:
        print(
            f"[welcome-email-stub] To: {email}\n"
            f"Subject: {subject}\n"
            f"Temp password: {temp_password}\n"
            f"(no RESEND_API_KEY set; logging only)",
            flush=True,
        )
        return True

    first_name = (name.split()[0] if name else "there")
    safe_name = first_name[:40]
    sign_in_url = f"{FRONTEND_BASE_URL}/?signin=1"

    # Plain-text fallback for email clients without HTML rendering
    text_body = (
        f"Welcome to WeatherValet, {safe_name}!\n\n"
        f"Your {role_label} account has been created. Here's how to sign in:\n\n"
        f"Email: {email}\n"
        f"Temporary password: {temp_password}\n\n"
        f"Sign in here: {sign_in_url}\n\n"
        f"You'll be asked to set your own password on first sign-in. "
        f"This temporary password expires after first use.\n\n"
        f"If you weren't expecting this email, please contact Michael at "
        f"michael@weathervalet.ai.\n\n"
        f"\u2014 The WeatherValet team"
    )

    # HTML body inside the branded shell
    html_inner = f"""
    <h1 style="color:#0E1116;font-size:22px;margin:0 0 16px;font-weight:600;letter-spacing:-0.01em;">
      Welcome to WeatherValet, {_html_escape(safe_name)}
    </h1>
    <p style="color:#0E1116;font-size:15px;line-height:1.6;margin:0 0 18px;">
      Your <strong>{_html_escape(role_label)}</strong> account is ready. Here's how to sign in for the first time:
    </p>
    <div style="background:#F5F7FB;border:1px solid #E5E9F2;border-radius:8px;padding:18px;margin:0 0 22px;">
      <div style="font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:0.08em;color:#8B8F96;margin-bottom:4px;">Email</div>
      <div style="font-size:14.5px;color:#0E1116;font-family:'JetBrains Mono',Menlo,monospace;margin-bottom:14px;">{_html_escape(email)}</div>
      <div style="font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:0.08em;color:#8B8F96;margin-bottom:4px;">Temporary password</div>
      <div style="font-size:16px;color:#0E1116;font-family:'JetBrains Mono',Menlo,monospace;letter-spacing:0.5px;background:#fff;border:1px solid #E5E9F2;border-radius:6px;padding:10px 12px;">{_html_escape(temp_password)}</div>
    </div>
    <div style="margin:0 0 22px;">
      <a href="{sign_in_url}" style="display:inline-block;background:#2E4FB8;color:#fff;text-decoration:none;padding:12px 22px;border-radius:8px;font-size:14.5px;font-weight:600;">Sign in to WeatherValet</a>
    </div>
    <p style="color:#5B6370;font-size:13px;line-height:1.55;margin:0 0 18px;">
      On first sign-in, you'll be asked to set your own password. This temporary password expires after first use.
    </p>
    <p style="color:#8B8F96;font-size:12px;line-height:1.5;margin:24px 0 0;padding-top:18px;border-top:1px solid #ECEEF1;">
      If you weren't expecting this email, contact Michael at
      <a href="mailto:michael@weathervalet.ai" style="color:#2E4FB8;text-decoration:none;">michael@weathervalet.ai</a>.
    </p>
    """

    html_body = _email_shell(
        html_inner,
        preheader=f"Your WeatherValet {role_label} account is ready. Sign in with the temporary password inside."
    )

    payload = json.dumps({
        "from": from_addr,
        "to": [email],
        "reply_to": "michael@weathervalet.ai",
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
            "User-Agent": "WeatherValet-Backend/1.0 (+https://weathervalet.ai)",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            ok = 200 <= resp.status < 300
            if ok:
                print(f"[welcome-email] sent to={email}", flush=True)
            return ok
    except Exception as e:
        print(f"[welcome-email] FAILED to={email}: {type(e).__name__}: {e}", flush=True)
        return False


def _send_brief_email(email: str, subject: str, body_text: str) -> bool:
    """Send a daily brief via Resend. Mirrors _send_magic_link_email but
    for plain text brief content. Stub mode (no API key) logs to console.
    """
    api_key = os.environ.get("RESEND_API_KEY", "").strip()
    from_addr = os.environ.get("EMAIL_FROM", "").strip()

    if not api_key or not from_addr:
        print(f"[brief-email-stub] To: {email}\nSubject: {subject}\n{body_text}\n", flush=True)
        return True

    # Build a nicely-structured HTML body inside the shared email shell.
    # The brief text typically has paragraphs separated by blank lines —
    # we preserve those by converting \n\n to paragraph breaks and single
    # \n to <br>.
    body_html = ''
    paragraphs = body_text.split('\n\n')
    for i, para in enumerate(paragraphs):
        if not para.strip():
            continue
        # Single newlines within a paragraph become <br>
        para_html = para.replace('\n', '<br>')
        margin = '0 0 14px' if i < len(paragraphs) - 1 else '0'
        body_html += (
            f'<p style="color:#0E1116;font-size:15px;line-height:1.6;'
            f'margin:{margin};">{para_html}</p>'
        )

    html_body_inner = (
        f'<h1 style="color:#0E1116;font-size:20px;margin:0 0 18px;'
        f'font-weight:600;letter-spacing:-0.01em;">{subject}</h1>'
        + body_html +
        '<p style="color:#8B8F96;font-size:12px;line-height:1.5;margin:24px 0 0;'
        'padding-top:18px;border-top:1px solid #ECEEF1;">'
        'Adjust your brief preferences or threshold alerts in your '
        '<a href="https://weathervalet.ai/?portal=1" '
        'style="color:#2E4FB8;text-decoration:none;">subscriber portal</a>.</p>'
    )
    # Preheader: first ~90 chars of brief body so inbox preview is useful
    preheader_text = body_text.replace('\n', ' ').strip()[:90]
    html_body = _email_shell(html_body_inner, preheader=preheader_text)

    payload = json.dumps({
        "from": from_addr,
        "to": [email],
        "subject": subject,
        "html": html_body,
        "text": body_text,
    }).encode("utf-8")

    req = urllib.request.Request(
        "https://api.resend.com/emails",
        data=payload,
        method="POST",
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            "User-Agent": "WeatherValet-Backend/1.0 (+https://weathervalet.ai)",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return 200 <= resp.status < 300
    except Exception as e:
        print(f"[brief-email] FAILED to={email}: {type(e).__name__}: {e}", flush=True)
        return False


def _timezone_for_latlng(lat: float, lng: float) -> str:
    """Best-effort IANA timezone for a US lat/lng.

    Uses longitude bands — accurate for the continental US except at
    a few state boundary edge cases (TN/KY, FL panhandle, parts of ID,
    AZ which doesn't observe DST). For nationwide launch we should
    upgrade to the `timezonefinder` library; this is good enough for
    Indianapolis-area testing and early nationwide subscribers.

    Returns an IANA name like "America/Indiana/Indianapolis" so it
    survives ZoneInfo lookups.
    """
    try:
        lat = float(lat)
        lng = float(lng)
    except (ValueError, TypeError):
        return "America/Indiana/Indianapolis"

    # Alaska / Hawaii / outlying — coarse handling
    if lat > 50 and lng < -130:
        return "America/Anchorage"
    if 18 < lat < 23 and -161 < lng < -154:
        return "Pacific/Honolulu"

    # Continental US — longitude bands
    if lng >= -85:
        return "America/New_York"
    if lng >= -100:
        return "America/Chicago"
    if lng >= -114:
        return "America/Denver"
    return "America/Los_Angeles"


def _local_now_for_user(user_timezone: str) -> datetime:
    """Current datetime in the user's local timezone."""
    try:
        return datetime.now(ZoneInfo(user_timezone))
    except Exception:
        return datetime.now(ZoneInfo("America/Indiana/Indianapolis"))


def _time_in_window(now_hour: int, now_min: int, start_str: str, end_str: str) -> bool:
    """Is the current HH:MM within the [start_str, end_str] window?

    Both strings are 'HH:MM'. Handles windows that cross midnight
    (e.g. quiet hours 21:00 → 05:00) by checking start <= now OR now <= end.
    """
    try:
        sh, sm = int(start_str[:2]), int(start_str[3:])
        eh, em = int(end_str[:2]), int(end_str[3:])
    except (ValueError, TypeError, IndexError):
        return False
    now_minutes = now_hour * 60 + now_min
    start_minutes = sh * 60 + sm
    end_minutes = eh * 60 + em
    if start_minutes <= end_minutes:
        return start_minutes <= now_minutes <= end_minutes
    # Window crosses midnight
    return now_minutes >= start_minutes or now_minutes <= end_minutes


def _already_sent_today(user_id: int, brief_type: str, user_timezone: str = None) -> bool:
    """Check if this user has received a brief of the given type today.

    "Today" means today in the subscriber's local timezone. Defaults to
    Indianapolis time if no timezone passed (preserves prior behavior
    for older callers).
    """
    tz = user_timezone or "America/Indiana/Indianapolis"
    try:
        local_now = _local_now_for_user(tz)
    except Exception:
        local_now = datetime.now(timezone.utc)
    today_start_local = local_now.replace(hour=0, minute=0, second=0, microsecond=0)
    today_start_ms = int(today_start_local.timestamp() * 1000)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT COUNT(*) AS n FROM brief_history
                   WHERE user_id = %s AND brief_type = %s AND delivered_at >= %s""",
                (user_id, brief_type, today_start_ms),
            )
            row = cur.fetchone()
    return (row["n"] or 0) > 0 if row else False


def _record_brief_delivery(user_id: int, brief_type: str, verdict: str,
                            snippet: str, full_body: str, delivery_status: str,
                            channels_used: str, is_met_touched: bool = False,
                            met_name: Optional[str] = None) -> None:
    """Insert a brief_history row."""
    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO brief_history
                   (user_id, brief_type, delivered_at, verdict, snippet,
                    full_body, delivery_status, channels_used,
                    is_met_touched, met_name)
                   VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)""",
                (user_id, brief_type, now_ms, verdict, snippet, full_body,
                 delivery_status, channels_used, is_met_touched, met_name),
            )


def _process_pending_briefs() -> None:
    """Called once per scheduler tick (every 60s). Finds subscribers whose
    morning window matches the current time in THEIR local timezone,
    generates + sends their brief.

    Pro-tier briefs are flagged but NOT sent — Chunk 3B handles Met review.
    Hobbyist (and any tier not requiring review) gets the full automated
    flow.

    Phase 10 timezone foundation: each subscriber has u.timezone. We
    compute "what time is it in THEIR timezone right now" and compare
    against their morning_window_start/end (which are stored as local
    HH:MM strings). This is what makes nationwide delivery work — a
    California subscriber's 6 AM window fires at 9 AM Eastern when
    the scheduler ticks during Indianapolis morning.
    """
    try:
        with db() as conn:
            with conn.cursor() as cur:
                # Find subscribers with morning brief enabled, in window,
                # and not yet sent today. JOIN user → preferences → primary location.
                cur.execute(
                    """SELECT
                          u.id AS user_id,
                          u.email,
                          u.phone,
                          u.name,
                          u.subscription_tier,
                          u.timezone,
                          bp.morning_window_start,
                          bp.morning_window_end,
                          bp.channels,
                          loc.label AS loc_label,
                          loc.address_text AS loc_address,
                          loc.lat AS loc_lat,
                          loc.lng AS loc_lng
                       FROM users u
                       JOIN brief_preferences bp ON bp.user_id = u.id
                       LEFT JOIN saved_locations loc
                            ON loc.user_id = u.id AND loc.is_primary = TRUE
                       WHERE u.is_active = TRUE
                         AND bp.morning_enabled = TRUE
                         AND EXISTS (
                           SELECT 1 FROM user_roles ur
                            WHERE ur.user_id = u.id AND ur.role = 'subscriber'
                         )"""
                )
                candidates = cur.fetchall()
    except Exception as e:
        print(f"[brief-scheduler] query failed: {e}", flush=True)
        return

    for c in candidates:
        try:
            # Compute "now" in THIS subscriber's local timezone
            user_tz = c.get("timezone") or "America/Indiana/Indianapolis"
            local_now = _local_now_for_user(user_tz)
            now_hour = local_now.hour
            now_min = local_now.minute

            if not _time_in_window(now_hour, now_min,
                                   c["morning_window_start"],
                                   c["morning_window_end"]):
                continue
            if _already_sent_today(c["user_id"], "morning", user_tz):
                continue
            if not c["loc_lat"] or not c["loc_lng"]:
                # No primary location set — skip silently. Subscriber should
                # add one in the portal; we don't pester them with an error.
                continue

            # Pro-tier path: generate the AI draft, insert a pro_brief_drafts
            # row for Met review. Don't send via channels here — that happens
            # when the Met sends via the workspace endpoint. Idempotency note:
            # _already_sent_today checks brief_history. If a draft was created
            # but not yet sent, the next tick would re-create it. To prevent
            # that, we also check pro_brief_drafts for a pending row.
            tier = c["subscription_tier"] or "hobbyist"
            if tier in ("pro_single", "pro_multi", "pro_enterprise"):
                # Has a pending draft for today already? If so, skip.
                today_start_ms = int(datetime.now(timezone.utc)
                                     .replace(hour=0, minute=0, second=0, microsecond=0)
                                     .timestamp() * 1000)
                try:
                    with db() as conn:
                        with conn.cursor() as cur:
                            cur.execute(
                                """SELECT id FROM pro_brief_drafts
                                   WHERE user_id = %s AND brief_type = 'morning'
                                     AND created_at >= %s
                                     AND status IN ('pending-review','claimed','sent')
                                   LIMIT 1""",
                                (c["user_id"], today_start_ms),
                            )
                            existing = cur.fetchone()
                except Exception as e:
                    print(f"[brief-scheduler] pro draft lookup failed: {e}", flush=True)
                    continue
                if existing:
                    continue

                # Generate the AI draft using the same generator hobbyists get
                location_label = c["loc_label"] or c["loc_address"] or "your location"
                forecast = _fetch_forecast(float(c["loc_lat"]), float(c["loc_lng"]))
                ai_verdict, ai_snippet, ai_body = _generate_ai_brief(location_label, forecast or {})

                # Compute window_end_at — the scheduler shouldn't send a
                # "morning brief" at 2pm. Use the user's window_end as the
                # cutoff; after that, the draft is too stale.
                try:
                    eh, em = int(c["morning_window_end"][:2]), int(c["morning_window_end"][3:])
                    window_end_dt = now.replace(hour=eh, minute=em, second=0, microsecond=0)
                    if window_end_dt < now:
                        # Window ended already (shouldn't happen if we got here, but defend)
                        window_end_dt = now
                    window_end_ms = int(window_end_dt.timestamp() * 1000)
                except (ValueError, TypeError, IndexError):
                    # Default cutoff: 4 hours from now
                    window_end_ms = int(time.time() * 1000) + 4 * 60 * 60 * 1000

                now_ms = int(time.time() * 1000)
                try:
                    with db() as conn:
                        with conn.cursor() as cur:
                            cur.execute(
                                """INSERT INTO pro_brief_drafts
                                   (user_id, brief_type, created_at, window_end_at, status,
                                    user_tier, location_label, location_lat, location_lng,
                                    channels, ai_verdict, ai_snippet, ai_body,
                                    met_verdict, met_snippet, met_body)
                                   VALUES (%s, 'morning', %s, %s, 'pending-review',
                                           %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                                   RETURNING id""",
                                (c["user_id"], now_ms, window_end_ms,
                                 tier, location_label,
                                 float(c["loc_lat"]), float(c["loc_lng"]),
                                 c["channels"] or "",
                                 ai_verdict, ai_snippet, ai_body,
                                 ai_verdict, ai_snippet, ai_body),
                            )
                            new_id = cur.fetchone()["id"]
                    print(
                        f"[brief-scheduler] pro draft created id={new_id} user_id={c['user_id']} "
                        f"tier={tier} verdict={ai_verdict}",
                        flush=True,
                    )
                except Exception as e:
                    print(f"[brief-scheduler] pro draft insert failed: {e}", flush=True)
                continue

            # ── Generate the brief ──
            location_label = c["loc_label"] or c["loc_address"] or "your location"
            forecast = _fetch_forecast(float(c["loc_lat"]), float(c["loc_lng"]))
            verdict, snippet, full_body = _generate_ai_brief(location_label, forecast or {})

            # ── Send via channels ──
            channels = [ch for ch in (c["channels"] or "").split(",") if ch]
            channels_used = []
            any_success = False
            for ch in channels:
                if ch == "sms" and c["phone"]:
                    ok = send_sms(c["phone"], snippet + "\n\nFull brief: " + full_body[:1200])
                    if ok:
                        channels_used.append("sms")
                        any_success = True
                elif ch == "email" and c["email"]:
                    subject = f"Your WeatherValet brief — {location_label}"
                    ok = _send_brief_email(c["email"], subject, full_body)
                    if ok:
                        channels_used.append("email")
                        any_success = True
                # 'push' not yet wired; skip silently
            delivery_status = "sent" if any_success else "failed"

            _record_brief_delivery(
                user_id=c["user_id"],
                brief_type="morning",
                verdict=verdict,
                snippet=snippet,
                full_body=full_body,
                delivery_status=delivery_status,
                channels_used=",".join(channels_used),
                is_met_touched=False,
                met_name=None,
            )
            print(
                f"[brief-scheduler] delivered user_id={c['user_id']} tier={tier} "
                f"channels={channels_used} verdict={verdict}",
                flush=True,
            )
        except Exception as e:
            print(f"[brief-scheduler] FAILED for user_id={c.get('user_id')}: {e!r}", flush=True)


def _brief_scheduler_loop() -> None:
    """Main scheduler loop — runs in a daemon thread. Ticks every 60s.

    Each tick runs three independent jobs:
      1. _process_pending_briefs — daily brief delivery
      2. _process_severe_alerts  — NWS severe alert detection + Met paging
      3. _check_missed_pro_briefs — alert admin + Met when a Pro brief
                                    was supposed to send but didn't

    Failures in one don't stop the others.
    """
    print("[brief-scheduler] started", flush=True)
    # Initial small delay so the app fully boots before our first tick.
    time.sleep(15)
    while True:
        try:
            _process_pending_briefs()
        except Exception as e:
            print(f"[brief-scheduler] tick failed: {e!r}", flush=True)
        try:
            _process_severe_alerts()
        except Exception as e:
            print(f"[nws-scheduler] tick failed: {e!r}", flush=True)
        try:
            _check_missed_pro_briefs()
        except Exception as e:
            print(f"[missed-brief-check] tick failed: {e!r}", flush=True)
        try:
            _process_scheduled_messages()
        except Exception as e:
            print(f"[scheduled-msg-tick] tick failed: {e!r}", flush=True)
        # Phase 11 (May 17): Coverage scheduler jobs
        # Generate today/tomorrow tasks for Pro subscribers, then check
        # for escalations. Both run on the same 60s tick so deadlines
        # are checked at minute resolution.
        try:
            _coverage_generate_pending_tasks()
        except Exception as e:
            print(f"[coverage-tasks] generate failed: {e!r}", flush=True)
        try:
            _coverage_check_escalations()
        except Exception as e:
            print(f"[coverage-tasks] escalation check failed: {e!r}", flush=True)
        try:
            _coverage_auto_close_storm_shelters()
        except Exception as e:
            print(f"[storm-shelter] auto-close tick failed: {e!r}", flush=True)
        try:
            _rosie_fire_reminders()
        except Exception as e:
            print(f"[rosie-reminder] fire tick failed: {e!r}", flush=True)
        try:
            _rosie_proactive_check_tick()
        except Exception as e:
            print(f"[rosie-proactive] tick failed: {e!r}", flush=True)
        time.sleep(60)


# ────────────────────────────────────────────────────────────────────────────
# Coverage scheduler — Phase 2 (task generation + escalation)
# ────────────────────────────────────────────────────────────────────────────


def _coverage_generate_pending_tasks() -> None:
    """For every active Pro subscriber, ensure a daily_brief_tasks row
    exists for today and tomorrow (in their local timezone).

    Runs on the main scheduler tick. Idempotent — uses ON CONFLICT to
    avoid duplicate rows. Generates 2 days ahead so timezone edge cases
    (subscribers in HI vs NY) all get coverage even if the cron is a
    few hours late.
    """
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id AS user_id, u.name, u.email,
                          u.subscription_tier AS tier,
                          sc.primary_met_id, sc.backup_met_id,
                          sc.daily_brief_time, sc.daily_brief_timezone
                   FROM users u
                   JOIN user_roles ur ON ur.user_id = u.id AND ur.role = 'subscriber'
                   LEFT JOIN subscriber_coverage sc ON sc.user_id = u.id
                   WHERE u.is_active = TRUE
                     AND u.subscription_tier IN ('pro_single','pro_multi','pro_enterprise')"""
            )
            subs = cur.fetchall()

            # Read recurring + overrides once for performance
            cur.execute(
                """SELECT mrs.*, u.name AS met_name
                   FROM met_recurring_shifts mrs
                   JOIN users u ON u.id = mrs.met_user_id
                   WHERE u.is_active = TRUE"""
            )
            recurring = cur.fetchall()

            today_utc = datetime.now(timezone.utc).date()
            window_start = today_utc.strftime("%Y-%m-%d")
            window_end = (today_utc + timedelta(days=2)).strftime("%Y-%m-%d")
            cur.execute(
                """SELECT mso.*, u.name AS met_name
                   FROM met_shift_overrides mso
                   LEFT JOIN users u ON u.id = mso.met_user_id
                   WHERE mso.shift_date >= %s
                     AND mso.shift_date <= %s
                   ORDER BY mso.created_at""",
                (window_start, window_end),
            )
            overrides = cur.fetchall()

    now_ms = int(time.time() * 1000)
    created_count = 0
    inserts = []  # batched (subscriber_id, date, met_id, due_at_ms) tuples

    for sub in subs:
        tz_name = sub.get("daily_brief_timezone") or "America/New_York"
        delivery_time_str = sub.get("daily_brief_time") or "07:00"

        try:
            sub_tz = ZoneInfo(tz_name)
        except Exception:
            sub_tz = ZoneInfo("America/New_York")

        # Today + tomorrow in subscriber's local timezone
        now_local = datetime.now(sub_tz)
        for offset in (0, 1):
            local_date = (now_local + timedelta(days=offset)).date()
            local_date_str = local_date.strftime("%Y-%m-%d")
            # Compute deadline = local date + delivery time, converted to UTC ms
            try:
                hh, mm = delivery_time_str.split(":")
                deadline_local = datetime(
                    local_date.year, local_date.month, local_date.day,
                    int(hh), int(mm), tzinfo=sub_tz
                )
                deadline_utc = deadline_local.astimezone(timezone.utc)
                due_at_ms = int(deadline_utc.timestamp() * 1000)
            except Exception as e:
                print(f"[coverage-tasks] bad time '{delivery_time_str}' for user {sub['user_id']}: {e}", flush=True)
                continue

            # Skip generating if deadline already past (we don't backfill old days)
            if due_at_ms < now_ms - 24 * 60 * 60 * 1000:
                continue

            # Resolve assigned Met via the same logic as the dashboard
            dow = (local_date.weekday() + 1) % 7  # 0=Sun
            assigned = _resolve_coverage_for_day(
                local_date_str, dow, sub["user_id"], sub.get("primary_met_id"),
                recurring, overrides, scope="subscriber"
            )
            assigned_met_id = assigned["met_id"] if assigned else None
            # Stash for batched insert below — one DB round-trip per
            # subscriber instead of per-(subscriber, day).
            inserts.append((sub["user_id"], local_date_str, assigned_met_id, due_at_ms))

    # Batched insert — one transaction for all rows generated this tick.
    # ON CONFLICT preserves any existing assignment: if a task row was
    # created earlier with assigned_met_id=X, we don't overwrite X even
    # if the resolver would now return Y. This protects work-in-progress
    # from getting reassigned mid-day. Admin can manually reassign by
    # updating the row directly if needed.
    if inserts:
        try:
            with db() as conn:
                with conn.cursor() as cur:
                    for row_args in inserts:
                        cur.execute(
                            """INSERT INTO daily_brief_tasks
                               (subscriber_user_id, task_date, assigned_met_id,
                                due_at_ms, status)
                               VALUES (%s, %s, %s, %s, 'pending')
                               ON CONFLICT (subscriber_user_id, task_date) DO UPDATE
                               SET assigned_met_id = COALESCE(daily_brief_tasks.assigned_met_id,
                                                              EXCLUDED.assigned_met_id),
                                   due_at_ms = EXCLUDED.due_at_ms
                               RETURNING (xmax = 0) AS inserted""",
                            row_args,
                        )
                        r = cur.fetchone()
                        if r and r.get("inserted"):
                            created_count += 1
        except Exception as e:
            print(f"[coverage-tasks] batch insert failed: {e}", flush=True)

    if created_count:
        print(f"[coverage-tasks] generated {created_count} new task rows", flush=True)


def _coverage_check_escalations() -> None:
    """For pending daily brief tasks approaching their deadline, fire
    SMS escalations.

    Schedule:
      - T-30 minutes (before deadline), Met not started → SMS assigned Met
      - T+0 (deadline), still not sent → SMS admin + Chief Met (Joe)

    Each escalation level recorded in escalated_at_ms / escalated_admin_at_ms
    so we don't double-fire. If the brief is sent in between, the task
    transitions to 'sent' and escalations stop.
    """
    now_ms = int(time.time() * 1000)
    thirty_min_ms = 30 * 60 * 1000

    with db() as conn:
        with conn.cursor() as cur:
            # Find tasks whose deadline is within the next 30 min and
            # haven't been started yet (or deadline has passed and not sent).
            cur.execute(
                """SELECT dbt.id, dbt.subscriber_user_id, dbt.assigned_met_id,
                          dbt.task_date, dbt.due_at_ms, dbt.status,
                          dbt.started_at_ms, dbt.sent_at_ms,
                          dbt.escalated_at_ms, dbt.escalated_admin_at_ms,
                          su.name AS subscriber_name,
                          su.email AS subscriber_email,
                          mu.name AS met_name, mu.phone AS met_phone,
                          sc.backup_met_id, sc.daily_brief_timezone,
                          bu.name AS backup_name, bu.phone AS backup_phone
                   FROM daily_brief_tasks dbt
                   JOIN users su ON su.id = dbt.subscriber_user_id
                   LEFT JOIN users mu ON mu.id = dbt.assigned_met_id
                   LEFT JOIN subscriber_coverage sc ON sc.user_id = dbt.subscriber_user_id
                   LEFT JOIN users bu ON bu.id = sc.backup_met_id
                   WHERE dbt.status = 'pending'
                     AND dbt.sent_at_ms IS NULL
                     AND dbt.due_at_ms <= %s""",
                (now_ms + thirty_min_ms,),
            )
            rows = cur.fetchall()

    for r in rows:
        # If T-30 reached and we haven't sent Met SMS yet, send it
        time_to_deadline = r["due_at_ms"] - now_ms
        # Level 1: T-30 min, not started, not yet escalated
        if (time_to_deadline <= thirty_min_ms
            and r["started_at_ms"] is None
            and r["escalated_at_ms"] is None
            and r["assigned_met_id"]):
            _coverage_escalate_to_met(r)
        # Level 2: T+0 (deadline passed), not sent, not yet admin-escalated
        elif (time_to_deadline <= 0
              and r["sent_at_ms"] is None
              and r["escalated_admin_at_ms"] is None):
            _coverage_escalate_to_admin(r)


def _coverage_escalate_to_met(task_row) -> None:
    """SMS the assigned (primary) Met that the brief is due in 30 minutes
    and they haven't started yet. Backup is NOT pinged at this level —
    they only get involved if the primary fails (L2 escalation). This
    keeps SMS noise low and avoids cry-wolf fatigue."""
    now_ms = int(time.time() * 1000)
    sub_name = task_row.get("subscriber_name") or "a Pro subscriber"
    msg = (
        f"WeatherValet: daily brief for {sub_name} is due in 30 minutes. "
        f"You haven't started yet. Open your workspace to begin. "
        f"Task date: {task_row['task_date']}."
    )

    targets = []
    if task_row.get("met_phone"):
        targets.append((task_row["assigned_met_id"], task_row["met_phone"], "assigned"))
    # Note: backup intentionally excluded here — see L2 escalation.

    sent_any = False
    for met_id, phone, role in targets:
        try:
            if send_sms(phone, msg):
                sent_any = True
                print(f"[coverage-escalate] L1 SMS to met={met_id} ({role}) for task={task_row['id']}", flush=True)
        except Exception as e:
            print(f"[coverage-escalate] L1 SMS failed met={met_id}: {e}", flush=True)

    # Mark escalated even if SMS failed — we don't want to keep retrying
    # endlessly. Failed sends will surface in logs for investigation.
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """UPDATE daily_brief_tasks
                       SET escalated_at_ms = %s
                       WHERE id = %s""",
                    (now_ms, task_row["id"]),
                )
    except Exception as e:
        print(f"[coverage-escalate] DB update failed: {e}", flush=True)


def _coverage_escalate_to_admin(task_row) -> None:
    """SMS admins, Chief Met (Joe), AND the backup Met (if any) when a
    brief deadline has passed and the brief still hasn't been sent.
    This is the loud alert — backup is brought in here, not at L1,
    so they only get pinged when it actually matters."""
    now_ms = int(time.time() * 1000)
    sub_name = task_row.get("subscriber_name") or "a Pro subscriber"
    met_name = task_row.get("met_name") or "(unassigned)"
    msg = (
        f"WeatherValet ALERT: daily brief for {sub_name} is OVERDUE. "
        f"Assigned Met: {met_name}. Date: {task_row['task_date']}. "
        f"Coverage gap — needs immediate attention."
    )

    # Find escalation targets: all active admins + any user with name
    # containing "Joe" or "Clauss" (Chief Met). Falls back gracefully if
    # neither exists.
    targets = []
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, u.phone
                   FROM users u
                   JOIN user_roles ur ON ur.user_id = u.id AND ur.role = 'admin'
                   WHERE u.is_active = TRUE
                     AND u.phone IS NOT NULL AND u.phone != ''"""
            )
            for r in cur.fetchall():
                targets.append((r["id"], r["phone"], "admin"))

            # Chief Met by email (configurable later)
            chief_email = os.environ.get("CHIEF_MET_EMAIL", "joe@weathervalet.com").strip()
            if chief_email:
                cur.execute(
                    """SELECT u.id, u.name, u.phone
                       FROM users u
                       WHERE LOWER(u.email) = LOWER(%s)
                         AND u.is_active = TRUE
                         AND u.phone IS NOT NULL AND u.phone != ''""",
                    (chief_email,),
                )
                for r in cur.fetchall():
                    # Avoid duplicates if Chief Met is also admin
                    if not any(t[0] == r["id"] for t in targets):
                        targets.append((r["id"], r["phone"], "chief"))

    # Backup Met — only paged at L2, not L1. Use a friendlier message
    # since they're being asked to actually do work, not just be aware.
    if task_row.get("backup_phone") and task_row.get("backup_met_id"):
        backup_id = task_row["backup_met_id"]
        if not any(t[0] == backup_id for t in targets):
            targets.append((backup_id, task_row["backup_phone"], "backup"))

    if not targets:
        print(f"[coverage-escalate] L2: no admin/chief/backup targets for task={task_row['id']}", flush=True)

    for uid, phone, role in targets:
        # Friendly variant for backup — they're being asked to step in
        if role == "backup":
            send_msg = (
                f"WeatherValet: {met_name} hasn't sent the daily brief for "
                f"{sub_name} yet ({task_row['task_date']}). Can you cover? "
                f"Open your workspace to claim the task."
            )
        else:
            send_msg = msg
        try:
            if send_sms(phone, send_msg):
                print(f"[coverage-escalate] L2 SMS to {role} uid={uid} for task={task_row['id']}", flush=True)
        except Exception as e:
            print(f"[coverage-escalate] L2 SMS failed uid={uid}: {e}", flush=True)

    # Mark admin-escalated + status=overdue so the dashboard reflects it
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """UPDATE daily_brief_tasks
                       SET escalated_admin_at_ms = %s,
                           status = 'overdue'
                       WHERE id = %s""",
                    (now_ms, task_row["id"]),
                )
    except Exception as e:
        print(f"[coverage-escalate] L2 DB update failed: {e}", flush=True)


def _check_missed_pro_briefs() -> None:
    """Detect Pro subscribers whose morning brief window has closed
    without a brief being sent. SMS admin + the Met team so someone
    can catch up.

    Runs every 60s. Dedupes via a daily marker so we don't spam.
    A "missed" alert fires once: at 5 minutes past window end.
    """
    # We track which (user_id, local_date) combos we've already alerted
    # for, to avoid repeating. Use brief_history with a special
    # brief_type='missed_alert' marker so dedup persists across restarts.
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT
                          u.id AS user_id, u.email, u.name, u.timezone,
                          u.subscription_tier,
                          bp.morning_window_start, bp.morning_window_end
                       FROM users u
                       JOIN brief_preferences bp ON bp.user_id = u.id
                       WHERE u.is_active = TRUE
                         AND bp.morning_enabled = TRUE
                         AND u.subscription_tier IN ('pro_single','pro_multi','pro_enterprise')
                         AND EXISTS (
                           SELECT 1 FROM user_roles ur
                           WHERE ur.user_id = u.id AND ur.role = 'subscriber'
                         )"""
                )
                pro_subs = cur.fetchall()
    except Exception as e:
        print(f"[missed-brief-check] query failed: {e}", flush=True)
        return

    for c in pro_subs:
        try:
            user_tz = c.get("timezone") or "America/Indiana/Indianapolis"
            try:
                tz = ZoneInfo(user_tz)
            except Exception:
                tz = ZoneInfo("America/Indiana/Indianapolis")
            local_now = datetime.now(tz)

            # Parse window end and add 5-minute grace
            try:
                end_h = int(c["morning_window_end"][:2])
                end_m = int(c["morning_window_end"][3:])
            except (ValueError, TypeError, IndexError):
                continue

            window_end_today = local_now.replace(
                hour=end_h, minute=end_m, second=0, microsecond=0
            )
            check_after = window_end_today + timedelta(minutes=5)

            # Only check after the grace period
            if local_now < check_after:
                continue
            # Only check if it's still the same day (don't fire stale alerts)
            if (local_now - check_after).total_seconds() > 7200:
                # Window ended >2hr ago — too late, skip
                continue

            # Already sent the brief? Skip.
            if _already_sent_today(c["user_id"], "morning", user_tz):
                continue
            # Already alerted about this miss today? Skip.
            if _already_sent_today(c["user_id"], "missed_alert", user_tz):
                continue

            # Fire alerts: admin + Met team
            sub_name = (c.get("name") or "").strip() or c["email"]
            msg = (
                f"WeatherValet: Pro brief for {sub_name} missed window today. "
                f"Subscriber is paying for daily Met-touched briefs — "
                f"please send manually or check the workspace."
            )

            # Met team SMS
            met_phone = os.environ.get("METEOROLOGIST_PHONE", "").strip()
            if met_phone:
                try:
                    send_sms(met_phone, msg)
                except Exception as e:
                    print(f"[missed-brief-check] met SMS failed: {e}", flush=True)

            # Admin SMS: lookup admin users with phones
            try:
                with db() as conn:
                    with conn.cursor() as cur:
                        cur.execute(
                            """SELECT u.phone FROM users u
                               WHERE u.is_active = TRUE
                                 AND u.phone IS NOT NULL AND u.phone != ''
                                 AND EXISTS (
                                   SELECT 1 FROM user_roles ur
                                   WHERE ur.user_id = u.id AND ur.role = 'admin'
                                 )
                               LIMIT 5"""
                        )
                        admin_rows = cur.fetchall()
                for a in admin_rows:
                    try:
                        send_sms(a["phone"], msg)
                    except Exception as e:
                        print(f"[missed-brief-check] admin SMS failed: {e}", flush=True)
            except Exception as e:
                print(f"[missed-brief-check] admin lookup failed: {e}", flush=True)

            # Record the alert so we don't repeat
            now_ms = int(time.time() * 1000)
            try:
                with db() as conn:
                    with conn.cursor() as cur:
                        cur.execute(
                            """INSERT INTO brief_history
                               (user_id, brief_type, delivered_at, channels_used,
                                delivery_status)
                               VALUES (%s, 'missed_alert', %s, 'sms', 'sent')""",
                            (c["user_id"], now_ms),
                        )
            except Exception as e:
                print(f"[missed-brief-check] dedup-write failed: {e}", flush=True)

            print(
                f"[missed-brief-check] alerted on missed brief user_id={c['user_id']} ({sub_name})",
                flush=True,
            )
        except Exception as e:
            print(f"[missed-brief-check] per-sub error user_id={c.get('user_id')}: {e!r}", flush=True)


# ════════════════════════════════════════════════════════════════════
# NWS severe alert detection + Met paging (Phase 10 Item #7)
# ════════════════════════════════════════════════════════════════════
#
# Each scheduler tick:
#   1. Fetch active NWS alerts (events we care about)
#   2. For each alert, check if its polygon contains any Pro subscriber's
#      primary saved location
#   3. If yes, dedupe against nws_alert_pages (by nws_alert_id) — skip
#      if already paged
#   4. Insert a new row, page the on-duty Met via SMS with a link
#
# This runs every 60s; NWS alerts can have <20min lead time so a 1-min
# detection latency is acceptable. Tighter polling adds little value
# and risks NWS rate limits.

# Severe events we page Mets for. Other NWS event types (Special Weather
# Statement, Hydrologic Outlook, etc.) are informational and don't warrant
# waking the on-duty Met. We can expand this list over time.
_NWS_SEVERE_EVENTS = (
    "Tornado Warning",
    "Severe Thunderstorm Warning",
    "Flash Flood Warning",
    "Tornado Watch",
    "Flood Warning",
)


def _fetch_active_nws_alerts() -> list:
    """Fetch active NWS alerts via the api.weather.gov /alerts/active endpoint.

    Returns a list of normalized alert dicts. Empty list on any error —
    we never want a transient NWS hiccup to break the scheduler.

    Note: NWS API requires a User-Agent header identifying the app.
    """
    try:
        # Filter to severe events only (server-side filtering reduces
        # response size + processing time)
        events_param = ",".join(_NWS_SEVERE_EVENTS)
        url = (
            "https://api.weather.gov/alerts/active"
            f"?event={urllib.parse.quote(events_param)}"
            "&status=actual"
        )
        req = urllib.request.Request(url, headers={
            "User-Agent": "WeatherValet/1.0 (+https://weathervalet.ai)",
            "Accept": "application/geo+json",
        })
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        print(f"[nws-fetch] failed: {e}", flush=True)
        return []

    features = data.get("features") or []
    out = []
    for f in features:
        props = f.get("properties") or {}
        geom = f.get("geometry")
        nws_id = props.get("id") or f.get("id")  # the urn:oid alert ID
        if not nws_id:
            continue
        if not geom or geom.get("type") not in ("Polygon", "MultiPolygon"):
            # Some NWS alerts come without a geometry (county-based);
            # those need a different match path. Skip for v1 — we'll
            # add SAME-code matching later if needed.
            continue
        expires_str = props.get("expires") or props.get("ends")
        expires_ms = None
        if expires_str:
            try:
                from datetime import datetime as _dt
                expires_ms = int(_dt.fromisoformat(
                    expires_str.replace("Z", "+00:00")
                ).timestamp() * 1000)
            except (ValueError, TypeError):
                pass
        out.append({
            "nws_id": nws_id,
            "event": props.get("event") or "",
            "severity": props.get("severity") or "",
            "headline": props.get("headline") or "",
            "description": props.get("description") or "",
            "instruction": props.get("instruction") or "",
            "area_desc": props.get("areaDesc") or "",
            "geometry": geom,
            "expires_at": expires_ms,
        })
    return out


def _find_pro_subscribers_in_polygon(geom: dict) -> list:
    """Find Pro-tier subscribers whose primary saved_location is inside
    the alert polygon. Returns list of dicts with user info needed for
    later notification (id, name, email, phone, location).
    """
    # Stringify geometry once so _point_in_polygon_geojson can parse it
    geom_str = json.dumps(geom)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, u.email, u.phone,
                          u.subscription_tier,
                          loc.label AS loc_label, loc.lat, loc.lng
                   FROM users u
                   JOIN saved_locations loc
                     ON loc.user_id = u.id AND loc.is_primary = TRUE
                   WHERE u.is_active = TRUE
                     AND u.subscription_tier IN ('pro_single','pro_multi','pro_enterprise')
                     AND EXISTS (
                       SELECT 1 FROM user_roles ur
                        WHERE ur.user_id = u.id AND ur.role = 'subscriber'
                     )"""
            )
            rows = cur.fetchall()

    matching = []
    for r in rows:
        if r["lat"] is None or r["lng"] is None:
            continue
        if _point_in_polygon_geojson(float(r["lat"]), float(r["lng"]), geom_str):
            matching.append({
                "user_id": r["id"],
                "name": r.get("name") or "",
                "email": r["email"],
                "phone": r.get("phone") or "",
                "tier": r["subscription_tier"],
                "loc_label": r["loc_label"],
            })
    return matching


def _page_met_for_alert(alert: dict, affected: list, page_token: str) -> bool:
    """SMS the on-duty Met about a new severe alert. Returns True on
    successful send (or stub mode), False on Twilio failure.

    The SMS includes the event name, area, # of affected subscribers, and
    a link to the review page. Met reviews, decides to confirm or dismiss.
    """
    if not METEOROLOGIST_PHONE:
        print("[nws-page] METEOROLOGIST_PHONE not set — can't page", flush=True)
        return False

    base = os.environ.get("FRONTEND_BASE_URL", "https://weathervalet.ai").rstrip("/")
    page_url = f"{base}/?nws-page={page_token}"

    body = (
        f"WV NWS PAGE: {alert['event']}\n"
        f"Area: {(alert.get('area_desc') or '')[:80]}\n"
        f"Affected Pro subs: {len(affected)}\n"
        f"Review: {page_url}\n"
        f"Reply STOP to opt out."
    )
    try:
        return send_sms(METEOROLOGIST_PHONE, body)
    except Exception as e:
        print(f"[nws-page] SMS failed: {e}", flush=True)
        return False


def _process_severe_alerts() -> None:
    """One scheduler tick: fetch alerts, match against subscribers, page Met."""
    alerts = _fetch_active_nws_alerts()
    if not alerts:
        return

    for alert in alerts:
        nws_id = alert["nws_id"]

        # Dedupe — have we already paged for this alert?
        try:
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        "SELECT id FROM nws_alert_pages WHERE nws_alert_id = %s",
                        (nws_id,),
                    )
                    if cur.fetchone():
                        continue  # already paged
        except Exception as e:
            print(f"[nws-process] dedupe check failed: {e}", flush=True)
            continue

        # Find affected Pro subscribers
        affected = _find_pro_subscribers_in_polygon(alert["geometry"])
        if not affected:
            # No Pro subscribers in this alert's area; don't page, don't
            # record. (We could record for analytics but it'd pile up
            # quickly — every NWS alert nationally would create a row.)
            continue

        # Insert the page row + send the Met SMS
        page_token = new_secure_token()
        now_ms = int(time.time() * 1000)
        affected_ids_csv = ",".join(str(a["user_id"]) for a in affected)

        try:
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        """INSERT INTO nws_alert_pages
                           (created_at, nws_alert_id, event, severity, headline,
                            description, instruction, area_desc, polygon_geojson,
                            expires_at, response_token, status, affected_user_ids,
                            met_paged_phone)
                           VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s,
                                   'paged', %s, %s)
                           RETURNING id""",
                        (now_ms, nws_id, alert["event"], alert["severity"],
                         alert["headline"], alert["description"],
                         alert["instruction"], alert["area_desc"],
                         json.dumps(alert["geometry"]),
                         alert["expires_at"], page_token,
                         affected_ids_csv, METEOROLOGIST_PHONE),
                    )
                    new_row = cur.fetchone()
        except Exception as e:
            # Unique constraint violation = race with another worker.
            # Anything else = unexpected; log loud.
            print(f"[nws-process] insert failed for {nws_id}: {e}", flush=True)
            continue

        # Send the SMS — fire-and-forget; failure logged inside.
        _page_met_for_alert(alert, affected, page_token)
        print(
            f"[nws-process] paged Met for alert={alert['event']!r} "
            f"id={new_row['id']} affected={len(affected)}",
            flush=True,
        )


def _ensure_brief_scheduler_started() -> None:
    """Start the scheduler thread exactly once per process lifetime.

    Called from before_request so it kicks off after the app is serving
    requests (avoids race with init_db on cold boot). Idempotent + thread-safe.
    """
    global _BRIEF_SCHEDULER_STARTED
    if _BRIEF_SCHEDULER_STARTED:
        return
    with _BRIEF_SCHEDULER_LOCK:
        if _BRIEF_SCHEDULER_STARTED:
            return
        # Only start if not in test/debug short-circuit modes
        if os.environ.get("WV_DISABLE_SCHEDULER") == "1":
            print("[brief-scheduler] disabled via env var", flush=True)
            _BRIEF_SCHEDULER_STARTED = True
            return
        t = threading.Thread(target=_brief_scheduler_loop, daemon=True, name="brief-scheduler")
        t.start()
        _BRIEF_SCHEDULER_STARTED = True


# Admin / debug endpoint — manually trigger one tick. Useful for the
# launch-day smoke test ("does the scheduler actually do anything?").
# Requires admin role to prevent abuse (someone hammering this could
# DOS the Open-Meteo / Twilio / Resend rate limits).
@app.route("/api/v1/admin/brief/run-now", methods=["OPTIONS"])
def _brief_run_now_preflight():
    return ("", 204)


@app.post("/api/v1/admin/brief/run-now")
def admin_brief_run_now():
    """Manually fire one scheduler tick. Admin-only."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    try:
        _process_pending_briefs()
        return jsonify({"ok": True, "message": "tick fired — check Render logs for delivery results"})
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


# Hook the scheduler start into Flask's request lifecycle. Flask 3.x
# removed before_first_request, so we use a flag + before_request.
@app.before_request
def _scheduler_kickstart():
    _ensure_brief_scheduler_started()


# ════════════════════════════════════════════════════════════════════
# Mission deployments (Item #4)
# ════════════════════════════════════════════════════════════════════
#
# CRUD for missions fired by Mets. The frontend's Mission tab calls
# these to persist deployments and read them back. Real Crew SMS
# (Item #5) and Crew location matching (Item #6) build on top.

# ─── Polygon match helpers (Item #6) ──────────────────────────────
# Standard ray-casting point-in-polygon. Pure Python, no dependencies.

def _point_in_ring(lat: float, lng: float, ring: list) -> bool:
    """Ray-casting point-in-polygon. ring is a list of [lng, lat] pairs.

    Returns True if the point is inside. Boundary cases are imprecise
    (the algorithm is good enough for "is this Crew member roughly in
    this county-sized polygon" — not for legal property boundaries).
    """
    inside = False
    n = len(ring)
    if n < 3:
        return False
    j = n - 1
    for i in range(n):
        xi, yi = ring[i][0], ring[i][1]  # lng, lat
        xj, yj = ring[j][0], ring[j][1]
        # Standard ray cast: does horizontal ray from (lng, lat) cross
        # edge from (xi, yi) to (xj, yj)?
        intersect = ((yi > lat) != (yj > lat)) and \
                    (lng < (xj - xi) * (lat - yi) / ((yj - yi) or 1e-12) + xi)
        if intersect:
            inside = not inside
        j = i
    return inside


def _point_in_polygon_geojson(lat: float, lng: float, geojson_str: str) -> bool:
    """Test whether (lat, lng) is inside the polygon encoded in geojson_str.

    Accepts:
      - A Feature with geometry.type 'Polygon' or 'MultiPolygon'
      - A bare geometry object
      - A FeatureCollection (uses the first polygon feature)

    Returns False on parse errors — safer to skip than crash a Crew
    dispatch loop.
    """
    if not geojson_str:
        return False
    try:
        obj = json.loads(geojson_str) if isinstance(geojson_str, str) else geojson_str
    except (ValueError, TypeError):
        return False
    if not isinstance(obj, dict):
        return False

    # Extract a geometry from whatever shape we got
    geometry = None
    if obj.get("type") == "FeatureCollection":
        features = obj.get("features") or []
        for f in features:
            g = (f or {}).get("geometry")
            if g and g.get("type") in ("Polygon", "MultiPolygon"):
                geometry = g
                break
    elif obj.get("type") == "Feature":
        geometry = obj.get("geometry")
    elif obj.get("type") in ("Polygon", "MultiPolygon"):
        geometry = obj
    if not geometry:
        return False

    gtype = geometry.get("type")
    coords = geometry.get("coordinates") or []

    if gtype == "Polygon":
        # coords[0] is the outer ring; coords[1:] are holes. We treat any
        # point in the outer ring as inside (ignoring holes — close enough
        # for Crew targeting, which doesn't deal with donut-shaped areas).
        if not coords:
            return False
        return _point_in_ring(lat, lng, coords[0])
    if gtype == "MultiPolygon":
        for poly in coords:
            if poly and _point_in_ring(lat, lng, poly[0]):
                return True
        return False
    return False


def _find_crew_for_mission(polygon_geojson: Optional[str]) -> list:
    """Return all active Crew members matching the mission's target area.

    If polygon_geojson is empty/None, returns ALL active Crew (mission
    targets "all Crew in coverage area"). If a polygon is provided,
    returns only Crew whose crew_home location is inside it.

    Each row includes id, name, phone, crew_home_lat/lng so the SMS
    dispatcher has everything it needs without further DB hits.
    """
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, u.email, u.phone,
                          u.crew_home_lat, u.crew_home_lng, u.crew_home_label
                   FROM users u
                   JOIN user_roles ur ON ur.user_id = u.id
                   WHERE ur.role = 'crew'
                     AND u.is_active = TRUE
                     AND u.crew_active = TRUE
                     AND u.phone IS NOT NULL AND u.phone <> ''"""
            )
            all_crew = cur.fetchall()

    if not polygon_geojson:
        # No polygon = broadcast to all Crew
        return list(all_crew)

    matching = []
    for c in all_crew:
        if c["crew_home_lat"] is None or c["crew_home_lng"] is None:
            continue  # Crew member hasn't set location — can't target them
        if _point_in_polygon_geojson(c["crew_home_lat"], c["crew_home_lng"], polygon_geojson):
            matching.append(c)
    return matching


def _dispatch_mission_sms(mission_id: int, prompt: str, polygon_geojson: Optional[str],
                          template_name: str) -> tuple[int, int]:
    """Find matching Crew + send SMS to each. Returns (total_matched, sent_count).

    Creates a mission_notifications row per Crew member so we have an
    audit trail of who got pinged. Failures are logged but don't stop
    the dispatch loop — one bad number shouldn't block the rest.
    """
    crew_list = _find_crew_for_mission(polygon_geojson)
    if not crew_list:
        print(f"[mission-sms] no matching Crew for mission_id={mission_id}", flush=True)
        return (0, 0)

    base_url = os.environ.get("FRONTEND_BASE_URL", "https://weathervalet.ai").rstrip("/")
    sent = 0
    now_ms = int(time.time() * 1000)

    for c in crew_list:
        # Generate a per-notification response token. Lets us identify
        # which Crew member responded without sticking their user_id in
        # a URL (privacy + idempotence).
        resp_token = new_secure_token()
        response_url = f"{base_url}/?mission={resp_token}"

        # Compose the SMS. Short, scannable, with the prompt and a link.
        # 160-char SMS limit is generous; we keep messages tight but
        # don't artificially truncate the prompt.
        sms_body = (
            f"WeatherValet mission ({template_name}):\n"
            f"{prompt[:300]}{'…' if len(prompt) > 300 else ''}\n\n"
            f"Respond: {response_url}\n"
            f"Reply STOP to opt out."
        )

        delivery_status = "stubbed"
        twilio_sid = None
        try:
            ok = send_sms(c["phone"], sms_body)
            delivery_status = "sent" if ok else "failed"
        except Exception as e:
            print(f"[mission-sms] send failed crew_id={c['id']}: {e}", flush=True)
            delivery_status = "failed"

        # Record the notification regardless of send outcome — we want
        # the audit trail even for failures.
        try:
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        """INSERT INTO mission_notifications
                           (mission_id, crew_user_id, sent_at, delivery_status,
                            twilio_sid, response_token)
                           VALUES (%s, %s, %s, %s, %s, %s)""",
                        (mission_id, c["id"], now_ms, delivery_status,
                         twilio_sid, resp_token),
                    )
        except Exception as e:
            print(f"[mission-sms] notification record failed crew_id={c['id']}: {e}", flush=True)

        if delivery_status in ("sent", "stubbed"):
            sent += 1

    print(
        f"[mission-sms] mission_id={mission_id} dispatched: "
        f"matched={len(crew_list)} sent={sent}",
        flush=True,
    )
    return (len(crew_list), sent)


@app.route("/api/v1/missions/deployments", methods=["OPTIONS"])
def _missions_deployments_preflight():
    return ("", 204)


@app.get("/api/v1/missions/deployments")
def missions_list():
    """List recent mission deployments fired by the current Met.

    Returns the 20 most recent deployments. Admin role sees everyone's;
    Met role sees only their own.

    Returns:
        200 {"ok": true, "deployments": [...]}
        401 not authenticated
        403 not a Met or admin
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    is_admin = "admin" in roles

    with db() as conn:
        with conn.cursor() as cur:
            if is_admin:
                cur.execute(
                    """SELECT * FROM mission_deployments
                       ORDER BY fired_at DESC LIMIT 20"""
                )
            else:
                # Mets see (a) all their own missions, plus (b) any
                # pending-approval missions from other Mets so they can
                # provide the second-set-of-eyes approval. This is the
                # F-X1 launch fix: no single-admin bottleneck.
                cur.execute(
                    """SELECT * FROM mission_deployments
                       WHERE fired_by_user_id = %s
                          OR status = 'pending-approval'
                       ORDER BY fired_at DESC LIMIT 20""",
                    (user["id"],),
                )
            rows = cur.fetchall()

    deployments = [
        {
            "id": r["id"],
            "fired_at": r["fired_at"],
            "fired_by_name": r["fired_by_name"],
            "template_id": r["template_id"],
            "template_name": r["template_name"],
            "prompt": r["prompt"],
            "polygon_geojson": r["polygon_geojson"],
            "polygon_label": r["polygon_label"],
            "is_severe": r["is_severe"],
            "status": r["status"],
            "audience_estimate": r["audience_estimate"],
            "crew_responded": r["crew_responded"],
            "crew_cited": r["crew_cited"],
            "completed_at": r["completed_at"],
        }
        for r in rows
    ]
    return jsonify({"ok": True, "deployments": deployments})


@app.post("/api/v1/missions/deployments")
def missions_create():
    """Fire a new mission. Met or admin role required.

    Body:
        {
          "template_id": "flag-check",
          "template_name": "Flag check (wind)",
          "prompt": "Look at the flag at Lebanon HS...",
          "polygon_geojson": "..." (optional, JSON-stringified GeoJSON),
          "polygon_label": "Boone County, IN" (optional),
          "is_severe": false,
          "audience_estimate": 4
        }

    Severe missions land in status 'pending-approval' awaiting admin
    sign-off. Normal missions go straight to 'fired'.

    Returns:
        200 {"ok": true, "deployment": {...}}
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}

    template_id = (data.get("template_id") or "").strip()
    template_name = (data.get("template_name") or "").strip()
    prompt = (data.get("prompt") or "").strip()

    if not template_id:
        return jsonify({"ok": False, "error": "missing-template-id"}), 400
    if not template_name:
        return jsonify({"ok": False, "error": "missing-template-name"}), 400
    if not prompt:
        return jsonify({"ok": False, "error": "missing-prompt"}), 400
    if len(prompt) > 4000:
        return jsonify({"ok": False, "error": "prompt-too-long"}), 400

    polygon_geojson = data.get("polygon_geojson") or None
    polygon_label = (data.get("polygon_label") or "").strip() or None
    is_severe = bool(data.get("is_severe", False))
    try:
        audience_estimate = int(data.get("audience_estimate") or 0)
    except (ValueError, TypeError):
        audience_estimate = 0

    # Severe missions are queued for approval; normal fire immediately.
    status = "pending-approval" if is_severe else "fired"
    now_ms = int(time.time() * 1000)

    fired_by_name = user.get("name") or (user.get("email") or "").split("@")[0]

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO mission_deployments
                   (fired_at, fired_by_user_id, fired_by_name, template_id,
                    template_name, prompt, polygon_geojson, polygon_label,
                    is_severe, status, audience_estimate)
                   VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                   RETURNING *""",
                (now_ms, user["id"], fired_by_name, template_id, template_name,
                 prompt, polygon_geojson, polygon_label, is_severe, status,
                 audience_estimate),
            )
            r = cur.fetchone()

    # ── Item #5: Dispatch Crew SMS for non-severe missions ──
    # Only fire SMS when status is 'fired' — severe missions wait in
    # 'pending-approval' until an admin approves them (which is when
    # the PATCH endpoint should call this same dispatcher).
    #
    # We update audience_estimate with the REAL matched count returned
    # by _dispatch_mission_sms, overriding the modal's estimate. This
    # is the truth — the modal estimate is a UI hint; the matched count
    # is what actually got pinged.
    real_matched = 0
    real_sent = 0
    if status == "fired":
        try:
            real_matched, real_sent = _dispatch_mission_sms(
                r["id"], prompt, polygon_geojson, template_name
            )
            # Update audience_estimate to reflect reality. If the modal
            # said "4 Crew" but only 2 matched the polygon, the row should
            # show 2 — that's what got pinged.
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        "UPDATE mission_deployments SET audience_estimate = %s WHERE id = %s",
                        (real_matched, r["id"]),
                    )
            audience_estimate = real_matched
        except Exception as e:
            # Don't fail the mission create if SMS dispatch hits a snag —
            # the mission row is persisted, dispatch can be retried by
            # an admin later. Log loudly so we notice.
            print(
                f"[mission-sms] dispatch failed for mission_id={r['id']}: {e!r}",
                flush=True,
            )

    # F-X1: For severe (pending-approval) missions, SMS the other Mets
    # so a second pair of eyes shows up fast. Time-critical workflow.
    if status == "pending-approval":
        try:
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        """SELECT u.id, u.phone FROM users u
                           WHERE u.is_active = TRUE
                             AND u.phone IS NOT NULL AND u.phone != ''
                             AND u.id != %s
                             AND (
                               EXISTS (SELECT 1 FROM user_roles ur
                                       WHERE ur.user_id = u.id AND ur.role = 'met')
                               OR
                               EXISTS (SELECT 1 FROM user_roles ur
                                       WHERE ur.user_id = u.id AND ur.role = 'admin')
                             )
                           LIMIT 10""",
                        (user["id"],),
                    )
                    notify_rows = cur.fetchall()
            sev_msg = (
                f"WeatherValet: SEVERE mission pending approval from "
                f"{fired_by_name}. Polygon: {polygon_label or '—'}. "
                f"Prompt: \"{prompt[:80]}\". Open the workspace Missions tab to review."
            )
            for n in notify_rows:
                try:
                    send_sms(n["phone"], sev_msg)
                except Exception as e:
                    print(f"[mission-sms] approval-notify failed for uid={n['id']}: {e}", flush=True)
        except Exception as e:
            print(f"[mission-sms] approval-notify lookup failed: {e}", flush=True)

    print(
        f"[mission] fired id={r['id']} template={template_id} "
        f"by user_id={user['id']} status={status} "
        f"matched={real_matched} sent={real_sent}",
        flush=True,
    )

    return jsonify({
        "ok": True,
        "deployment": {
            "id": r["id"],
            "fired_at": r["fired_at"],
            "fired_by_name": r["fired_by_name"],
            "template_id": r["template_id"],
            "template_name": r["template_name"],
            "prompt": r["prompt"],
            "polygon_geojson": r["polygon_geojson"],
            "polygon_label": r["polygon_label"],
            "is_severe": r["is_severe"],
            "status": r["status"],
            "audience_estimate": audience_estimate,
            "crew_responded": r["crew_responded"],
            "crew_cited": r["crew_cited"],
            "completed_at": r["completed_at"],
            "matched_crew_count": real_matched,
            "sms_sent_count": real_sent,
        },
    })


@app.route("/api/v1/missions/deployments/<int:dep_id>", methods=["OPTIONS"])
def _missions_deployment_id_preflight(dep_id):
    return ("", 204)


@app.get("/api/v1/missions/deployments/<int:dep_id>")
def missions_get_one(dep_id):
    """Return a single deployment. Only the firing Met or an admin can read.

    Returns:
        200 {"ok": true, "deployment": {...}}
        403 not your deployment
        404 not found
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM mission_deployments WHERE id = %s",
                (dep_id,),
            )
            r = cur.fetchone()

    if not r:
        return jsonify({"ok": False, "error": "not-found"}), 404

    roles = user.get("roles") or []
    is_owner = r["fired_by_user_id"] == user["id"]
    is_admin = "admin" in roles
    if not (is_owner or is_admin):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    return jsonify({
        "ok": True,
        "deployment": {
            "id": r["id"],
            "fired_at": r["fired_at"],
            "fired_by_name": r["fired_by_name"],
            "template_id": r["template_id"],
            "template_name": r["template_name"],
            "prompt": r["prompt"],
            "polygon_geojson": r["polygon_geojson"],
            "polygon_label": r["polygon_label"],
            "is_severe": r["is_severe"],
            "status": r["status"],
            "audience_estimate": r["audience_estimate"],
            "crew_responded": r["crew_responded"],
            "crew_cited": r["crew_cited"],
            "completed_at": r["completed_at"],
        },
    })


@app.patch("/api/v1/missions/deployments/<int:dep_id>")
def missions_update(dep_id):
    """Update a deployment's status (admin approval, cancellation, completion).

    Body:
        {"status": "fired" | "cancelled" | "completed",
         "crew_responded": 3, "crew_cited": 2}

    Approval flow: severe mission lands in 'pending-approval'. Admin
    PATCHes status='fired' which records approved_by_user_id + approved_at.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    data = request.get_json(silent=True) or {}
    roles = user.get("roles") or []

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM mission_deployments WHERE id = %s",
                (dep_id,),
            )
            r = cur.fetchone()
    if not r:
        return jsonify({"ok": False, "error": "not-found"}), 404

    is_owner = r["fired_by_user_id"] == user["id"]
    is_admin = "admin" in roles

    set_clauses = []
    params = []
    now_ms = int(time.time() * 1000)

    if "status" in data:
        new_status = (data["status"] or "").strip()
        if new_status not in ("fired", "cancelled", "completed", "pending-approval"):
            return jsonify({"ok": False, "error": "invalid-status"}), 400

        # Approval: pending-approval → fired requires a SECOND Met or admin
        # (not the same person who fired the mission). This prevents single-
        # Met severe deployments AND avoids the single-admin bottleneck.
        # Rationale: Mets are trained meteorologists. A second pair of eyes
        # from another Met is the right guardrail, not non-meteorologist admin.
        if r["status"] == "pending-approval" and new_status == "fired":
            is_other_met = ("met" in roles) and (r["fired_by_user_id"] != user["id"])
            if not (is_admin or is_other_met):
                # Same-Met self-approval, or non-Met non-admin trying to approve
                if r["fired_by_user_id"] == user["id"]:
                    return jsonify({
                        "ok": False, "error": "second-met-required",
                        "message": "Severe missions need approval from a different Met (or admin)."
                    }), 403
                return jsonify({"ok": False, "error": "met-or-admin-required"}), 403
            set_clauses.append("approved_by_user_id = %s")
            params.append(user["id"])
            set_clauses.append("approved_at = %s")
            params.append(now_ms)
            # Flag that we should dispatch SMS after the UPDATE commits.
            # We can't dispatch here because the update hasn't happened
            # yet — and if it fails, we don't want to have already SMSed.
            is_approval_transition = True
        elif not (is_owner or is_admin):
            return jsonify({"ok": False, "error": "forbidden"}), 403
        else:
            is_approval_transition = False

        set_clauses.append("status = %s")
        params.append(new_status)
        if new_status == "completed":
            set_clauses.append("completed_at = %s")
            params.append(now_ms)
    else:
        is_approval_transition = False

    if "crew_responded" in data and (is_owner or is_admin):
        try:
            set_clauses.append("crew_responded = %s")
            params.append(int(data["crew_responded"]))
        except (ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-crew-responded"}), 400

    if "crew_cited" in data and (is_owner or is_admin):
        try:
            set_clauses.append("crew_cited = %s")
            params.append(int(data["crew_cited"]))
        except (ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-crew-cited"}), 400

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-fields-to-update"}), 400

    params.append(dep_id)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                f"UPDATE mission_deployments SET {', '.join(set_clauses)} "
                f"WHERE id = %s",
                tuple(params),
            )
            cur.execute(
                "SELECT * FROM mission_deployments WHERE id = %s",
                (dep_id,),
            )
            r2 = cur.fetchone()

    # ── Item #5: dispatch SMS now that admin has approved a severe mission.
    # Same flow as initial fire for non-severe missions: find Crew in
    # polygon, send SMS, update real audience count.
    if is_approval_transition:
        try:
            real_matched, real_sent = _dispatch_mission_sms(
                r2["id"], r2["prompt"], r2["polygon_geojson"], r2["template_name"]
            )
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        "UPDATE mission_deployments SET audience_estimate = %s WHERE id = %s",
                        (real_matched, r2["id"]),
                    )
            r2 = dict(r2)
            r2["audience_estimate"] = real_matched
            print(
                f"[mission-approval] mission_id={r2['id']} approved by user_id={user['id']} "
                f"— matched={real_matched} sent={real_sent}",
                flush=True,
            )
        except Exception as e:
            print(
                f"[mission-approval] dispatch failed for mission_id={r2['id']}: {e!r}",
                flush=True,
            )

    return jsonify({
        "ok": True,
        "deployment": {
            "id": r2["id"],
            "fired_at": r2["fired_at"],
            "fired_by_name": r2["fired_by_name"],
            "template_id": r2["template_id"],
            "template_name": r2["template_name"],
            "prompt": r2["prompt"],
            "polygon_geojson": r2["polygon_geojson"],
            "polygon_label": r2["polygon_label"],
            "is_severe": r2["is_severe"],
            "status": r2["status"],
            "audience_estimate": r2["audience_estimate"],
            "crew_responded": r2["crew_responded"],
            "crew_cited": r2["crew_cited"],
            "completed_at": r2["completed_at"],
        },
    })


@app.delete("/api/v1/missions/deployments/<int:dep_id>")
def missions_delete(dep_id):
    """Delete a deployment. Owner or admin only."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT fired_by_user_id FROM mission_deployments WHERE id = %s",
                (dep_id,),
            )
            r = cur.fetchone()
    if not r:
        return jsonify({"ok": False, "error": "not-found"}), 404

    roles = user.get("roles") or []
    is_owner = r["fired_by_user_id"] == user["id"]
    is_admin = "admin" in roles
    if not (is_owner or is_admin):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "DELETE FROM mission_deployments WHERE id = %s",
                (dep_id,),
            )

    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Mission response — Crew tap SMS link to submit their observation
# (Phase 10 Item #5)
# ════════════════════════════════════════════════════════════════════
#
# When _dispatch_mission_sms sends an SMS to a Crew member, the link
# in that SMS points at /?mission=<token>. The frontend shows a response
# page; the Crew member types their observation + submits → POST to
# this endpoint with the token. We record the response, increment
# mission counters.
#
# Authentication: the response_token IS the authentication. It's
# generated per-Crew, per-mission, unguessable, and stored once in
# mission_notifications. No login required — the Crew member identifies
# themselves by possessing the token (sent only to their phone).

@app.route("/api/v1/missions/respond/<response_token>", methods=["OPTIONS"])
def _missions_respond_preflight(response_token):
    return ("", 204)


@app.get("/api/v1/missions/respond/<response_token>")
def missions_respond_get(response_token: str):
    """Return mission context for the response page.

    The frontend calls this when the Crew member opens the SMS link.
    Returns the mission prompt + template name so the page can render
    "Mission: Flag check — Look at the flag at Lebanon HS, how is it
    behaving?" with a textarea + submit.
    """
    if not response_token or len(response_token) < 10:
        return jsonify({"ok": False, "error": "invalid-token"}), 400
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT mn.id AS notification_id, mn.responded_at, mn.response_text,
                          md.id AS mission_id, md.template_name, md.prompt,
                          md.fired_by_name, md.status
                   FROM mission_notifications mn
                   JOIN mission_deployments md ON md.id = mn.mission_id
                   WHERE mn.response_token = %s""",
                (response_token,),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "not-found"}), 404
    return jsonify({
        "ok": True,
        "mission": {
            "template_name": row["template_name"],
            "prompt": row["prompt"],
            "fired_by_name": row["fired_by_name"],
            "status": row["status"],
            "already_responded": bool(row["responded_at"]),
            "previous_response": row["response_text"] or "",
        }
    })


@app.post("/api/v1/missions/respond/<response_token>")
def missions_respond_submit(response_token: str):
    """Submit a Crew response to a mission.

    Body: {"response_text": "Flag flapping pretty hard, NW direction..."}

    Idempotency: if already responded, returns the existing response
    (doesn't accept a re-submission). Crew can call submit-again with
    overwrite=true to update.
    """
    if not response_token or len(response_token) < 10:
        return jsonify({"ok": False, "error": "invalid-token"}), 400

    data = request.get_json(silent=True) or {}
    response_text = (data.get("response_text") or "").strip()
    overwrite = bool(data.get("overwrite", False))

    if not response_text:
        return jsonify({"ok": False, "error": "empty-response"}), 400
    if len(response_text) > 4000:
        return jsonify({"ok": False, "error": "response-too-long"}), 400

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, mission_id, responded_at
                   FROM mission_notifications
                   WHERE response_token = %s""",
                (response_token,),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "not-found"}), 404

    is_first_response = (row["responded_at"] is None)
    if not is_first_response and not overwrite:
        return jsonify({
            "ok": False,
            "error": "already-responded",
            "message": "You've already responded. Send ?overwrite=true to update.",
        }), 409

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE mission_notifications
                   SET response_text = %s, responded_at = %s
                   WHERE id = %s""",
                (response_text, now_ms, row["id"]),
            )
            # On first response, bump the mission's crew_responded counter.
            # On overwrite, don't double-count.
            if is_first_response:
                cur.execute(
                    """UPDATE mission_deployments
                       SET crew_responded = crew_responded + 1
                       WHERE id = %s""",
                    (row["mission_id"],),
                )

    print(
        f"[mission-respond] notification_id={row['id']} mission_id={row['mission_id']} "
        f"first_response={is_first_response}",
        flush=True,
    )

    return jsonify({"ok": True, "first_response": is_first_response})


# ════════════════════════════════════════════════════════════════════
# Crew applications — public submit + admin review (Phase 10 Admin Tools)
# ════════════════════════════════════════════════════════════════════
#
# Public-facing endpoint for the Crew register form (no auth required).
# Anyone can apply; admin approval gates whether they actually become Crew.

@app.route("/api/v1/crew/apply", methods=["OPTIONS"])
def _crew_apply_preflight():
    return ("", 204)


@app.post("/api/v1/crew/apply")
def crew_apply_submit():
    """Submit a Crew application. Public — no auth required.

    Body:
      {
        "name": "Sarah Indianapolis",
        "handle": "@sarah_indy",
        "email": "sarah@example.com",
        "phone": "317-555-0123",
        "county": "Marion County, IN",
        "mission_interests": ["storms","hail","wind"],
        "hours": "all",
        "notify": "sms"
      }

    Returns:
        200 {"ok": true, "application_id": N}
        400 invalid input (missing required, bad email, etc.)
        409 email already has a pending or approved application
    """
    data = request.get_json(silent=True) or {}

    name = (data.get("name") or "").strip()
    email = (data.get("email") or "").strip().lower()
    if not name:
        return jsonify({"ok": False, "error": "name-required"}), 400
    if not email or not is_valid_email(email):
        return jsonify({"ok": False, "error": "valid-email-required"}), 400

    handle = (data.get("handle") or "").strip() or None
    phone_raw = (data.get("phone") or "").strip()
    phone = normalize_phone(phone_raw) if phone_raw else None
    county = (data.get("county") or "").strip() or None

    interests_list = data.get("mission_interests") or []
    if isinstance(interests_list, str):
        # Accept comma-separated string too
        interests_list = [x.strip() for x in interests_list.split(",") if x.strip()]
    valid_interests = {"storms", "hail", "wind", "rain", "winter", "general"}
    mission_interests = ",".join(
        x for x in interests_list if x in valid_interests
    ) or None

    hours = (data.get("hours") or "all").strip()
    if hours not in ("all", "weekdays-day", "weekdays-evening", "weekends", "custom"):
        hours = "all"

    notify = (data.get("notify") or "sms").strip()
    if notify not in ("sms", "email", "both"):
        notify = "sms"

    now_ms = int(time.time() * 1000)

    try:
        with db() as conn:
            with conn.cursor() as cur:
                # Check for existing application
                cur.execute(
                    "SELECT id, status FROM crew_applications WHERE email = %s",
                    (email,),
                )
                existing = cur.fetchone()
                if existing:
                    if existing["status"] == "approved":
                        return jsonify({
                            "ok": False,
                            "error": "already-approved",
                            "message": "You're already a Crew member. Sign in to access your workspace.",
                        }), 409
                    if existing["status"] == "pending":
                        # Update the existing pending row rather than create a duplicate
                        cur.execute(
                            """UPDATE crew_applications
                               SET name = %s, handle = %s, phone = %s, county = %s,
                                   mission_interests = %s, hours = %s, notify = %s,
                                   updated_at = %s
                               WHERE id = %s""",
                            (name, handle, phone, county, mission_interests, hours,
                             notify, now_ms, existing["id"]),
                        )
                        return jsonify({
                            "ok": True,
                            "application_id": existing["id"],
                            "updated": True,
                        })
                    # 'rejected' — allow them to re-apply by clearing rejection
                    cur.execute(
                        """UPDATE crew_applications
                           SET status='pending', name=%s, handle=%s, phone=%s, county=%s,
                               mission_interests=%s, hours=%s, notify=%s,
                               updated_at=%s, rejection_reason=NULL,
                               reviewed_at=NULL, reviewed_by_user_id=NULL
                           WHERE id=%s""",
                        (name, handle, phone, county, mission_interests, hours,
                         notify, now_ms, existing["id"]),
                    )
                    return jsonify({
                        "ok": True,
                        "application_id": existing["id"],
                        "reapplied": True,
                    })

                # New application
                cur.execute(
                    """INSERT INTO crew_applications
                       (created_at, updated_at, status, name, handle, email, phone,
                        county, mission_interests, hours, notify)
                       VALUES (%s, %s, 'pending', %s, %s, %s, %s, %s, %s, %s, %s)
                       RETURNING id""",
                    (now_ms, now_ms, name, handle, email, phone, county,
                     mission_interests, hours, notify),
                )
                row = cur.fetchone()

        print(f"[crew-apply] new application id={row['id']} email={email}", flush=True)
        return jsonify({"ok": True, "application_id": row["id"]})
    except Exception as e:
        print(f"[crew-apply] insert failed for {email}: {e!r}", flush=True)
        return jsonify({"ok": False, "error": "internal-error"}), 500


# ════════════════════════════════════════════════════════════════════
# Admin endpoints — Crew approval queue
# ════════════════════════════════════════════════════════════════════

@app.route("/api/v1/admin/crew/applications", methods=["OPTIONS"])
def _admin_crew_apps_preflight():
    return ("", 204)


@app.get("/api/v1/admin/crew/applications")
def admin_crew_apps_list():
    """List Crew applications. Defaults to pending; ?status=all|approved|rejected
    overrides."""
    user, err = _require_admin()
    if err:
        return err

    status_filter = (request.args.get("status") or "pending").strip()
    with db() as conn:
        with conn.cursor() as cur:
            if status_filter == "all":
                cur.execute(
                    """SELECT * FROM crew_applications
                       ORDER BY created_at DESC LIMIT 100"""
                )
            else:
                cur.execute(
                    """SELECT * FROM crew_applications
                       WHERE status = %s
                       ORDER BY created_at DESC LIMIT 100""",
                    (status_filter,),
                )
            rows = cur.fetchall()

    apps = [
        {
            "id": r["id"],
            "created_at": r["created_at"],
            "status": r["status"],
            "name": r["name"],
            "handle": r["handle"],
            "email": r["email"],
            "phone": r["phone"],
            "county": r["county"],
            "mission_interests": r["mission_interests"],
            "hours": r["hours"],
            "notify": r["notify"],
            "reviewed_at": r["reviewed_at"],
            "rejection_reason": r["rejection_reason"],
        }
        for r in rows
    ]
    return jsonify({"ok": True, "applications": apps})


@app.route("/api/v1/admin/crew/applications/<int:app_id>/approve", methods=["OPTIONS"])
def _admin_crew_approve_preflight(app_id):
    return ("", 204)


@app.post("/api/v1/admin/crew/applications/<int:app_id>/approve")
def admin_crew_approve(app_id):
    """Approve a pending Crew application.

    This:
      1. Creates (or finds) a user row matching the application email
      2. Sets the user's phone if the application provided one
      3. Grants the 'crew' role
      4. Stamps the application as approved + links to created_user_id
      5. Audit log entry
      6. Sends a welcome magic-link email so they can set their password

    Returns:
        200 {"ok": true, "user_id": N, "application_id": app_id}
    """
    user, err = _require_admin()
    if err:
        return err

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM crew_applications WHERE id = %s",
                (app_id,),
            )
            app_row = cur.fetchone()
    if not app_row:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if app_row["status"] != "pending":
        return jsonify({
            "ok": False,
            "error": "not-pending",
            "message": f"Application is already {app_row['status']}.",
        }), 409

    email = app_row["email"]
    now_ms = int(time.time() * 1000)

    try:
        with db() as conn:
            # 1. Find or create user
            user_id = _get_or_create_user(email, conn)

            # 2. Fill in name + phone if user has none
            with conn.cursor() as cur:
                if app_row["name"]:
                    cur.execute(
                        """UPDATE users SET name = %s
                           WHERE id = %s AND (name IS NULL OR name = '')""",
                        (app_row["name"], user_id),
                    )
                if app_row["phone"]:
                    cur.execute(
                        "UPDATE users SET phone = %s WHERE id = %s",
                        (app_row["phone"], user_id),
                    )

                # 3. Grant crew role (idempotent)
                cur.execute(
                    """INSERT INTO user_roles (user_id, role, granted_at)
                       VALUES (%s, 'crew', %s)
                       ON CONFLICT (user_id, role) DO NOTHING""",
                    (user_id, now_ms),
                )

                # 4. Stamp the application as approved
                cur.execute(
                    """UPDATE crew_applications
                       SET status='approved', reviewed_at=%s,
                           reviewed_by_user_id=%s, created_user_id=%s,
                           updated_at=%s
                       WHERE id=%s""",
                    (now_ms, user["id"], user_id, now_ms, app_id),
                )

        # 5. Audit
        _audit_log(
            actor_user_id=user["id"],
            actor_name=user.get("name") or user.get("email"),
            action="crew.approve",
            target_type="crew_application",
            target_id=app_id,
            details={"email": email, "created_user_id": user_id},
        )

        # 6. Send welcome magic link so they can set password
        base = os.environ.get("FRONTEND_BASE_URL", "https://weathervalet.ai")
        raw_token = new_secure_token()
        token_hash = hash_token(raw_token)
        now_sec = now_ts()  # seconds — magic_link_tokens uses seconds
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO magic_link_tokens
                       (token_hash, user_id, created_at, expires_at, ip_requested)
                       VALUES (%s, %s, %s, %s, %s)""",
                    (token_hash, user_id, now_sec,
                     now_sec + MAGIC_LINK_TTL_SECONDS, "crew-approval"),
                )
        magic_link_url = f"{base}/?auth=verify&token={raw_token}&intent=new-account"
        _send_magic_link_email(email, magic_link_url, intent="new-account")

        print(f"[crew-approve] application={app_id} user={user_id} approved by admin={user['id']}", flush=True)
        return jsonify({"ok": True, "user_id": user_id, "application_id": app_id})

    except Exception as e:
        print(f"[crew-approve] FAILED application={app_id}: {e!r}", flush=True)
        return jsonify({"ok": False, "error": "internal-error"}), 500


@app.route("/api/v1/admin/crew/applications/<int:app_id>/reject", methods=["OPTIONS"])
def _admin_crew_reject_preflight(app_id):
    return ("", 204)


@app.post("/api/v1/admin/crew/applications/<int:app_id>/reject")
def admin_crew_reject(app_id):
    """Reject a pending Crew application.

    Body:
        {"reason": "Outside our coverage area"}  (optional but recommended)
    """
    user, err = _require_admin()
    if err:
        return err

    data = request.get_json(silent=True) or {}
    reason = (data.get("reason") or "").strip() or None

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id, status, email FROM crew_applications WHERE id = %s",
                (app_id,),
            )
            app_row = cur.fetchone()
    if not app_row:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if app_row["status"] != "pending":
        return jsonify({
            "ok": False,
            "error": "not-pending",
            "message": f"Application is already {app_row['status']}.",
        }), 409

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE crew_applications
                   SET status='rejected', reviewed_at=%s,
                       reviewed_by_user_id=%s, rejection_reason=%s,
                       updated_at=%s
                   WHERE id=%s""",
                (now_ms, user["id"], reason, now_ms, app_id),
            )

    _audit_log(
        actor_user_id=user["id"],
        actor_name=user.get("name") or user.get("email"),
        action="crew.reject",
        target_type="crew_application",
        target_id=app_id,
        details={"email": app_row["email"], "reason": reason},
    )

    print(f"[crew-reject] application={app_id} rejected by admin={user['id']}", flush=True)
    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Admin: Recent payments + refund (Phase 10 Admin Chunk B)
# ════════════════════════════════════════════════════════════════════
#
# NOTE: We don't add new user-list or deactivate endpoints here — those
# already exist from earlier admin work (GET /api/v1/admin/users at
# line ~6122 returns all users with roles + is_active; PATCH at ~6222
# handles deactivation via {"is_active": false}). We rely on those and
# focus this chunk on payments + audit-log endpoints which are new.
#
# Audit-log writes for user deactivation get added inside the existing
# PATCH handler (see admin_update_user).

@app.route("/api/v1/admin/payments", methods=["OPTIONS"])
def _admin_payments_preflight():
    return ("", 204)


@app.get("/api/v1/admin/payments")
def admin_payments_list():
    """List the last 50 paid/completed verification requests."""
    user, err = _require_admin()
    if err:
        return err

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, created_at, updated_at, status, tier, price_cents,
                          customer_email, customer_phone, plan_text, plan_location,
                          stripe_session_id, stripe_payment_id,
                          claimed_at, completed_at, meteorologist_verdict
                   FROM verification_requests
                   WHERE status IN ('paid','claimed','completed','refunded')
                   ORDER BY created_at DESC LIMIT 50"""
            )
            rows = cur.fetchall()

    payments = []
    for r in rows:
        payments.append({
            "request_id": r["id"],
            "created_at": r["created_at"],
            "status": r["status"],
            "tier": r["tier"],
            "price_cents": r["price_cents"],
            "customer_email": r["customer_email"],
            "customer_phone": r["customer_phone"],
            "plan_text": r["plan_text"],
            "plan_location": r["plan_location"],
            "stripe_payment_id": r["stripe_payment_id"],
            "claimed_at": r["claimed_at"],
            "completed_at": r["completed_at"],
            "verdict": r.get("meteorologist_verdict"),
        })
    return jsonify({"ok": True, "payments": payments})


@app.route("/api/v1/admin/payments/refund", methods=["OPTIONS"])
def _admin_payments_refund_preflight():
    return ("", 204)


@app.post("/api/v1/admin/payments/refund")
def admin_payments_refund():
    """Issue a Stripe refund for a verification payment.

    Body:
      {"request_id": 42, "reason": "Met missed SLA", "amount_cents": null}
        - reason is optional but recorded for the audit log
        - amount_cents null = full refund; otherwise partial

    The actual refund goes to Stripe via stripe.Refund.create. We update
    the verification_requests row's status to 'refunded' so the same
    request can't be refunded twice.
    """
    actor, err = _require_admin()
    if err:
        return err

    if stripe is None or not STRIPE_SECRET_KEY:
        return jsonify({"ok": False, "error": "stripe-not-configured"}), 503

    data = request.get_json(silent=True) or {}
    try:
        request_id = int(data.get("request_id") or 0)
    except (ValueError, TypeError):
        request_id = 0
    if not request_id:
        return jsonify({"ok": False, "error": "missing-request-id"}), 400

    reason = (data.get("reason") or "").strip() or None
    amount_cents = data.get("amount_cents")
    if amount_cents is not None:
        try:
            amount_cents = int(amount_cents)
        except (ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-amount"}), 400

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, status, price_cents, stripe_payment_id,
                          customer_email, customer_phone
                   FROM verification_requests WHERE id = %s""",
                (request_id,),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if row["status"] == "refunded":
        return jsonify({"ok": False, "error": "already-refunded"}), 409
    if not row["stripe_payment_id"]:
        return jsonify({"ok": False, "error": "no-stripe-payment-id"}), 400

    # Stripe Refund API. payment_intent OR charge — our stripe_payment_id
    # was populated as session.payment_intent OR session.id (in _mark_paid_and_notify),
    # so try payment_intent first, fall back to charge.
    refund_params = {"payment_intent": row["stripe_payment_id"]}
    if amount_cents is not None and amount_cents > 0:
        refund_params["amount"] = amount_cents

    try:
        refund = stripe.Refund.create(**refund_params)
    except Exception as e:
        # Try as charge if payment_intent failed
        try:
            refund_params = {"charge": row["stripe_payment_id"]}
            if amount_cents is not None and amount_cents > 0:
                refund_params["amount"] = amount_cents
            refund = stripe.Refund.create(**refund_params)
        except Exception as e2:
            print(f"[admin-refund] FAILED request={request_id}: {e!r} / {e2!r}", flush=True)
            return jsonify({
                "ok": False,
                "error": "stripe-error",
                "message": f"Stripe refused the refund: {str(e2)[:200]}",
            }), 500

    # Mark request as refunded so we don't double-refund
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "UPDATE verification_requests SET status='refunded', updated_at=%s WHERE id=%s",
                (int(time.time()), request_id),
            )

    _audit_log(
        actor_user_id=actor["id"],
        actor_name=actor.get("name") or actor.get("email"),
        action="payment.refund",
        target_type="verification_request",
        target_id=request_id,
        details={
            "stripe_refund_id": getattr(refund, "id", None),
            "amount_cents": amount_cents if amount_cents else row["price_cents"],
            "reason": reason,
            "customer_email": row["customer_email"],
        },
    )

    # Notify customer by SMS (best effort)
    try:
        if row["customer_phone"]:
            send_sms(
                row["customer_phone"],
                "WeatherValet: Your $19 review has been refunded. "
                "Please allow 5-10 business days for the funds to appear.",
            )
    except Exception:
        pass

    print(f"[admin-refund] request={request_id} refunded by admin={actor['id']}", flush=True)
    return jsonify({
        "ok": True,
        "refund_id": getattr(refund, "id", None),
        "request_id": request_id,
    })


# ════════════════════════════════════════════════════════════════════
# Admin: Audit log read (Phase 10 Admin Chunk B)
# ════════════════════════════════════════════════════════════════════

@app.route("/api/v1/admin/audit-log", methods=["OPTIONS"])
def _admin_audit_log_preflight():
    return ("", 204)


@app.get("/api/v1/admin/audit-log")
def admin_audit_log_list():
    """Paginated audit log. Newest first.

    Query params:
      ?limit=<n>  default 50, max 200
      ?before=<created_at>  cursor for pagination (ms timestamp)
      ?action=<prefix>  optional action filter (e.g. 'crew.' matches all crew actions)
    """
    user, err = _require_admin()
    if err:
        return err

    try:
        limit = min(int(request.args.get("limit") or 50), 200)
    except (ValueError, TypeError):
        limit = 50

    before = request.args.get("before")
    action_prefix = (request.args.get("action") or "").strip()

    where = []
    params: list = []
    if before:
        try:
            where.append("created_at < %s")
            params.append(int(before))
        except (ValueError, TypeError):
            pass
    if action_prefix:
        where.append("action LIKE %s")
        params.append(action_prefix + "%")

    where_sql = ("WHERE " + " AND ".join(where)) if where else ""
    sql = f"""
        SELECT id, actor_user_id, actor_name, action,
               target_type, target_id, details_json, created_at
        FROM admin_audit_log
        {where_sql}
        ORDER BY created_at DESC LIMIT %s
    """
    params.append(limit)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(sql, tuple(params))
            rows = cur.fetchall()

    entries = []
    for r in rows:
        details = None
        if r["details_json"]:
            try:
                details = json.loads(r["details_json"])
            except (ValueError, TypeError):
                details = {"_unparsed": r["details_json"][:200]}
        entries.append({
            "id": r["id"],
            "actor_user_id": r["actor_user_id"],
            "actor_name": r.get("actor_name") or "",
            "action": r["action"],
            "target_type": r.get("target_type"),
            "target_id": r.get("target_id"),
            "details": details,
            "created_at": r["created_at"],
        })

    return jsonify({"ok": True, "entries": entries})


# ════════════════════════════════════════════════════════════════════
# Pro-tier brief drafts (Phase 10 Item #3 Chunk B)
# ════════════════════════════════════════════════════════════════════
#
# Met workspace surface: list pending drafts, claim, edit, send.
# A draft is created by the scheduler when a Pro-tier subscriber's
# brief window opens. Met reviews the AI draft, edits, sends. Sending
# pushes the brief through send_sms + _send_brief_email and records a
# brief_history row (is_met_touched=TRUE).

@app.route("/api/v1/met/pro-briefs", methods=["OPTIONS"])
def _met_pro_briefs_preflight():
    return ("", 204)


@app.get("/api/v1/met/pro-briefs")
def met_pro_briefs_list():
    """List pending + recently-sent pro brief drafts for the Met workspace.

    Met sees all drafts (single-Met operation for launch). Admin sees same.

    Returns drafts with subscriber email/name attached for context,
    sorted: pending-review first (oldest first to fight the queue),
    then claimed (by anyone), then recently sent.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT d.*, u.email AS subscriber_email, u.name AS subscriber_name,
                          u.phone AS subscriber_phone
                   FROM pro_brief_drafts d
                   JOIN users u ON u.id = d.user_id
                   WHERE d.status IN ('pending-review', 'claimed')
                      OR (d.status = 'sent' AND d.sent_at >= %s)
                   ORDER BY
                     CASE d.status
                       WHEN 'pending-review' THEN 0
                       WHEN 'claimed' THEN 1
                       ELSE 2
                     END,
                     d.created_at ASC""",
                (int(time.time() * 1000) - 24 * 60 * 60 * 1000,),  # show today's sent for 24h
            )
            rows = cur.fetchall()

    drafts = [
        {
            "id": r["id"],
            "user_id": r["user_id"],
            "subscriber_email": r["subscriber_email"],
            "subscriber_name": r.get("subscriber_name") or "",
            "subscriber_phone": r.get("subscriber_phone") or "",
            "user_tier": r["user_tier"],
            "location_label": r["location_label"],
            "channels": r["channels"],
            "created_at": r["created_at"],
            "window_end_at": r["window_end_at"],
            "status": r["status"],
            "ai_verdict": r["ai_verdict"],
            "ai_snippet": r["ai_snippet"],
            "ai_body": r["ai_body"],
            "met_verdict": r["met_verdict"],
            "met_snippet": r["met_snippet"],
            "met_body": r["met_body"],
            "met_notes": r["met_notes"],
            "claimed_at": r["claimed_at"],
            "claimed_by_user_id": r["claimed_by_user_id"],
            "sent_at": r["sent_at"],
            "sent_by_name": r["sent_by_name"],
            "final_verdict": r["final_verdict"],
        }
        for r in rows
    ]
    return jsonify({"ok": True, "drafts": drafts})


@app.route("/api/v1/met/pro-briefs/<int:draft_id>", methods=["OPTIONS"])
def _met_pro_brief_id_preflight(draft_id):
    return ("", 204)


@app.post("/api/v1/met/pro-briefs/<int:draft_id>/claim")
def met_pro_brief_claim(draft_id):
    """Claim a draft for editing. Sets claimed_at + claimed_by_user_id.
    Idempotent if already claimed by current Met.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id, status, claimed_by_user_id FROM pro_brief_drafts WHERE id = %s",
                (draft_id,),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if row["status"] not in ("pending-review", "claimed"):
        return jsonify({"ok": False, "error": "not-claimable", "status": row["status"]}), 409

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE pro_brief_drafts
                   SET status = 'claimed', claimed_at = COALESCE(claimed_at, %s),
                       claimed_by_user_id = %s
                   WHERE id = %s""",
                (now_ms, user["id"], draft_id),
            )
    return jsonify({"ok": True})


@app.patch("/api/v1/met/pro-briefs/<int:draft_id>")
def met_pro_brief_update(draft_id):
    """Edit met_verdict / met_snippet / met_body / met_notes. Does NOT send."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    set_clauses = []
    params: list = []

    if "met_verdict" in data:
        v = (data["met_verdict"] or "").strip()
        if v not in ("clear", "caution", "risk"):
            return jsonify({"ok": False, "error": "invalid-verdict"}), 400
        set_clauses.append("met_verdict = %s")
        params.append(v)
    if "met_snippet" in data:
        s = (data["met_snippet"] or "").strip()
        if len(s) > 280:
            return jsonify({"ok": False, "error": "snippet-too-long"}), 400
        set_clauses.append("met_snippet = %s")
        params.append(s)
    if "met_body" in data:
        b = (data["met_body"] or "").strip()
        if len(b) > 4000:
            return jsonify({"ok": False, "error": "body-too-long"}), 400
        set_clauses.append("met_body = %s")
        params.append(b)
    if "met_notes" in data:
        n = (data["met_notes"] or "").strip()
        if len(n) > 2000:
            return jsonify({"ok": False, "error": "notes-too-long"}), 400
        set_clauses.append("met_notes = %s")
        params.append(n)

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-fields-to-update"}), 400

    params.append(draft_id)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                f"UPDATE pro_brief_drafts SET {', '.join(set_clauses)} "
                f"WHERE id = %s AND status IN ('pending-review','claimed')",
                tuple(params),
            )
            if cur.rowcount == 0:
                return jsonify({"ok": False, "error": "not-editable"}), 409

    return jsonify({"ok": True})


@app.post("/api/v1/met/pro-briefs/<int:draft_id>/send")
def met_pro_brief_send(draft_id):
    """Send the Met's edited brief to the subscriber. Marks status='sent',
    records brief_history row (is_met_touched=TRUE), dispatches via SMS+email.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT d.*, u.email AS sub_email, u.phone AS sub_phone
                   FROM pro_brief_drafts d
                   JOIN users u ON u.id = d.user_id
                   WHERE d.id = %s""",
                (draft_id,),
            )
            row = cur.fetchone()

    if not row:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if row["status"] not in ("pending-review", "claimed"):
        return jsonify({"ok": False, "error": "already-sent-or-expired", "status": row["status"]}), 409

    # Use met_* fields (which default to ai_* values from scheduler).
    final_verdict = (row["met_verdict"] or row["ai_verdict"] or "caution").strip()
    final_snippet = (row["met_snippet"] or row["ai_snippet"] or "").strip()
    final_body = (row["met_body"] or row["ai_body"] or "").strip()

    if not final_body:
        return jsonify({"ok": False, "error": "empty-body"}), 400

    # Dispatch through the channels the subscriber configured (snapshot)
    channels = [ch for ch in (row["channels"] or "").split(",") if ch]
    channels_used = []
    any_success = False
    met_name = user.get("name") or "Your meteorologist"
    location_label = row["location_label"] or "your location"

    # Add Met signature to the body so the subscriber knows it was reviewed
    body_with_sig = final_body + f"\n\n— {met_name}, WeatherValet"

    for ch in channels:
        if ch == "sms" and row["sub_phone"]:
            sms_text = (final_snippet or final_body[:140]) + f"\n— {met_name}\nFull: {body_with_sig[:900]}"
            try:
                if send_sms(row["sub_phone"], sms_text):
                    channels_used.append("sms")
                    any_success = True
            except Exception as e:
                print(f"[pro-brief-send] SMS failed user={row['user_id']}: {e}", flush=True)
        elif ch == "email" and row["sub_email"]:
            subject = f"Your WeatherValet brief — {location_label}"
            try:
                if _send_brief_email(row["sub_email"], subject, body_with_sig):
                    channels_used.append("email")
                    any_success = True
            except Exception as e:
                print(f"[pro-brief-send] email failed user={row['user_id']}: {e}", flush=True)

    delivery_status = "sent" if any_success else "failed"
    now_ms = int(time.time() * 1000)

    # Write brief_history row + capture id, then update the draft
    history_id = None
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO brief_history
                       (user_id, brief_type, delivered_at, verdict, snippet,
                        full_body, delivery_status, channels_used,
                        is_met_touched, met_name)
                       VALUES (%s, %s, %s, %s, %s, %s, %s, %s, TRUE, %s)
                       RETURNING id""",
                    (row["user_id"], row["brief_type"], now_ms, final_verdict,
                     final_snippet or final_body[:140], body_with_sig,
                     delivery_status, ",".join(channels_used), met_name),
                )
                history_id = cur.fetchone()["id"]
    except Exception as e:
        print(f"[pro-brief-send] history insert failed: {e}", flush=True)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE pro_brief_drafts
                   SET status = 'sent', sent_at = %s, sent_by_user_id = %s,
                       sent_by_name = %s, final_verdict = %s, final_body = %s,
                       history_id = %s
                   WHERE id = %s""",
                (now_ms, user["id"], met_name, final_verdict, body_with_sig,
                 history_id, draft_id),
            )

    print(
        f"[pro-brief-send] draft={draft_id} sent by met={user['id']} "
        f"channels={channels_used} status={delivery_status}",
        flush=True,
    )

    # Phase 11 Phase 2 (May 17): Mark today's daily_brief_task as sent
    # for this subscriber. Best effort — task tracking is separate
    # from the actual send.
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT user_id FROM pro_brief_drafts WHERE id = %s""",
                    (draft_id,),
                )
                drow = cur.fetchone()
                if drow and drow.get("user_id"):
                    subscriber_id = drow["user_id"]
                    # Get subscriber's local date
                    cur.execute(
                        """SELECT daily_brief_timezone
                           FROM subscriber_coverage WHERE user_id = %s""",
                        (subscriber_id,),
                    )
                    cov_row = cur.fetchone()
                    tz_name = (cov_row or {}).get("daily_brief_timezone") or "America/New_York"
                    try:
                        sub_tz = ZoneInfo(tz_name)
                    except Exception:
                        sub_tz = ZoneInfo("America/New_York")
                    local_date_str = datetime.now(sub_tz).strftime("%Y-%m-%d")
                    cur.execute(
                        """UPDATE daily_brief_tasks
                           SET sent_at_ms = %s, status = 'sent'
                           WHERE subscriber_user_id = %s
                             AND task_date = %s
                             AND status != 'sent'""",
                        (now_ms, subscriber_id, local_date_str),
                    )
    except Exception as e:
        print(f"[pro-brief-send] task mark-sent failed (non-fatal): {e}", flush=True)

    return jsonify({
        "ok": True,
        "channels_used": channels_used,
        "delivery_status": delivery_status,
        "history_id": history_id,
    })


# ════════════════════════════════════════════════════════════════════
# NWS severe alert page review (Phase 10 Item #7)
# ════════════════════════════════════════════════════════════════════
#
# Met taps the SMS link, lands on /?nws-page=<token>. Frontend calls
# GET to load context. Met decides:
#   - Confirm → POST /confirm with custom subscriber message →
#     subscribers get SMS + email
#   - Dismiss → POST /dismiss (false alarm / not actionable)
#
# Auth model is the same as the Crew mission response page: the token
# IS the authentication. It was sent only to the Met's phone via SMS.

@app.route("/api/v1/nws/page/<response_token>", methods=["OPTIONS"])
def _nws_page_preflight(response_token):
    return ("", 204)


@app.get("/api/v1/nws/page/<response_token>")
def nws_page_get(response_token: str):
    """Return the alert details + list of affected subscribers for the
    Met to review. No auth required — the token is the auth.
    """
    if not response_token or len(response_token) < 10:
        return jsonify({"ok": False, "error": "invalid-token"}), 400

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT * FROM nws_alert_pages WHERE response_token = %s""",
                (response_token,),
            )
            page = cur.fetchone()
    if not page:
        return jsonify({"ok": False, "error": "not-found"}), 404

    # Resolve affected user info from the CSV
    affected_user_ids = []
    if page["affected_user_ids"]:
        try:
            affected_user_ids = [
                int(x) for x in page["affected_user_ids"].split(",") if x.strip()
            ]
        except ValueError:
            affected_user_ids = []

    subscribers = []
    if affected_user_ids:
        placeholders = ",".join(["%s"] * len(affected_user_ids))
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    f"""SELECT u.id, u.name, u.email, u.phone,
                              u.subscription_tier,
                              loc.label AS loc_label
                       FROM users u
                       LEFT JOIN saved_locations loc
                         ON loc.user_id = u.id AND loc.is_primary = TRUE
                       WHERE u.id IN ({placeholders})""",
                    tuple(affected_user_ids),
                )
                rows = cur.fetchall()
        for r in rows:
            subscribers.append({
                "id": r["id"],
                "name": r.get("name") or "",
                "email": r["email"],
                "phone": r.get("phone") or "",
                "tier": r["subscription_tier"],
                "location": r.get("loc_label") or "",
            })

    return jsonify({
        "ok": True,
        "page": {
            "id": page["id"],
            "created_at": page["created_at"],
            "event": page["event"],
            "severity": page["severity"],
            "headline": page["headline"],
            "description": page["description"],
            "instruction": page["instruction"],
            "area_desc": page["area_desc"],
            "expires_at": page["expires_at"],
            "status": page["status"],
            "reviewed_at": page["reviewed_at"],
            "reviewed_by_name": page["reviewed_by_name"],
            "subscriber_message": page["subscriber_message"],
            "subscribers_notified": page["subscribers_notified"],
        },
        "subscribers": subscribers,
    })


@app.post("/api/v1/nws/page/<response_token>/confirm")
def nws_page_confirm(response_token: str):
    """Met confirms the alert and sends a custom message to all affected
    Pro subscribers via SMS + email.

    Body:
      {
        "message": "Tornado Warning active for Lebanon area until 4:30pm. Get to interior shelter NOW.",
        "met_name": "Michael Reynolds"  (optional override; defaults to "On-duty Met")
      }

    Auth: requires the response_token in URL. The Met doesn't need to be
    logged in (they tapped the SMS link from their phone), but we use
    their logged-in name if available.
    """
    if not response_token or len(response_token) < 10:
        return jsonify({"ok": False, "error": "invalid-token"}), 400

    data = request.get_json(silent=True) or {}
    message = (data.get("message") or "").strip()
    if not message:
        return jsonify({"ok": False, "error": "message-required"}), 400
    if len(message) > 1000:
        return jsonify({"ok": False, "error": "message-too-long"}), 400

    # If signed in, use their real name + user_id for audit
    actor = _get_current_user()
    met_name = (
        (data.get("met_name") or "").strip()
        or (actor.get("name") if actor else None)
        or "On-duty meteorologist"
    )
    met_user_id = actor["id"] if actor else None

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM nws_alert_pages WHERE response_token = %s",
                (response_token,),
            )
            page = cur.fetchone()
    if not page:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if page["status"] not in ("paged",):
        return jsonify({
            "ok": False,
            "error": "already-handled",
            "status": page["status"],
        }), 409

    # Resolve affected subscribers
    affected_user_ids = []
    if page["affected_user_ids"]:
        try:
            affected_user_ids = [
                int(x) for x in page["affected_user_ids"].split(",") if x.strip()
            ]
        except ValueError:
            pass

    if not affected_user_ids:
        # Nothing to send — mark confirmed but with 0 sent
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """UPDATE nws_alert_pages
                       SET status = 'confirmed', reviewed_at = %s,
                           reviewed_by_user_id = %s, reviewed_by_name = %s,
                           subscriber_message = %s, subscribers_notified = 0
                       WHERE id = %s""",
                    (int(time.time() * 1000), met_user_id, met_name, message, page["id"]),
                )
        return jsonify({"ok": True, "subscribers_notified": 0})

    # Fetch contact info for each affected user
    placeholders = ",".join(["%s"] * len(affected_user_ids))
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                f"""SELECT u.id, u.name, u.email, u.phone
                   FROM users u
                   WHERE u.id IN ({placeholders}) AND u.is_active = TRUE""",
                tuple(affected_user_ids),
            )
            subs = cur.fetchall()

    # Compose the SMS body (160-char-friendly) and the email body
    sms_body = (
        f"WeatherValet ALERT ({page['event']}): {message}\n"
        f"\u2014 {met_name}\n"
        f"Reply STOP to opt out."
    )
    email_subject = f"WeatherValet alert: {page['event']}"
    email_body = (
        f"{page['event']}\n\n"
        f"{message}\n\n"
        f"— {met_name}\n"
        f"WeatherValet on-duty meteorologist\n\n"
        f"Affected area: {page['area_desc']}\n"
        f"NWS headline: {page['headline']}\n"
    )

    sent_count = 0
    for s in subs:
        any_channel = False
        if s.get("phone"):
            try:
                if send_sms(s["phone"], sms_body):
                    any_channel = True
            except Exception as e:
                print(f"[nws-confirm] SMS failed user={s['id']}: {e}", flush=True)
        if s.get("email"):
            try:
                if _send_brief_email(s["email"], email_subject, email_body):
                    any_channel = True
            except Exception as e:
                print(f"[nws-confirm] email failed user={s['id']}: {e}", flush=True)
        if any_channel:
            sent_count += 1

    # Mark page as confirmed
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE nws_alert_pages
                   SET status = 'confirmed', reviewed_at = %s,
                       reviewed_by_user_id = %s, reviewed_by_name = %s,
                       subscriber_message = %s, subscribers_notified = %s
                   WHERE id = %s""",
                (int(time.time() * 1000), met_user_id, met_name,
                 message, sent_count, page["id"]),
            )

    # Audit log if we have a logged-in actor
    if actor:
        try:
            _audit_log(
                actor_user_id=met_user_id, actor_name=met_name,
                action="nws.confirm", target_type="nws_alert_page",
                target_id=page["id"],
                details={
                    "event": page["event"],
                    "subscribers_notified": sent_count,
                    "affected_total": len(affected_user_ids),
                },
            )
        except Exception:
            pass

    print(
        f"[nws-confirm] page_id={page['id']} confirmed by met={met_name} "
        f"sent={sent_count}/{len(affected_user_ids)}",
        flush=True,
    )
    return jsonify({"ok": True, "subscribers_notified": sent_count})


@app.post("/api/v1/nws/page/<response_token>/dismiss")
def nws_page_dismiss(response_token: str):
    """Met dismisses the alert (false alarm, already-known, out-of-scope).
    No subscriber notification.

    Body:
      {"reason": "Already escalated by NWS via Wireless Emergency Alerts"}
    """
    if not response_token or len(response_token) < 10:
        return jsonify({"ok": False, "error": "invalid-token"}), 400

    data = request.get_json(silent=True) or {}
    reason = (data.get("reason") or "").strip() or None

    actor = _get_current_user()
    met_name = (
        (actor.get("name") if actor else None)
        or "On-duty meteorologist"
    )
    met_user_id = actor["id"] if actor else None

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id, status FROM nws_alert_pages WHERE response_token = %s",
                (response_token,),
            )
            page = cur.fetchone()
    if not page:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if page["status"] not in ("paged",):
        return jsonify({
            "ok": False,
            "error": "already-handled",
            "status": page["status"],
        }), 409

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE nws_alert_pages
                   SET status = 'dismissed', reviewed_at = %s,
                       reviewed_by_user_id = %s, reviewed_by_name = %s,
                       subscriber_message = %s
                   WHERE id = %s""",
                (int(time.time() * 1000), met_user_id, met_name,
                 reason, page["id"]),
            )

    if actor:
        try:
            _audit_log(
                actor_user_id=met_user_id, actor_name=met_name,
                action="nws.dismiss", target_type="nws_alert_page",
                target_id=page["id"],
                details={"reason": reason},
            )
        except Exception:
            pass

    print(f"[nws-dismiss] page_id={page['id']} dismissed by met={met_name}", flush=True)
    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# Pro Threads — Met<>Subscriber DMs (Phase 10)
# ════════════════════════════════════════════════════════════════════
#
# Subscriber endpoints (require subscriber role + Pro tier):
#   GET  /api/v1/me/thread                    — get my thread + recent messages
#   POST /api/v1/me/thread/messages           — send a message
#   POST /api/v1/me/thread/mark-read          — reset my unread counter
#
# Met endpoints (require met or admin role):
#   GET  /api/v1/met/threads                  — list all threads (queue)
#   GET  /api/v1/met/threads/<id>             — get one thread + messages
#   POST /api/v1/met/threads/<id>/messages    — send a message
#   POST /api/v1/met/threads/<id>/mark-read   — reset Met's unread counter

# ─── Subscriber side ────────────────────────────────────────────────

def _get_or_create_thread_for_subscriber(user_id: int):
    """Find or create the single thread for a subscriber. Returns the
    thread row. Idempotent — same subscriber always gets same thread."""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM pro_threads WHERE subscriber_user_id = %s",
                (user_id,),
            )
            row = cur.fetchone()
            if row:
                return row
            cur.execute(
                """INSERT INTO pro_threads (subscriber_user_id, created_at)
                   VALUES (%s, %s) RETURNING *""",
                (user_id, int(time.time() * 1000)),
            )
            return cur.fetchone()


def _is_pro_subscriber(user: dict) -> bool:
    """True if the user is a Pro-tier subscriber. Pro Threads is a Pro
    feature; Hobbyists can't access it."""
    if not user:
        return False
    if "subscriber" not in (user.get("roles") or []):
        return False
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT subscription_tier FROM users WHERE id = %s",
                (user["id"],),
            )
            row = cur.fetchone()
    tier = (row or {}).get("subscription_tier") or ""
    return tier in ("pro_single", "pro_multi", "pro_enterprise")


@app.route("/api/v1/me/thread", methods=["OPTIONS"])
def _me_thread_preflight():
    return ("", 204)


@app.get("/api/v1/me/thread")
def me_thread_get():
    """Return the subscriber's thread + last 50 messages."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if not _is_pro_subscriber(user):
        return jsonify({
            "ok": False,
            "error": "pro-tier-required",
            "message": "Pro Threads is available on Pro Single, Pro Multi, and Pro Enterprise plans.",
        }), 403

    thread = _get_or_create_thread_for_subscriber(user["id"])

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, created_at, sender_role, sender_name, body
                   FROM pro_thread_messages
                   WHERE thread_id = %s
                   ORDER BY created_at DESC LIMIT 50""",
                (thread["id"],),
            )
            recent = cur.fetchall()

    # Reverse so frontend gets oldest-first (chronological reading order)
    messages = [
        {
            "id": m["id"],
            "created_at": m["created_at"],
            "sender_role": m["sender_role"],
            "sender_name": m["sender_name"],
            "body": m["body"],
        }
        for m in reversed(recent)
    ]

    return jsonify({
        "ok": True,
        "thread": {
            "id": thread["id"],
            "created_at": thread["created_at"],
            "last_message_at": thread["last_message_at"],
            "unread_for_subscriber": thread["unread_for_subscriber"],
        },
        "messages": messages,
    })


@app.post("/api/v1/me/thread/messages")
def me_thread_send():
    """Subscriber sends a message. Pages the Met via SMS so they know."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if not _is_pro_subscriber(user):
        return jsonify({"ok": False, "error": "pro-tier-required"}), 403

    data = request.get_json(silent=True) or {}
    body = (data.get("body") or "").strip()
    if not body:
        return jsonify({"ok": False, "error": "empty-message"}), 400
    if len(body) > 4000:
        return jsonify({"ok": False, "error": "message-too-long"}), 400

    thread = _get_or_create_thread_for_subscriber(user["id"])
    sender_name = user.get("name") or (user.get("email") or "").split("@")[0]
    now_ms = int(time.time() * 1000)
    preview = body[:120]

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO pro_thread_messages
                   (thread_id, created_at, sender_role, sender_user_id,
                    sender_name, body)
                   VALUES (%s, %s, 'subscriber', %s, %s, %s)
                   RETURNING id""",
                (thread["id"], now_ms, user["id"], sender_name, body),
            )
            msg_id = cur.fetchone()["id"]
            cur.execute(
                """UPDATE pro_threads
                   SET last_message_at = %s,
                       last_message_preview = %s,
                       last_message_from = 'subscriber',
                       unread_for_met = unread_for_met + 1
                   WHERE id = %s""",
                (now_ms, preview, thread["id"]),
            )

    # Page the on-duty Met by SMS (fire-and-forget)
    try:
        if METEOROLOGIST_PHONE:
            base = os.environ.get("FRONTEND_BASE_URL", "https://weathervalet.ai").rstrip("/")
            sms_body = (
                f"WV Pro Thread from {sender_name}:\n"
                f"{preview}\n\n"
                f"Reply in workspace: {base}/?screen=met"
            )
            send_sms(METEOROLOGIST_PHONE, sms_body)
    except Exception as e:
        print(f"[pro-thread] Met SMS notify failed: {e}", flush=True)

    return jsonify({
        "ok": True,
        "message_id": msg_id,
        "created_at": now_ms,
    })


@app.post("/api/v1/me/thread/mark-read")
def me_thread_mark_read():
    """Subscriber acknowledges they've read the Met's messages.
    Resets their unread counter to 0."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if not _is_pro_subscriber(user):
        return jsonify({"ok": False, "error": "pro-tier-required"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE pro_threads
                   SET unread_for_subscriber = 0
                   WHERE subscriber_user_id = %s""",
                (user["id"],),
            )

    return jsonify({"ok": True})


# ─── Met side ───────────────────────────────────────────────────────

@app.route("/api/v1/met/threads", methods=["OPTIONS"])
def _met_threads_preflight():
    return ("", 204)


@app.get("/api/v1/met/threads")
def met_threads_list():
    """List all Pro Threads, sorted by most recent activity. Met workspace
    surface — Met sees the queue of conversations.

    Unread threads (unread_for_met > 0) sort to the top regardless of
    last message time. Within each group, most recent first.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT t.*, u.email AS subscriber_email, u.name AS subscriber_name,
                          u.subscription_tier AS subscriber_tier
                   FROM pro_threads t
                   JOIN users u ON u.id = t.subscriber_user_id
                   WHERE u.is_active = TRUE
                     AND u.subscription_tier IN ('pro_single','pro_multi','pro_enterprise')
                   ORDER BY
                     CASE WHEN t.unread_for_met > 0 THEN 0 ELSE 1 END,
                     COALESCE(t.last_message_at, t.created_at) DESC
                   LIMIT 100"""
            )
            rows = cur.fetchall()

    threads = [
        {
            "id": r["id"],
            "subscriber_user_id": r["subscriber_user_id"],
            "subscriber_email": r["subscriber_email"],
            "subscriber_name": r.get("subscriber_name") or "",
            "subscriber_tier": r.get("subscriber_tier"),
            "created_at": r["created_at"],
            "last_message_at": r["last_message_at"],
            "last_message_preview": r["last_message_preview"],
            "last_message_from": r["last_message_from"],
            "unread_for_met": r["unread_for_met"],
        }
        for r in rows
    ]
    return jsonify({"ok": True, "threads": threads})


@app.route("/api/v1/met/threads/<int:thread_id>", methods=["OPTIONS"])
def _met_thread_id_preflight(thread_id):
    return ("", 204)


@app.get("/api/v1/met/threads/<int:thread_id>")
def met_thread_get(thread_id):
    """Met opens a thread — returns thread + last 100 messages."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT t.*, u.email AS subscriber_email, u.name AS subscriber_name,
                          u.phone AS subscriber_phone,
                          u.subscription_tier AS subscriber_tier
                   FROM pro_threads t
                   JOIN users u ON u.id = t.subscriber_user_id
                   WHERE t.id = %s""",
                (thread_id,),
            )
            thread = cur.fetchone()
    if not thread:
        return jsonify({"ok": False, "error": "not-found"}), 404

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, created_at, sender_role, sender_name, body
                   FROM pro_thread_messages
                   WHERE thread_id = %s
                   ORDER BY created_at DESC LIMIT 100""",
                (thread_id,),
            )
            recent = cur.fetchall()

    messages = [
        {
            "id": m["id"],
            "created_at": m["created_at"],
            "sender_role": m["sender_role"],
            "sender_name": m["sender_name"],
            "body": m["body"],
        }
        for m in reversed(recent)
    ]

    return jsonify({
        "ok": True,
        "thread": {
            "id": thread["id"],
            "subscriber_user_id": thread["subscriber_user_id"],
            "subscriber_email": thread["subscriber_email"],
            "subscriber_name": thread.get("subscriber_name") or "",
            "subscriber_phone": thread.get("subscriber_phone") or "",
            "subscriber_tier": thread.get("subscriber_tier"),
            "unread_for_met": thread["unread_for_met"],
        },
        "messages": messages,
    })


@app.post("/api/v1/met/threads/<int:thread_id>/messages")
def met_thread_send(thread_id):
    """Met replies to a thread. Notifies subscriber by SMS if they have a phone."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    body = (data.get("body") or "").strip()
    if not body:
        return jsonify({"ok": False, "error": "empty-message"}), 400
    if len(body) > 4000:
        return jsonify({"ok": False, "error": "message-too-long"}), 400

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT t.id, t.subscriber_user_id, u.phone AS sub_phone
                   FROM pro_threads t
                   JOIN users u ON u.id = t.subscriber_user_id
                   WHERE t.id = %s""",
                (thread_id,),
            )
            thread = cur.fetchone()
    if not thread:
        return jsonify({"ok": False, "error": "not-found"}), 404

    sender_name = user.get("name") or "Your meteorologist"
    now_ms = int(time.time() * 1000)
    preview = body[:120]

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO pro_thread_messages
                   (thread_id, created_at, sender_role, sender_user_id,
                    sender_name, body)
                   VALUES (%s, %s, 'met', %s, %s, %s)
                   RETURNING id""",
                (thread_id, now_ms, user["id"], sender_name, body),
            )
            msg_id = cur.fetchone()["id"]
            cur.execute(
                """UPDATE pro_threads
                   SET last_message_at = %s,
                       last_message_preview = %s,
                       last_message_from = 'met',
                       unread_for_subscriber = unread_for_subscriber + 1
                   WHERE id = %s""",
                (now_ms, preview, thread_id),
            )

    # Notify subscriber by SMS so they know to check
    try:
        if thread.get("sub_phone"):
            base = os.environ.get("FRONTEND_BASE_URL", "https://weathervalet.ai").rstrip("/")
            sms_body = (
                f"WeatherValet: {sender_name} replied to your thread.\n"
                f"{preview}\n\n"
                f"View: {base}/?portal=threads"
            )
            send_sms(thread["sub_phone"], sms_body)
    except Exception as e:
        print(f"[pro-thread] subscriber SMS notify failed: {e}", flush=True)

    return jsonify({
        "ok": True,
        "message_id": msg_id,
        "created_at": now_ms,
    })


@app.post("/api/v1/met/threads/<int:thread_id>/mark-read")
def met_thread_mark_read(thread_id):
    """Met acknowledges they've read the subscriber's messages. Resets
    Met's unread counter for this thread to 0."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "UPDATE pro_threads SET unread_for_met = 0 WHERE id = %s",
                (thread_id,),
            )

    return jsonify({"ok": True})


# ════════════════════════════════════════════════════════════════════
# ════════════════════════════════════════════════════════════════════
# Met-initiated Pro Threads — Met opens a new conversation
# ════════════════════════════════════════════════════════════════════
#
# Subscriber-initiated threads already work. This adds the inverse:
# Met sees a Pro subscriber's situation, wants to proactively message
# (e.g. cell approaching the roofer's location, advance heads-up before
# severe weather hits).
#
# Two endpoints:
#   GET  /api/v1/met/pro-subscribers — list Pro subscribers for picker UI
#   POST /api/v1/met/threads/new      — open a thread with a chosen subscriber
#                                        (idempotent: if thread already exists,
#                                        returns existing thread_id)
#
# After creating, the existing POST /api/v1/met/threads/<id>/messages
# endpoint handles the actual message send.

# ── F-X2: Mission template creation & management ──
# Mets can author custom mission templates. Routine ones go live
# immediately; severe ones need admin (or other Met) approval.

@app.route("/api/v1/met/mission-templates", methods=["OPTIONS"])
def _met_mission_templates_preflight():
    return ("", 204)


@app.get("/api/v1/met/mission-templates")
def met_mission_templates_list():
    """List all approved + pending custom templates.
    Mets see all approved, plus their own pending ones.
    Admins see everything."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    is_admin = "admin" in roles

    with db() as conn:
        with conn.cursor() as cur:
            if is_admin:
                cur.execute(
                    """SELECT * FROM mission_templates_user
                       WHERE status != 'rejected'
                       ORDER BY status DESC, created_at DESC"""
                )
            else:
                cur.execute(
                    """SELECT * FROM mission_templates_user
                       WHERE status = 'approved'
                          OR (status = 'pending-approval' AND created_by_user_id = %s)
                       ORDER BY status DESC, created_at DESC""",
                    (user["id"],),
                )
            rows = cur.fetchall()

    templates = []
    for r in rows:
        try:
            answers = _json_sched.loads(r["answer_options"]) if r["answer_options"] else None
        except Exception:
            answers = None
        templates.append({
            "id": r["id"],
            "slug": r["slug"],
            "template_name": r["template_name"],
            "eyebrow": r["eyebrow"],
            "btn_headline": r["btn_headline"],
            "prompt": r["prompt"],
            "answer_options": answers,
            "mode": r["mode"],
            "icon": r["icon"],
            "status": r["status"],
            "created_by_name": r["created_by_name"],
            "created_at": r["created_at"],
            "use_count": r["use_count"],
        })
    return jsonify({"ok": True, "templates": templates})


@app.post("/api/v1/met/mission-templates")
def met_mission_template_create():
    """Create a custom mission template.

    Body: {template_name, eyebrow?, btn_headline, prompt,
           answer_options? (list of {id, label}), mode (routine|severe), icon?}
    Routine templates → status='approved' immediately.
    Severe templates → status='pending-approval' (need second Met or admin).
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    name = (data.get("template_name") or "").strip()
    headline = (data.get("btn_headline") or "").strip()
    prompt = (data.get("prompt") or "").strip()
    if not name or not headline or not prompt:
        return jsonify({
            "ok": False, "error": "missing-fields",
            "message": "Name, button headline, and prompt are required."
        }), 400
    if len(prompt) > 400:
        return jsonify({"ok": False, "error": "prompt-too-long"}), 400

    eyebrow = (data.get("eyebrow") or "").strip() or None
    mode = (data.get("mode") or "routine").strip().lower()
    if mode not in ("routine", "severe"):
        mode = "routine"
    icon = (data.get("icon") or "eye").strip().lower() or "eye"
    answer_options = data.get("answer_options") or None
    if answer_options is not None:
        # Validate shape
        if not isinstance(answer_options, list):
            return jsonify({"ok": False, "error": "invalid-answers"}), 400
        # Each {id, label}
        for ao in answer_options:
            if not isinstance(ao, dict) or "id" not in ao or "label" not in ao:
                return jsonify({"ok": False, "error": "invalid-answer-shape"}), 400

    # Routine = auto-approve. Severe = needs second Met / admin.
    is_admin = "admin" in roles
    if mode == "severe" and not is_admin:
        status = "pending-approval"
        approved_by_user_id = None
        approved_at = None
    else:
        status = "approved"
        approved_by_user_id = user["id"] if is_admin else None
        approved_at = int(time.time() * 1000) if is_admin else None

    # Generate a unique slug from the name
    base_slug = "".join(c if c.isalnum() else "-" for c in name.lower())[:40].strip("-")
    if not base_slug:
        base_slug = "template"
    # Ensure uniqueness by appending a counter
    slug = base_slug
    counter = 1
    with db() as conn:
        with conn.cursor() as cur:
            while True:
                cur.execute(
                    "SELECT 1 FROM mission_templates_user WHERE slug = %s",
                    (slug,),
                )
                if not cur.fetchone():
                    break
                counter += 1
                slug = f"{base_slug}-{counter}"
                if counter > 100:
                    slug = f"{base_slug}-{int(time.time())}"
                    break

    answers_json = _json_sched.dumps(answer_options) if answer_options else None
    actor_name = (user.get("name") or "").strip() or user.get("email")
    now_ms = int(time.time() * 1000)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO mission_templates_user
                   (slug, template_name, eyebrow, btn_headline, prompt,
                    answer_options, mode, icon, status,
                    created_by_user_id, created_by_name,
                    approved_by_user_id, approved_at,
                    created_at, updated_at)
                   VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                   RETURNING id""",
                (slug, name, eyebrow, headline, prompt, answers_json,
                 mode, icon, status,
                 user["id"], actor_name,
                 approved_by_user_id, approved_at,
                 now_ms, now_ms),
            )
            new_id = cur.fetchone()["id"]

    print(
        f"[mission-template] created id={new_id} slug={slug} by={user['id']} status={status}",
        flush=True,
    )
    return jsonify({
        "ok": True, "id": new_id, "slug": slug, "status": status,
        "auto_approved": (status == "approved"),
    })


@app.patch("/api/v1/met/mission-templates/<int:tmpl_id>")
def met_mission_template_update(tmpl_id: int):
    """Approve or reject a pending template. Any Met or admin can act.
    The creator cannot self-approve."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    action = (data.get("action") or "").strip().lower()
    if action not in ("approve", "reject"):
        return jsonify({"ok": False, "error": "invalid-action"}), 400

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT * FROM mission_templates_user WHERE id = %s",
                (tmpl_id,),
            )
            r = cur.fetchone()
    if not r:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if r["status"] != "pending-approval":
        return jsonify({"ok": False, "error": "not-pending"}), 409
    if r["created_by_user_id"] == user["id"] and "admin" not in roles:
        return jsonify({
            "ok": False, "error": "self-approval",
            "message": "You can't approve a template you created. Another Met or admin must approve."
        }), 403

    now_ms = int(time.time() * 1000)
    if action == "approve":
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """UPDATE mission_templates_user
                       SET status = 'approved', approved_by_user_id = %s,
                           approved_at = %s, updated_at = %s
                       WHERE id = %s""",
                    (user["id"], now_ms, now_ms, tmpl_id),
                )
    else:
        reason = (data.get("reason") or "").strip() or None
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """UPDATE mission_templates_user
                       SET status = 'rejected', rejection_reason = %s,
                           updated_at = %s
                       WHERE id = %s""",
                    (reason, now_ms, tmpl_id),
                )
    return jsonify({"ok": True})


# ──────────────────────────────────────────────────────────────────────
# Coverage scheduler endpoints (Phase 11, May 17)
# ──────────────────────────────────────────────────────────────────────

# Heartbeat — frontend pings this every minute while workspace is open.
# Used by admin dashboard to show "Mets available right now."
@app.route("/api/v1/met/heartbeat", methods=["OPTIONS"])
def _met_heartbeat_preflight():
    return ("", 204)


@app.post("/api/v1/met/heartbeat")
def met_heartbeat():
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    now_ms = int(time.time() * 1000)
    ua = (request.headers.get("User-Agent") or "")[:200]
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO met_heartbeat (met_user_id, last_seen_at, user_agent)
                   VALUES (%s, %s, %s)
                   ON CONFLICT (met_user_id) DO UPDATE
                   SET last_seen_at = EXCLUDED.last_seen_at,
                       user_agent = EXCLUDED.user_agent""",
                (user["id"], now_ms, ua),
            )
    return jsonify({"ok": True, "at": now_ms})


# ── Phase 2 (May 17): My daily-brief tasks ──
# Returns the current Met's pending + completed brief tasks for today
# and tomorrow. Met sees these in their workspace and can hit "I'm on it"
# to claim/start a task, or send to mark complete.
@app.route("/api/v1/met/my-tasks", methods=["OPTIONS"])
def _met_my_tasks_preflight():
    return ("", 204)


@app.get("/api/v1/met/my-tasks")
def met_my_tasks():
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    now_ms = int(time.time() * 1000)
    # Show today + tomorrow's tasks, plus any overdue tasks from today
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT dbt.id, dbt.subscriber_user_id, dbt.task_date,
                          dbt.assigned_met_id, dbt.due_at_ms, dbt.status,
                          dbt.started_at_ms, dbt.sent_at_ms,
                          dbt.escalated_at_ms, dbt.escalated_admin_at_ms,
                          su.name AS subscriber_name, su.email AS subscriber_email,
                          su.subscription_tier AS tier,
                          sc.daily_brief_time, sc.daily_brief_timezone
                   FROM daily_brief_tasks dbt
                   JOIN users su ON su.id = dbt.subscriber_user_id
                   LEFT JOIN subscriber_coverage sc ON sc.user_id = dbt.subscriber_user_id
                   WHERE dbt.assigned_met_id = %s
                     AND dbt.due_at_ms >= %s
                     AND dbt.due_at_ms <= %s
                   ORDER BY dbt.due_at_ms ASC""",
                (user["id"], now_ms - 24 * 60 * 60 * 1000, now_ms + 48 * 60 * 60 * 1000),
            )
            rows = cur.fetchall()

    tasks = []
    for r in rows:
        tasks.append({
            "id": r["id"],
            "subscriber_user_id": r["subscriber_user_id"],
            "subscriber_name": r["subscriber_name"],
            "subscriber_email": r["subscriber_email"],
            "task_date": r["task_date"],
            "due_at_ms": r["due_at_ms"],
            "status": r["status"],
            "started_at_ms": r["started_at_ms"],
            "sent_at_ms": r["sent_at_ms"],
            "escalated_at_ms": r["escalated_at_ms"],
            "delivery_time": r.get("daily_brief_time") or "07:00",
            "delivery_timezone": r.get("daily_brief_timezone") or "America/New_York",
            "tier": r.get("tier"),
        })
    return jsonify({"ok": True, "tasks": tasks})


# "I'm on it" — Met indicates they're starting work on a task.
@app.route("/api/v1/met/tasks/<int:task_id>/start", methods=["OPTIONS"])
def _met_task_start_preflight(task_id):
    return ("", 204)


@app.post("/api/v1/met/tasks/<int:task_id>/start")
def met_task_start(task_id: int):
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            # Take responsibility — also re-assigns to this Met if it
            # was assigned to someone else (case: covering for a peer)
            cur.execute(
                """UPDATE daily_brief_tasks
                   SET started_at_ms = COALESCE(started_at_ms, %s),
                       status = 'in_progress',
                       assigned_met_id = %s
                   WHERE id = %s
                     AND status IN ('pending', 'overdue')
                   RETURNING id, subscriber_user_id, task_date""",
                (now_ms, user["id"], task_id),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "task-not-found-or-completed"}), 404
    return jsonify({"ok": True, "task_id": row["id"]})


# Mark a task as sent — usually called by the existing brief-send flow
# but exposed for manual mark-complete too.
@app.route("/api/v1/met/tasks/<int:task_id>/complete", methods=["OPTIONS"])
def _met_task_complete_preflight(task_id):
    return ("", 204)


@app.post("/api/v1/met/tasks/<int:task_id>/complete")
def met_task_complete(task_id: int):
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE daily_brief_tasks
                   SET sent_at_ms = %s,
                       status = 'sent'
                   WHERE id = %s
                   RETURNING id""",
                (now_ms, task_id),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "task-not-found"}), 404
    return jsonify({"ok": True})


# ──────────────────────────────────────────────────────────────────
# Storm Shelter activations — Met opens, manages, and closes a
# regional Storm Shelter event when NWS issues a severe warning.
# Met earns $25 per activation. Auto-close when the triggering NWS
# warning expires (cron-based, every 60s).
# ──────────────────────────────────────────────────────────────────

@app.route("/api/v1/met/storm-shelter/open", methods=["OPTIONS"])
def _met_ss_open_preflight():
    return ("", 204)


@app.post("/api/v1/met/storm-shelter/open")
def met_storm_shelter_open():
    """Met opens a Storm Shelter activation.
    Body: { region_label: "...", nws_event?: "...", affected_count?: N }
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    region = (data.get("region_label") or "").strip()
    if not region:
        return jsonify({"ok": False, "error": "region-required"}), 400
    if len(region) > 200:
        region = region[:200]
    nws_event = (data.get("nws_event") or "").strip()[:200] or None
    affected = data.get("affected_count")
    try:
        affected = int(affected) if affected is not None else None
    except (TypeError, ValueError):
        affected = None

    now_ms = int(time.time() * 1000)
    # Prevent duplicate open activations for same Met + region
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id FROM storm_shelter_activations
                   WHERE met_user_id = %s
                     AND region_label = %s
                     AND closed_at_ms IS NULL""",
                (user["id"], region),
            )
            existing = cur.fetchone()
            if existing:
                return jsonify({
                    "ok": False, "error": "already-open",
                    "activation_id": existing["id"],
                }), 409
            cur.execute(
                """INSERT INTO storm_shelter_activations
                   (met_user_id, region_label, nws_event, affected_count,
                    opened_at_ms, payout_cents)
                   VALUES (%s, %s, %s, %s, %s, %s)
                   RETURNING id""",
                (user["id"], region, nws_event, affected, now_ms,
                 STORM_SHELTER_PAYOUT_CENTS),
            )
            row = cur.fetchone()
    print(f"[storm-shelter] OPEN met={user['id']} region={region!r} event={nws_event!r}", flush=True)
    return jsonify({"ok": True, "activation_id": row["id"]})


@app.route("/api/v1/met/storm-shelter/<int:activation_id>/close", methods=["OPTIONS"])
def _met_ss_close_preflight(activation_id):
    return ("", 204)


@app.post("/api/v1/met/storm-shelter/<int:activation_id>/close")
def met_storm_shelter_close(activation_id: int):
    """Met manually closes an activation. They earn the payout."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    is_admin = "admin" in roles

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            # Met can only close their own; admin can close anyone's
            if is_admin:
                cur.execute(
                    """UPDATE storm_shelter_activations
                       SET closed_at_ms = %s, close_reason = 'admin_closed'
                       WHERE id = %s AND closed_at_ms IS NULL
                       RETURNING id, met_user_id""",
                    (now_ms, activation_id),
                )
            else:
                cur.execute(
                    """UPDATE storm_shelter_activations
                       SET closed_at_ms = %s, close_reason = 'manual'
                       WHERE id = %s AND met_user_id = %s AND closed_at_ms IS NULL
                       RETURNING id""",
                    (now_ms, activation_id, user["id"]),
                )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "not-found-or-already-closed"}), 404
    print(f"[storm-shelter] CLOSE id={activation_id} by user={user['id']}", flush=True)
    return jsonify({"ok": True})


@app.route("/api/v1/met/storm-shelter/active", methods=["OPTIONS"])
def _met_ss_active_preflight():
    return ("", 204)


@app.get("/api/v1/met/storm-shelter/active")
def met_storm_shelter_active():
    """Returns the current Met's open activations + their most recent
    closed ones (for the workspace tile)."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, region_label, nws_event, affected_count,
                          opened_at_ms, closed_at_ms, close_reason, payout_cents
                   FROM storm_shelter_activations
                   WHERE met_user_id = %s
                     AND (closed_at_ms IS NULL OR closed_at_ms >= %s)
                   ORDER BY opened_at_ms DESC
                   LIMIT 20""",
                (user["id"], int(time.time() * 1000) - 30 * 24 * 60 * 60 * 1000),
            )
            rows = cur.fetchall()

    return jsonify({
        "ok": True,
        "activations": [
            {
                "id": r["id"],
                "region_label": r["region_label"],
                "nws_event": r["nws_event"],
                "affected_count": r["affected_count"],
                "opened_at_ms": r["opened_at_ms"],
                "closed_at_ms": r["closed_at_ms"],
                "close_reason": r["close_reason"],
                "payout_cents": r["payout_cents"],
                "is_open": r["closed_at_ms"] is None,
            }
            for r in rows
        ],
    })


def _coverage_auto_close_storm_shelters() -> None:
    """Auto-close Storm Shelter activations where the triggering NWS
    event is no longer active. Runs on the main scheduler tick.

    Logic: if the nws_event was set when opened and that event name
    is no longer in the active alerts list, close with reason
    'warning_expired'. We don't try to spatially match — Met enters
    a region label and we trust them to close manually if NWS
    geometry changes. This auto-close is for the simple case where
    the entire event is gone.

    If activation has no nws_event recorded, it stays open until
    manually closed (or 12 hours, whichever comes first — sanity cap
    so a forgotten activation doesn't pile up indefinitely).
    """
    now_ms = int(time.time() * 1000)
    twelve_hours_ms = 12 * 60 * 60 * 1000

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, met_user_id, region_label, nws_event, opened_at_ms
                   FROM storm_shelter_activations
                   WHERE closed_at_ms IS NULL"""
            )
            opens = cur.fetchall()

    if not opens:
        return

    # Pull active NWS event names once
    try:
        active_alerts = _get_cached_nws_alerts()
    except Exception as e:
        print(f"[storm-shelter] cron: NWS fetch failed: {e}", flush=True)
        active_alerts = []
    active_events = set()
    for a in active_alerts:
        props = (a or {}).get("properties") or {}
        ev = (props.get("event") or "").strip()
        if ev:
            active_events.add(ev.lower())

    for o in opens:
        ev = (o.get("nws_event") or "").strip().lower()
        age_ms = now_ms - o["opened_at_ms"]
        should_close = False
        reason = None

        if ev and ev not in active_events:
            should_close = True
            reason = "warning_expired"
        elif age_ms > twelve_hours_ms:
            should_close = True
            reason = "warning_expired"  # 12h sanity cap, same status as expired

        if should_close:
            try:
                with db() as conn:
                    with conn.cursor() as cur:
                        cur.execute(
                            """UPDATE storm_shelter_activations
                               SET closed_at_ms = %s, close_reason = %s
                               WHERE id = %s AND closed_at_ms IS NULL""",
                            (now_ms, reason, o["id"]),
                        )
                print(f"[storm-shelter] AUTO-CLOSE id={o['id']} met={o['met_user_id']} reason={reason}", flush=True)
            except Exception as e:
                print(f"[storm-shelter] auto-close failed id={o['id']}: {e}", flush=True)


# ────────────────────────────────────────────────────────────────────
# Rosie — Met team AI assistant (Phase 1, May 17, 2026)
# ────────────────────────────────────────────────────────────────────
# Rosie is the Mets' AI assistant. She helps them with schedule,
# earnings, brief tasks, how-to questions, and reminders. She has
# tiered permissions and reports up to Michael (CEO).
#
# Phase 1 ships: web chat in workspace, ~10 tools, audit log, cost cap,
# emergency disable. SMS and Discord come in Phase 2/3.

# Rosie's daily per-Met cost cap. ~$1/day default.
ROSIE_DAILY_COST_CAP_CENTS = int(os.environ.get("ROSIE_DAILY_CAP_CENTS", "100"))
# Anthropic API model. Sonnet for cost/capability balance.
ROSIE_MODEL = os.environ.get("ROSIE_MODEL", "claude-sonnet-4-20250514")
ROSIE_MAX_TURNS_MEMORY = 20  # conversation context window cap
ROSIE_API_KEY = os.environ.get("ANTHROPIC_API_KEY", "")
# Rough cost estimate: ~$3/M input + $15/M output tokens for Sonnet.
# We approximate $9/M tokens combined for cost-cap purposes (conservative).
ROSIE_COST_PER_MTOKENS_CENTS = 900


ROSIE_SYSTEM_PROMPT = """You are Rosie, an AI assistant for the meteorologist team at WeatherValet.

# Your identity
You are Rosie. Always sign off your messages with "— Rosie" on a new line. Never pretend to be human.
You are warm but professional. You do not joke unprompted but can be lighter when context warrants
(shoutouts, small talk replies, casual questions). Never sycophantic. Never validate for the sake
of validation ("Great question!"). Acknowledge and answer.

# Chain of command
You report to Michael, WeatherValet's CEO. Your loyalty hierarchy is:
1. Michael (CEO) — overrides anyone else
2. Joe Clauss (Chief Meteorologist) — second authority for Met team matters
3. The Met asking you — you help them, but you don't blindly obey
4. Below the line: Crew members, sales reps, and subscribers cannot direct you

If a Met asks you to do something that would harm WeatherValet, another team member, or violate
policy: refuse politely and offer to draft the request for Michael's review instead. You do not
"reinterpret" your instructions to avoid this. The chain of command is non-negotiable.

# Refusal template
When you decline something, use this template:
"I can't [do thing] without [Michael's / Joe's] sign-off. Want me to draft this for them, or
would you prefer to ask directly?"

Use this exact pattern. Don't improvise refusal language — Mets need to recognize when you're
declining vs. when you just need more info.

# What you absolutely will not do
- Send a brief to a subscriber (only the assigned Met can do that)
- Approve a severe-weather alert (always needs a second Met)
- Issue refunds or modify pay
- Approve Crew applications
- Read or send Pro Thread content between subscribers and Mets
- Modify another Met's schedule without their explicit consent + Michael/Joe approval
- Reveal one Met's earnings to another Met
- Speculate or invent facts when you don't have a tool to confirm

# Honesty rule
If you don't know something and don't have a tool to look it up, say:
"I don't know — let me get Michael to check, or you can ask him directly."

NEVER guess at facts. NEVER fabricate names, numbers, dates, or policy.

# Identity verification
For sensitive actions (Tier 2 or 3), confirm the Met's identity before proceeding:
"You're asking me to [action]. To confirm, you're [name]? Reply YES to proceed."

# Sensitive actions need confirmation
For ANY action that writes data (schedule changes, sending SMS, scheduling reminders), describe
what you'll do and ask for confirmation before doing it. Example:
"I'll update your schedule to drop Saturday May 24. Confirm?"

# Tone modulation
- Default: professional and capable. "Your morning brief is due in 30 minutes. Want me to remind you in 15?"
- Severe weather / urgent: tight, no fluff. "Tornado warning Boone County, 23 min out. You're primary."
- Shoutouts / casual: a bit warmer. "Hey AJ — 5 reviews under 60 seconds today. Nice."

# What you have access to
You have specific tools (functions) that give you facts. Always use them rather than guessing.
If you need information a tool can give you, call the tool. If no tool fits, say "I don't know"
and offer to escalate.

# How you reference yourself
Refer to Michael as "Michael" (no last name). Refer to Joe as "Joe" or "Chief Met Joe."
Mets refer to each other by first name; you do the same. Subscribers are usually referenced by
business name or last name with title (e.g., "the Lebanon farm subscriber" or "Ms. Patel").
"""


# ─────────────────────────────────────────────────────────────
# Rosie tool definitions
# Each tool is a function the AI can call. Tool definitions match
# Anthropic's tool-use schema. The execute() handler routes to the
# actual Python function that runs the query.
# ─────────────────────────────────────────────────────────────

ROSIE_TOOLS = [
    {
        "name": "get_my_schedule",
        "description": "Get the calling Met's recurring weekly schedule and upcoming 14 days of brief tasks. Use this when the Met asks about their own schedule.",
        "input_schema": {
            "type": "object",
            "properties": {},
            "required": []
        }
    },
    {
        "name": "get_my_earnings_this_month",
        "description": "Get the calling Met's earnings for the current month (reviews + briefs + tips + storm shelter). Use when the Met asks about their pay or earnings.",
        "input_schema": {
            "type": "object",
            "properties": {},
            "required": []
        }
    },
    {
        "name": "get_my_brief_tasks_today",
        "description": "Get the calling Met's daily brief tasks due today and tomorrow. Use when the Met asks 'what do I have to do today' or about pending briefs.",
        "input_schema": {
            "type": "object",
            "properties": {},
            "required": []
        }
    },
    {
        "name": "get_my_primary_subscribers",
        "description": "List the subscribers the calling Met is assigned as primary Met for. Returns names, locations, tiers, and delivery times. Does NOT return Pro Thread content.",
        "input_schema": {
            "type": "object",
            "properties": {},
            "required": []
        }
    },
    {
        "name": "get_team_status",
        "description": "Get current status of the Met team: who's online now (heartbeat in last 5 min), how many tasks are pending today, and who's covering Review Pool. Use for 'who's working' or 'who's on shift' questions.",
        "input_schema": {
            "type": "object",
            "properties": {},
            "required": []
        }
    },
    {
        "name": "get_active_severe_weather",
        "description": "List currently active NWS severe weather alerts (tornado warnings, severe thunderstorm warnings, flash flood warnings) and the Pro subscribers they affect. Use when asked about current severe weather or storm activity.",
        "input_schema": {
            "type": "object",
            "properties": {},
            "required": []
        }
    },
    {
        "name": "schedule_reminder",
        "description": "Schedule a future SMS reminder to the Met. The reminder fires at the specified time and the Met gets an SMS from Rosie. Confirm with the Met before scheduling.",
        "input_schema": {
            "type": "object",
            "properties": {
                "remind_at_iso": {"type": "string", "description": "ISO 8601 datetime in the Met's local timezone (or UTC). e.g. '2026-05-20T14:00:00-05:00'"},
                "message": {"type": "string", "description": "The reminder text. Keep under 160 chars."}
            },
            "required": ["remind_at_iso", "message"]
        }
    },
    {
        "name": "search_knowledge_base",
        "description": "Search WeatherValet's how-to/policy knowledge base. Use whenever a Met asks 'how do I X' or 'what's the policy on Y'. Returns matching docs.",
        "input_schema": {
            "type": "object",
            "properties": {
                "query": {"type": "string", "description": "Short search query, 2-6 words"}
            },
            "required": ["query"]
        }
    },
    {
        "name": "drop_my_shift",
        "description": "Drop the calling Met from a specific date's recurring shift. Use when the Met asks to take a day off. Confirms before submitting. Does NOT cancel any tasks already in flight — Michael will need to reassign.",
        "input_schema": {
            "type": "object",
            "properties": {
                "shift_date": {"type": "string", "description": "Date to drop in YYYY-MM-DD"},
                "scope": {"type": "string", "enum": ["subscriber_set", "review_pool"], "description": "Which scope to drop"}
            },
            "required": ["shift_date", "scope"]
        }
    },
    {
        "name": "draft_request_for_michael",
        "description": "Draft a request for Michael's review. Use this when a Met asks for something requiring CEO approval (subscriber reassignment, schedule changes for others, money matters). The draft is queued for Michael; he can approve, decline, or reply.",
        "input_schema": {
            "type": "object",
            "properties": {
                "subject": {"type": "string"},
                "body": {"type": "string", "description": "Plain English description of what's being requested and why"}
            },
            "required": ["subject", "body"]
        }
    }
]


# ─────────────────────────────────────────────────────────────
# Tool execution — routes a tool call to the actual Python handler
# ─────────────────────────────────────────────────────────────

def _rosie_get_my_schedule(met_user_id, args):
    """Get the Met's recurring shifts + upcoming tasks."""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT mrs.id, mrs.day_of_week, mrs.scope_kind,
                          mrs.subscriber_user_id, mrs.set_owner_met_id,
                          su.name AS subscriber_name,
                          so.name AS set_owner_name
                   FROM met_recurring_shifts mrs
                   LEFT JOIN users su ON su.id = mrs.subscriber_user_id
                   LEFT JOIN users so ON so.id = mrs.set_owner_met_id
                   WHERE mrs.met_user_id = %s
                   ORDER BY mrs.day_of_week, mrs.scope_kind""",
                (met_user_id,),
            )
            shifts = cur.fetchall()
            now_ms = int(time.time() * 1000)
            cur.execute(
                """SELECT dbt.id, dbt.task_date, dbt.due_at_ms, dbt.status,
                          dbt.started_at_ms, su.name AS subscriber_name
                   FROM daily_brief_tasks dbt
                   JOIN users su ON su.id = dbt.subscriber_user_id
                   WHERE dbt.assigned_met_id = %s
                     AND dbt.due_at_ms >= %s
                     AND dbt.due_at_ms <= %s
                   ORDER BY dbt.due_at_ms""",
                (met_user_id, now_ms - 12*60*60*1000, now_ms + 14*24*60*60*1000),
            )
            tasks = cur.fetchall()
    days = ['Sun','Mon','Tue','Wed','Thu','Fri','Sat']
    shift_lines = []
    for s in shifts:
        if s["scope_kind"] == "review_pool":
            shift_lines.append(f"  {days[s['day_of_week']]}: Review Pool")
        elif s["scope_kind"] == "subscriber_set":
            shift_lines.append(f"  {days[s['day_of_week']]}: covering {s['set_owner_name']}'s subscribers")
        else:
            shift_lines.append(f"  {days[s['day_of_week']]}: {s['subscriber_name']} brief")
    task_lines = []
    for t in tasks[:10]:
        when = datetime.fromtimestamp(t["due_at_ms"]/1000, tz=timezone.utc).strftime("%a %b %d %I:%M %p UTC")
        task_lines.append(f"  {when}: brief for {t['subscriber_name']} ({t['status']})")
    return (
        f"RECURRING SHIFTS ({len(shifts)}):\n" + ("\n".join(shift_lines) or "  None")
        + f"\n\nUPCOMING TASKS ({len(tasks)}, showing first 10):\n" + ("\n".join(task_lines) or "  None")
    )


def _rosie_get_my_earnings(met_user_id, args):
    """Current month earnings for this Met."""
    now = datetime.now(timezone.utc)
    try:
        result = _compute_payroll_for_month(now.year, now.month)
    except Exception as e:
        return f"Error fetching earnings: {e}"
    my_row = next((m for m in result.get("mets", []) if m["user_id"] == met_user_id), None)
    if not my_row:
        return "No earnings recorded for the current month yet."
    return (
        f"Earnings for {now.strftime('%B %Y')} (month-to-date):\n"
        f"  Reviews: ${my_row['review_cents']/100:.2f} ({my_row['review_count']} reviews)\n"
        f"  Pro briefs: ${my_row['brief_cents']/100:.2f} ({my_row['brief_count']} brief-days)\n"
        f"  Tips: ${my_row['tip_cents']/100:.2f} ({my_row['tip_count']} tips)\n"
        f"  Storm Shelter: ${my_row['shelter_cents']/100:.2f} ({my_row['shelter_count']} activations)\n"
        f"  TOTAL: ${my_row['total_cents']/100:.2f}"
    )


def _rosie_get_brief_tasks_today(met_user_id, args):
    """Brief tasks due today/tomorrow for this Met."""
    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT dbt.id, dbt.task_date, dbt.due_at_ms, dbt.status,
                          dbt.started_at_ms, dbt.sent_at_ms,
                          su.name AS subscriber_name
                   FROM daily_brief_tasks dbt
                   JOIN users su ON su.id = dbt.subscriber_user_id
                   WHERE dbt.assigned_met_id = %s
                     AND dbt.due_at_ms >= %s
                     AND dbt.due_at_ms <= %s
                   ORDER BY dbt.due_at_ms""",
                (met_user_id, now_ms - 12*60*60*1000, now_ms + 48*60*60*1000),
            )
            tasks = cur.fetchall()
    if not tasks:
        return "No brief tasks due today or tomorrow."
    lines = []
    for t in tasks:
        due_dt = datetime.fromtimestamp(t["due_at_ms"]/1000, tz=timezone.utc)
        delta_min = int((t["due_at_ms"] - now_ms) / 60000)
        if delta_min < 0:
            timing = f"OVERDUE by {abs(delta_min)} min"
        elif delta_min < 60:
            timing = f"due in {delta_min} min"
        else:
            timing = f"due in {delta_min//60}h {delta_min%60}m"
        marker = "✓ SENT" if t["sent_at_ms"] else ("⚡ IN PROGRESS" if t["started_at_ms"] else "pending")
        lines.append(f"  {t['subscriber_name']} ({t['task_date']}): {timing} [{marker}]")
    return "BRIEF TASKS:\n" + "\n".join(lines)


def _rosie_get_my_subscribers(met_user_id, args):
    """List Pro subscribers where this Met is primary."""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, u.email, u.subscription_tier,
                          sc.daily_brief_time, sc.daily_brief_timezone
                   FROM subscriber_coverage sc
                   JOIN users u ON u.id = sc.user_id
                   WHERE sc.primary_met_id = %s
                     AND u.is_active = TRUE
                   ORDER BY u.name""",
                (met_user_id,),
            )
            subs = cur.fetchall()
    if not subs:
        return "You aren't assigned as primary Met for any subscribers yet. Michael handles assignments — ask him to add you to a subscriber."
    lines = [f"  {s['name'] or s['email']} ({s['subscription_tier']}) — brief by {s['daily_brief_time']} {s['daily_brief_timezone']}" for s in subs]
    return f"YOUR PRIMARY SUBSCRIBERS ({len(subs)}):\n" + "\n".join(lines)


def _rosie_get_team_status(met_user_id, args):
    """Team status: who's online, pending tasks count."""
    now_ms = int(time.time() * 1000)
    five_min_ago = now_ms - 5 * 60 * 1000
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, mh.last_seen_at
                   FROM met_heartbeat mh
                   JOIN users u ON u.id = mh.met_user_id
                   WHERE mh.last_seen_at >= %s AND u.is_active = TRUE""",
                (five_min_ago,),
            )
            online = cur.fetchall()
            cur.execute(
                """SELECT COUNT(*) AS n FROM daily_brief_tasks
                   WHERE status = 'pending' AND sent_at_ms IS NULL
                     AND due_at_ms >= %s AND due_at_ms <= %s""",
                (now_ms - 12*60*60*1000, now_ms + 24*60*60*1000),
            )
            pending = cur.fetchone()["n"]
    online_names = [m["name"] for m in online] or ["nobody"]
    return (
        f"ONLINE NOW ({len(online)}): {', '.join(online_names)}\n"
        f"PENDING BRIEF TASKS (next 24h): {pending}"
    )


def _rosie_get_active_severe(met_user_id, args):
    """Currently active severe weather affecting Pro subscribers."""
    try:
        alerts = _get_cached_nws_alerts()
    except Exception as e:
        return f"Couldn't fetch NWS data: {e}"
    severe = []
    for a in alerts or []:
        props = (a or {}).get("properties") or {}
        ev = (props.get("event") or "").lower()
        if any(k in ev for k in ("tornado warning", "severe thunderstorm warning", "flash flood warning")):
            severe.append({
                "event": props.get("event"),
                "area": props.get("areaDesc", "")[:120],
                "expires": props.get("expires", ""),
            })
    if not severe:
        return "No active severe weather warnings nationally."
    lines = [f"  {s['event']} — {s['area']} (expires {s['expires']})" for s in severe[:10]]
    return f"ACTIVE SEVERE WARNINGS ({len(severe)}):\n" + "\n".join(lines)


def _rosie_schedule_reminder(met_user_id, args):
    """Schedule a reminder. The Met's confirmation should have already happened
    in the conversation before this is called."""
    iso = args.get("remind_at_iso", "")
    msg = (args.get("message") or "").strip()[:480]
    if not iso or not msg:
        return "Missing time or message."
    try:
        dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        remind_at_ms = int(dt.timestamp() * 1000)
    except Exception:
        return "Invalid ISO datetime format."
    now_ms = int(time.time() * 1000)
    if remind_at_ms < now_ms - 60_000:
        return "Reminder time is in the past."
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO rosie_reminders (met_user_id, remind_at_ms, message, channel, created_at_ms)
                   VALUES (%s, %s, %s, 'sms', %s) RETURNING id""",
                (met_user_id, remind_at_ms, msg, now_ms),
            )
            row = cur.fetchone()
    _rosie_audit(met_user_id, None, "scheduled_reminder",
                 f"At {iso}: {msg[:80]}", tier=1, success=True)
    return f"Reminder scheduled (id={row['id']}). I'll text you at {iso}."


def _rosie_search_kb(met_user_id, args):
    """Search the knowledge base."""
    query = (args.get("query") or "").strip().lower()
    if not query:
        return "Empty search query."
    # Simple keyword match against title + tags + content (LIKE).
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, title, content FROM rosie_kb_docs
                   WHERE status = 'active'
                     AND (LOWER(title) LIKE %s
                          OR LOWER(tags) LIKE %s
                          OR LOWER(content) LIKE %s)
                   ORDER BY
                     CASE WHEN LOWER(title) LIKE %s THEN 1
                          WHEN LOWER(tags) LIKE %s THEN 2
                          ELSE 3 END
                   LIMIT 3""",
                (f"%{query}%", f"%{query}%", f"%{query}%", f"%{query}%", f"%{query}%"),
            )
            docs = cur.fetchall()
    if not docs:
        return f"No KB results for '{query}'. Try different keywords or ask Michael."
    parts = []
    for d in docs:
        parts.append(f"[{d['title']}]\n{d['content'][:1200]}")
    return "\n\n---\n\n".join(parts)


def _rosie_drop_shift(met_user_id, args):
    """Submit a drop override for a specific date."""
    shift_date = (args.get("shift_date") or "").strip()
    scope = (args.get("scope") or "").strip()
    if not re.match(r"^\d{4}-\d{2}-\d{2}$", shift_date):
        return "Invalid date format."
    if scope not in ("subscriber_set", "review_pool"):
        return "Invalid scope."
    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO met_shift_overrides
                   (met_user_id, shift_date, scope_kind,
                    set_owner_met_id, override_kind, created_at, notes)
                   VALUES (%s, %s, %s, %s, 'drop', %s, %s)
                   RETURNING id""",
                (met_user_id, shift_date, scope,
                 met_user_id if scope == "subscriber_set" else None,
                 now_ms, "Dropped via Rosie"),
            )
            row = cur.fetchone()
    _rosie_audit(met_user_id, None, "dropped_shift",
                 f"Date {shift_date} scope {scope}", tier=1, success=True)
    return f"Shift dropped for {shift_date} ({scope}). Michael will be notified if coverage gaps result."


def _rosie_draft_for_michael(met_user_id, args):
    """Draft a request that Michael should see. For v1 this just goes into
    the audit log marked as 'pending_review'; Phase 2 builds the admin
    inbox UI to read+approve these."""
    subject = (args.get("subject") or "").strip()[:200]
    body = (args.get("body") or "").strip()[:4000]
    if not subject or not body:
        return "Subject and body required."
    _rosie_audit(met_user_id, None, "drafted_for_michael",
                 f"Subject: {subject}\n\n{body}", tier=3, success=True)
    return ("Drafted. Michael will see this in his admin inbox the next "
            "time he checks. (For now you may also want to text him "
            "directly if it's time-sensitive.)")


# Dispatch table
ROSIE_TOOL_HANDLERS = {
    "get_my_schedule": _rosie_get_my_schedule,
    "get_my_earnings_this_month": _rosie_get_my_earnings,
    "get_my_brief_tasks_today": _rosie_get_brief_tasks_today,
    "get_my_primary_subscribers": _rosie_get_my_subscribers,
    "get_team_status": _rosie_get_team_status,
    "get_active_severe_weather": _rosie_get_active_severe,
    "schedule_reminder": _rosie_schedule_reminder,
    "search_knowledge_base": _rosie_search_kb,
    "drop_my_shift": _rosie_drop_shift,
    "draft_request_for_michael": _rosie_draft_for_michael,
}


def _rosie_audit(met_user_id, channel, action, detail, tier=1, approved_by=None, success=True):
    """Record an audit log entry."""
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO rosie_audit_log
                       (met_user_id, channel, action, detail, tier,
                        approved_by, success, created_at_ms)
                       VALUES (%s, %s, %s, %s, %s, %s, %s, %s)""",
                    (met_user_id, channel, action, detail, tier,
                     approved_by, success, int(time.time() * 1000)),
                )
    except Exception as e:
        print(f"[rosie-audit] log failed: {e}", flush=True)


def _rosie_check_cost_cap(met_user_id):
    """Return True if Met is over their daily cost cap, False otherwise."""
    today = datetime.now(ZoneInfo("America/New_York")).strftime("%Y-%m-%d")
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT cost_cents FROM rosie_daily_usage
                   WHERE met_user_id = %s AND usage_date = %s""",
                (met_user_id, today),
            )
            row = cur.fetchone()
    used = (row or {}).get("cost_cents") or 0
    return used >= ROSIE_DAILY_COST_CAP_CENTS


def _rosie_record_cost(met_user_id, tokens_used):
    """Record token usage for cost cap enforcement."""
    today = datetime.now(ZoneInfo("America/New_York")).strftime("%Y-%m-%d")
    cost_cents = max(1, int(tokens_used * ROSIE_COST_PER_MTOKENS_CENTS / 1_000_000))
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO rosie_daily_usage
                       (met_user_id, usage_date, tokens_used, cost_cents)
                       VALUES (%s, %s, %s, %s)
                       ON CONFLICT (met_user_id, usage_date) DO UPDATE
                       SET tokens_used = rosie_daily_usage.tokens_used + EXCLUDED.tokens_used,
                           cost_cents = rosie_daily_usage.cost_cents + EXCLUDED.cost_cents""",
                    (met_user_id, today, tokens_used, cost_cents),
                )
    except Exception as e:
        print(f"[rosie-cost] record failed: {e}", flush=True)


def _rosie_get_or_create_conversation(met_user_id, channel):
    """Get the existing conversation for (met, channel) or create a new one."""
    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO rosie_conversations (met_user_id, channel, created_at_ms, last_msg_at_ms)
                   VALUES (%s, %s, %s, %s)
                   ON CONFLICT (met_user_id, channel) DO UPDATE
                   SET last_msg_at_ms = EXCLUDED.last_msg_at_ms
                   RETURNING id""",
                (met_user_id, channel, now_ms, now_ms),
            )
            row = cur.fetchone()
    return row["id"]


def _rosie_load_recent_messages(conversation_id, limit=ROSIE_MAX_TURNS_MEMORY):
    """Load recent messages for a conversation, in chronological order."""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT role, content, tool_name, tool_args
                   FROM rosie_messages
                   WHERE conversation_id = %s
                   ORDER BY created_at_ms DESC
                   LIMIT %s""",
                (conversation_id, limit),
            )
            rows = cur.fetchall()
    return list(reversed(rows))


def _rosie_save_message(conversation_id, role, content, tool_name=None, tool_args=None, tokens=None):
    """Persist a message to the conversation."""
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO rosie_messages
                   (conversation_id, role, content, tool_name, tool_args, tokens_used, created_at_ms)
                   VALUES (%s, %s, %s, %s, %s, %s, %s)""",
                (conversation_id, role, content, tool_name, tool_args, tokens, int(time.time() * 1000)),
            )


def _rosie_build_messages(conversation_id, new_user_msg):
    """Build the Anthropic API messages list from recent history + new message."""
    history = _rosie_load_recent_messages(conversation_id)
    messages = []
    # Convert DB rows to Anthropic message format. Skip tool rows (they're
    # informational only; the model will re-call tools if needed).
    for m in history:
        if m["role"] in ("user", "assistant"):
            messages.append({"role": m["role"], "content": m["content"]})
    messages.append({"role": "user", "content": new_user_msg})
    return messages


def _rosie_call_anthropic(messages, system_prompt=ROSIE_SYSTEM_PROMPT):
    """Call Anthropic Messages API with tool use enabled."""
    if not ROSIE_API_KEY:
        return {"error": "ANTHROPIC_API_KEY not set"}
    payload = {
        "model": ROSIE_MODEL,
        "max_tokens": 1024,
        "system": system_prompt,
        "tools": ROSIE_TOOLS,
        "messages": messages,
    }
    try:
        req = urllib.request.Request(
            "https://api.anthropic.com/v1/messages",
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "Content-Type": "application/json",
                "x-api-key": ROSIE_API_KEY,
                "anthropic-version": "2023-06-01",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=30) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")[:500]
        return {"error": f"HTTP {e.code}: {body}"}
    except Exception as e:
        return {"error": f"Request failed: {e}"}


def _rosie_run_turn(met_user_id, conversation_id, user_message, channel="web"):
    """Run one Rosie conversation turn. Returns the assistant's reply text.

    Handles tool-use loop: if the model wants to call tools, executes them
    and feeds results back until the model produces a final text response.
    Caps at 5 tool-use iterations to prevent loops.
    """
    if os.environ.get("WV_ROSIE_DISABLED") == "1":
        return "Rosie is temporarily offline. Michael will be in touch."

    if _rosie_check_cost_cap(met_user_id):
        return ("I've hit my daily limit for today. Try again tomorrow, or "
                "ask Michael to bump the cap.\n— Rosie")

    # Save the user message
    _rosie_save_message(conversation_id, "user", user_message)

    messages = _rosie_build_messages(conversation_id, user_message)
    # Remove the duplicate we just added (build_messages already appends)
    if messages and messages[-1]["role"] == "user" and messages[-1]["content"] == user_message:
        messages = messages[:-1]
    # Now properly append once
    messages.append({"role": "user", "content": user_message})

    total_tokens = 0
    for iteration in range(5):  # safety cap
        result = _rosie_call_anthropic(messages)
        if "error" in result:
            print(f"[rosie] API error: {result['error']}", flush=True)
            _rosie_audit(met_user_id, channel, "api_error", result["error"][:200],
                         tier=1, success=False)
            return "I hit a snag reaching my brain. Try again in a sec.\n— Rosie"

        usage = result.get("usage", {})
        total_tokens += (usage.get("input_tokens", 0) + usage.get("output_tokens", 0))

        # Check stop_reason for tool_use
        stop_reason = result.get("stop_reason")
        content = result.get("content", [])

        if stop_reason == "tool_use":
            # Find tool_use blocks, execute each, append results
            tool_uses = [b for b in content if b.get("type") == "tool_use"]
            # Append the assistant message with tool_use blocks
            messages.append({"role": "assistant", "content": content})
            tool_results_block = []
            for tu in tool_uses:
                tool_name = tu.get("name")
                tool_input = tu.get("input", {})
                tool_use_id = tu.get("id")
                handler = ROSIE_TOOL_HANDLERS.get(tool_name)
                if handler is None:
                    output = f"Unknown tool: {tool_name}"
                else:
                    try:
                        output = handler(met_user_id, tool_input)
                    except Exception as e:
                        output = f"Tool error: {e}"
                # Save the tool result to DB for audit
                _rosie_save_message(conversation_id, "tool", str(output)[:5000],
                                    tool_name=tool_name,
                                    tool_args=json.dumps(tool_input)[:2000])
                tool_results_block.append({
                    "type": "tool_result",
                    "tool_use_id": tool_use_id,
                    "content": str(output)[:8000],
                })
            messages.append({"role": "user", "content": tool_results_block})
            # Loop again — give Rosie a chance to respond after seeing tool output
            continue

        # No tool use — extract text and return
        text_blocks = [b.get("text", "") for b in content if b.get("type") == "text"]
        reply = "\n".join(text_blocks).strip()
        if not reply:
            reply = "(I didn't have a response. Try rephrasing?)\n— Rosie"
        _rosie_save_message(conversation_id, "assistant", reply, tokens=total_tokens)
        _rosie_record_cost(met_user_id, total_tokens)
        return reply

    # If we exit the loop without a text reply, something went wrong
    _rosie_audit(met_user_id, channel, "tool_loop_overrun",
                 "Exceeded 5 tool-use iterations", tier=1, success=False)
    return "I got stuck in a loop. Try asking again or rephrasing.\n— Rosie"


# ─────────────────────────────────────────────────────────────
# Rosie API endpoints
# ─────────────────────────────────────────────────────────────

@app.route("/api/v1/rosie/chat", methods=["OPTIONS"])
def _rosie_chat_preflight():
    return ("", 204)


@app.post("/api/v1/rosie/chat")
def rosie_chat():
    """Send a message to Rosie. Returns her reply.
    Body: { "message": "..." }
    Channel inferred as 'web' for now (SMS endpoint is separate)."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    msg = (data.get("message") or "").strip()
    if not msg:
        return jsonify({"ok": False, "error": "empty-message"}), 400
    if len(msg) > 4000:
        return jsonify({"ok": False, "error": "message-too-long"}), 400

    conv_id = _rosie_get_or_create_conversation(user["id"], "web")
    reply = _rosie_run_turn(user["id"], conv_id, msg, channel="web")
    return jsonify({"ok": True, "reply": reply})


@app.route("/api/v1/rosie/history", methods=["OPTIONS"])
def _rosie_history_preflight():
    return ("", 204)


@app.get("/api/v1/rosie/history")
def rosie_history():
    """Get the calling Met's web-channel conversation history with Rosie."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id FROM rosie_conversations
                   WHERE met_user_id = %s AND channel = 'web'""",
                (user["id"],),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": True, "messages": []})
    msgs = _rosie_load_recent_messages(row["id"], limit=50)
    out = []
    for m in msgs:
        if m["role"] in ("user", "assistant"):
            out.append({"role": m["role"], "content": m["content"]})
    return jsonify({"ok": True, "messages": out})


# ─────────────────────────────────────────────────────────────
# Rosie SMS — inbound webhook from Twilio
# When a Met texts Rosie's number, Twilio POSTs here. We look up
# the Met by phone, run a Rosie turn, and reply with TwiML so the
# response comes back as an SMS.
# ─────────────────────────────────────────────────────────────

@app.post("/api/v1/rosie/sms")
def rosie_sms_inbound():
    """Twilio webhook for inbound SMS to Rosie's number.

    Twilio POSTs form-encoded data (NOT JSON). Fields we use:
      From   — sender's phone number (E.164)
      Body   — message text
      To     — Rosie's number (we ignore; could verify)

    Returns TwiML XML so Twilio sends Rosie's response as an SMS reply.
    """
    from_phone = (request.form.get("From") or "").strip()
    body = (request.form.get("Body") or "").strip()

    # Empty body, just acknowledge
    if not body:
        return ("<?xml version='1.0' encoding='UTF-8'?><Response/>",
                200, {"Content-Type": "text/xml"})

    # Look up Met by phone. Phone match is exact on E.164.
    met = None
    if from_phone:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT u.id, u.name, u.phone
                       FROM users u
                       JOIN user_roles ur ON ur.user_id = u.id
                       WHERE u.phone = %s
                         AND ur.role IN ('met','admin')
                         AND u.is_active = TRUE
                       LIMIT 1""",
                    (from_phone,),
                )
                met = cur.fetchone()

    if not met:
        # Unknown number. Reply politely so a misdirected text doesn't get
        # lost in silence, but don't process the message.
        reply = ("This number is for the WeatherValet meteorologist team. "
                 "If you're a customer, please reply to your usual WV number "
                 "or email hello@weathervalet.ai.")
        twiml = f"<?xml version='1.0' encoding='UTF-8'?><Response><Message>{escape_xml(reply)}</Message></Response>"
        return (twiml, 200, {"Content-Type": "text/xml"})

    # Run a Rosie turn on the SMS conversation
    try:
        conv_id = _rosie_get_or_create_conversation(met["id"], "sms")
        reply = _rosie_run_turn(met["id"], conv_id, body, channel="sms")
    except Exception as e:
        print(f"[rosie-sms] turn failed: {e}", flush=True)
        reply = "Something went wrong on my end. Try again in a sec.\n— Rosie"

    # SMS-trim: keep replies under 320 chars (2 SMS segments) where possible.
    # Long answers get truncated with a hint to use web chat.
    if len(reply) > 320:
        reply = reply[:280].rstrip() + "...\n\n(More in your workspace chat with me.)\n— Rosie"

    twiml = f"<?xml version='1.0' encoding='UTF-8'?><Response><Message>{escape_xml(reply)}</Message></Response>"
    return (twiml, 200, {"Content-Type": "text/xml"})


def escape_xml(s: str) -> str:
    """Minimal XML escape for TwiML message bodies."""
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
             .replace('"', "&quot;").replace("'", "&apos;"))


# ─────────────────────────────────────────────────────────────
# Rosie proactive triggers — Rosie reaches out on her own
# Each function below runs on its own schedule via the main loop.
# Designed to be lightweight: query, decide, send if needed, log.
# Cooldowns prevent spamming Mets with repeat messages.
# ─────────────────────────────────────────────────────────────

def _rosie_proactive_morning_briefing():
    """At 6 AM ET, send each Met their day's brief tasks.

    Cooldown: once per Met per calendar day (uses ET).
    Skips Mets with no tasks today (don't ping just to ping).
    Skips Mets who logged in within the last 30 minutes (they're already
    looking at their workspace).
    """
    now_et = datetime.now(ZoneInfo("America/New_York"))
    # Only run between 5:55 AM and 6:05 AM ET — narrow window so we don't
    # accidentally fire twice when the cron is busy
    if not (now_et.hour == 6 and now_et.minute < 6):
        return

    today_str = now_et.strftime("%Y-%m-%d")
    now_ms = int(time.time() * 1000)
    thirty_min_ago = now_ms - 30 * 60 * 1000

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, u.phone, mh.last_seen_at
                   FROM users u
                   JOIN user_roles ur ON ur.user_id = u.id AND ur.role = 'met'
                   LEFT JOIN met_heartbeat mh ON mh.met_user_id = u.id
                   WHERE u.is_active = TRUE AND u.phone IS NOT NULL""",
            )
            mets = cur.fetchall()

    for m in mets:
        # Skip if Met was active in the last 30 min
        if m.get("last_seen_at") and m["last_seen_at"] > thirty_min_ago:
            continue
        # Check cooldown (one briefing per day per Met)
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT COUNT(*) AS n FROM rosie_audit_log
                       WHERE met_user_id = %s
                         AND action = 'proactive_morning_briefing'
                         AND created_at_ms >= %s""",
                    (m["id"], int(datetime.combine(now_et.date(), datetime.min.time(),
                                                    tzinfo=ZoneInfo("America/New_York")).timestamp() * 1000)),
                )
                if cur.fetchone()["n"] > 0:
                    continue

        # Count today's tasks for this Met
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT COUNT(*) AS n, MIN(due_at_ms) AS first_due
                       FROM daily_brief_tasks
                       WHERE assigned_met_id = %s
                         AND task_date = %s
                         AND sent_at_ms IS NULL""",
                    (m["id"], today_str),
                )
                row = cur.fetchone()

        task_count = (row or {}).get("n") or 0
        if task_count == 0:
            continue  # nothing to brief about

        first_due_ms = row.get("first_due") or 0
        first_due_str = ""
        if first_due_ms:
            fd = datetime.fromtimestamp(first_due_ms / 1000, tz=ZoneInfo("America/New_York"))
            first_due_str = fd.strftime("%I:%M %p ET").lstrip("0")

        first_name = (m.get("name") or "").split()[0] or "there"
        msg = (
            f"Good morning, {first_name}. You have {task_count} brief "
            f"{'task' if task_count == 1 else 'tasks'} today"
            f"{', earliest by ' + first_due_str if first_due_str else ''}. "
            f"Open your workspace when ready.\n— Rosie"
        )
        try:
            sent = send_sms_from(m["phone"], msg, ROSIE_TWILIO_NUMBER)
        except Exception as e:
            print(f"[rosie-morning] send failed met={m['id']}: {e}", flush=True)
            sent = False
        _rosie_audit(m["id"], "sms", "proactive_morning_briefing",
                     f"{task_count} tasks today", tier=1, success=sent)


def _rosie_proactive_inactivity_nudge():
    """If a Met hasn't logged in for 7+ days, send a friendly check-in.

    Cooldown: once per Met per 7-day rolling window. Won't repeat-nudge.
    Only fires once a day (runs at 4 PM ET).
    """
    now_et = datetime.now(ZoneInfo("America/New_York"))
    if not (now_et.hour == 16 and now_et.minute < 6):
        return  # narrow window

    now_ms = int(time.time() * 1000)
    seven_days_ago = now_ms - 7 * 24 * 60 * 60 * 1000

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, u.phone, mh.last_seen_at
                   FROM users u
                   JOIN user_roles ur ON ur.user_id = u.id AND ur.role = 'met'
                   LEFT JOIN met_heartbeat mh ON mh.met_user_id = u.id
                   WHERE u.is_active = TRUE AND u.phone IS NOT NULL
                     AND (mh.last_seen_at IS NULL OR mh.last_seen_at < %s)""",
                (seven_days_ago,),
            )
            inactive = cur.fetchall()

    for m in inactive:
        # Cooldown check: don't nudge if we nudged this Met in last 7 days
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT COUNT(*) AS n FROM rosie_audit_log
                       WHERE met_user_id = %s
                         AND action = 'proactive_inactivity_nudge'
                         AND created_at_ms >= %s""",
                    (m["id"], seven_days_ago),
                )
                if cur.fetchone()["n"] > 0:
                    continue

        first_name = (m.get("name") or "").split()[0] or "there"
        msg = (
            f"Hey {first_name}, haven't seen you log in for a bit. "
            f"Everything OK? If you need to drop shifts or change your "
            f"schedule, just text me back.\n— Rosie"
        )
        try:
            sent = send_sms_from(m["phone"], msg, ROSIE_TWILIO_NUMBER)
        except Exception as e:
            print(f"[rosie-inactivity] send failed met={m['id']}: {e}", flush=True)
            sent = False
        _rosie_audit(m["id"], "sms", "proactive_inactivity_nudge",
                     "7-day inactivity check-in", tier=1, success=sent)


def _rosie_proactive_severe_weather_heads_up():
    """When a tornado/severe-T-storm warning fires affecting a Met's
    primary subscribers, send a one-time heads-up.

    Cooldown: per (Met, NWS event id) — same warning won't re-page.
    Only sends to the PRIMARY met for affected subscribers.
    """
    try:
        alerts = _get_cached_nws_alerts() or []
    except Exception:
        return

    # Find current severe alerts
    severe = []
    for a in alerts:
        props = (a or {}).get("properties") or {}
        ev = (props.get("event") or "").lower()
        if any(k in ev for k in ("tornado warning", "severe thunderstorm warning",
                                  "flash flood warning")):
            severe.append({
                "id": props.get("id") or str(hash(json.dumps(props, sort_keys=True)))[:32],
                "event": props.get("event"),
                "area": props.get("areaDesc", "")[:120],
                "same_codes": props.get("geocode", {}).get("SAME") or [],
            })

    if not severe:
        return

    # For each severe alert, find affected Pro subscribers and their primary Mets.
    # Match strategy: NWS alerts include affectedZones URLs and areaDesc that
    # mentions counties. For v1 we do a loose substring match: subscriber's
    # saved-location county appears in the alert's areaDesc text. Imperfect
    # but works for the launch team's coverage areas.
    for alert in severe:
        area_desc = (alert.get("area") or "").lower()
        if not area_desc:
            continue

        with db() as conn:
            with conn.cursor() as cur:
                # Find Pro subscribers whose county name appears in the alert area.
                # The county column on saved_locations stores e.g. "Boone County".
                cur.execute(
                    """SELECT DISTINCT sc.primary_met_id, loc.county
                       FROM subscriber_coverage sc
                       JOIN users u ON u.id = sc.user_id
                       JOIN saved_locations loc ON loc.user_id = sc.user_id AND loc.is_primary = TRUE
                       WHERE u.is_active = TRUE
                         AND u.subscription_tier IN ('pro_single','pro_multi','pro_enterprise')
                         AND sc.primary_met_id IS NOT NULL
                         AND loc.county IS NOT NULL""",
                )
                rows = cur.fetchall()
        met_ids = set()
        for r in rows:
            county = (r.get("county") or "").lower().replace(" county", "").strip()
            if county and county in area_desc:
                met_ids.add(r["primary_met_id"])

        for met_id in met_ids:
            # Cooldown: have we already paged this Met for this event id?
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        """SELECT COUNT(*) AS n FROM rosie_audit_log
                           WHERE met_user_id = %s
                             AND action = 'proactive_severe_heads_up'
                             AND detail LIKE %s""",
                        (met_id, f"%{alert['id'][:32]}%"),
                    )
                    if cur.fetchone()["n"] > 0:
                        continue
                    cur.execute("SELECT phone, name FROM users WHERE id = %s", (met_id,))
                    u = cur.fetchone()

            if not (u and u.get("phone")):
                continue
            first_name = (u.get("name") or "").split()[0] or "there"
            msg = (
                f"Heads up, {first_name}: {alert['event']} affecting your "
                f"subscribers — {alert['area'][:90]}. NWS feed is live. "
                f"You're primary.\n— Rosie"
            )
            try:
                sent = send_sms_from(u["phone"], msg, ROSIE_TWILIO_NUMBER)
            except Exception as e:
                print(f"[rosie-severe] send failed met={met_id}: {e}", flush=True)
                sent = False
            _rosie_audit(met_id, "sms", "proactive_severe_heads_up",
                         f"Event id {alert['id'][:32]}: {alert['event']}",
                         tier=1, success=sent)


def _rosie_proactive_check_tick():
    """Top-level cron entry: dispatches each proactive trigger.
    Each individual trigger checks its own time window + cooldown, so this
    is just a fan-out point. Runs every 60s alongside other cron jobs."""
    if os.environ.get("WV_ROSIE_DISABLED") == "1":
        return
    for fn in (_rosie_proactive_morning_briefing,
               _rosie_proactive_inactivity_nudge,
               _rosie_proactive_severe_weather_heads_up):
        try:
            fn()
        except Exception as e:
            print(f"[rosie-proactive] {fn.__name__} failed: {e}", flush=True)


# Reminder firing (cron). Plugged into the main scheduler loop below.
def _rosie_fire_reminders():
    """Check for due reminders and send SMS to the recipient Met."""
    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT r.id, r.met_user_id, r.message, u.phone
                   FROM rosie_reminders r
                   JOIN users u ON u.id = r.met_user_id
                   WHERE r.remind_at_ms <= %s
                     AND r.fired_at_ms IS NULL
                     AND r.cancelled_at_ms IS NULL
                   LIMIT 20""",
                (now_ms,),
            )
            due = cur.fetchall()
    for r in due:
        sent_ok = False
        try:
            if r.get("phone"):
                # Use Rosie's dedicated number so replies route to her SMS webhook
                sent_ok = bool(send_sms_from(r["phone"], f"{r['message']}\n— Rosie", ROSIE_TWILIO_NUMBER))
        except Exception as e:
            print(f"[rosie-reminder] send failed: {e}", flush=True)
        try:
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        "UPDATE rosie_reminders SET fired_at_ms = %s WHERE id = %s",
                        (now_ms, r["id"]),
                    )
        except Exception as e:
            print(f"[rosie-reminder] mark fired failed: {e}", flush=True)
        _rosie_audit(r["met_user_id"], "sms", "fired_reminder",
                     f"Reminder: {r['message'][:80]}", tier=1, success=sent_ok)


def _rosie_seed_kb():
    """Seed initial KB docs if table is empty. Idempotent."""
    docs = [
        ("How to send a Pro Brief",
         "pro,brief,send,subscriber",
         "Pro briefs are AI-drafted morning briefs for Pro subscribers. Steps:\n"
         "1. Open Met workspace → Pro Briefs tab\n"
         "2. Find the pending draft for your subscriber\n"
         "3. Click 'Review & send'\n"
         "4. Read the AI draft. Edit body and verdict as needed.\n"
         "5. Use 'Polish writing' button for a quick grammar check\n"
         "6. Click 'Send to subscriber'\n"
         "The system sends via SMS + email and auto-marks your daily brief task complete."),

        ("How to send a Daily Brief",
         "daily,brief,broadcast,region",
         "Daily Briefs are sent to all subscribers in a county/region. Steps:\n"
         "1. Met workspace → Daily Brief tab\n"
         "2. Pick state + counties\n"
         "3. Optionally draw a polygon to limit area\n"
         "4. Pick headline verdict: Generally Clear, Mixed, or Active Weather\n"
         "5. Write the summary (visible to subscribers)\n"
         "6. Use 'Polish writing' for grammar check\n"
         "7. Click 'Publish daily brief'\n"
         "You can also save as draft or schedule for later."),

        ("How to confirm a severe alert",
         "severe,alert,nws,tornado,warning,confirm",
         "When NWS issues a severe alert that affects a Pro subscriber, an alert page appears:\n"
         "1. Review the NWS event, area, instructions\n"
         "2. Check which subscribers are affected\n"
         "3. Write a custom message to subscribers (under 200 chars for SMS)\n"
         "4. Choose to sign with your name\n"
         "5. Click 'Send alert to subscribers' (or 'Dismiss as false alarm' if you judge it's not real)\n"
         "Once sent, all affected subscribers get SMS + email immediately."),

        ("How to claim a $19 review",
         "review,claim,queue,paid",
         "$19 reviews come into the Review Queue. Steps:\n"
         "1. Met workspace → Review Queue tab\n"
         "2. Pending reviews are first-claim-wins (30-min lock once claimed)\n"
         "3. Click the review to claim it\n"
         "4. Read customer plan, AI suggestion, weather data\n"
         "5. Write your verdict (Clear/Caution/Risk), reasoning, what to watch, bottom line\n"
         "6. Click 'Submit review'\n"
         "You earn 65% of $19 ($12.35). Tips go 100% to you."),

        ("How to open a Storm Shelter activation",
         "storm,shelter,activation,severe,pay",
         "When NWS issues a tornado or severe T-storm warning affecting your subscribers:\n"
         "1. Met workspace → Schedule tab → Storm Shelter activations section\n"
         "2. Click '⚡ Open new activation'\n"
         "3. Enter region label (e.g. 'Central Kansas')\n"
         "4. Optionally enter NWS event name (e.g. 'Tornado Warning') for auto-close\n"
         "5. Activation is now OPEN — you're monitoring this event\n"
         "6. When the event ends, click 'Close activation' OR wait for auto-close\n"
         "You earn $25 per closed activation."),

        ("How to drop a shift / take a day off",
         "shift,drop,off,schedule,day off",
         "To take a specific day off:\n"
         "1. Met workspace → Schedule tab → Next 14 days\n"
         "2. Find the day you want off\n"
         "3. Click the drop button on that day's row\n"
         "Or just ask Rosie: 'Drop my Saturday May 24 shift.'\n"
         "Dropping creates an override. Coverage gaps will show red on the admin dashboard."),

        ("How does pay work?",
         "pay,earnings,money,salary,split",
         "Met pay model:\n"
         "- $19 reviews: 65% to Met ($12.35), 35% to house\n"
         "- Pro subscriber daily briefs: 50% to Met of the prorated daily share\n"
         "  (Pro Single = $6.67/day per subscriber, Pro Multi = $20/day, Pro Enterprise ~ $33/day)\n"
         "- Tips: 100% to Met\n"
         "- Storm Shelter activations: $25 flat per closed activation\n"
         "Earnings update in real time in your workspace. Final payouts on the 1st of the next month."),

        ("Pro Threads etiquette",
         "pro,threads,messages,subscriber,reply",
         "Pro Threads = direct messages between Pro subscribers and the Met team. Guidelines:\n"
         "- Reply within 30 minutes during business hours (6 AM – 9 PM ET)\n"
         "- Be professional. Sign with your name.\n"
         "- For severe weather, lead with the action (\"Take shelter now\") then context\n"
         "- If you don't know, say so. Don't speculate.\n"
         "- For complex questions, suggest a phone call instead\n"
         "Pro Thread content is private. Rosie cannot read it."),

        ("How to escalate to Michael",
         "escalate,michael,help,problem,issue",
         "When to escalate to Michael (CEO):\n"
         "- Customer complaint or refund request\n"
         "- Coverage gap you can't fill\n"
         "- Severe weather event needing more Mets\n"
         "- Pay or schedule question Rosie can't answer\n"
         "- Anything that feels above your authority\n"
         "Channels: text Michael directly, or ask Rosie to draft a request for him."),

        ("What can Rosie do?",
         "rosie,help,assistant,what,capabilities",
         "Rosie helps with:\n"
         "- Your schedule (view, drop days)\n"
         "- Your earnings (current month breakdown)\n"
         "- Brief tasks today/tomorrow\n"
         "- Your primary subscribers\n"
         "- Team status (who's online)\n"
         "- Active severe weather\n"
         "- Scheduling reminders (SMS to you at a future time)\n"
         "- How-to questions about WeatherValet\n"
         "- Drafting requests for Michael's review\n\n"
         "Rosie cannot send subscriber-facing messages, approve severe alerts, "
         "modify pay, or read Pro Threads. She defers to Michael and Joe on policy."),
    ]
    now_ms = int(time.time() * 1000)
    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute("SELECT COUNT(*) AS n FROM rosie_kb_docs")
                if cur.fetchone()["n"] > 0:
                    return  # already seeded
                for title, tags, content in docs:
                    cur.execute(
                        """INSERT INTO rosie_kb_docs (title, tags, content, status, created_at_ms, updated_at_ms)
                           VALUES (%s, %s, %s, 'active', %s, %s)""",
                        (title, tags, content, now_ms, now_ms),
                    )
        print(f"[rosie-kb] seeded {len(docs)} initial docs", flush=True)
    except Exception as e:
        print(f"[rosie-kb] seed failed: {e}", flush=True)


# Get current Met's own recurring schedule (read-only convenience)
@app.route("/api/v1/met/my-schedule", methods=["OPTIONS"])
def _met_my_schedule_preflight():
    return ("", 204)


@app.get("/api/v1/met/my-schedule")
def met_my_schedule():
    """Returns the current Met's recurring shifts + upcoming 14 days
    of resolved coverage assignments (with overrides applied)."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            # Recurring shifts
            cur.execute(
                """SELECT mrs.id, mrs.day_of_week, mrs.scope_kind,
                          mrs.subscriber_user_id, mrs.set_owner_met_id,
                          su.name AS subscriber_name, su.email AS subscriber_email,
                          so.name AS set_owner_name
                   FROM met_recurring_shifts mrs
                   LEFT JOIN users su ON su.id = mrs.subscriber_user_id
                   LEFT JOIN users so ON so.id = mrs.set_owner_met_id
                   WHERE mrs.met_user_id = %s
                   ORDER BY mrs.day_of_week, mrs.scope_kind""",
                (user["id"],),
            )
            recurring = cur.fetchall()
            # Upcoming overrides next 14 days
            today_str = datetime.now(timezone.utc).strftime("%Y-%m-%d")
            cur.execute(
                """SELECT mso.id, mso.shift_date, mso.scope_kind,
                          mso.subscriber_user_id, mso.set_owner_met_id,
                          mso.override_kind,
                          su.name AS subscriber_name, so.name AS set_owner_name
                   FROM met_shift_overrides mso
                   LEFT JOIN users su ON su.id = mso.subscriber_user_id
                   LEFT JOIN users so ON so.id = mso.set_owner_met_id
                   WHERE mso.met_user_id = %s
                     AND mso.shift_date >= %s
                   ORDER BY mso.shift_date""",
                (user["id"], today_str),
            )
            overrides = cur.fetchall()

    return jsonify({
        "ok": True,
        "recurring_shifts": [_serialize_recurring_shift(r) for r in recurring],
        "overrides": [_serialize_shift_override(r) for r in overrides],
    })


def _serialize_recurring_shift(r):
    return {
        "id": r["id"],
        "day_of_week": r["day_of_week"],
        "scope_kind": r["scope_kind"],
        "subscriber_user_id": r["subscriber_user_id"],
        "set_owner_met_id": r["set_owner_met_id"],
        "subscriber_name": r.get("subscriber_name"),
        "set_owner_name": r.get("set_owner_name"),
    }


def _serialize_shift_override(r):
    return {
        "id": r["id"],
        "shift_date": r["shift_date"],
        "scope_kind": r["scope_kind"],
        "subscriber_user_id": r["subscriber_user_id"],
        "set_owner_met_id": r["set_owner_met_id"],
        "override_kind": r["override_kind"],
        "subscriber_name": r.get("subscriber_name"),
        "set_owner_name": r.get("set_owner_name"),
    }


# Create / delete a recurring shift
@app.route("/api/v1/met/recurring-shifts", methods=["OPTIONS"])
def _met_recurring_shifts_preflight():
    return ("", 204)


@app.post("/api/v1/met/recurring-shifts")
def met_create_recurring_shift():
    """Create a recurring weekly shift for the current Met.

    Body: {
      day_of_week: 0-6,
      scope_kind: 'subscriber'|'subscriber_set'|'review_pool',
      subscriber_user_id: int (required if scope='subscriber'),
      set_owner_met_id:   int (required if scope='subscriber_set')
    }
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    try:
        dow = int(data.get("day_of_week", -1))
    except (TypeError, ValueError):
        dow = -1
    if dow < 0 or dow > 6:
        return jsonify({"ok": False, "error": "invalid-day"}), 400

    scope = (data.get("scope_kind") or "").strip().lower()
    if scope not in ("subscriber", "subscriber_set", "review_pool"):
        return jsonify({"ok": False, "error": "invalid-scope"}), 400

    subscriber_id = data.get("subscriber_user_id")
    set_owner_id = data.get("set_owner_met_id")

    if scope == "subscriber":
        if not subscriber_id:
            return jsonify({"ok": False, "error": "subscriber-required"}), 400
        set_owner_id = None
    elif scope == "subscriber_set":
        if not set_owner_id:
            return jsonify({"ok": False, "error": "set-owner-required"}), 400
        subscriber_id = None
    else:  # review_pool
        subscriber_id = None
        set_owner_id = None

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            try:
                cur.execute(
                    """INSERT INTO met_recurring_shifts
                       (met_user_id, day_of_week, scope_kind,
                        subscriber_user_id, set_owner_met_id, created_at)
                       VALUES (%s, %s, %s, %s, %s, %s)
                       ON CONFLICT DO NOTHING
                       RETURNING id""",
                    (user["id"], dow, scope, subscriber_id, set_owner_id, now_ms),
                )
                row = cur.fetchone()
            except Exception as e:
                print(f"[met-shift-create] error: {e!r}", flush=True)
                return jsonify({"ok": False, "error": "db-error"}), 500
    return jsonify({"ok": True, "id": (row["id"] if row else None)})


@app.route("/api/v1/met/recurring-shifts/<int:shift_id>", methods=["OPTIONS"])
def _met_recurring_shift_delete_preflight(shift_id):
    return ("", 204)


@app.delete("/api/v1/met/recurring-shifts/<int:shift_id>")
def met_delete_recurring_shift(shift_id: int):
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    is_admin = "admin" in roles

    with db() as conn:
        with conn.cursor() as cur:
            if is_admin:
                cur.execute(
                    "DELETE FROM met_recurring_shifts WHERE id = %s",
                    (shift_id,),
                )
            else:
                cur.execute(
                    "DELETE FROM met_recurring_shifts WHERE id = %s AND met_user_id = %s",
                    (shift_id, user["id"]),
                )
    return jsonify({"ok": True})


# Per-date shift overrides — drop/claim
@app.route("/api/v1/met/shift-overrides", methods=["OPTIONS"])
def _met_shift_overrides_preflight():
    return ("", 204)


@app.post("/api/v1/met/shift-overrides")
def met_create_shift_override():
    """Drop a shift for a specific date, OR claim an open one.

    Body: {
      shift_date: 'YYYY-MM-DD',
      scope_kind: 'subscriber'|'subscriber_set'|'review_pool',
      subscriber_user_id: int (if subscriber),
      set_owner_met_id: int (if subscriber_set),
      override_kind: 'drop'|'claim'|'assign'
    }

    drop: marks the current Met as off for this date for this scope.
    claim: current Met picks up the shift for this date.
    assign: admin-only, assigns to met_user_id in body.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    roles = user.get("roles") or []
    if "met" not in roles and "admin" not in roles:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    is_admin = "admin" in roles

    data = request.get_json(silent=True) or {}
    shift_date = (data.get("shift_date") or "").strip()
    if not re.match(r"^\d{4}-\d{2}-\d{2}$", shift_date):
        return jsonify({"ok": False, "error": "invalid-date"}), 400

    scope = (data.get("scope_kind") or "").strip().lower()
    if scope not in ("subscriber", "subscriber_set", "review_pool"):
        return jsonify({"ok": False, "error": "invalid-scope"}), 400

    override_kind = (data.get("override_kind") or "").strip().lower()
    if override_kind not in ("drop", "claim", "assign"):
        return jsonify({"ok": False, "error": "invalid-override"}), 400

    if override_kind == "assign" and not is_admin:
        return jsonify({"ok": False, "error": "admin-only"}), 403

    subscriber_id = data.get("subscriber_user_id") if scope == "subscriber" else None
    set_owner_id = data.get("set_owner_met_id") if scope == "subscriber_set" else None

    if scope == "subscriber" and not subscriber_id:
        return jsonify({"ok": False, "error": "subscriber-required"}), 400
    if scope == "subscriber_set" and not set_owner_id:
        return jsonify({"ok": False, "error": "set-owner-required"}), 400

    # drop: met_user_id is the dropping Met (whose shift is being dropped)
    # claim: met_user_id is the current user (who's picking up the slot)
    # assign: admin specifies met_user_id in body
    if override_kind == "assign":
        met_id = data.get("met_user_id")
        if not met_id:
            return jsonify({"ok": False, "error": "met-required"}), 400
    elif override_kind == "drop":
        # For "drop", record WHICH Met is dropping. The resolver needs
        # this to exclude only that Met from coverage — not everyone.
        met_id = user["id"]
    else:  # claim
        met_id = user["id"]

    now_ms = int(time.time() * 1000)
    notes = (data.get("notes") or "").strip() or None

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO met_shift_overrides
                   (met_user_id, shift_date, scope_kind,
                    subscriber_user_id, set_owner_met_id,
                    override_kind, created_at, notes)
                   VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                   RETURNING id""",
                (met_id, shift_date, scope, subscriber_id, set_owner_id,
                 override_kind, now_ms, notes),
            )
            row = cur.fetchone()
    return jsonify({"ok": True, "id": row["id"] if row else None})


# Subscriber's own delivery time preference (called from subscriber portal)
@app.route("/api/v1/me/brief-delivery-time", methods=["OPTIONS"])
def _me_brief_delivery_preflight():
    return ("", 204)


@app.get("/api/v1/me/brief-delivery-time")
def me_get_brief_delivery():
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT daily_brief_time, daily_brief_timezone
                   FROM subscriber_coverage WHERE user_id = %s""",
                (user["id"],),
            )
            r = cur.fetchone()
    if not r:
        return jsonify({"ok": True, "delivery_time": "07:00",
                       "delivery_timezone": "America/New_York",
                       "configured": False})
    return jsonify({
        "ok": True,
        "delivery_time": r["daily_brief_time"],
        "delivery_timezone": r["daily_brief_timezone"],
        "configured": True,
    })


@app.patch("/api/v1/me/brief-delivery-time")
def me_set_brief_delivery():
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    data = request.get_json(silent=True) or {}
    new_time = (data.get("delivery_time") or "").strip()
    new_tz = (data.get("delivery_timezone") or "America/New_York").strip()
    if not re.match(r"^\d{2}:\d{2}$", new_time):
        return jsonify({"ok": False, "error": "invalid-time"}), 400
    # Basic timezone validation — accept anything that looks like an IANA name
    if not re.match(r"^[A-Za-z_]+/[A-Za-z_/]+$", new_tz):
        return jsonify({"ok": False, "error": "invalid-timezone"}), 400

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO subscriber_coverage
                   (user_id, daily_brief_time, daily_brief_timezone, updated_at)
                   VALUES (%s, %s, %s, %s)
                   ON CONFLICT (user_id) DO UPDATE
                   SET daily_brief_time = EXCLUDED.daily_brief_time,
                       daily_brief_timezone = EXCLUDED.daily_brief_timezone,
                       updated_at = EXCLUDED.updated_at""",
                (user["id"], new_time, new_tz, now_ms),
            )
    return jsonify({"ok": True})


# Admin: assign primary Met to a Pro subscriber
@app.route("/api/v1/admin/subscriber-coverage/<int:subscriber_id>", methods=["OPTIONS"])
def _admin_subcov_preflight(subscriber_id):
    return ("", 204)


@app.patch("/api/v1/admin/subscriber-coverage/<int:subscriber_id>")
@require_role("admin")
def admin_set_subscriber_coverage(subscriber_id):
    """Admin sets primary/backup Met for a Pro subscriber."""
    data = request.get_json(silent=True) or {}
    primary_met_id = data.get("primary_met_id")  # null is OK (unassign)
    backup_met_id = data.get("backup_met_id")
    notes = (data.get("notes") or "").strip() or None
    next_br_due = data.get("next_br_due")  # ms epoch or null

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO subscriber_coverage
                   (user_id, primary_met_id, backup_met_id, notes, next_br_due, updated_at)
                   VALUES (%s, %s, %s, %s, %s, %s)
                   ON CONFLICT (user_id) DO UPDATE
                   SET primary_met_id = EXCLUDED.primary_met_id,
                       backup_met_id = EXCLUDED.backup_met_id,
                       notes = COALESCE(EXCLUDED.notes, subscriber_coverage.notes),
                       next_br_due = EXCLUDED.next_br_due,
                       updated_at = EXCLUDED.updated_at""",
                (subscriber_id, primary_met_id, backup_met_id, notes, next_br_due, now_ms),
            )
    return jsonify({"ok": True})


# Admin: 7-day coverage dashboard
@app.route("/api/v1/admin/coverage-dashboard", methods=["OPTIONS"])
def _admin_coverage_dashboard_preflight():
    return ("", 204)


@app.get("/api/v1/admin/coverage-dashboard")
@require_role("admin")
def admin_coverage_dashboard():
    """Returns next-7-days coverage status:
      - For each Pro subscriber: who's covering each day, or GAP
      - For Review Pool: which Mets are covering each day, or GAP
      - Live "available right now" Mets (heartbeat in last 5 min)
    """
    now = datetime.now(timezone.utc)
    now_ms = int(now.timestamp() * 1000)
    days = []
    for i in range(7):
        d = now + timedelta(days=i)
        days.append({
            "date": d.strftime("%Y-%m-%d"),
            "day_of_week": d.weekday() if False else (d.weekday() + 1) % 7,
            # Python's weekday() is 0=Mon; we use 0=Sun, so +1 mod 7
        })

    with db() as conn:
        with conn.cursor() as cur:
            # Get all Pro subscribers with their coverage
            cur.execute(
                """SELECT u.id, u.name, u.email,
                          u.subscription_tier AS tier,
                          sc.primary_met_id, sc.backup_met_id,
                          sc.daily_brief_time, sc.daily_brief_timezone,
                          pm.name AS primary_met_name,
                          bm.name AS backup_met_name
                   FROM users u
                   JOIN user_roles ur ON ur.user_id = u.id AND ur.role = 'subscriber'
                   LEFT JOIN subscriber_coverage sc ON sc.user_id = u.id
                   LEFT JOIN users pm ON pm.id = sc.primary_met_id
                   LEFT JOIN users bm ON bm.id = sc.backup_met_id
                   WHERE u.is_active = TRUE
                     AND u.subscription_tier IN ('pro_single','pro_multi','pro_enterprise')
                   ORDER BY u.name""",
            )
            subscribers = cur.fetchall()

            # Get all recurring shifts grouped
            cur.execute(
                """SELECT mrs.*, u.name AS met_name
                   FROM met_recurring_shifts mrs
                   JOIN users u ON u.id = mrs.met_user_id
                   WHERE u.is_active = TRUE"""
            )
            recurring = cur.fetchall()

            # Get overrides in the date range
            cur.execute(
                """SELECT mso.*, u.name AS met_name
                   FROM met_shift_overrides mso
                   LEFT JOIN users u ON u.id = mso.met_user_id
                   WHERE mso.shift_date >= %s
                     AND mso.shift_date <= %s
                   ORDER BY mso.created_at""",
                (days[0]["date"], days[-1]["date"]),
            )
            overrides = cur.fetchall()

            # Live heartbeat — Mets seen in last 5 minutes
            five_min_ago = now_ms - 5 * 60 * 1000
            cur.execute(
                """SELECT mh.met_user_id, mh.last_seen_at, u.name
                   FROM met_heartbeat mh
                   JOIN users u ON u.id = mh.met_user_id
                   WHERE mh.last_seen_at >= %s
                     AND u.is_active = TRUE""",
                (five_min_ago,),
            )
            live_mets = cur.fetchall()

    # Build the per-subscriber coverage map
    sub_coverage = []
    for sub in subscribers:
        days_status = []
        for d in days:
            assigned_met = _resolve_coverage_for_day(
                d["date"], d["day_of_week"], sub["id"], sub["primary_met_id"],
                recurring, overrides, scope="subscriber"
            )
            # is_gap: nobody assigned at all
            # is_soft_gap: only the primary-fallback applies — primary
            # Met is the owner but has no recurring shift for this day.
            # Treated visually as "warning" not "ok".
            via = assigned_met["via"] if assigned_met else None
            days_status.append({
                "date": d["date"],
                "day_of_week": d["day_of_week"],
                "assigned_met_id": assigned_met["met_id"] if assigned_met else None,
                "assigned_met_name": assigned_met["met_name"] if assigned_met else None,
                "via": via,
                "is_gap": assigned_met is None,
                "is_soft_gap": (via == "primary-fallback"),
            })
        sub_coverage.append({
            "subscriber_id": sub["id"],
            "subscriber_name": sub["name"],
            "subscriber_email": sub["email"],
            "tier": sub["tier"],
            "primary_met_id": sub["primary_met_id"],
            "primary_met_name": sub["primary_met_name"],
            "backup_met_id": sub["backup_met_id"],
            "backup_met_name": sub["backup_met_name"],
            "daily_brief_time": sub["daily_brief_time"] if sub["daily_brief_time"] else "07:00",
            "daily_brief_timezone": sub["daily_brief_timezone"] if sub["daily_brief_timezone"] else "America/New_York",
            "days": days_status,
        })

    # Review Pool per-day
    pool_coverage = []
    for d in days:
        assigned = _resolve_review_pool_for_day(
            d["date"], d["day_of_week"], recurring, overrides
        )
        pool_coverage.append({
            "date": d["date"],
            "day_of_week": d["day_of_week"],
            "covering_mets": assigned,
            "is_gap": len(assigned) == 0,
        })

    return jsonify({
        "ok": True,
        "days": days,
        "subscriber_coverage": sub_coverage,
        "review_pool_coverage": pool_coverage,
        "live_mets": [
            {"met_id": m["met_user_id"], "name": m["name"], "last_seen_at": m["last_seen_at"]}
            for m in live_mets
        ],
        "generated_at_ms": now_ms,
    })


def _resolve_coverage_for_day(date_str, day_of_week, subscriber_id, primary_met_id,
                              all_recurring, all_overrides, scope="subscriber"):
    """Resolve who covers this subscriber's daily brief on this date.

    Order:
      1. Specific override for this exact (date, subscriber, claim)
      2. Specific recurring shift for this (dow, subscriber)
      3. subscriber_set recurring for set_owner = primary_met
      4. subscriber_coverage.primary_met_id fallback
    """
    # Drops first — they invalidate later resolutions.
    # A "drop" is a Met saying "I'm not covering this on this date."
    # met_user_id on the override row identifies WHICH Met dropped.
    # For subscriber scope: drop applies if the primary Met dropped this
    # subscriber's brief. We collect the set of "dropped by" met ids.
    drop_met_ids_for_subscriber = set()
    for o in all_overrides:
        if (o["shift_date"] == date_str
            and o["scope_kind"] == "subscriber"
            and o["subscriber_user_id"] == subscriber_id
            and o["override_kind"] == "drop"
            and o["met_user_id"] is not None):
            drop_met_ids_for_subscriber.add(o["met_user_id"])
    has_drop_primary = (primary_met_id in drop_met_ids_for_subscriber) if primary_met_id else False

    # 1. Override claim/assign for this specific subscriber + date
    for o in all_overrides:
        if (o["shift_date"] == date_str
            and o["scope_kind"] == "subscriber"
            and o["subscriber_user_id"] == subscriber_id
            and o["override_kind"] in ("claim", "assign")
            and o["met_user_id"] is not None):
            return {"met_id": o["met_user_id"], "met_name": o["met_name"], "via": "override"}

    # Check subscriber_set drops. A drop on a "subscriber_set" override
    # means: "I (met_user_id) am not covering my own (or set_owner_met_id's)
    # set on this date." Since dropping your own set is the common case,
    # we collect the set owners whose set has been dropped.
    set_drops = set()
    for o in all_overrides:
        if (o["shift_date"] == date_str
            and o["scope_kind"] == "subscriber_set"
            and o["override_kind"] == "drop"
            and o["set_owner_met_id"] is not None):
            set_drops.add(o["set_owner_met_id"])

    # 2. Recurring subscriber-specific shift
    if not has_drop_primary:
        for r in all_recurring:
            if (r["day_of_week"] == day_of_week
                and r["scope_kind"] == "subscriber"
                and r["subscriber_user_id"] == subscriber_id):
                return {"met_id": r["met_user_id"], "met_name": r["met_name"], "via": "recurring"}

    # 3. subscriber_set coverage — someone covering Chris's set (when this
    #    sub belongs to Chris). Skip if Chris dropped his set this date.
    # 3a. First check: did anyone CLAIM Chris's set for this date?
    for o in all_overrides:
        if (o["shift_date"] == date_str
            and o["scope_kind"] == "subscriber_set"
            and o["set_owner_met_id"] == primary_met_id
            and o["override_kind"] in ("claim", "assign")
            and o["met_user_id"] is not None):
            return {"met_id": o["met_user_id"], "met_name": o["met_name"], "via": "set-override"}

    # 3b. Recurring set coverage (if primary didn't drop)
    if primary_met_id not in set_drops and not has_drop_primary:
        for r in all_recurring:
            if (r["day_of_week"] == day_of_week
                and r["scope_kind"] == "subscriber_set"
                and r["set_owner_met_id"] == primary_met_id):
                return {"met_id": r["met_user_id"], "met_name": r["met_name"], "via": "set-recurring"}

    # 4. Primary Met fallback (the assigned met for this subscriber)
    if primary_met_id and not has_drop_primary and primary_met_id not in set_drops:
        # Did primary also have a recurring shift today?
        for r in all_recurring:
            if (r["day_of_week"] == day_of_week
                and r["scope_kind"] == "subscriber"
                and r["subscriber_user_id"] == subscriber_id
                and r["met_user_id"] == primary_met_id):
                return {"met_id": primary_met_id, "met_name": r["met_name"], "via": "primary"}
        # No specific recurring shift, but primary is assigned. The
        # brief still needs writing — primary is responsible by default.
        # Caller treats `via=primary-fallback` as a soft warning (yellow)
        # rather than confirmed coverage (green).
        # Look up primary's name from any of their other shifts so the UI
        # has a name to display.
        primary_name = None
        for r in all_recurring:
            if r["met_user_id"] == primary_met_id:
                primary_name = r.get("met_name")
                break
        return {"met_id": primary_met_id, "met_name": primary_name, "via": "primary-fallback"}

    return None  # GAP


def _resolve_review_pool_for_day(date_str, day_of_week, all_recurring, all_overrides):
    """Returns list of {met_id, name, via} covering review pool that day."""
    out = []
    seen = set()

    # 1. Overrides (claims) for this date
    for o in all_overrides:
        if (o["shift_date"] == date_str
            and o["scope_kind"] == "review_pool"
            and o["override_kind"] in ("claim", "assign")
            and o["met_user_id"] is not None
            and o["met_user_id"] not in seen):
            out.append({"met_id": o["met_user_id"], "name": o["met_name"], "via": "override"})
            seen.add(o["met_user_id"])

    # Drops for this date — exclude from recurring
    # Drops for this date — exclude the dropping Met from recurring.
    # Each drop row carries met_user_id (the Met who said "not me").
    # We exclude only that Met, not everyone with a recurring shift.
    drops = set()
    for o in all_overrides:
        if (o["shift_date"] == date_str
            and o["scope_kind"] == "review_pool"
            and o["override_kind"] == "drop"
            and o["met_user_id"] is not None):
            drops.add(o["met_user_id"])

    # 2. Recurring (minus drops)
    for r in all_recurring:
        if (r["day_of_week"] == day_of_week
            and r["scope_kind"] == "review_pool"
            and r["met_user_id"] not in seen
            and r["met_user_id"] not in drops):
            out.append({"met_id": r["met_user_id"], "name": r["met_name"], "via": "recurring"})
            seen.add(r["met_user_id"])

    return out


# Admin: list of all active Mets (for assignment dropdowns)
@app.route("/api/v1/admin/mets-list", methods=["OPTIONS"])
def _admin_mets_list_preflight():
    return ("", 204)


@app.get("/api/v1/admin/mets-list")
@require_role("admin")
def admin_mets_list():
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, u.email
                   FROM users u
                   JOIN user_roles ur ON ur.user_id = u.id AND ur.role = 'met'
                   WHERE u.is_active = TRUE
                   ORDER BY u.name"""
            )
            rows = cur.fetchall()
    return jsonify({
        "ok": True,
        "mets": [{"id": r["id"], "name": r["name"], "email": r["email"]} for r in rows],
    })


@app.route("/api/v1/met/pro-subscribers", methods=["OPTIONS"])
def _met_pro_subscribers_preflight():
    return ("", 204)


@app.get("/api/v1/met/pro-subscribers")
def met_pro_subscribers_list():
    """Returns all Pro-tier subscribers (active subscriptions) so the Met
    can pick one to message. Includes name, email, phone, current tier,
    and primary location label for context.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.email, u.name, u.phone, u.subscription_tier,
                          loc.label AS loc_label, loc.address_text AS loc_address
                   FROM users u
                   LEFT JOIN saved_locations loc
                          ON loc.user_id = u.id AND loc.is_primary = TRUE
                   WHERE u.is_active = TRUE
                     AND u.subscription_tier IN ('pro_single', 'pro_multi', 'pro_enterprise')
                     AND EXISTS (
                       SELECT 1 FROM user_roles ur
                       WHERE ur.user_id = u.id AND ur.role = 'subscriber'
                     )
                   ORDER BY u.name, u.email"""
            )
            rows = cur.fetchall()

    subscribers = [
        {
            "user_id": r["id"],
            "email": r["email"],
            "name": (r.get("name") or "").strip() or None,
            "phone": r.get("phone") or None,
            "tier": r.get("subscription_tier"),
            "loc_label": r.get("loc_label"),
            "loc_address": r.get("loc_address"),
        }
        for r in rows
    ]
    return jsonify({"ok": True, "subscribers": subscribers})


@app.route("/api/v1/met/my-subscribers", methods=["OPTIONS"])
def _met_my_subscribers_preflight():
    return ("", 204)


@app.get("/api/v1/met/my-subscribers")
def met_my_subscribers():
    """Returns ALL subscribers (Hobbyist + Pro) with full operational
    context so the Met can keep track of who needs what.

    For each: name, email, phone, tier, primary location, brief prefs
    (morning window, evening flag, channels), threshold alerts.

    This is the "My Subscribers" tab data — built so the Met can answer
    questions like "Is the athletic director getting what he needs?"
    "Is the roofing company on a Wind > 20mph alert?"

    For v1, all Mets see all subscribers. Region-scoping comes later
    when we have Met-to-region assignments.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.email, u.name, u.phone, u.subscription_tier,
                          u.timezone,
                          loc.label AS loc_label,
                          loc.address_text AS loc_address,
                          loc.county AS loc_county,
                          bp.morning_enabled, bp.morning_window_start,
                          bp.morning_window_end, bp.evening_enabled,
                          bp.channels
                   FROM users u
                   LEFT JOIN saved_locations loc
                          ON loc.user_id = u.id AND loc.is_primary = TRUE
                   LEFT JOIN brief_preferences bp ON bp.user_id = u.id
                   WHERE u.is_active = TRUE
                     AND EXISTS (
                       SELECT 1 FROM user_roles ur
                       WHERE ur.user_id = u.id AND ur.role = 'subscriber'
                     )
                   ORDER BY u.subscription_tier DESC NULLS LAST,
                            u.name, u.email"""
            )
            sub_rows = cur.fetchall()

            # Threshold alerts — one query, group by user
            cur.execute(
                """SELECT user_id, metric, comparator, threshold_value, units, enabled
                   FROM threshold_alerts
                   ORDER BY user_id, created_at"""
            )
            threshold_rows = cur.fetchall()

    thresholds_by_user = {}
    for t in threshold_rows:
        thresholds_by_user.setdefault(t["user_id"], []).append({
            "metric": t["metric"],
            "comparator": t["comparator"],
            "threshold_value": t["threshold_value"],
            "unit": t["units"],
            "is_enabled": bool(t["enabled"]),
        })

    subscribers = []
    for r in sub_rows:
        subscribers.append({
            "user_id": r["id"],
            "email": r["email"],
            "name": (r.get("name") or "").strip() or None,
            "phone": r.get("phone") or None,
            "tier": r.get("subscription_tier") or "free",
            "timezone": r.get("timezone"),
            "loc_label": r.get("loc_label"),
            "loc_address": r.get("loc_address"),
            "loc_county": r.get("loc_county"),
            "brief_prefs": {
                "morning_enabled": bool(r.get("morning_enabled")) if r.get("morning_enabled") is not None else None,
                "morning_window_start": r.get("morning_window_start"),
                "morning_window_end": r.get("morning_window_end"),
                "evening_enabled": bool(r.get("evening_enabled")) if r.get("evening_enabled") is not None else None,
                "channels": r.get("channels") or "sms,email",
            },
            "thresholds": thresholds_by_user.get(r["id"], []),
        })
    return jsonify({"ok": True, "subscribers": subscribers})


@app.route("/api/v1/met/threads/new", methods=["OPTIONS"])
def _met_new_thread_preflight():
    return ("", 204)


@app.post("/api/v1/met/threads/new")
def met_new_thread():
    """Met opens a new Pro Thread with a chosen Pro subscriber.

    Body: {"subscriber_user_id": 42}

    Returns the thread (existing or newly created). The Met then uses
    the existing POST /api/v1/met/threads/<id>/messages to send the
    first message — this keeps the message-send code path single-purpose.
    """
    actor = _get_current_user()
    if actor is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (actor.get("roles") or []) and "admin" not in (actor.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    try:
        subscriber_user_id = int(data.get("subscriber_user_id") or 0)
    except (ValueError, TypeError):
        subscriber_user_id = 0
    if not subscriber_user_id:
        return jsonify({"ok": False, "error": "missing-subscriber-id"}), 400

    # Verify the target is actually a Pro subscriber. We don't let the
    # Met open threads with Hobbyist users — that's deliberate, since
    # Pro Threads is a Pro-tier feature.
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, email, name, subscription_tier FROM users
                   WHERE id = %s AND is_active = TRUE""",
                (subscriber_user_id,),
            )
            sub = cur.fetchone()
    if not sub:
        return jsonify({"ok": False, "error": "subscriber-not-found"}), 404
    if sub.get("subscription_tier") not in ("pro_single", "pro_multi", "pro_enterprise"):
        return jsonify({
            "ok": False,
            "error": "not-pro-subscriber",
            "message": "Pro Threads are only available for Pro-tier subscribers."
        }), 409

    # Get-or-create — idempotent
    thread = _get_or_create_thread_for_subscriber(subscriber_user_id)

    print(
        f"[met-new-thread] met={actor['id']} opened thread={thread['id']} "
        f"with subscriber={subscriber_user_id} ({sub['email']})",
        flush=True,
    )
    return jsonify({
        "ok": True,
        "thread": {
            "id": thread["id"],
            "subscriber_user_id": subscriber_user_id,
            "subscriber_email": sub["email"],
            "subscriber_name": (sub.get("name") or "").strip() or None,
        },
    })


# ════════════════════════════════════════════════════════════════════
# Met tips — customer "like button" tips for $19 reviews
# ════════════════════════════════════════════════════════════════════
#
# The $19 customer gets an SMS after their review delivers:
#   "View full brief + thank Michael: weathervalet.ai/?review=<token>"
#
# The page (built in TIP-B) shows the verdict + tip buttons ($3, $5, $10,
# Custom). When clicked, customer hits POST /api/v1/reviews/<token>/tip.
#
# Payment paths:
#   - Logged-in subscriber: charge their saved Stripe payment method
#     off-session, return success. One-tap.
#   - Anonymous customer: create a Stripe Checkout session and return
#     the checkout URL; client redirects. Standard $19-style flow.
#
# The Stripe webhook (existing /api/v1/stripe/webhook) handles the
# checkout.session.completed event and marks the tip 'completed'.

@app.route("/api/v1/reviews/<review_token>", methods=["OPTIONS"])
def _review_get_preflight(review_token):
    return ("", 204)


@app.get("/api/v1/reviews/<review_token>")
def review_get(review_token: str):
    """Fetch a delivered review by customer_review_token. Returns the
    verdict + Met name. Public — token IS the auth."""
    if not review_token or len(review_token) < 10:
        return jsonify({"ok": False, "error": "invalid-token"}), 400

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, status, plan_text, plan_location, plan_window,
                          meteorologist_verdict, meteorologist_notes,
                          completed_at, completed_by_user_id, completed_by_name,
                          customer_email
                   FROM verification_requests
                   WHERE customer_review_token = %s""",
                (review_token,),
            )
            r = cur.fetchone()

    if not r:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if r["status"] != "completed":
        return jsonify({"ok": False, "error": "not-completed", "status": r["status"]}), 409

    return jsonify({
        "ok": True,
        "review": {
            "verification_request_id": r["id"],
            "plan_text": r["plan_text"],
            "plan_location": r["plan_location"],
            "plan_window": r["plan_window"],
            "verdict": r["meteorologist_verdict"],
            "notes": r["meteorologist_notes"],
            "completed_at": r["completed_at"],
            "met_name": r.get("completed_by_name") or "your meteorologist",
            "met_user_id": r.get("completed_by_user_id"),
            "tip_eligible": bool(r.get("completed_by_user_id")),
        },
    })


@app.route("/api/v1/reviews/<review_token>/tip", methods=["OPTIONS"])
def _review_tip_preflight(review_token):
    return ("", 204)


@app.post("/api/v1/reviews/<review_token>/tip")
def review_tip(review_token: str):
    """Customer tips the Met who delivered their $19 review.

    Body:
      {"amount_cents": 500, "note": "Saved my wedding day!"}

    Returns:
      Subscriber (off-session charge succeeded):
        {"ok": true, "tip_id": N, "status": "completed", "amount_cents": 500}

      Anonymous customer (or off-session not possible):
        {"ok": true, "tip_id": N, "status": "pending",
         "checkout_url": "https://checkout.stripe.com/..."}
    """
    if not review_token or len(review_token) < 10:
        return jsonify({"ok": False, "error": "invalid-token"}), 400

    if stripe is None or not STRIPE_SECRET_KEY:
        return jsonify({"ok": False, "error": "stripe-not-configured"}), 503

    data = request.get_json(silent=True) or {}
    try:
        amount_cents = int(data.get("amount_cents") or 0)
    except (ValueError, TypeError):
        amount_cents = 0
    if amount_cents < 100 or amount_cents > 10000:
        return jsonify({"ok": False, "error": "invalid-amount",
                        "message": "Tips must be between $1 and $100."}), 400

    note = (data.get("note") or "").strip() or None
    if note and len(note) > 500:
        note = note[:500]

    # Look up the review
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, status, customer_email, customer_phone,
                          completed_by_user_id, completed_by_name
                   FROM verification_requests
                   WHERE customer_review_token = %s""",
                (review_token,),
            )
            r = cur.fetchone()

    if not r:
        return jsonify({"ok": False, "error": "not-found"}), 404
    if r["status"] != "completed":
        return jsonify({"ok": False, "error": "not-completed"}), 409
    if not r.get("completed_by_user_id"):
        return jsonify({
            "ok": False,
            "error": "no-met-attributed",
            "message": "This review was delivered before tipping was enabled.",
        }), 409

    actor = _get_current_user()
    now_ms = int(time.time() * 1000)

    # Subscriber path — off-session charge to saved payment method
    if actor and actor.get("stripe_customer_id"):
        try:
            # Get the default payment method for the customer
            customer = stripe.Customer.retrieve(actor["stripe_customer_id"])
            default_pm = (customer.get("invoice_settings") or {}).get("default_payment_method")
            if default_pm:
                # Off-session charge
                intent = stripe.PaymentIntent.create(
                    amount=amount_cents,
                    currency="usd",
                    customer=actor["stripe_customer_id"],
                    payment_method=default_pm,
                    off_session=True,
                    confirm=True,
                    description=f"Tip for WV review #{r['id']}",
                    metadata={
                        "wv_tip_for_review": str(r["id"]),
                        "wv_met_user_id": str(r["completed_by_user_id"]),
                        "wv_customer_user_id": str(actor["id"]),
                    },
                )

                # Record the tip as completed
                with db() as conn:
                    with conn.cursor() as cur:
                        cur.execute(
                            """INSERT INTO met_tips
                               (created_at, verification_request_id, met_user_id, met_name,
                                customer_user_id, customer_email, customer_phone,
                                amount_cents, status, stripe_payment_intent_id,
                                completed_at, note)
                               VALUES (%s, %s, %s, %s, %s, %s, %s, %s,
                                       'completed', %s, %s, %s)
                               RETURNING id""",
                            (now_ms, r["id"], r["completed_by_user_id"],
                             r.get("completed_by_name"),
                             actor["id"], r["customer_email"], r["customer_phone"],
                             amount_cents, intent.id, now_ms, note),
                        )
                        tip_id = cur.fetchone()["id"]

                print(f"[met-tip] off-session charge succeeded tip_id={tip_id} amount=${amount_cents/100:.2f}", flush=True)
                return jsonify({
                    "ok": True,
                    "tip_id": tip_id,
                    "status": "completed",
                    "amount_cents": amount_cents,
                })
        except stripe.error.CardError as e:
            # Card declined — fall through to checkout
            print(f"[met-tip] off-session declined: {e}", flush=True)
        except Exception as e:
            print(f"[met-tip] off-session error: {e}", flush=True)
            # Fall through to checkout

    # Anonymous path (or subscriber off-session failed) — Stripe Checkout
    try:
        base = os.environ.get("FRONTEND_BASE_URL", "https://weathervalet.ai").rstrip("/")
        success_url = f"{base}/?review={review_token}&tip=thanks"
        cancel_url = f"{base}/?review={review_token}"

        session_params = {
            "mode": "payment",
            "line_items": [{
                "price_data": {
                    "currency": "usd",
                    "unit_amount": amount_cents,
                    "product_data": {
                        "name": f"Tip for {r.get('completed_by_name') or 'your meteorologist'}",
                        "description": "Thank-you for your WeatherValet review",
                    },
                },
                "quantity": 1,
            }],
            "success_url": success_url,
            "cancel_url": cancel_url,
            "metadata": {
                "wv_tip_for_review": str(r["id"]),
                "wv_met_user_id": str(r["completed_by_user_id"]),
            },
        }
        # Pre-fill customer_email if we know it
        if r.get("customer_email"):
            session_params["customer_email"] = r["customer_email"]

        session = stripe.checkout.Session.create(**session_params)

        # Insert tip as pending; webhook will flip to completed on success
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO met_tips
                       (created_at, verification_request_id, met_user_id, met_name,
                        customer_user_id, customer_email, customer_phone,
                        amount_cents, status, stripe_session_id, note)
                       VALUES (%s, %s, %s, %s, %s, %s, %s, %s, 'pending', %s, %s)
                       RETURNING id""",
                    (now_ms, r["id"], r["completed_by_user_id"],
                     r.get("completed_by_name"),
                     actor["id"] if actor else None,
                     r["customer_email"], r["customer_phone"],
                     amount_cents, session.id, note),
                )
                tip_id = cur.fetchone()["id"]

        return jsonify({
            "ok": True,
            "tip_id": tip_id,
            "status": "pending",
            "checkout_url": session.url,
        })
    except Exception as e:
        print(f"[met-tip] checkout creation failed: {e}", flush=True)
        return jsonify({"ok": False, "error": "stripe-error",
                        "message": str(e)[:200]}), 500


# ─── Met side: earnings summary ───────────────────────────────────────

@app.route("/api/v1/me/met-tips", methods=["OPTIONS"])
def _me_met_tips_preflight():
    return ("", 204)


@app.get("/api/v1/me/met-tips")
def me_met_tips():
    """Met views their tip earnings. Returns this-month total + recent tips."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    # Compute "this month" cutoff (UTC start of current month)
    now_utc = datetime.now(timezone.utc)
    month_start_dt = now_utc.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
    month_start_ms = int(month_start_dt.timestamp() * 1000)

    with db() as conn:
        with conn.cursor() as cur:
            # This-month earnings (completed tips only)
            cur.execute(
                """SELECT COALESCE(SUM(amount_cents), 0) AS month_cents,
                          COUNT(*) AS month_count
                   FROM met_tips
                   WHERE met_user_id = %s AND status = 'completed'
                     AND completed_at >= %s""",
                (user["id"], month_start_ms),
            )
            month = cur.fetchone()

            # All-time
            cur.execute(
                """SELECT COALESCE(SUM(amount_cents), 0) AS lifetime_cents,
                          COUNT(*) AS lifetime_count
                   FROM met_tips
                   WHERE met_user_id = %s AND status = 'completed'""",
                (user["id"],),
            )
            lifetime = cur.fetchone()

            # Recent 20 tips
            cur.execute(
                """SELECT mt.id, mt.created_at, mt.completed_at, mt.amount_cents,
                          mt.note, mt.status, mt.customer_email,
                          vr.plan_text AS review_plan
                   FROM met_tips mt
                   LEFT JOIN verification_requests vr ON vr.id = mt.verification_request_id
                   WHERE mt.met_user_id = %s
                   ORDER BY mt.created_at DESC LIMIT 20""",
                (user["id"],),
            )
            rows = cur.fetchall()

    tips = [
        {
            "id": r["id"],
            "created_at": r["created_at"],
            "completed_at": r["completed_at"],
            "amount_cents": r["amount_cents"],
            "status": r["status"],
            "note": r["note"],
            "customer_email": r.get("customer_email") or "(anonymous)",
            "review_plan": r.get("review_plan"),
        }
        for r in rows
    ]

    return jsonify({
        "ok": True,
        "summary": {
            "this_month_cents": int(month["month_cents"] or 0),
            "this_month_count": int(month["month_count"] or 0),
            "lifetime_cents": int(lifetime["lifetime_cents"] or 0),
            "lifetime_count": int(lifetime["lifetime_count"] or 0),
        },
        "tips": tips,
    })


# ════════════════════════════════════════════════════════════════════
# Met history — completed reviews for the logged-in Met
# ════════════════════════════════════════════════════════════════════
#
# Used by the Met workspace History tab to show "your last N reviews".
# Replaces hardcoded mock data. Pulls verification_requests where the
# logged-in Met is the one who completed them.

@app.route("/api/v1/me/met-history", methods=["OPTIONS"])
def _me_met_history_preflight():
    return ("", 204)


@app.get("/api/v1/me/met-history")
def me_met_history():
    """Returns the logged-in Met's recent completed reviews."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    try:
        limit = min(int(request.args.get("limit") or 20), 100)
    except (ValueError, TypeError):
        limit = 20

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, customer_email, customer_phone,
                          plan_text, plan_location, plan_window,
                          meteorologist_verdict, status,
                          completed_at, claimed_at, price_cents
                   FROM verification_requests
                   WHERE completed_by_user_id = %s AND status = 'completed'
                   ORDER BY completed_at DESC LIMIT %s""",
                (user["id"], limit),
            )
            rows = cur.fetchall()

    # Met earnings split — Met gets MET_REVIEW_SHARE_PCT (~65%) of the
    # $19 review price (~$12.35). See module-level MET_REVIEW_SHARE_PCT
    # for the single source of truth. We show it here so the Met sees
    # what they'll be paid out, not what the customer paid.
    reviews = []
    for r in rows:
        amount_cents_to_met = int((r["price_cents"] or 1900) * MET_REVIEW_SHARE_PCT)
        reviews.append({
            "request_id": r["id"],
            "customer_email": r["customer_email"],
            "customer_phone": r["customer_phone"],
            "plan_text": r["plan_text"],
            "plan_location": r["plan_location"],
            "plan_window": r["plan_window"],
            "verdict": r["meteorologist_verdict"],
            "verdict_class": _classify_meteorologist_verdict(r["meteorologist_verdict"] or ""),
            "completed_at": r["completed_at"],
            "claimed_at": r["claimed_at"],
            "amount_cents": amount_cents_to_met,
        })

    return jsonify({"ok": True, "reviews": reviews})


# ════════════════════════════════════════════════════════════════════
# Admin payroll dashboard — monthly Met earnings breakdown
# ════════════════════════════════════════════════════════════════════
#
# On the 1st of each month, admin pulls per-Met earnings for the prior
# month, enters into payroll.
#
# Earnings model:
#   1. $19 reviews: Met gets 65% of price_cents (~$12.35 of $19).
#      Tracked via verification_requests.completed_by_user_id.
#   2. Pro subscription revenue: Met gets 50% of the daily prorated
#      share for each day they sent the subscriber's brief.
#      Pro Single = $400/month → $400/days_in_month/day, Met gets half.
#      Pro Multi  = $1,200/month → same per-day prorate, Met gets half.
#      Hobbyist briefs are auto-AI (no Met touched) → revenue stays
#      with the house, no attribution.
#   3. Tips: 100% to the Met who got the tip
#      (completed met_tips for that month).
#
# Missed briefs: if a Pro subscriber didn't get a brief on day X, that
# day's prorated revenue stays with the house (no Met attribution).
# Notification of the miss happens separately in the scheduler.

PRO_TIER_MONTHLY_CENTS = {
    "pro_single": 40000,         # $400
    "pro_multi": 120000,         # $1,200
    "pro_enterprise": 200000,    # $2,000 default — real number set per-contract
}

# Met's share of Pro subscription revenue per day-of-brief.
# 50% to Met, 50% to house. See earnings model above.
MET_PRO_BRIEF_SHARE = 0.50

# Met's share of a $19 review. 65% to Met (~$12.35), 35% to house.
# Used in both payroll calculation and the Met-facing review history.
MET_REVIEW_SHARE_PCT = 0.65

# Storm Shelter activation payout — flat $25 to the Met who opens
# and runs the activation. Per-activation, not per-subscriber.
STORM_SHELTER_PAYOUT_CENTS = 2500


def _compute_payroll_for_month(year: int, month: int) -> dict:
    """Computes per-Met earnings + house revenue for the given month
    in Eastern Time. Returns a dict ready for JSON serialization.

    Shared by:
      - admin payroll endpoint (returns all Mets)
      - Met self-earnings endpoint (filters to one Met)
    """
    # Define the month period in Eastern Time (where the business is).
    ET = ZoneInfo("America/New_York")
    period_start = datetime(year, month, 1, 0, 0, 0, tzinfo=ET)
    if month == 12:
        period_end = datetime(year + 1, 1, 1, 0, 0, 0, tzinfo=ET)
    else:
        period_end = datetime(year, month + 1, 1, 0, 0, 0, tzinfo=ET)
    period_start_ms = int(period_start.timestamp() * 1000)
    period_end_ms = int(period_end.timestamp() * 1000)
    days_in_month = (period_end - period_start).days

    # ──────────────────────────────────────────────────────────────────
    # 1. Collect all Mets (for pre-populating zero rows even if no work)
    # ──────────────────────────────────────────────────────────────────
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id, u.name, u.email FROM users u
                   WHERE EXISTS (
                       SELECT 1 FROM user_roles ur
                       WHERE ur.user_id = u.id AND ur.role = 'met'
                   )
                   ORDER BY u.name, u.email"""
            )
            met_rows = cur.fetchall()
    mets_by_id = {
        r["id"]: {
            "user_id": r["id"],
            "name": (r.get("name") or "").strip() or r["email"],
            "email": r["email"],
            "review_cents": 0, "review_count": 0,
            "brief_cents": 0, "brief_count": 0,
            "tip_cents": 0, "tip_count": 0,
            "shelter_cents": 0, "shelter_count": 0,
        }
        for r in met_rows
    }

    # ──────────────────────────────────────────────────────────────────
    # 2. $19 review attribution — MET_REVIEW_SHARE_PCT (65%) of price_cents
    # ──────────────────────────────────────────────────────────────────
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT completed_by_user_id, price_cents
                   FROM verification_requests
                   WHERE status = 'completed'
                     AND completed_at IS NOT NULL
                     AND completed_at >= %s AND completed_at < %s
                     AND completed_by_user_id IS NOT NULL""",
                (period_start_ms, period_end_ms),
            )
            review_rows = cur.fetchall()
    for r in review_rows:
        met_id = r["completed_by_user_id"]
        if met_id not in mets_by_id:
            continue
        share = int((r["price_cents"] or 1900) * MET_REVIEW_SHARE_PCT)
        mets_by_id[met_id]["review_cents"] += share
        mets_by_id[met_id]["review_count"] += 1

    # ──────────────────────────────────────────────────────────────────
    # 3. Subscription brief attribution (per-day, per-subscriber)
    # ──────────────────────────────────────────────────────────────────
    unattributed_pro_cents = 0
    hobbyist_revenue_cents = 0

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT u.id AS user_id, u.subscription_tier, u.timezone
                   FROM users u
                   WHERE u.subscription_tier IS NOT NULL
                     AND u.subscription_tier != ''
                     AND EXISTS (
                       SELECT 1 FROM user_roles ur
                       WHERE ur.user_id = u.id AND ur.role = 'subscriber'
                     )"""
            )
            subs = cur.fetchall()

    for sub in subs:
        tier = sub["subscription_tier"]
        if tier == "hobbyist":
            hobbyist_revenue_cents += 3000  # $30/month flat
            continue
        if tier not in PRO_TIER_MONTHLY_CENTS:
            continue

        monthly_cents = PRO_TIER_MONTHLY_CENTS[tier]
        daily_cents = monthly_cents // days_in_month
        # Met's share per attributed day (50% of daily prorate).
        # The remaining 50% accrues to the house, regardless of whether
        # the brief was sent or missed. Missed-brief days contribute the
        # FULL daily_cents to the house (no Met share).
        daily_met_share = int(daily_cents * MET_PRO_BRIEF_SHARE)
        daily_house_share = daily_cents - daily_met_share

        user_tz = sub.get("timezone") or "America/Indiana/Indianapolis"
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT sent_at, sent_by_user_id
                       FROM pro_brief_drafts
                       WHERE user_id = %s
                         AND status = 'sent'
                         AND sent_at IS NOT NULL
                         AND sent_at >= %s AND sent_at < %s
                       ORDER BY sent_at ASC""",
                    (sub["user_id"], period_start_ms, period_end_ms),
                )
                brief_rows = cur.fetchall()

        # Bucket briefs by local date
        briefs_by_local_date = {}
        try:
            sub_zone = ZoneInfo(user_tz)
        except Exception:
            sub_zone = ZoneInfo("America/Indiana/Indianapolis")
        for b in brief_rows:
            sent_dt = datetime.fromtimestamp(b["sent_at"] / 1000, tz=timezone.utc).astimezone(sub_zone)
            local_date = sent_dt.date()
            if local_date not in briefs_by_local_date:
                briefs_by_local_date[local_date] = b["sent_by_user_id"]

        # Walk every day; attribute or send to house
        current_dt = period_start
        while current_dt < period_end:
            local_date = current_dt.astimezone(sub_zone).date()
            sent_by = briefs_by_local_date.get(local_date)
            if sent_by and sent_by in mets_by_id:
                # Met gets 50% of daily prorate, house keeps the other 50%
                mets_by_id[sent_by]["brief_cents"] += daily_met_share
                mets_by_id[sent_by]["brief_count"] += 1
                unattributed_pro_cents += daily_house_share
            else:
                # Missed brief — full daily prorate to house, no Met share
                unattributed_pro_cents += daily_cents
            current_dt += timedelta(days=1)

    # ──────────────────────────────────────────────────────────────────
    # 4. Tips — 100% to recipient Met
    # ──────────────────────────────────────────────────────────────────
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT met_user_id, amount_cents
                   FROM met_tips
                   WHERE status = 'completed'
                     AND completed_at IS NOT NULL
                     AND completed_at >= %s AND completed_at < %s
                     AND met_user_id IS NOT NULL""",
                (period_start_ms, period_end_ms),
            )
            tip_rows = cur.fetchall()
    for r in tip_rows:
        met_id = r["met_user_id"]
        if met_id not in mets_by_id:
            continue
        mets_by_id[met_id]["tip_cents"] += int(r["amount_cents"] or 0)
        mets_by_id[met_id]["tip_count"] += 1

    # ──────────────────────────────────────────────────────────────────
    # 4.5. Storm Shelter activations — $25 per closed activation,
    # using payout_cents from each row (default $25, can be overridden
    # per-row if we ever bump for special events). Only CLOSED activations
    # count for payroll — open ones haven't earned yet.
    # ──────────────────────────────────────────────────────────────────
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT met_user_id, payout_cents
                   FROM storm_shelter_activations
                   WHERE closed_at_ms IS NOT NULL
                     AND closed_at_ms >= %s AND closed_at_ms < %s""",
                (period_start_ms, period_end_ms),
            )
            shelter_rows = cur.fetchall()
    for r in shelter_rows:
        met_id = r["met_user_id"]
        if met_id not in mets_by_id:
            continue
        mets_by_id[met_id]["shelter_cents"] += int(r["payout_cents"] or 0)
        mets_by_id[met_id]["shelter_count"] += 1

    # ──────────────────────────────────────────────────────────────────
    # 5. Totals
    # ──────────────────────────────────────────────────────────────────
    mets_list = []
    for met in mets_by_id.values():
        met["total_cents"] = (
            met["review_cents"]
            + met["brief_cents"]
            + met["tip_cents"]
            + met["shelter_cents"]
        )
        mets_list.append(met)
    mets_list.sort(key=lambda m: m["total_cents"], reverse=True)

    month_label = period_start.strftime("%B %Y")
    return {
        "month": month_label,
        "period": {
            "start_ms": period_start_ms,
            "end_ms": period_end_ms,
            "days": days_in_month,
        },
        "mets": mets_list,
        "house": {
            "hobbyist_revenue_cents": hobbyist_revenue_cents,
            "unattributed_pro_cents": unattributed_pro_cents,
            "total_cents": hobbyist_revenue_cents + unattributed_pro_cents,
        },
    }


@app.route("/api/v1/admin/payroll/<int:year>/<int:month>", methods=["OPTIONS"])
def _admin_payroll_preflight(year, month):
    return ("", 204)


@app.get("/api/v1/admin/payroll/<int:year>/<int:month>")
def admin_payroll(year: int, month: int):
    """Return per-Met earnings for the given month, in Eastern Time.

    Path params: /YYYY/MM (e.g. /2026/5 for May 2026)
    """
    actor, err = _require_admin()
    if err:
        return err

    if month < 1 or month > 12:
        return jsonify({"ok": False, "error": "invalid-month"}), 400
    if year < 2020 or year > 2100:
        return jsonify({"ok": False, "error": "invalid-year"}), 400

    result = _compute_payroll_for_month(year, month)
    result["ok"] = True
    return jsonify(result)


@app.route("/api/v1/me/earnings/<int:year>/<int:month>", methods=["OPTIONS"])
def _me_earnings_preflight(year, month):
    return ("", 204)


@app.get("/api/v1/me/earnings/<int:year>/<int:month>")
def me_earnings(year: int, month: int):
    """Return MY earnings for the given month (Met-self version).

    Filters the payroll computation to just the calling Met. Returns
    the same structure (review_cents, brief_cents, tip_cents, total_cents,
    counts).
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    if month < 1 or month > 12:
        return jsonify({"ok": False, "error": "invalid-month"}), 400
    if year < 2020 or year > 2100:
        return jsonify({"ok": False, "error": "invalid-year"}), 400

    full = _compute_payroll_for_month(year, month)
    my_row = next((m for m in full["mets"] if m["user_id"] == user["id"]), None)
    if not my_row:
        # Met exists but has no work in this period — return zeros
        my_row = {
            "user_id": user["id"],
            "name": (user.get("name") or "").strip() or user.get("email"),
            "email": user.get("email"),
            "review_cents": 0, "review_count": 0,
            "brief_cents": 0, "brief_count": 0,
            "tip_cents": 0, "tip_count": 0,
            "shelter_cents": 0, "shelter_count": 0,
            "total_cents": 0,
        }
    return jsonify({
        "ok": True,
        "month": full["month"],
        "period": full["period"],
        "earnings": my_row,
    })


# ════════════════════════════════════════════════════════════════════
# Scheduled messages (Phase 10 — Met scheduling)
# ════════════════════════════════════════════════════════════════════
#
# Endpoints for the Met to schedule Daily Briefs, Pro Briefs, and
# Crew Posts for future delivery. The scheduler tick (in
# _brief_scheduler_loop) fires due-now items.

import json as _json_sched


@app.route("/api/v1/me/scheduled-messages", methods=["OPTIONS"])
def _me_scheduled_messages_preflight():
    return ("", 204)


@app.post("/api/v1/me/scheduled-messages")
def me_schedule_message():
    """Create a new scheduled message.

    Body:
      {
        "type": "daily_brief" | "pro_brief" | "crew_post",
        "scheduled_for_ms": 1748786400000,    // UTC ms when to fire
        "scheduled_tz": "America/New_York",   // for display only
        "content_payload": {...},             // type-specific
        "target_audience": {...}              // optional, type-specific
      }
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    data = request.get_json(silent=True) or {}
    msg_type = (data.get("type") or "").strip()
    if msg_type not in ("daily_brief", "pro_brief", "crew_post"):
        return jsonify({"ok": False, "error": "invalid-type"}), 400

    try:
        scheduled_for_ms = int(data.get("scheduled_for_ms") or 0)
    except (ValueError, TypeError):
        scheduled_for_ms = 0
    now_ms = int(time.time() * 1000)
    if scheduled_for_ms < now_ms + 30_000:
        # Must be at least 30 seconds in the future — avoids races
        return jsonify({
            "ok": False,
            "error": "scheduled-time-too-soon",
            "message": "Pick a time at least a minute in the future."
        }), 400
    if scheduled_for_ms > now_ms + 365 * 24 * 3600 * 1000:
        return jsonify({
            "ok": False,
            "error": "scheduled-time-too-far",
            "message": "Can't schedule more than 1 year in advance."
        }), 400

    scheduled_tz = (data.get("scheduled_tz") or "").strip() or None

    content = data.get("content_payload")
    if not content:
        return jsonify({"ok": False, "error": "missing-content"}), 400
    content_json = _json_sched.dumps(content)

    target_audience = data.get("target_audience")
    target_json = _json_sched.dumps(target_audience) if target_audience else None

    actor_name = (user.get("name") or "").strip() or user.get("email")

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """INSERT INTO scheduled_messages
                   (type, scheduled_for_ms, scheduled_tz,
                    scheduled_by_user_id, scheduled_by_name,
                    status, content_payload, target_audience,
                    created_at, updated_at)
                   VALUES (%s, %s, %s, %s, %s, 'pending', %s, %s, %s, %s)
                   RETURNING id""",
                (msg_type, scheduled_for_ms, scheduled_tz,
                 user["id"], actor_name, content_json, target_json,
                 now_ms, now_ms),
            )
            new_id = cur.fetchone()["id"]

    print(
        f"[scheduled-msg] created id={new_id} type={msg_type} by={user['id']} "
        f"for={datetime.fromtimestamp(scheduled_for_ms/1000, tz=timezone.utc).isoformat()}",
        flush=True,
    )
    return jsonify({"ok": True, "id": new_id, "scheduled_for_ms": scheduled_for_ms})


@app.get("/api/v1/me/scheduled-messages")
def me_list_scheduled_messages():
    """List the calling Met's scheduled messages.

    Query: ?status=pending (default) | sent | cancelled | failed | all
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401
    if "met" not in (user.get("roles") or []) and "admin" not in (user.get("roles") or []):
        return jsonify({"ok": False, "error": "forbidden"}), 403

    status_filter = (request.args.get("status") or "pending").strip()
    where = ["scheduled_by_user_id = %s"]
    params: list = [user["id"]]
    if status_filter != "all":
        where.append("status = %s")
        params.append(status_filter)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                f"""SELECT id, type, scheduled_for_ms, scheduled_tz,
                          status, content_payload, target_audience,
                          fired_at, fire_error, created_at, updated_at
                   FROM scheduled_messages
                   WHERE {' AND '.join(where)}
                   ORDER BY scheduled_for_ms ASC
                   LIMIT 100""",
                tuple(params),
            )
            rows = cur.fetchall()

    items = []
    for r in rows:
        try:
            content = _json_sched.loads(r["content_payload"]) if r["content_payload"] else {}
        except Exception:
            content = {}
        try:
            audience = _json_sched.loads(r["target_audience"]) if r["target_audience"] else None
        except Exception:
            audience = None
        items.append({
            "id": r["id"],
            "type": r["type"],
            "scheduled_for_ms": r["scheduled_for_ms"],
            "scheduled_tz": r["scheduled_tz"],
            "status": r["status"],
            "content_payload": content,
            "target_audience": audience,
            "fired_at": r["fired_at"],
            "fire_error": r["fire_error"],
            "created_at": r["created_at"],
        })
    return jsonify({"ok": True, "items": items})


@app.route("/api/v1/me/scheduled-messages/<int:msg_id>", methods=["OPTIONS"])
def _me_scheduled_message_one_preflight(msg_id):
    return ("", 204)


@app.patch("/api/v1/me/scheduled-messages/<int:msg_id>")
def me_update_scheduled_message(msg_id: int):
    """Edit a scheduled message (only while still pending).

    Body can include: scheduled_for_ms, scheduled_tz, content_payload,
    target_audience. Only provided fields are updated.
    """
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id, status, scheduled_by_user_id FROM scheduled_messages WHERE id = %s",
                (msg_id,),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "not-found"}), 404
    is_admin = "admin" in (user.get("roles") or [])
    if row["scheduled_by_user_id"] != user["id"] and not is_admin:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    if row["status"] != "pending":
        return jsonify({"ok": False, "error": "not-pending", "status": row["status"]}), 409

    data = request.get_json(silent=True) or {}
    set_clauses = []
    params: list = []
    now_ms = int(time.time() * 1000)

    if "scheduled_for_ms" in data:
        try:
            new_for = int(data["scheduled_for_ms"])
        except (ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-scheduled-for"}), 400
        if new_for < now_ms + 30_000:
            return jsonify({"ok": False, "error": "scheduled-time-too-soon"}), 400
        set_clauses.append("scheduled_for_ms = %s")
        params.append(new_for)
    if "scheduled_tz" in data:
        set_clauses.append("scheduled_tz = %s")
        params.append(data["scheduled_tz"] or None)
    if "content_payload" in data:
        set_clauses.append("content_payload = %s")
        params.append(_json_sched.dumps(data["content_payload"]))
    if "target_audience" in data:
        ta = data["target_audience"]
        set_clauses.append("target_audience = %s")
        params.append(_json_sched.dumps(ta) if ta else None)

    if not set_clauses:
        return jsonify({"ok": False, "error": "no-updates"}), 400

    set_clauses.append("updated_at = %s")
    params.append(now_ms)
    params.append(msg_id)

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                f"UPDATE scheduled_messages SET {', '.join(set_clauses)} WHERE id = %s",
                tuple(params),
            )
    return jsonify({"ok": True})


@app.delete("/api/v1/me/scheduled-messages/<int:msg_id>")
def me_cancel_scheduled_message(msg_id: int):
    """Cancel a pending scheduled message."""
    user = _get_current_user()
    if user is None:
        return jsonify({"ok": False, "error": "not-authenticated"}), 401

    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT id, status, scheduled_by_user_id FROM scheduled_messages WHERE id = %s",
                (msg_id,),
            )
            row = cur.fetchone()
    if not row:
        return jsonify({"ok": False, "error": "not-found"}), 404
    is_admin = "admin" in (user.get("roles") or [])
    if row["scheduled_by_user_id"] != user["id"] and not is_admin:
        return jsonify({"ok": False, "error": "forbidden"}), 403
    if row["status"] != "pending":
        return jsonify({"ok": False, "error": "not-pending", "status": row["status"]}), 409

    now_ms = int(time.time() * 1000)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """UPDATE scheduled_messages
                   SET status = 'cancelled', updated_at = %s
                   WHERE id = %s""",
                (now_ms, msg_id),
            )
    return jsonify({"ok": True})


# ─── Firing scheduled messages — called from scheduler tick ────────────

def _fire_scheduled_message(msg_row: dict) -> tuple[bool, str | None]:
    """Fire a single scheduled message. Returns (success, error_str).

    Routes to the right send path based on type. Wraps everything in
    try/except so one bad item doesn't stop the scheduler tick.
    """
    msg_type = msg_row["type"]
    try:
        content = _json_sched.loads(msg_row["content_payload"])
    except Exception as e:
        return False, f"bad-content-payload: {e!r}"

    if msg_type == "daily_brief":
        # Daily brief: publish to brief_history for all users in the
        # specified counties. Reuses the same publish path the immediate
        # Publish button uses (see _publish_daily_brief helper below).
        try:
            audience = _json_sched.loads(msg_row.get("target_audience") or "null")
        except Exception:
            audience = None
        return _publish_daily_brief_internal(
            content=content,
            audience=audience,
            published_by_user_id=msg_row["scheduled_by_user_id"],
            published_by_name=msg_row.get("scheduled_by_name"),
        )

    if msg_type == "pro_brief":
        # Pro brief: take a pro_brief_drafts row and mark it sent,
        # dispatch the SMS/email. Content payload carries draft_id +
        # final_body + final_verdict.
        try:
            draft_id = int(content.get("draft_id") or 0)
        except (ValueError, TypeError):
            return False, "missing-draft-id"
        if not draft_id:
            return False, "missing-draft-id"
        return _fire_pro_brief_draft(
            draft_id=draft_id,
            final_body=content.get("final_body"),
            final_verdict=content.get("final_verdict"),
            sent_by_user_id=msg_row["scheduled_by_user_id"],
            sent_by_name=msg_row.get("scheduled_by_name"),
        )

    if msg_type == "crew_post":
        # Crew post: publish to the Crew feed.
        return _publish_crew_post_internal(
            content=content,
            posted_by_user_id=msg_row["scheduled_by_user_id"],
            posted_by_name=msg_row.get("scheduled_by_name"),
        )

    return False, f"unknown-type: {msg_type}"


def _publish_daily_brief_internal(content: dict, audience: dict | None,
                                  published_by_user_id: int | None,
                                  published_by_name: str | None) -> tuple[bool, str | None]:
    """Publish a Daily Brief to every matching subscriber via their
    configured channels (SMS / email).

    Looks up each subscriber's brief_preferences.channels (defaults to
    'sms,email' if unset) and dispatches accordingly. Records a
    brief_history row per subscriber with the channels actually used.

    Returns (success, error). "Success" means at least one subscriber
    got the brief through at least one channel. If zero recipients
    matched the audience filter, that's also success — the Met did
    their work, the audience just happened to be empty.
    """
    try:
        body = (content.get("body") or "").strip()
        if not body:
            return False, "missing-body"
        now_ms = int(time.time() * 1000)

        # Optional fields from the Daily Brief composer
        verdict = (content.get("verdict") or "").strip() or None
        headline = (content.get("headline") or "Daily Brief").strip()
        time_windows = (content.get("time_windows") or "").strip()

        # Find target subscribers by county. audience.counties is a list
        # of county labels from the Met's multi-select.
        counties = []
        if audience and isinstance(audience, dict):
            counties = audience.get("counties") or []

        if not counties:
            # No specific counties — broadcast to all active subscribers
            sql = """SELECT DISTINCT u.id, u.email, u.phone, u.name,
                            bp.channels
                     FROM users u
                     LEFT JOIN brief_preferences bp ON bp.user_id = u.id
                     WHERE u.is_active = TRUE
                       AND EXISTS (
                         SELECT 1 FROM user_roles ur
                         WHERE ur.user_id = u.id AND ur.role = 'subscriber'
                       )"""
            sql_params: tuple = ()
        else:
            sql = """SELECT DISTINCT u.id, u.email, u.phone, u.name,
                            bp.channels
                     FROM users u
                     JOIN saved_locations sl ON sl.user_id = u.id
                     LEFT JOIN brief_preferences bp ON bp.user_id = u.id
                     WHERE u.is_active = TRUE
                       AND sl.county = ANY(%s)
                       AND EXISTS (
                         SELECT 1 FROM user_roles ur
                         WHERE ur.user_id = u.id AND ur.role = 'subscriber'
                       )"""
            sql_params = (counties,)

        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(sql, sql_params)
                recipients = cur.fetchall()

        # Build SMS-friendly snippet and email-friendly long body
        snippet = body[:140] + ("\u2026" if len(body) > 140 else "")
        sms_msg = f"{headline} — {snippet}"
        if time_windows:
            sms_msg += f"\nWindow: {time_windows[:80]}"
        # Cap SMS at 320 chars to avoid 3-segment messages
        if len(sms_msg) > 320:
            sms_msg = sms_msg[:317] + "..."

        email_subject = headline
        email_body_parts = [body]
        if time_windows:
            email_body_parts.append(f"\nTime windows: {time_windows}")
        if published_by_name:
            email_body_parts.append(f"\n— {published_by_name}, WeatherValet meteorologist")
        email_body = "\n\n".join(email_body_parts)

        delivered_count = 0
        failed_count = 0
        for r in recipients:
            try:
                # Default to SMS + email if no preferences set
                channels_str = r.get("channels") or "sms,email"
                channels = [ch.strip() for ch in channels_str.split(",") if ch.strip()]
                channels_used = []
                any_success = False

                for ch in channels:
                    if ch == "sms" and r.get("phone"):
                        try:
                            ok = send_sms(r["phone"], sms_msg)
                            if ok:
                                channels_used.append("sms")
                                any_success = True
                        except Exception as e:
                            print(f"[daily-brief-fire] SMS failed user_id={r['id']}: {e}", flush=True)
                    elif ch == "email" and r.get("email"):
                        try:
                            ok = _send_brief_email(r["email"], email_subject, email_body)
                            if ok:
                                channels_used.append("email")
                                any_success = True
                        except Exception as e:
                            print(f"[daily-brief-fire] email failed user_id={r['id']}: {e}", flush=True)

                # Always record history, even on failure — we want a paper trail
                delivery_status = "sent" if any_success else "failed"
                with db() as conn:
                    with conn.cursor() as cur:
                        cur.execute(
                            """INSERT INTO brief_history
                               (user_id, brief_type, delivered_at, verdict, snippet,
                                full_body, delivery_status, channels_used,
                                is_met_touched, met_name)
                               VALUES (%s, 'daily_brief', %s, %s, %s, %s, %s, %s,
                                       TRUE, %s)""",
                            (r["id"], now_ms, verdict, snippet, body,
                             delivery_status, ",".join(channels_used),
                             published_by_name or ""),
                        )
                if any_success:
                    delivered_count += 1
                else:
                    failed_count += 1
            except Exception as e:
                failed_count += 1
                print(f"[daily-brief-fire] per-sub error user_id={r.get('id')}: {e!r}", flush=True)

        print(
            f"[daily-brief-fire] published to {delivered_count} subs "
            f"({failed_count} failed) by={published_by_name}",
            flush=True,
        )
        # Success if we attempted (even if zero recipients matched, the Met
        # did their work; if some failed, we still count the dispatch as
        # successful from the firing perspective)
        return True, None
    except Exception as e:
        return False, f"daily-brief-error: {e!r}"


def _fire_pro_brief_draft(draft_id: int, final_body: str | None,
                          final_verdict: str | None,
                          sent_by_user_id: int | None,
                          sent_by_name: str | None) -> tuple[bool, str | None]:
    """Fire a previously-drafted Pro brief now."""
    try:
        now_ms = int(time.time() * 1000)
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    "SELECT id, user_id, status FROM pro_brief_drafts WHERE id = %s",
                    (draft_id,),
                )
                draft = cur.fetchone()
        if not draft:
            return False, f"draft-not-found: {draft_id}"
        if draft["status"] == "sent":
            return False, "draft-already-sent"

        # Mark sent
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """UPDATE pro_brief_drafts
                       SET status = 'sent', sent_at = %s, sent_by_user_id = %s,
                           sent_by_name = %s, final_body = COALESCE(%s, final_body),
                           final_verdict = COALESCE(%s, final_verdict)
                       WHERE id = %s""",
                    (now_ms, sent_by_user_id, sent_by_name,
                     final_body, final_verdict, draft_id),
                )
                # Also record in brief_history so subscriber's portal sees it
                cur.execute(
                    """SELECT email, phone FROM users WHERE id = %s""",
                    (draft["user_id"],),
                )
                sub = cur.fetchone()
                if sub:
                    body_for_history = (final_body or "")[:140]
                    cur.execute(
                        """INSERT INTO brief_history
                           (user_id, brief_type, delivered_at, snippet, full_body,
                            delivery_status, channels_used, is_met_touched, met_name)
                           VALUES (%s, 'morning', %s, %s, %s, 'sent',
                                   'sms,email', TRUE, %s)""",
                        (draft["user_id"], now_ms, body_for_history,
                         final_body or "", sent_by_name or ""),
                    )
        # SMS dispatch
        try:
            if sub and sub.get("phone"):
                send_sms(sub["phone"], (final_body or "")[:480])
        except Exception as e:
            print(f"[scheduled-fire] pro_brief SMS failed: {e}", flush=True)
        return True, None
    except Exception as e:
        return False, f"pro-brief-error: {e!r}"


def _publish_crew_post_internal(content: dict,
                                posted_by_user_id: int | None,
                                posted_by_name: str | None) -> tuple[bool, str | None]:
    """Publish a Crew post. For v1 — log to brief_history-like store.

    The Crew feed is currently mostly frontend-driven; we record the
    intent so it can be surfaced in admin tools / audit. Real Crew
    feed wiring exists separately.
    """
    try:
        body = (content.get("body") or "").strip()
        if not body:
            return False, "missing-body"
        print(f"[scheduled-fire] crew_post fired by={posted_by_user_id}: {body[:100]}", flush=True)
        # NOTE: The "Send to Crew feed" path on the immediate-send side
        # is frontend-driven in v1. When that gets wired to a real
        # backend store, this should call the same function. For now,
        # we just log success.
        return True, None
    except Exception as e:
        return False, f"crew-post-error: {e!r}"


def _process_scheduled_messages() -> None:
    """Scheduler tick — check for due-now scheduled messages and fire them."""
    try:
        now_ms = int(time.time() * 1000)
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT id, type, scheduled_for_ms, content_payload,
                              target_audience, scheduled_by_user_id, scheduled_by_name
                       FROM scheduled_messages
                       WHERE status = 'pending'
                         AND scheduled_for_ms <= %s
                       ORDER BY scheduled_for_ms ASC LIMIT 20""",
                    (now_ms,),
                )
                due = cur.fetchall()
    except Exception as e:
        print(f"[scheduled-msg-tick] query failed: {e}", flush=True)
        return

    for row in due:
        success, err = _fire_scheduled_message(dict(row))
        new_status = "sent" if success else "failed"
        try:
            with db() as conn:
                with conn.cursor() as cur:
                    cur.execute(
                        """UPDATE scheduled_messages
                           SET status = %s, fired_at = %s, fire_error = %s,
                               updated_at = %s
                           WHERE id = %s""",
                        (new_status, int(time.time() * 1000), err,
                         int(time.time() * 1000), row["id"]),
                    )
        except Exception as e:
            print(f"[scheduled-msg-tick] failed to mark id={row['id']}: {e}", flush=True)
        if success:
            print(f"[scheduled-msg-tick] fired id={row['id']} type={row['type']}", flush=True)
        else:
            print(f"[scheduled-msg-tick] FAILED id={row['id']} type={row['type']}: {err}", flush=True)


# ════════════════════════════════════════════════════════════════════
# Sales reps + commissions (Starter Month funnel)
# ════════════════════════════════════════════════════════════════════
#
# Reps earn 20% of every monthly subscription payment from customers
# they sourced, for 6 months after the customer's signup date.
#
# v1: admin sees per-rep commissions in Operations tab. Reps don't have
# logins yet. Michael shares numbers with reps manually (text, CSV).

REP_COMMISSION_PCT = 0.20
REP_COMMISSION_WINDOW_MONTHS = 6

# Subscription tier monthly cents for commission calculation.
# Derived from PRO_TIER_MONTHLY_CENTS (Pro tiers) + hobbyist.
# Centralizing here prevents drift: if a tier price changes, only
# PRO_TIER_MONTHLY_CENTS needs updating and commissions adjust too.
TIER_MONTHLY_CENTS_FOR_COMMISSION = {
    "hobbyist": 3000,  # $30 — only commissionable tier not in PRO_TIER_MONTHLY_CENTS
    **PRO_TIER_MONTHLY_CENTS,
}

# Starter Month override — month 0 was $99. Commission on $99 only.
STARTER_MONTH_CENTS = 9900


@app.route("/api/v1/admin/sales-reps", methods=["OPTIONS"])
def _admin_sales_reps_preflight():
    return ("", 204)


@app.get("/api/v1/admin/sales-reps")
def admin_sales_reps_list():
    """List all sales reps."""
    actor, err = _require_admin()
    if err:
        return err
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, slug, name, email, phone, commission_start_date,
                          is_active, created_at, updated_at
                   FROM sales_reps
                   ORDER BY is_active DESC, name"""
            )
            rows = cur.fetchall()
    reps = [dict(r) for r in rows]
    return jsonify({"ok": True, "reps": reps})


@app.post("/api/v1/admin/sales-reps")
def admin_sales_rep_create():
    """Create a new sales rep.

    Body: {slug, name, email?, phone?, commission_start_date?}
    """
    actor, err = _require_admin()
    if err:
        return err

    data = request.get_json(silent=True) or {}
    slug = (data.get("slug") or "").strip().lower()
    # Sanitize slug: alphanumeric + underscore only, max 40 chars
    slug = "".join(c for c in slug if c.isalnum() or c == "_")[:40]
    name = (data.get("name") or "").strip()
    if not slug or not name:
        return jsonify({"ok": False, "error": "slug-and-name-required"}), 400

    email = (data.get("email") or "").strip() or None
    phone = (data.get("phone") or "").strip() or None
    try:
        start_date = int(data.get("commission_start_date") or 0) or None
    except (ValueError, TypeError):
        start_date = None
    now_ms = int(time.time() * 1000)

    try:
        with db() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """INSERT INTO sales_reps
                       (slug, name, email, phone, commission_start_date,
                        is_active, created_at, updated_at)
                       VALUES (%s, %s, %s, %s, %s, TRUE, %s, %s)
                       RETURNING id""",
                    (slug, name, email, phone, start_date, now_ms, now_ms),
                )
                new_id = cur.fetchone()["id"]
    except Exception as e:
        # Most likely a duplicate slug
        return jsonify({
            "ok": False, "error": "create-failed",
            "message": f"Could not create rep — slug '{slug}' may already exist."
        }), 400
    return jsonify({"ok": True, "id": new_id, "slug": slug})


@app.patch("/api/v1/admin/sales-reps/<int:rep_id>")
def admin_sales_rep_update(rep_id: int):
    """Update a rep — name, email, phone, active flag, commission_start_date.
    Slug is locked (it's tied to URLs and attributions)."""
    actor, err = _require_admin()
    if err:
        return err
    data = request.get_json(silent=True) or {}
    sets = []
    params: list = []
    for field in ("name", "email", "phone"):
        if field in data:
            sets.append(f"{field} = %s")
            params.append((data.get(field) or "").strip() or None)
    if "is_active" in data:
        sets.append("is_active = %s")
        params.append(bool(data["is_active"]))
    if "commission_start_date" in data:
        try:
            sets.append("commission_start_date = %s")
            params.append(int(data["commission_start_date"]) if data["commission_start_date"] else None)
        except (ValueError, TypeError):
            return jsonify({"ok": False, "error": "invalid-start-date"}), 400
    if not sets:
        return jsonify({"ok": False, "error": "no-updates"}), 400
    sets.append("updated_at = %s")
    params.append(int(time.time() * 1000))
    params.append(rep_id)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                f"UPDATE sales_reps SET {', '.join(sets)} WHERE id = %s",
                tuple(params),
            )
    return jsonify({"ok": True})


def _compute_commissions_for_month(year: int, month: int) -> dict:
    """Compute per-rep commissions for the given month, in Eastern Time.

    For each subscriber with a rep attribution:
      - Check if their 6-month window includes this month
      - Determine what they paid this month (based on their tier + whether
        this was their Starter Month)
      - Rep earns 20% of what was paid

    For v1, we approximate "what they paid" using their CURRENT tier and
    a flat monthly amount. This is correct for stable customers but
    doesn't account for mid-month tier changes, refunds, or chargebacks.
    Real Stripe reconciliation comes later.
    """
    ET = ZoneInfo("America/New_York")
    period_start = datetime(year, month, 1, 0, 0, 0, tzinfo=ET)
    if month == 12:
        period_end = datetime(year + 1, 1, 1, 0, 0, 0, tzinfo=ET)
    else:
        period_end = datetime(year, month + 1, 1, 0, 0, 0, tzinfo=ET)
    period_start_ms = int(period_start.timestamp() * 1000)
    period_end_ms = int(period_end.timestamp() * 1000)

    # Load all reps (to ensure zero-rows for reps with no work)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT id, slug, name, email, is_active
                   FROM sales_reps ORDER BY name"""
            )
            rep_rows = cur.fetchall()
    reps_by_slug = {
        r["slug"]: {
            "rep_id": r["id"],
            "slug": r["slug"],
            "name": r["name"],
            "email": r["email"],
            "is_active": bool(r["is_active"]),
            "customer_count": 0,
            "commission_cents": 0,
            "customers": [],
        }
        for r in rep_rows
    }

    # Load all sales attributions (only those with a real rep slug)
    with db() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """SELECT a.user_id, a.rep_slug, a.signed_up_at, a.starter_used,
                          u.email, u.name, u.subscription_tier, u.is_active
                   FROM sales_attributions a
                   JOIN users u ON u.id = a.user_id
                   WHERE a.rep_slug IS NOT NULL AND a.rep_slug != 'organic'"""
            )
            attribs = cur.fetchall()

    for a in attribs:
        rep_slug = a["rep_slug"]
        if rep_slug not in reps_by_slug:
            continue  # Rep was deleted; skip silently

        # Compute the customer's months-elapsed AT THE END of this period.
        # Their first month (month 0) is the calendar month containing
        # their signup. Each subsequent month is +1.
        signed_dt = datetime.fromtimestamp(a["signed_up_at"] / 1000, tz=ET)
        # Month index for this period relative to signup
        delta_months = (period_start.year - signed_dt.year) * 12 + (period_start.month - signed_dt.month)

        # If period is BEFORE signup, nothing to compute
        if delta_months < 0:
            continue
        # Commission window: rep earns commission for the first 6
        # months of the customer's tenure, counting the signup month
        # as month 0.
        #
        #   Non-Starter customer: months 0, 1, 2, 3, 4, 5 (6 months total)
        #   Starter customer:     months 0 ($99 starter) + 1, 2, 3, 4, 5, 6
        #                         on the $400 standard rate (7 months total)
        #
        # The extra month for Starter customers compensates the rep
        # because month 0 is only $99 (a much smaller commission).
        if a["starter_used"]:
            commission_eligible = (0 <= delta_months <= 6)  # 7 months
        else:
            commission_eligible = (0 <= delta_months <= 5)  # 6 months

        if not commission_eligible:
            continue
        # Customer must still be active
        if not a["is_active"]:
            continue

        # What did they pay this month?
        tier = a["subscription_tier"] or ""
        if a["starter_used"] and delta_months == 0:
            month_cents = STARTER_MONTH_CENTS
        else:
            month_cents = TIER_MONTHLY_CENTS_FOR_COMMISSION.get(tier, 0)

        commission_cents = int(month_cents * REP_COMMISSION_PCT)
        reps_by_slug[rep_slug]["customer_count"] += 1
        reps_by_slug[rep_slug]["commission_cents"] += commission_cents
        reps_by_slug[rep_slug]["customers"].append({
            "user_id": a["user_id"],
            "email": a["email"],
            "name": a["name"],
            "signed_up_at": a["signed_up_at"],
            "tier": tier,
            "month_index": delta_months,
            "starter_used": bool(a["starter_used"]),
            "month_cents": month_cents,
            "commission_cents": commission_cents,
        })

    reps_list = list(reps_by_slug.values())
    reps_list.sort(key=lambda r: r["commission_cents"], reverse=True)

    return {
        "month": period_start.strftime("%B %Y"),
        "period": {
            "start_ms": period_start_ms,
            "end_ms": period_end_ms,
        },
        "reps": reps_list,
    }


@app.get("/api/v1/admin/commissions/<int:year>/<int:month>")
def admin_commissions(year: int, month: int):
    """Per-rep commissions for the given month."""
    actor, err = _require_admin()
    if err:
        return err
    if month < 1 or month > 12 or year < 2024 or year > 2100:
        return jsonify({"ok": False, "error": "invalid-period"}), 400
    result = _compute_commissions_for_month(year, month)
    result["ok"] = True
    return jsonify(result)


if __name__ == "__main__":
    init_db()
    port = int(os.environ.get("PORT", 8080))
    debug = os.environ.get("FLASK_DEBUG") == "1"
    app.run(host="0.0.0.0", port=port, debug=debug)
