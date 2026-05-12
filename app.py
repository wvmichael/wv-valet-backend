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
                                                                                    ├─ inserts row in SQLite (status='pending')
                                                                                    └─ returns hosted_url to frontend
                                                                                    
    Customer ──redirected to Stripe──▶  pays  ──redirect──▶  /verification/standby
                                          │
                                          ▼
                                      Stripe webhook ──▶ /webhooks/stripe
                                                              │
                                                              ├─ verifies signature
                                                              ├─ marks SQLite row 'paid'
                                                              ├─ Twilio SMS to customer
                                                              └─ Twilio SMS to meteorologist (with brief + claim link)
                                                              
    Meteorologist ──/meteorologist/<token>──▶ types verdict ──POST──▶ marks 'completed', SMSes customer

Run:

    pip install flask stripe twilio
    export STRIPE_SECRET_KEY=sk_test_...
    export STRIPE_WEBHOOK_SECRET=whsec_...
    export TWILIO_ACCOUNT_SID=AC...
    export TWILIO_AUTH_TOKEN=...
    export TWILIO_FROM_NUMBER=+15555550100
    export METEOROLOGIST_PHONE=+15555550101    # Timmy's phone for v1
    export PUBLIC_BASE_URL=https://api.weathervalet.ai   # how Stripe webhooks reach us
    export FRONTEND_BASE_URL=https://weathervalet.ai     # where customers come from
    python app.py

The frontend changes are in static/upsell.js — they replace the v2.4 modal
behavior with calls to this server. That file is in the same directory.
"""

from __future__ import annotations

import json
import os
import secrets
import sqlite3
import sys
import time
from contextlib import contextmanager
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

from flask import Flask, abort, jsonify, redirect, render_template_string, request

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

# Where SQLite lives. Override for tests.
DB_PATH = Path(os.environ.get("WV_DB_PATH", "wv_valet.db"))

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
# Database — SQLite, single file, no setup
# ════════════════════════════════════════════════════════════════════════════
#
# One table for now. The columns map directly to the lifecycle of a request:
#
#   pending   → checkout session created, customer hasn't paid yet
#   paid      → Stripe webhook fired, SMSes sent
#   claimed   → meteorologist tapped the claim link in their SMS
#   completed → meteorologist published their verdict, customer notified
#   expired   → customer never paid (Stripe sessions expire after 24h)
#
# The `claim_token` is a per-request secret in the meteorologist's SMS link,
# so we don't need them logged in. It's a 32-char URL-safe random token.

SCHEMA = """
CREATE TABLE IF NOT EXISTS verification_requests (
    id                  INTEGER PRIMARY KEY AUTOINCREMENT,
    created_at          INTEGER NOT NULL,
    updated_at          INTEGER NOT NULL,
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
    claimed_at          INTEGER,
    completed_at        INTEGER,
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
    id                  INTEGER PRIMARY KEY AUTOINCREMENT,
    submitted_at        INTEGER NOT NULL,        -- Unix timestamp seconds
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
"""


@contextmanager
def db():
    """Context-managed SQLite connection with row factory and foreign keys on."""
    conn = sqlite3.connect(DB_PATH, isolation_level=None)  # autocommit
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA journal_mode = WAL")  # better concurrent reads
    try:
        yield conn
    finally:
        conn.close()


def init_db() -> None:
    """Create tables on first boot. Idempotent — safe to call every start."""
    with db() as conn:
        conn.executescript(SCHEMA)


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
            conn.execute(
                """INSERT INTO brief_submissions
                   (submitted_at, meteorologist_name, region_name, verdict,
                    start_time, end_time, summary, confidence, notes)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)""",
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
import urllib.request
import urllib.error


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
        cur = conn.execute(
            """INSERT INTO verification_requests
               (created_at, updated_at, status, tier, price_cents,
                customer_email, customer_phone,
                plan_text, plan_industry, plan_location, plan_window,
                ai_brief_markdown, ai_status_key, claim_token)
               VALUES (?, ?, 'pending', ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (now_ts(), now_ts(), tier_key, tier["price_cents"],
             customer_email, customer_phone,
             plan_text, body.get("plan_industry"), body.get("plan_location"),
             body.get("plan_window"),
             ai_brief, body.get("ai_status_key"), claim_token),
        )
        request_id = cur.lastrowid

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
        conn.execute(
            "UPDATE verification_requests SET stripe_session_id = ?, updated_at = ? WHERE id = ?",
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
        row = conn.execute(
            "SELECT * FROM verification_requests WHERE id = ?",
            (request_id,),
        ).fetchone()
        if row is None:
            print(f"[webhook] no row for request_id={request_id}", flush=True)
            return
        if row["status"] != "pending":
            print(f"[webhook] request {request_id} already {row['status']}, skipping notifications", flush=True)
            return
        conn.execute(
            "UPDATE verification_requests SET status='paid', stripe_payment_id=?, updated_at=? WHERE id=?",
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
        row = conn.execute(
            """SELECT id, status, created_at, claimed_at, completed_at,
                      meteorologist_verdict, meteorologist_notes
               FROM verification_requests WHERE id = ?""",
            (request_id,),
        ).fetchone()
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
            rows = conn.execute(
                """SELECT id, submitted_at, meteorologist_name, region_name,
                          verdict, start_time, end_time, summary, confidence
                   FROM brief_submissions
                   ORDER BY submitted_at DESC
                   LIMIT 20"""
            ).fetchall()
    except sqlite3.OperationalError:
        # Table might not exist yet on a fresh boot — _ensure_db hasn't run
        # for this process. Treat as empty.
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
        row = conn.execute(
            "SELECT * FROM verification_requests WHERE claim_token = ?",
            (claim_token,),
        ).fetchone()
    if not row:
        abort(404)

    if row["status"] == "paid":
        # First view — mark it claimed so the dashboard shows accountability.
        with db() as conn:
            conn.execute(
                "UPDATE verification_requests SET status='claimed', claimed_at=?, updated_at=? WHERE id=?",
                (now_ts(), now_ts(), row["id"]),
            )

    return render_template_string(METEOROLOGIST_TEMPLATE, row=dict(row),
                                  sla_minutes=SLA_MINUTES, now=now_ts())


@app.post("/meteorologist/<claim_token>/complete")
def meteorologist_complete(claim_token: str):
    """Meteorologist submits their verdict. We mark completed and SMS customer."""
    with db() as conn:
        row = conn.execute(
            "SELECT * FROM verification_requests WHERE claim_token = ?",
            (claim_token,),
        ).fetchone()
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
        conn.execute(
            """UPDATE verification_requests
               SET status='completed', completed_at=?, updated_at=?,
                   meteorologist_verdict=?, meteorologist_notes=?
               WHERE id=?""",
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
        rows = conn.execute(
            """SELECT id, created_at, status, tier, customer_phone,
                      plan_text, plan_location, ai_status_key,
                      claimed_at, completed_at
               FROM verification_requests
               WHERE created_at > ?
               ORDER BY created_at DESC LIMIT 100""",
            (now_ts() - 86400 * 7,),
        ).fetchall()
        counts = conn.execute(
            """SELECT status, COUNT(*) as n FROM verification_requests
               WHERE created_at > ? GROUP BY status""",
            (now_ts() - 86400 * 7,),
        ).fetchall()
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
        # Today's tickets, ordered with most recent first
        today_rows = conn.execute(
            """SELECT id, created_at, status, tier, price_cents,
                      customer_phone, plan_text, plan_location,
                      ai_status_key, claimed_at, completed_at,
                      meteorologist_verdict
               FROM verification_requests
               WHERE created_at >= ?
               ORDER BY created_at DESC""",
            (midnight,),
        ).fetchall()

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
        completed_history = conn.execute(
            """SELECT ai_status_key, meteorologist_verdict
               FROM verification_requests
               WHERE status = 'completed'
                 AND created_at >= ?
                 AND ai_status_key IS NOT NULL
                 AND meteorologist_verdict IS NOT NULL""",
            (now - 86400 * 30,),
        ).fetchall()

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
        row = conn.execute(
            "SELECT claim_token FROM verification_requests WHERE id = ?",
            (request_id,),
        ).fetchone()
    if not row:
        abort(404)
    return redirect(f"/meteorologist/{row['claim_token']}")


# ════════════════════════════════════════════════════════════════════════════
# Main
# ════════════════════════════════════════════════════════════════════════════


if __name__ == "__main__":
    init_db()
    port = int(os.environ.get("PORT", 8080))
    debug = os.environ.get("FLASK_DEBUG") == "1"
    app.run(host="0.0.0.0", port=port, debug=debug)
