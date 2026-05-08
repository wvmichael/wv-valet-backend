# Deploying WeatherValet's AI Backend to Render

**For the human who's clicking the buttons.** This guide walks you through everything you need to do to get the AI-powered "what this means for you" paragraph working. Plain English. ~30 minutes total. No coding required from you.

You'll do these things in order:

1. Get a free Gemini API key from Google
2. Put the backend code on GitHub
3. Connect the GitHub repo to Render
4. Set the environment variables
5. Deploy and verify
6. Send the deployed URL to Claude so we can wire it into the prototype

If anything looks different from what's written here (Render or Google may have updated their UI), just describe what you see and Claude will help you adapt.

---

## STEP 1 · Get a Gemini API key (5 minutes)

Google's Gemini AI is what generates the friendly paragraph. The free tier gives us about 15 requests per minute — plenty for prototype testing.

1. Open **https://aistudio.google.com/app/apikey** in your browser.
2. Sign in with your Google account if it asks.
3. You'll see a page titled "Get API key." If this is your first visit, you may see a "Create API key" button. Click it.
4. If it asks you to create a new project or select one, pick "Create API key in new project" — easiest path.
5. After a few seconds, a long string of letters and numbers appears (starts with `AIza...`). **This is your API key.**
6. Copy it. Save it in a password manager or somewhere safe. Do not paste it into a public document, do not commit it to GitHub, do not put it in a chat with anyone you don't trust. Anyone with this key can run up your quota.

That's all. You have the API key. Hold onto it; you'll paste it into Render in Step 4.

---

## STEP 2 · Put the backend code on GitHub (10 minutes)

Render reads your code from a GitHub repository. So we need to get the `wv-valet-backend/` folder onto GitHub.

**If you've never used GitHub before:**

1. Open **https://github.com** and sign up if you don't have an account. Free.
2. Once signed in, click the green **"New"** button (or "+" in the top-right → "New repository").
3. Name it `wv-valet-backend`. Leave it Private (recommended) or Public — both work.
4. Don't check any of the "Add README/gitignore/license" boxes — your folder already has these.
5. Click **"Create repository."**

You'll land on a page with instructions like *"Quick setup — if you've done this kind of thing before."* The page tells you several ways to upload code. We'll use the simplest: **drag and drop.**

6. On that empty repo page, find the link near the middle that says **"uploading an existing file"** (it's small, easy to miss). Click it.
7. A new page opens with a big "Drag files here" area.
8. Open your file explorer / Finder. Navigate to the `wv-valet-backend` folder Claude gave you.
9. Select all files inside the folder (everything: `app.py`, `requirements.txt`, `render.yaml`, `README.md`, `.env.example`, `static/`, `test_explain_prompt.py`). **Do not select the folder itself — select the contents.**
10. Drag them into the GitHub upload area.
11. At the bottom of the page, in the "Commit changes" box, the default message is fine. Click the green **"Commit changes"** button.

GitHub now has your code. The page refreshes and shows your files.

**Note for next time:** If you'd rather use a desktop app, GitHub Desktop (https://desktop.github.com) makes future updates one-click. Optional.

---

## STEP 3 · Connect Render to your GitHub repo (5 minutes)

1. Open **https://render.com** and sign up. You can sign in with GitHub directly — fastest. Free.
2. Once signed in, you land on the dashboard. Click the **"New +"** button (top-right) → **"Web Service."**
3. Render asks where your code lives. Click **"Connect GitHub"** if it isn't already connected. Authorize Render to see your repos.
4. Find `wv-valet-backend` in the list and click **"Connect."**
5. A configuration page appears. Most fields are auto-filled because of `render.yaml`, but verify:
   - **Name**: `wv-valet-backend` (or whatever you want the URL prefix to be)
   - **Region**: Pick closest to you (Ohio for US users)
   - **Branch**: `main`
   - **Runtime**: Python
   - **Build Command**: `pip install -r requirements.txt`
   - **Start Command**: `gunicorn app:app --bind 0.0.0.0:$PORT --timeout 30 --workers 2`
   - **Plan**: **Free**
6. Scroll down to **"Environment Variables."** **Don't click "Create Web Service" yet** — we need to add env vars first. Skip to Step 4 below.

---

## STEP 4 · Set environment variables (5 minutes)

Still on the Render service-creation page (or in your service's "Environment" tab if you already created it).

For each of these, click **"Add Environment Variable"** and enter the **Key** and **Value** as listed:

**Required for the AI paragraph to work:**

| Key | Value |
|---|---|
| `GEMINI_API_KEY` | The `AIza...` string from Step 1 |
| `WV_ALLOWED_ORIGINS` | `https://weathervalet.ai,https://www.weathervalet.ai,http://localhost:8000` |

**Required for the rest of the existing backend (Stripe, Twilio, meteorologist) — set as much as you have. The AI endpoint works without these, but the existing checkout/SMS features need them:**

| Key | Value |
|---|---|
| `STRIPE_SECRET_KEY` | `sk_test_...` (from Stripe dashboard, test mode) |
| `STRIPE_WEBHOOK_SECRET` | Set later, after you create the Stripe webhook |
| `TWILIO_ACCOUNT_SID` | From Twilio console |
| `TWILIO_AUTH_TOKEN` | From Twilio console |
| `TWILIO_FROM_NUMBER` | Your Twilio number, format `+15555550100` |
| `METEOROLOGIST_PHONE` | Your phone for testing, same format |
| `WV_ADMIN_PASS` | A password you choose for /admin pages |

If you're not setting up Stripe/Twilio yet, **just leave them blank** — the AI endpoint works without them. The /api/v1/verification/checkout endpoint will return errors but that's fine for now.

7. Now click **"Create Web Service."**

Render starts building. You'll see a stream of logs: it's installing Python, then your dependencies, then starting gunicorn. This takes 2-3 minutes.

When it succeeds, you'll see **"Your service is live"** and a URL like:

```
https://wv-valet-backend.onrender.com
```

(Yours might have extra characters in the name; that's fine.)

---

## STEP 5 · Verify it works (2 minutes)

1. Click the URL Render gave you. You should see a JSON response like:

```json
{
  "service": "wv-valet-backend",
  "status": "ok",
  "endpoints": [...]
}
```

If you see this, the service is alive.

2. Now test the AI endpoint specifically. Open a terminal on your computer and run:

```bash
export WV_API_URL=https://wv-valet-backend.onrender.com
python test_explain_prompt.py
```

(Replace `wv-valet-backend.onrender.com` with whatever URL Render gave you.)

You'll see 8 test queries run, each printing the paragraph Gemini generated. **Read these.** This is how you'll evaluate whether the prompt is working. If the paragraphs read like a friend's text message and don't invent venue details, we're in business. If they're stiff, generic, or full of made-up specifics, tell Claude — we'll tune the prompt in the next turn.

---

## STEP 6 · Send the URL to Claude

Once it's deployed and the test script returns sensible paragraphs, paste the URL into the next conversation with Claude:

> "The backend is deployed at https://wv-valet-backend.onrender.com — let's wire it into the prototype."

Claude will use that URL to hook the AI paragraph into the ticket UI. That's Turn 3 in our plan.

---

## Troubleshooting

**The Render build fails with "Module not found"** → Check `requirements.txt` is in your repo. If not, re-upload from the `wv-valet-backend/` folder.

**The service starts but `/` returns 502** → Wait 60 seconds. Free tier sometimes needs a moment to wake up after first deploy.

**`test_explain_prompt.py` returns paragraphs that say "Conditions look workable for your plan. Check the numbers below."** → That's the fallback paragraph. It means Gemini isn't being called. Most likely cause: `GEMINI_API_KEY` isn't set, or the value has a typo. Check the Render dashboard → your service → Environment.

**`test_explain_prompt.py` errors with "HTTP 429"** → You hit Gemini's rate limit. Wait 60 seconds and retry. If it happens often, your free quota is exhausted for the day; wait 24h or upgrade.

**`test_explain_prompt.py` errors with "HTTP 401"** → Your Gemini API key is invalid. Double-check you copied it correctly. Generate a new one from the AI Studio page if needed.

**Render says my service is asleep** → Free tier sleeps after 15 minutes idle. First request after sleep takes ~30 seconds to wake up. Subsequent requests are fast. For a prototype, this is acceptable. To remove sleep, upgrade to the $7/mo Starter plan in Render → your service → Settings → Plan.

---

## What you've built

After Step 6, you have:

- A live HTTPS backend at a permanent URL
- The AI paragraph endpoint working with real Gemini
- All the existing endpoints (Stripe checkout, meteorologist portal, admin dashboard) live too
- A test script you can run anytime to evaluate prompt quality

When Claude wires the prototype to this URL, your testers will see the real AI paragraphs on every ticket.
