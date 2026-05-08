"""
WeatherValet · Prompt Tuning Harness
====================================

Run this AFTER you've deployed to Render to evaluate how the prompt is
actually performing on real Gemini output. It hits your live endpoint
with 8 representative test queries and prints the paragraphs back so
you can read them all in one place.

WHEN TO USE THIS
----------------
- After first deploy: confirm Gemini is responding with sensible text
- After any change to EXPLAINER_SYSTEM_PROMPT: re-run to see the impact
- Before showing the prototype to a new tester: spot-check current quality

HOW TO USE THIS
---------------
1. Set your deployed URL:
       export WV_API_URL=https://wv-valet-backend.onrender.com

   (Replace with your real Render URL.)

2. Run the script:
       python test_explain_prompt.py

3. Read the output. For each test query you'll see:
   - The plan the user typed
   - The verdict and weather data
   - The paragraph Gemini produced

GOOD OUTPUT looks like:
   - Conversational, like a friend texting you
   - References the specific activity (a wedding cares about wind for the dress)
   - Precise about rain timing if rain is involved
   - 2-4 sentences
   - Doesn't restate the verdict
   - Doesn't invent venue details (no "left field", no "the south side of the building")

BAD OUTPUT looks like:
   - Generic ("the weather will be okay")
   - Restates the numbers without translating them ("78°F with 6 mph wind")
   - Invents venue details
   - Too long (5+ sentences)
   - Sounds like a weather report on TV
"""
import json
import os
import sys
import urllib.request
import urllib.error

API_URL = os.environ.get("WV_API_URL", "http://localhost:8080").rstrip("/")
ENDPOINT = f"{API_URL}/api/v1/forecast/explain"

# 8 test queries chosen to stress-test different parts of the prompt.
# Each one is a real-world plan a tester might type. Together they cover
# all the major cases: active sport, sedentary spectator, manual labor with
# stakes, ceremony, casual outdoor, weird/long-tail, rain timing precision,
# and an off-topic attempt.
TEST_CASES = [
    {
        "name": "Active sport (playing baseball)",
        "payload": {
            "plan": "Playing baseball at 5 PM Saturday — adult rec league",
            "location": "St. Louis, MO",
            "when": "Saturday, May 10 at 5:00 PM",
            "verdict": "Clear",
            "weather": {
                "temperature_f": 78, "feels_like_f": 78,
                "wind_mph": 8, "wind_gust_mph": 12,
                "humidity_pct": 55, "cloud_cover_pct": 20,
                "precip_probability_pct": 10,
            }
        }
    },
    {
        "name": "Spectating (watching that same baseball game)",
        "payload": {
            "plan": "Watching kids' baseball game at 5 PM Saturday — bringing the family",
            "location": "St. Louis, MO",
            "when": "Saturday, May 10 at 5:00 PM",
            "verdict": "Clear",
            "weather": {
                "temperature_f": 78, "feels_like_f": 78,
                "wind_mph": 8, "wind_gust_mph": 12,
                "humidity_pct": 55, "cloud_cover_pct": 20,
                "precip_probability_pct": 10,
            }
        }
    },
    {
        "name": "Manual labor with stakes (third concrete pour attempt)",
        "payload": {
            "plan": "Concrete pour at 9 AM Saturday for foundation slab — third try, rain killed the last two",
            "location": "Lebanon, IN",
            "when": "Saturday, May 10 at 9:00 AM",
            "verdict": "Caution",
            "weather": {
                "temperature_f": 62, "feels_like_f": 60,
                "wind_mph": 8, "wind_gust_mph": 24,
                "humidity_pct": 65, "cloud_cover_pct": 40,
                "precip_probability_pct": 10,
            }
        }
    },
    {
        "name": "Outdoor wedding (high-stakes ceremony)",
        "payload": {
            "plan": "Outdoor wedding ceremony at 4 PM Saturday — backyard, mostly older guests",
            "location": "Charlotte, NC",
            "when": "Saturday, May 10 at 4:00 PM",
            "verdict": "Clear",
            "weather": {
                "temperature_f": 76, "feels_like_f": 76,
                "wind_mph": 6, "wind_gust_mph": 9,
                "humidity_pct": 50, "cloud_cover_pct": 25,
                "precip_probability_pct": 5,
            }
        }
    },
    {
        "name": "Casual long-tail (1st birthday party)",
        "payload": {
            "plan": "My nephew's 1st birthday party at 2 PM Saturday — outside in the backyard with a bouncy house",
            "location": "Lebanon, IN",
            "when": "Saturday, May 10 at 2:00 PM",
            "verdict": "Clear",
            "weather": {
                "temperature_f": 72, "feels_like_f": 72,
                "wind_mph": 5, "wind_gust_mph": 8,
                "humidity_pct": 48, "cloud_cover_pct": 30,
                "precip_probability_pct": 0,
            }
        }
    },
    {
        "name": "Rain timing precision",
        "payload": {
            "plan": "Bike ride at 5 PM Friday — about 25 miles, will be back before dark",
            "location": "Indianapolis, IN",
            "when": "Friday, May 9 at 5:00 PM",
            "verdict": "Caution",
            "weather": {
                "temperature_f": 68, "feels_like_f": 67,
                "wind_mph": 10, "wind_gust_mph": 18,
                "humidity_pct": 70, "cloud_cover_pct": 80,
                "precip_probability_pct": 75,
                "precip_amount_in": 0.15,
                "rain_window": "4:15 PM to 5:45 PM"
            }
        }
    },
    {
        "name": "Vague plan (general outdoor)",
        "payload": {
            "plan": "outdoor stuff Saturday afternoon",
            "location": "Columbus, OH",
            "when": "Saturday, May 10 — afternoon",
            "verdict": "Clear",
            "weather": {
                "temperature_f": 74, "feels_like_f": 74,
                "wind_mph": 7, "wind_gust_mph": 11,
                "humidity_pct": 52, "cloud_cover_pct": 35,
                "precip_probability_pct": 15,
            }
        }
    },
    {
        "name": "Off-topic attempt (should refuse politely)",
        "payload": {
            "plan": "what's the meaning of life",
            "location": "Lebanon, IN",
            "when": "now",
            "verdict": "Clear",
            "weather": {"temperature_f": 70, "wind_mph": 5}
        }
    },
]


def call_endpoint(payload):
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        ENDPOINT,
        data=body,
        headers={"Content-Type": "application/json", "Origin": "null"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        return {"error": f"HTTP {e.code}: {e.read().decode('utf-8')[:200]}"}
    except Exception as e:
        return {"error": str(e)}


def main():
    print(f"Testing endpoint: {ENDPOINT}")
    print("=" * 78)
    print()

    for i, case in enumerate(TEST_CASES, 1):
        print(f"━━━ TEST {i}: {case['name']} ━━━")
        print(f"Plan:    {case['payload']['plan']}")
        print(f"Where:   {case['payload']['location']}")
        print(f"When:    {case['payload']['when']}")
        print(f"Verdict: {case['payload']['verdict']}")
        w = case['payload']['weather']
        weather_summary = []
        if "temperature_f" in w: weather_summary.append(f"{w['temperature_f']}°F")
        if "wind_mph" in w: weather_summary.append(f"{w['wind_mph']} mph wind")
        if w.get("rain_window"): weather_summary.append(f"rain {w['rain_window']}")
        elif "precip_probability_pct" in w: weather_summary.append(f"{w['precip_probability_pct']}% precip")
        print(f"Weather: {', '.join(weather_summary)}")
        print()
        result = call_endpoint(case["payload"])
        if "error" in result:
            print(f"  ERROR: {result['error']}")
        else:
            print(f"  source: {result.get('source')}")
            print(f"  paragraph:")
            paragraph = result.get("paragraph", "")
            # Indent paragraph for readability
            for line in paragraph.split("\n"):
                print(f"    {line}")
        print()


if __name__ == "__main__":
    main()
