#!/usr/bin/env python3
"""KB Driver daemon v2 (keyboard-driver project, 2026-11-05).
v5.1.0-daemon (v2 build, 2026-11-12, spec
kb-driver-fixes-spec-v2-2026-11-12.md; see "Stage 8" below).
v5.0.2-daemon (2026-11-06 night, step 4 phase 1: service_up STATUS/SET_TOKEN, /shot STATUS and /status STATUS switched to the channel (fields) form - the last broadcast-only bootstrap reads; the one legitimate broadcast moment left is first-ever token present on a fresh install. Base v5.0.1 (2026-11-06 evening, KB-A/KB-K consult step 0: /epoch and /tap handlers fetch EPOCH_GET in the fields form - channel-first, same-seq broadcast fallback - instead of the legacy broadcast-only form that made every epoch read depend on rish; base v5.0 (2026-11-06, Aragon review + Claude FIX-1106): a persistent
long-poll channel replaces the per-command `am` spawn (~1.6 s
each) - the service polls /next, commands carry the same fields a
broadcast would, results return via /result; delivery is
at-least-once with service-side seq dedup (effectively-once
actuation); broadcast remains for bootstrap/wake-up/fallback.
Sends are split at the journal boundary (set_text, then
SEND_ARMED) and every send posts a write-ahead ARMED marker
(/armed) before it may click; the composite SEND_VERIFIED keeps
the same marker + owner-touch checkpoints. The touch gate is
12 s + IME-absent; QUIET_COPY posts /progress heartbeats and the
exchange aborts a stalled extraction instead of waiting blind.

v4.0 (2026-11-06, implementing the Kimi evaluation): token auth on
the loopback API and on every broadcast verb (the service enforces
token + current epoch + fresh sequence on actuating verbs);
composite SEND_VERIFIED and QUIET_COPY replace the multi-trip send
and copy paths; extraction is anchored to the sent message;
an owner-touch admission gate waits for a quiet gap before an
exchange takes the screen; /status reports a wedge state whose
vocabulary is ok / anomaly / indeterminate - never a verdict the
evidence cannot carry.
v3.5 (2026-11-06): after the clipboard read the exchange no longer
returns to the target app before finishing - validation is local,
the target is re-foregrounded only for a genuine copy retry, and
the final restore fires only when the foreground is one this job
put there (target or Termux), never over the owner's own move.
v3.4 (2026-11-06): restore the OWNER's original foreground at the end
of every exchange (v3.3 restored the target app instead and left it
in front of him); extraction is validated (optional "expect" marker,
changed-vs-last-reply, non-empty) and retried before it may return,
so a stale clipboard can no longer be reported as the new reply;
a screen guard holds the display awake during an exchange and
restores the owner's exact screen_off_timeout afterwards.

Loopback HTTP on 127.0.0.1:8773, bus pattern. POST /exchange runs a
whole job through the KB Driver accessibility service v3:

  bank gate -> on-demand service enable -> STATUS pre-checks
  (sensitive foreground aborts before anything moves) ->
  SET_TEXT -> read-back SHA-256 verify (clear + abort on mismatch)
  -> CLICK Send -> WAIT_QUIET settle -> CLICK Copy -> clipboard
  read (Termux foregrounded, per the clipboard law) -> restore
  the owner's foreground and the accessibility list byte-equal
  if this job enabled it.

Banking considerations: ~/bankmode/active aborts any exchange; a
banking/finance foreground aborts before the target is foregrounded;
banking packages are never valid targets; the accessibility list is
left exactly as found after every job, so bank mode's save set is
never disturbed.

Design: ~/workspace/claude-design-keyboard-driver-2026-11-05.md
"""
import base64
import hashlib
import hmac
import json
import os
import re
import secrets
import subprocess
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HOME = os.path.expanduser("~")
PORT = 8773
ALLOW = {"com.anthropic.claude", "com.termux", "com.moonshot.kimichat", "com.google.android.apps.bard",
 "com.google.android.googlequicksearchbox", "ai.qwenlm.chat.android", "com.openai.chatgpt",
 "io.bigmoeonedge.example.dev", "com.google.android.packageinstaller"}
# Phone atlas (2026-11-07, phase 1 integration): the daemon reads the
# surface entry for a job package at exchange start and branches ONLY
# on its typed fields (window_pkg, extraction_allowed, patience_s) -
# per Kimi's ATLAS-1107 contract, prose notes never drive behaviour.
ATLAS_DIR = os.path.join(HOME, "phone-atlas", "surfaces")


def _atlas_entry(pkg):
    """(entry, snapshot_hash) for a job package. Lookup: the file
    <pkg>.json first, else any entry whose window_pkg == pkg, so a
    caller may address either the atlas package or its window."""
    try:
        names = sorted(os.listdir(ATLAS_DIR))
    except Exception:
        return None, ""
    fallback = (None, "")
    for fn in names:
        if not fn.endswith(".json"):
            continue
        try:
            raw = open(os.path.join(ATLAS_DIR, fn), "rb").read()
            e = json.loads(raw.decode("utf-8"))
        except Exception:
            continue
        h = hashlib.sha256(raw).hexdigest()[:12]
        if fn == pkg + ".json":
            return e, h
        if e.get("window_pkg") == pkg and fallback[0] is None:
            fallback = (e, h)
    return fallback
NEVER_SUBSTR = ("bank", "finance", "wallet", "superqi", "pay")
BANK_FLAG = os.path.join(HOME, "bankmode", "active")
SVC = "com.qebas.kbdriver/com.qebas.kbdriver.KbService"
RECEIPTS = os.path.join(HOME, "kb_driver_receipts.jsonl")

env = dict(os.environ)
env.setdefault("RISH_APPLICATION_ID", "com.termux")

_jobs = {}
_jobs_lock = threading.Lock()
_exchange_lock = threading.Lock()

# v5.0 channel state: a queue of pending commands the service
# long-polls for, the last time a poll was seen, per-job progress
# heartbeats, and ARMED markers received from the service.
_chan = {"cond": threading.Condition(), "queue": [],
         "poller_seen": 0.0}
_progress = {}
_armed = {}


def _channel_fresh():
    return time.time() - _chan["poller_seen"] < 10.0


# B.7 (2026-11-08, absorption): holder detection. A background
# thread periodically reads dumpsys accessibility + the process
# list through rish and parses WHO holds the accessibility floor:
# the bound services (vs the standing known set), crashed
# services, accessibility proxy connections, and running
# UiAutomation-class holder processes (uiautomator2 / Appium).
# /status serves the cached snapshot; it never blocks on dumpsys.
_KNOWN_A11Y = {
    "com.arlosoft.macrodroid/com.arlosoft.macrodroid.action.services.UIInteractionAccessibilityService",
    "com.arlosoft.macrodroid/com.arlosoft.macrodroid.triggers.services.MacroDroidAccessibilityServiceJellyBean",
    "com.artemis.helper/com.artemis.helper.ArtemisAccessibilityService",
    "com.catalinagroup.callrecorder.helper/com.catalinagroup.callrecorder.service.AnyCallListenerService",
    "com.qebas.kbdriver/com.qebas.kbdriver.KbService",
}
_KB_A11Y = "com.qebas.kbdriver/com.qebas.kbdriver.KbService"
_UIAUTO_PKGS = ("com.github.uiautomator",
                "io.appium.uiautomator2.server")
_HOLDER_PROC_PAT = ("com.github.uiautomator",
                    "io.appium.uiautomator2.server", "atx-agent")
_holders = {"ts": 0.0, "data": None, "error": None}


def _norm_a11y_id(raw):
    raw = raw.strip()
    if "/" not in raw:
        return raw
    pkg, cls = raw.split("/", 1)
    if cls.startswith("."):
        cls = pkg + cls
    return pkg + "/" + cls


def _parse_a11y_dump(text):
    bound = []
    for m in re.finditer(r"Service\[label=[^,\]]+,\s*id=([^\],]+)",
                         text):
        cid = _norm_a11y_id(m.group(1))
        if cid not in bound:
            bound.append(cid)
    crashed = []
    for m in re.finditer(r"Crashed services:\{([^}]*)\}", text):
        inner = m.group(1).strip()
        if inner:
            for part in inner.split(","):
                part = part.strip().strip("{}")
                if part:
                    crashed.append(_norm_a11y_id(part))
    proxy = None
    m = re.search(r"Number of proxy connections:\s*(\d+)", text)
    if m:
        proxy = int(m.group(1))
    return bound, crashed, proxy


def _holder_probe_once():
    dump = rish("dumpsys accessibility", timeout=25)
    bound, crashed, proxy = _parse_a11y_dump(dump or "")
    procs = []
    ps = rish("ps -A", timeout=20) or ""
    for line in ps.splitlines():
        for pat in _HOLDER_PROC_PAT:
            if pat in line:
                name = line.split()[-1]
                if name not in procs:
                    procs.append(name)
                break
    foreign = [b for b in bound if b not in _KNOWN_A11Y]
    uiauto = [b for b in foreign
              if b.split("/")[0] in _UIAUTO_PKGS]
    return {"kb_bound": _KB_A11Y in bound, "bound": bound,
            "foreign_bound": foreign, "uiautomation_bound": uiauto,
            "crashed": crashed, "proxy_connections": proxy,
            "holder_processes": procs}


def _holder_thread():
    while True:
        try:
            _holders["data"] = _holder_probe_once()
            _holders["error"] = None
        except Exception as e:
            _holders["error"] = str(e)[:120]
        _holders["ts"] = time.time()
        time.sleep(20)


def _holders_view():
    age = (round(time.time() - _holders["ts"], 1)
           if _holders["ts"] else None)
    d = _holders["data"]
    if d is None:
        return {"probe_age_s": age, "probe_error": _holders["error"],
                "kb_bound": None, "bound": [], "foreign_bound": [],
                "uiautomation_bound": [], "crashed": [],
                "proxy_connections": None, "holder_processes": []}
    out = dict(d)
    out["probe_age_s"] = age
    out["probe_error"] = _holders["error"]
    return out

# v4.0 (Kimi evaluation): the loopback API and the broadcast verb
# channel are authenticated with a per-install random token. The
# daemon holds it in a mode-600 file; the driver service holds its
# own copy in its private files (set via SET_TOKEN at first contact)
# and stamps every result post with it. Before v4.0 any app on the
# phone could drive this keyboard - that hole is closed.
TOKEN_FILE = os.path.join(HOME, "kb_driver_token")


def _load_token():
    try:
        with open(TOKEN_FILE, encoding="utf-8") as f:
            t = f.read().strip()
        if t:
            return t
    except Exception:
        pass
    t = secrets.token_hex(16)
    fd = os.open(TOKEN_FILE, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        f.write(t)
    return t


TOKEN = _load_token()
_seq = [int(time.time() * 1000)]
_seq_lock = threading.Lock()
_broadcast_lock = threading.Lock()
_svc_token_active = [False]


def _next_seq():
    with _seq_lock:
        _seq[0] += 1
        return _seq[0]


def _auth_ok(handler):
    return hmac.compare_digest(handler.headers.get("X-KB-Token", ""), TOKEN)


def rish(cmd, timeout=40):
    o = subprocess.run(["sh", os.path.join(HOME, "shizuku/rish"), "-c", cmd],
                       capture_output=True, text=True, timeout=timeout, env=env)
    return (o.stdout or "") + (o.stderr or "")


def sh(cmd, timeout=30):
    o = subprocess.run(cmd, shell=True, capture_output=True, text=True,
                       timeout=timeout, env=env)
    return (o.stdout or "") + (o.stderr or "")


def broadcast(action, pkg, job, extra="", seq=None):
    # Every broadcast carries the token and a fresh sequence number;
    # the service enforces both (sequence on actuating verbs).
    # Broadcasts are serialized: with multi-second delivery latency,
    # parallel sends could land out of order and trip the replay
    # guard against ourselves.
    if seq is None:
        seq = _next_seq()
    cmd = ("am broadcast -p com.qebas.kbdriver -a %s --es pkg %s --es job %s %s"
           " --es t '%s' --el seq %d"
           % (action, pkg, job, extra, TOKEN, seq))
    with _broadcast_lock:
        rish(cmd)


def _am_extra(fields):
    import shlex
    parts = []
    for k, v in (fields or {}).items():
        if isinstance(v, bool):
            parts.append("--ez %s %s" % (k, "true" if v else "false"))
        elif isinstance(v, int):
            parts.append("--el %s %d" % (k, v))
        else:
            parts.append("--es %s %s" % (k, shlex.quote(str(v))))
    return " ".join(parts)


def await_job(job, timeout=8.0):
    with _jobs_lock:
        ev = _jobs.setdefault(job, {"event": threading.Event(), "result": None})
    if ev["event"].wait(timeout):
        return ev["result"]
    return None


def await_job_stall(job, timeout, stall_after=15.0, stall_gap=12.0):
    """Like await_job, but a long verb that stops posting progress
    heartbeats is declared stalled instead of waited out blind
    (Claude FIX-1106 Q3: two missed beats = UNKNOWN)."""
    with _jobs_lock:
        ev = _jobs.setdefault(job, {"event": threading.Event(), "result": None})
    t0 = time.time()
    while time.time() - t0 < timeout:
        if ev["event"].wait(1.0):
            return ev["result"]
        el = time.time() - t0
        last = _progress.get(job, t0)
        if el > stall_after and time.time() - last > stall_gap:
            return {"ok": False, "reason": "progress-stalled",
                    "synthetic": True}
    return None


def new_job(prefix):
    return "%s-%d" % (prefix, int(time.time() * 1000))


def call(action, pkg, fields=None, timeout=8.0, extra="", job=None,
         stall_watch=False):
    """Dispatch one verb. With `fields` (the v5.0 form) the command
    goes over the persistent channel when the service's poller is
    fresh - no `am` spawn - and falls back to a broadcast with the
    SAME seq when the poller never picks it up, or when no poller
    is live. The legacy string-`extra` form is broadcast-only and
    remains for bootstrap paths (STATUS / SET_TOKEN / EPOCH_BUMP).
    A command that was picked up but whose result never arrives is
    NOT re-issued: its outcome is unknown, not absent."""
    job = job or new_job(action.rsplit(".", 1)[-1].lower())
    if fields is None:
        broadcast(action, pkg, job, extra)
        return await_job(job, timeout)
    seq = _next_seq()
    flds = dict(fields)
    flds["t"] = TOKEN
    flds["seq"] = seq
    # The broadcast path carries pkg + job as extras; the channel
    # must too - handle() reads them from the intent, and a result
    # posted with job=null is dropped by the /result correlator.
    flds["pkg"] = pkg
    flds["job"] = job
    awaiter = (lambda: await_job_stall(job, timeout)) if stall_watch \
        else (lambda: await_job(job, timeout))
    if _channel_fresh():
        cmd = {"job": job, "action": action, "pkg": pkg, "fields": flds}
        with _chan["cond"]:
            _chan["queue"].append(cmd)
            _chan["cond"].notify_all()
        # Pickup grace: if the poller dies before taking it, the
        # command is provably unexecuted - broadcast may take over.
        deadline = time.time() + 3.0
        picked = False
        while time.time() < deadline:
            with _chan["cond"]:
                if cmd not in _chan["queue"]:
                    picked = True
                    break
            r = await_job(job, 0.2)
            if r is not None:
                return r
        if not picked:
            with _chan["cond"]:
                if cmd in _chan["queue"]:
                    _chan["queue"].remove(cmd)
                else:
                    picked = True
        if not picked:
            broadcast(action, pkg, job, _am_extra(fields), seq=seq)
    else:
        broadcast(action, pkg, job, _am_extra(fields), seq=seq)
    return awaiter()


def call_text(action, pkg, text, timeout=8.0, fields=None, job=None,
              stall_watch=False):
    f = {"b64": base64.b64encode(text.encode("utf-8")).decode()}
    if fields:
        f.update(fields)
    return call(action, pkg, f, timeout, job=job,
                stall_watch=stall_watch)


def launch_app(pkg, epoch=None):
    """Foreground an app through the service's LAUNCH verb (v5.0.3,
    channel path - no shell spawn, works with Shizuku dead). Falls
    back to the rish monkey road only when the verb itself fails:
    the day the service is the thing that is down, the old road
    still exists."""
    if epoch is None:
        er = call("com.qebas.kbdriver.EPOCH_GET", "any", {})
        epoch = (er or {}).get("epoch")
    if epoch is not None:
        r = call("com.qebas.kbdriver.LAUNCH", pkg,
                 {"launch": pkg, "epoch": int(epoch)}, timeout=10.0)
        if r and r.get("ok"):
            return True
    rish("monkey -p %s -c android.intent.category.LAUNCHER 1" % pkg)
    return False

def a11y_get():
    out = rish("settings get secure enabled_accessibility_services")
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    return lines[-1] if lines else ""


def a11y_put(value, via_verb=False):
    # v5.0.9 (step 4 phase 3): when the service is running to hear
    # it, the write rides the channel and the service performs it
    # under its WRITE_SECURE_SETTINGS grant - no shell bridge. The
    # write that FIRST lists the service cannot be served by it
    # (it is not running yet), and any verb failure falls back to
    # the rish road as before.
    if via_verb:
        er = call("com.qebas.kbdriver.EPOCH_GET", "any", {})
        ep = (er or {}).get("epoch")
        if ep is not None:
            r = call("com.qebas.kbdriver.SETTING_PUT", "any",
                     {"key": "enabled_accessibility_services",
                      "value_b64": base64.b64encode(
                          value.encode("utf-8")).decode(),
                      "epoch": int(ep)}, timeout=12.0)
            if r and r.get("ok"):
                return
    rish('settings put secure enabled_accessibility_services "%s"' % value)


def service_up(timeout=8.0):
    deadline = time.time() + timeout
    while time.time() < deadline:
        r = call("com.qebas.kbdriver.STATUS", "status", {}, timeout=2.0)
        if r and r.get("ok"):
            if not r.get("auth_set"):
                # First contact: hand the service its token. It
                # accepts only while unset (or the same token).
                call("com.qebas.kbdriver.SET_TOKEN", "any", {}, timeout=4.0)
                r2 = call("com.qebas.kbdriver.STATUS", "status",
                          {}, timeout=2.0)
                if r2 and r2.get("ok") and r2.get("auth_set"):
                    _svc_token_active[0] = True
                    return r2
                return r
            _svc_token_active[0] = True
            return r
        if r and r.get("reason") == "auth":
            return r
        time.sleep(0.5)
    return None


def receipt(rec):
    rec["ts"] = time.strftime("%Y-%m-%dT%H:%M:%S+03:00")
    with open(RECEIPTS, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        f.flush()
        os.fsync(f.fileno())


LASTJOB = os.path.join(HOME, "kb_driver_lastjob.json")
DEATHS = os.path.join(HOME, "kb_deaths.jsonl")


def _lastjob(**kw):
    """Stage 1 (KB rebuild 2026-11-08): durable 'what is in flight'
    state, read by the supervisor wrapper at daemon death and by
    /status. Written atomically; failures are silent by design."""
    try:
        kw["ts"] = time.strftime("%Y-%m-%dT%H:%M:%S+03:00")
        tmp = LASTJOB + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(kw, f, ensure_ascii=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, LASTJOB)
    except Exception:
        pass


def _read_lastjob():
    try:
        with open(LASTJOB, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None


def _tail_jsonl(path, max_bytes=262144):
    try:
        with open(path, "rb") as f:
            f.seek(0, 2)
            f.seek(max(0, f.tell() - max_bytes))
            lines = f.read().decode("utf-8", "replace").splitlines()
    except Exception:
        return []
    out = []
    for ln in lines:
        try:
            out.append(json.loads(ln))
        except Exception:
            pass
    return out


def _unreconciled():
    """EXCHANGE_ARMED text_hashes with no terminal exchange record
    carrying the same sha256. Bounded tail scan (stage 1); stage 2
    replaces this with maintained reconciliation state."""
    armed = {}
    closed = set()
    for r in _tail_jsonl(RECEIPTS, 1048576):
        if r.get("kind") == "EXCHANGE_ARMED":
            armed[r.get("text_hash")] = r.get("job")
        elif r.get("sha256"):
            closed.add(r["sha256"])
    open_jobs = [j for h, j in armed.items() if h not in closed]
    return {"count": len(open_jobs), "jobs": open_jobs[:10]}


RECON = os.path.join(HOME, "kb_recon.json")
_recon_lock = threading.Lock()
_recon = {"open": {}, "quarantined": {}}


def _recon_save():
    try:
        tmp = RECON + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(_recon, f, ensure_ascii=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, RECON)
    except Exception:
        pass


def _recon_import():
    """First boot with reconciliation (Stage 2, KB rebuild
    2026-11-08): rebuild open/quarantined state from the receipts
    journal. Pairing is FIFO per text_hash, and only send==True
    terminal records close an ARMED job - a draft's record must not
    mask a killed send of the same text (proven live in stage 1)."""
    queues = {}
    for r in _tail_jsonl(RECEIPTS, 8388608):
        if r.get("kind") == "EXCHANGE_ARMED":
            job = r.get("job")
            if job:
                queues.setdefault(r.get("text_hash"), []).append(job)
                _recon["open"][job] = {"text_hash": r.get("text_hash"),
                                       "armed_ts": r.get("ts")}
        elif r.get("send") is True and r.get("sha256"):
            q = queues.get(r["sha256"])
            if q:
                _recon["open"].pop(q.pop(0), None)
    _recon["quarantined"] = dict(_recon["open"])
    _recon["open"] = {}
    _recon_save()
    receipt({"kind": "RECON_IMPORT",
             "open_jobs": sorted(_recon["quarantined"].keys())})


def _recon_boot():
    """At daemon start, any job still open was in flight when the
    previous instance died: close it UNKNOWN with identity and
    quarantine it. Sends refuse until each quarantined job is
    acknowledged via /recon_ack after far-side reading."""
    global _recon
    if os.path.exists(RECON):
        try:
            with open(RECON, encoding="utf-8") as f:
                _recon = json.load(f)
        except Exception:
            _recon = {"open": {}, "quarantined": {}}
        stranded = dict(_recon.get("open") or {})
        for job, info in stranded.items():
            receipt({"kind": "RECONCILED_UNKNOWN", "job": job,
                     "text_hash": (info or {}).get("text_hash"),
                     "armed_ts": (info or {}).get("armed_ts")})
            _recon.setdefault("quarantined", {})[job] = info
        _recon["open"] = {}
        _recon_save()
    else:
        _recon_import()


def _recon_armed(job, text_hash):
    if not job:
        return
    with _recon_lock:
        _recon.setdefault("open", {})[job] = {
            "text_hash": text_hash,
            "armed_ts": time.strftime("%Y-%m-%dT%H:%M:%S+03:00")}
        _recon_save()


def _recon_close(sha256, since_ts):
    """Close the earliest still-open job with this text hash armed at
    or after since_ts (i.e. armed by the exchange now completing);
    returns the job id or None."""
    with _recon_lock:
        best = None
        for job, info in (_recon.get("open") or {}).items():
            if (info or {}).get("text_hash") == sha256 and \
                    (info or {}).get("armed_ts", "") >= since_ts:
                if best is None or info["armed_ts"] < \
                        _recon["open"][best]["armed_ts"]:
                    best = job
        if best is not None:
            _recon["open"].pop(best, None)
            _recon_save()
        return best


# ---- Stage 8 (KB v2 build, 2026-11-12): spec
# kb-driver-fixes-spec-v2-2026-11-12.md (ChatGPT KB-CHUNK-1112 verdict
# adopted by the owner). Fixes:
#  1. Explicit focused-field check before typing (strengthens the
#     stage-6 respondent gate): wrong field or nothing focused stops
#     the job before any keystroke.
#  2. Chip + sender-side digest is diagnostic telemetry ONLY, never
#     proof. VERIFIED needs receiver-side readable content; otherwise
#     STAGED_UNVERIFIED / REJECTED / UNKNOWN, with the v2 retry rule.
#  3. Per-app chunk ceilings (defaults below) + calibration logging.
#     Shortcut/web-surface calibration is OUT OF SCOPE (owner dropped
#     it as not worthy) - nothing here measures a shortcut surface.
#  4. Standing error rule verified by inspection (see _exchange done()
#     + _send_verdict readback_copy + DELIVER_HELD part_text): every
#     error returns the exact chunk, the error and a message copy,
#     never silent. Enforced, not rebuilt.

# Fix 3: per-app chunk ceilings, used when neither the caller nor the
# atlas surface carries one. Gemini (Bard app, window Google app)
# 2100, Claude 2400, Kimi 2000; hard cap CHUNK_CAP (2554).
CHUNK_DEFAULTS = {"com.google.android.apps.bard": 2100,
                  "com.google.android.googlequicksearchbox": 2100,
                  "com.anthropic.claude": 2400,
                  "com.moonshot.kimichat": 2000}

CALIB_LOG = os.path.join(HOME, "kb_calibration.jsonl")


def _calib_log(entry):
    """Fix 3: per-part calibration log (app, surface, chunk size,
    result, failure shape). Best-effort; never fails a send."""
    try:
        line = {"ts": time.strftime("%Y-%m-%dT%H:%M:%S+03:00")}
        line.update(entry)
        with open(CALIB_LOG, "a", encoding="utf-8") as f:
            f.write(json.dumps(line, ensure_ascii=False) + "\n")
    except Exception:
        pass


# Fix 2 retry rule: failure classification for a delivery part.
# 'definite' = evidence the chunk was not accepted (the verb failed
# before typing, the focus gate stopped it, or the read-back proved
# the content wrong after the exchange cleared it): safe to retry
# the same chunk ONCE. 'size-limit' = split only this chunk.
# Anything else is 'ambiguous' (the chunk may already have landed):
# stop and report UNKNOWN, never blind-retry.
_DEFINITE_REASONS = frozenset({
    "set-text-failed", "paste-mismatch", "paste-no-focus",
    "paste-foreground-lost", "respondent-mismatch",
    "no-focused-field", "focus-wrong-field",
    "focus-status-unavailable", "cannot-foreground"})
_SIZE_LIMIT_MARKERS = ("too-long", "size-limit", "too_long")


def _classify_part_failure(resp):
    reason = str(resp.get("reason") or "")
    if any(m in reason for m in _SIZE_LIMIT_MARKERS):
        return "size-limit"
    if reason.startswith("verify-"):
        if reason in ("verify-unknown", "verify-stale-chip"):
            return "ambiguous"
        return "definite"
    if reason in _DEFINITE_REASONS:
        return "definite"
    return "ambiguous"


def _chip_snapshot(win_pkg):
    """Chip nodes in the live tree: (paths, payloads). A payload is
    text/description carried by a chip node beyond the generic label
    itself. Returns None when the digest is unavailable (UNKNOWN)."""
    try:
        dg = call("com.qebas.kbdriver.DIGEST", win_pkg,
                  {"since": 0, "wait_ms": 0}, timeout=20.0)
    except Exception:
        return None
    nodes = ((dg or {}).get("digest") or {}).get("nodes") or []
    paths, payloads = set(), []
    for n in nodes:
        t = (n[2] if len(n) > 2 else "") or ""
        d = (n[3] if len(n) > 3 else "") or ""
        if "pasted" in (t + " " + d).lower():
            paths.add(n[0] if len(n) > 0 else "")
            for cand in (t, d):
                c = (cand or "").strip()
                if c and "pasted" not in c.lower():
                    payloads.append((n[0] if len(n) > 0 else "", c))
    return paths, payloads


def _focus_check(win_pkg):
    """Fix 1: explicit focused-field check before typing.
    Returns (ok, detail). ok only when the service reports a focused
    field AND the tree shows an EditText composer to type into.
    detail names expected vs actual for the receipt. When the tree
    is empty the field cannot be verified from it, so the check
    falls back to the STATUS focused flag alone and says so
    (code ok-status-only) instead of inventing a field. Termux has
    no EditText composer, so STATUS focused alone is the check there."""
    try:
        st = call("com.qebas.kbdriver.STATUS", "status", {}, timeout=2.0)
    except Exception:
        st = None
    if not st or not st.get("ok"):
        return False, {"expected": "composer EditText",
                       "actual": "unknown (STATUS unavailable)",
                       "code": "focus-status-unavailable"}
    if not st.get("focused"):
        return False, {"expected": "composer EditText",
                       "actual": "none focused",
                       "code": "no-focused-field"}
    if win_pkg == "com.termux":
        return True, {"expected": "composer EditText",
                      "actual": "focused (termux: no composer; "
                      "STATUS focused only)",
                      "code": "ok-status-only"}
    try:
        dg = call("com.qebas.kbdriver.DIGEST", win_pkg,
                  {"since": 0, "wait_ms": 0}, timeout=20.0)
    except Exception:
        dg = None
    nodes = ((dg or {}).get("digest") or {}).get("nodes") or []
    if not nodes:
        return True, {"expected": "composer EditText",
                      "actual": "focused (digest empty; field not "
                      "verified from tree)",
                      "code": "ok-status-only"}
    edits = [n for n in nodes
             if "EditText" in str(n[1] if len(n) > 1 else "")]
    if not edits:
        return False, {"expected": "composer EditText",
                       "actual": "focused, no EditText in tree",
                       "code": "focus-wrong-field"}
    last = edits[-1]
    return True, {"expected": "composer EditText",
                  "actual": "EditText path=%s" % (
                      last[0] if len(last) > 0 else "?"),
                  "code": "ok"}


# ---- Stage 4 (KB rebuild 2026-11-08): verdict engine + split send --
# The owner's send-with-error rule (2026-11-08): for owner/consult
# traffic a message that was set with a small, measurable error is
# SENT and reported, not silently dropped; the erred read-back copy
# is journalled so the difference can be judged. Canonicalisation
# (Class A: unicode form, bidi/zero-width controls, whitespace, line
# endings, smart quotes/dashes) consumes no margin. Class C is zero
# margin at any rate: truncation (head/tail loss), any digit change,
# any caller-named critical token missing. Bands on character error
# rate after canonicalisation: 0 = clean; <=0.1% clean-noted;
# <=1% sent-with-error; >1% hold. "strict" policy restores the old
# hash-exact-or-abort discipline.
import difflib
import re
import unicodedata

_BIDI = dict.fromkeys(
    [0x200B, 0x200C, 0x200D, 0x200E, 0x200F, 0xFEFF]
    + list(range(0x202A, 0x202F)) + list(range(0x2066, 0x206A)), None)


def _canon(s):
    s = unicodedata.normalize("NFC", s or "")
    s = s.translate(_BIDI)
    s = s.replace("\r\n", "\n").replace("\r", "\n")
    s = (s.replace("‘", "'").replace("’", "'")
          .replace("“", '"').replace("”", '"')
          .replace("–", "-").replace("—", "-"))
    s = re.sub(r"[ \t]+", " ", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


def _digits(s):
    return re.findall(r"\d+", s or "")


def _lev_band(a, b, band):
    """Levenshtein distance, banded: returns the exact distance when
    it fits the band, else a value > band (a lower bound, which is
    all the margin bands need)."""
    la, lb = len(a), len(b)
    if abs(la - lb) > band:
        return band + 1
    INF = band + 1
    prev = [j if j <= band else INF for j in range(lb + 1)]
    for i in range(1, la + 1):
        lo = max(1, i - band)
        hi = min(lb, i + band)
        cur = [INF] * (lb + 1)
        if i <= band:
            cur[0] = i
        ca = a[i - 1]
        row_min = INF
        for j in range(lo, hi + 1):
            cost = 0 if ca == b[j - 1] else 1
            v = min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + cost)
            cur[j] = v if v <= band else INF
            if v < row_min:
                row_min = v
        if row_min > band:
            return band + 1
        prev = cur
    return prev[lb]


def _cer(a, b):
    """Character error rate between canonical strings. Common
    prefix/suffix stripping localises the difference (the normal
    case: a few local errors in a long text), so the banded
    Levenshtein on the differing middle is exact and cheap."""
    if a == b:
        return 0.0
    n = min(len(a), len(b))
    p = 0
    while p < n and a[p] == b[p]:
        p += 1
    s = 0
    while s < (n - p) and a[len(a) - 1 - s] == b[len(b) - 1 - s]:
        s += 1
    ma = a[p:len(a) - s if s else len(a)]
    mb = b[p:len(b) - s if s else len(b)]
    if not ma and not mb:
        return 0.0
    if len(ma) > 6000 or len(mb) > 6000:
        # Wholesale-difference fallback: windowed sampling estimate
        # (bounded cost; band precision is all the verdict needs).
        wins, wlen = 40, 250
        tot, cnt = 0.0, 0
        for i in range(wins):
            off = i * (max(len(ma), len(mb)) - wlen) // max(1, wins - 1)
            wa = ma[off:off + wlen]
            wb = mb[off:off + wlen]
            if not wa and not wb:
                continue
            band = max(48, abs(len(wa) - len(wb)) + 24)
            tot += _lev_band(wa, wb, band) / max(1, max(len(wa), len(wb)))
            cnt += 1
        return (tot / cnt) if cnt else 0.0
    band = max(48, abs(len(ma) - len(mb)) + 24)
    edits = _lev_band(ma, mb, band)
    return edits / max(1, max(len(a), len(b)))


def _verdict_engine(intended, recovered, critical):
    """Judge a recovered read-back against the intended text."""
    a, b = _canon(intended), _canon(recovered)
    fails = []
    if a and len(b) < len(a) and (a.startswith(b) or a.endswith(b)):
        fails.append("head-tail")  # truncated at either end
    elif a and len(b) < 0.85 * len(a):
        fails.append("gutted")
    elif a and len(b) > 1.15 * len(a) and a in b:
        fails.append("duplicated")
    if _digits(a) != _digits(b):
        fails.append("digits")
    for tok in critical or []:
        if tok and tok not in recovered:
            fails.append("critical-missing")
    cer = _cer(a, b)
    return {"cer": round(cer, 5), "class_c_fail": bool(fails),
            "class_c": fails,
            "readback_sha": hashlib.sha256(
                recovered.encode("utf-8")).hexdigest(),
            "readback_chars": len(recovered)}


def _digest_composer(win_pkg):
    """Recover the composer text from the service's tree model.
    Returns (text, chip_present): long pastes can collapse into a
    'Pasted content' chip above an empty composer, in which case the
    text is structurally unrecoverable from the tree."""
    dg = call("com.qebas.kbdriver.DIGEST", win_pkg,
              {"since": 0, "wait_ms": 0}, timeout=20.0)
    nodes = ((dg or {}).get("digest") or {}).get("nodes") or []
    comp = ""
    chip = False
    for n in nodes:
        cls = str(n[1]) if len(n) > 1 else ""
        t = (n[2] if len(n) > 2 else "") or ""
        d = (n[3] if len(n) > 3 else "") or ""
        if "pasted" in (t + " " + d).lower():
            chip = True
        if "EditText" in cls and len(t) > len(comp):
            comp = t
    return comp, chip


def _send_verdict(win_pkg, text, getres, spec, pre_chip_paths=None):
    """Decide whether a daemon-side set may be armed, and how the
    send will be reported. getres is the GET_TEXT result.
    v2 (KB-CHUNK-1112): chip presence + sender-side digest is
    diagnostic telemetry ONLY, never proof. chunk_state is one of
    VERIFIED / STAGED_UNVERIFIED / REJECTED / UNKNOWN:
    - VERIFIED: receiver-side readable content read back and matched
      within the standing tolerance (CER bands; exact digest match
      is the clean case). The band still records fidelity.
    - STAGED_UNVERIFIED: a fresh chip node and an empty editor, no
      readable payload. Staged, not proven.
    - REJECTED: definite evidence the chunk was not accepted as
      intended (class-C fail, CER > 1%).
    - UNKNOWN: ambiguous - digest unavailable, or the only chip is
      stale (predates this chunk)."""
    want = hashlib.sha256(text.encode("utf-8")).hexdigest()
    got = (getres or {}).get("sha256")
    if got == want:
        return {"band": "clean", "chunk_state": "VERIFIED", "cer": 0.0,
                "class_c_fail": False}
    policy = spec.get("policy") or "send_with_report"
    base = {"readback_sha": got,
            "readback_chars": (getres or {}).get("chars")}
    try:
        comp, chip = _digest_composer(win_pkg)
    except Exception:
        # Digest unreadable: the chunk may or may not have landed.
        # v2 reports UNKNOWN rather than crashing the exchange.
        v = {"band": "hold", "code": "digest-unavailable",
             "chunk_state": "UNKNOWN", "cer": None,
             "class_c_fail": False}
        v.update(base)
        return v
    if comp:
        v = _verdict_engine(text, comp, spec.get("critical") or [])
        v["recovered_via"] = "digest"
        v.update(base)
        if v["class_c_fail"]:
            v["band"] = "hold"
            v["chunk_state"] = "REJECTED"
        elif v["cer"] == 0:
            v["band"] = "clean"
            v["chunk_state"] = "VERIFIED"
        elif v["cer"] <= 0.001:
            v["band"] = "clean-noted"
            v["chunk_state"] = "VERIFIED"
        elif v["cer"] <= 0.01:
            v["band"] = "sent-with-error"
            v["chunk_state"] = "VERIFIED"
        else:
            v["band"] = "hold"
            v["chunk_state"] = "REJECTED"
        if v["band"] == "sent-with-error":
            v["readback_copy"] = comp[:20000]
        if policy == "strict" and v["band"] != "clean":
            v["band"] = "hold"
            v["chunk_state"] = "REJECTED"
            v["code"] = "strict"
        return v
    if chip:
        # A chip with no composer text: try the chip's own payload
        # before declaring the chunk unverified.
        snap = _chip_snapshot(win_pkg)
        if snap is None:
            v = {"band": "hold", "code": "unknown",
                 "chunk_state": "UNKNOWN", "cer": None,
                 "class_c_fail": False}
            v.update(base)
            return v
        paths, payloads = snap
        fresh = bool(pre_chip_paths is not None and
                     (paths - pre_chip_paths))
        for _path, payload in payloads:
            if pre_chip_paths is not None and \
                    _path in pre_chip_paths:
                continue  # stale node: never proof for this chunk
            pv = _verdict_engine(text, payload,
                                 spec.get("critical") or [])
            if not pv["class_c_fail"] and pv["cer"] <= 0.01:
                v = dict(pv)
                v["recovered_via"] = "chip-payload"
                v["chunk_state"] = "VERIFIED"
                v["band"] = ("clean" if pv["cer"] == 0 else
                             "clean-noted" if pv["cer"] <= 0.001 else
                             "sent-with-error")
                v["chip_fresh"] = fresh or pre_chip_paths is None
                if v["band"] == "sent-with-error":
                    v["readback_copy"] = payload[:20000]
                v.update(base)
                if policy == "strict" and v["band"] != "clean":
                    v["band"] = "hold"
                    v["chunk_state"] = "REJECTED"
                    v["code"] = "strict"
                return v
        if pre_chip_paths is not None and not fresh and paths:
            # The only chip predates this chunk: it may belong to an
            # earlier chunk. Ambiguous - stop, do not arm on it.
            v = {"band": "hold", "code": "stale-chip",
                 "chunk_state": "UNKNOWN", "cer": None,
                 "class_c_fail": False}
            v.update(base)
            return v
        v = {"band": "staged-unverified", "cer": None,
             "class_c_fail": False, "chunk_state": "STAGED_UNVERIFIED",
             "chip_fresh": fresh}
        v.update(base)
        return v
    if policy == "strict":
        v = {"band": "hold", "cer": None, "class_c_fail": False,
             "code": "mismatch", "chunk_state": "REJECTED"}
        v.update(base)
        return v
    # No readable content and no chip: the service accepted the set
    # (SET_TEXT returned ok) but nothing is observable. Labelled
    # honestly as staged-unverified; the old band name is kept so
    # callers that key on it keep working.
    v = {"band": "sent-with-error-unmeasured", "cer": None,
         "class_c_fail": False, "chunk_state": "STAGED_UNVERIFIED"}
    v.update(base)
    return v


def _paste_commit(win_pkg, launch_pkg, epoch, text, rec, saved_box):
    """Stage 7 paste road: put the text into the focused composer
    via the clipboard, the way the owner's hand-paste works - one
    commit down the app's own input path. Saves the owner's
    clipboard first (restored in the exchange's finally); aborts on
    owner touch at the commit moment. Returns None or a reason."""
    launch_app("com.termux", epoch)
    time.sleep(1.0)
    saved = sh("termux-clipboard-get") or ""
    saved_box["text"] = saved
    rec["clip_saved_chars"] = len(saved)
    tmp = os.path.join(HOME, "kb_paste_tmp.txt")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
    sh("termux-clipboard-set < " + tmp)
    try:
        os.remove(tmp)
    except Exception:
        pass
    launch_app(launch_pkg, epoch)
    time.sleep(1.2)
    st = call("com.qebas.kbdriver.STATUS", "status", {})
    if not st or st.get("pkg") != win_pkg:
        return "paste-foreground-lost"
    if not st.get("focused"):
        dg = call("com.qebas.kbdriver.DIGEST", win_pkg,
                  {"since": 0, "wait_ms": 0}, timeout=20.0)
        nodes = ((dg or {}).get("digest") or {}).get("nodes") or []
        edits = [n[0] for n in nodes if "EditText" in str(n[1])]
        if edits:
            call("com.qebas.kbdriver.CLICK_PATH", win_pkg,
                 {"path": edits[-1], "expect": "",
                  "epoch": int(epoch)}, timeout=12.0)
            time.sleep(0.8)
            st = call("com.qebas.kbdriver.STATUS", "status", {})
        if not st or not st.get("focused"):
            return "paste-no-focus"
    # v2 Fix 1: re-check the focused field after the window
    # switches above; a re-focus can land on the wrong control.
    fok, fdetail = _focus_check(win_pkg)
    rec["focus_check"] = fdetail
    if not fok:
        return "paste-no-focus"
    lt = int(st.get("last_touch_ms") or 0)
    if lt and (int(time.time() * 1000) - lt) < 3000:
        return "owner-touch"
    rish("input keyevent 279")
    time.sleep(0.8)
    rec["paste"] = True
    return None


def _respondent_claim(win_pkg, entry):
    """Stage 6: read WHO is answering, per the atlas locator, from
    the live tree - never assumed from the package. Returns the
    claim string or None (no locator, or label unreadable). The
    claim is a claim: recorded as respondent_claimed, not verified
    identity."""
    loc = (entry or {}).get("respondent") or {}
    if loc.get("kind") != "header_text_prefix":
        return None
    prefixes = loc.get("prefixes") or []
    dg = call("com.qebas.kbdriver.DIGEST", win_pkg,
              {"since": 0, "wait_ms": 0}, timeout=20.0)
    nodes = ((dg or {}).get("digest") or {}).get("nodes") or []
    for n in nodes:
        t = (n[2] if len(n) > 2 else "") or ""
        if not t or len(t) > 60:
            continue
        y1 = n[6] if len(n) > 6 else 9999
        if isinstance(y1, (int, float)) and y1 > 300:
            continue
        for p in prefixes:
            if t.startswith(p):
                return t
    return None


_xchg = {}


# ---- Stage 5 (KB rebuild 2026-11-08): resident multi-part delivery.
# One job in (whole text + target + policy); the daemon chunks AT the
# target, paces the parts itself, journals every part, checkpoints to
# ~/kb_deliveries/<job>.json after each part, extracts ONCE at the
# end. Design per RESD-1108 (Claude) as amended by the owner:
# conservative chunking (atlas chunk_chars when the surface carries
# one, else 2400; hard cap 2554), paragraph boundaries first, adapt
# DOWN only (-30% when a part runs >2x the running median or its
# anchor is unbound; adaptation journalled), floor 500 chars (two
# floor failures -> HOLD floor-reached), one same-part retry on
# definite rejection only (v2), per-part verdicts from the
# stage-4 engine, parts carry the job tag and a
# final-part flag (no upfront N: adaptive re-chunking would make it
# a lie; the payload's own END sentinel is the completeness
# contract). A daemon death mid-job marks the job INTERRUPTED at
# boot - never auto-resumed; /deliver_resume continues it by
# explicit order only.
DELIV_DIR = os.path.join(HOME, "kb_deliveries")
_deliveries = {}
_delivery_lock = threading.Lock()
_delivery_active = {"job": None}

CHUNK_CAP = 2554
CHUNK_FLOOR = 500


def _chunk_text(text, ceiling):
    parts = []
    rest = text
    while rest:
        if len(rest) <= ceiling:
            parts.append(rest)
            break
        window = rest[:ceiling]
        cut = window.rfind("\n\n")
        if cut < ceiling * 0.4:
            cut = window.rfind("\n")
        if cut < ceiling * 0.4:
            cut = window.rfind(". ")
        if cut < 200:
            cut = ceiling
        parts.append(rest[:cut])
        rest = rest[cut:]
        if rest.startswith("\n\n"):
            rest = rest[2:]
        elif rest.startswith("\n"):
            rest = rest[1:]
    return [p for p in parts if p.strip()]


def _delivery_save(job):
    try:
        os.makedirs(DELIV_DIR, exist_ok=True)
        tmp = os.path.join(DELIV_DIR, job["job"] + ".json.tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(job, f, ensure_ascii=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, os.path.join(DELIV_DIR, job["job"] + ".json"))
    except Exception:
        pass


def _delivery_boot():
    """Mark jobs that were running when the daemon died as
    interrupted. Never auto-resume (RESD-1108 stage 2 rule)."""
    try:
        os.makedirs(DELIV_DIR, exist_ok=True)
        for name in os.listdir(DELIV_DIR):
            if not name.endswith(".json"):
                continue
            try:
                with open(os.path.join(DELIV_DIR, name),
                          encoding="utf-8") as f:
                    job = json.load(f)
            except Exception:
                continue
            if job.get("state") == "running":
                job["state"] = "interrupted"
                job["updated"] = time.strftime("%Y-%m-%dT%H:%M:%S+03:00")
                _delivery_save(job)
                receipt({"kind": "DELIVER_INTERRUPTED",
                         "job": job.get("job"),
                         "parts_sent": job.get("parts_sent")})
            _deliveries[job["job"]] = job
    except Exception:
        pass


def _delivery_run(job):
    """Worker: sends the job's remaining parts, then one wait."""
    short = job["job"][-6:]
    try:
        while job["remaining"]:
            part_text = job["remaining"][0]
            k = job["parts_sent"] + 1
            final = len(job["remaining"]) == 1
            # Stage 6: a respondent CHANGE stops the job at this
            # part boundary, before the part is sent. An unreadable
            # label (None) does not stop it - claims are claims.
            ctx = _delivery_ctx.get(job["job"]) or {}
            if job.get("respondent_claimed"):
                now_claim = _respondent_claim(
                    ctx.get("win_pkg") or job["pkg"], ctx.get("entry"))
                if now_claim and \
                        now_claim != job["respondent_claimed"]:
                    job["state"] = "held"
                    job["hold_reason"] = "respondent-changed:%s->%s" % (
                        job["respondent_claimed"], now_claim)
                    job["updated"] = time.strftime(
                        "%Y-%m-%dT%H:%M:%S+03:00")
                    _delivery_save(job)
                    receipt({"kind": "DELIVER_HELD", "job": job["job"],
                             "reason": job["hold_reason"]})
                    return
            marker = "[dlv-%s %d%s]\n" % (short, k,
                                          " final" if final else "")
            crit = [t for t in (job.get("critical") or [])
                    if t in part_text]
            spec = {"pkg": job["pkg"], "text": marker + part_text,
                    "send": True, "path": "split",
                    "policy": job.get("policy"),
                    "critical": crit,
                    "paste": bool(job.get("paste")),
                    "expect_respondent": job.get("expect_respondent")}
            t0 = time.time()
            resp = exchange(spec)
            wall = time.time() - t0
            verdict = resp.get("verdict") or {}
            band = verdict.get("band")
            chunk_state = verdict.get("chunk_state")
            job.setdefault("chunk_states", []).append(chunk_state)
            if chunk_state == "STAGED_UNVERIFIED":
                job["unverified_parts"] = \
                    job.get("unverified_parts", 0) + 1
            _calib_log({"job": job["job"], "app": job["pkg"],
                        "surface": (ctx.get("win_pkg") or job["pkg"]),
                        "chunk_size": job["ceiling"],
                        "result": chunk_state or band,
                        "failure_shape": resp.get("reason") or ""})
            receipt({"kind": "DELIVER_PART", "job": job["job"], "k": k,
                     "status": resp.get("status"), "band": band,
                     "chunk_state": chunk_state,
                     "reason": resp.get("reason"),
                     "sha256": hashlib.sha256(
                         part_text.encode("utf-8")).hexdigest(),
                     "ms": int(wall * 1000),
                     "ceiling": job["ceiling"]})
            if resp.get("status") != "sent":
                # v2 Fix 2 retry rule: classify the failure first.
                job.setdefault("retries", {})
                kind = _classify_part_failure(resp)
                if kind == "size-limit":
                    # Split ONLY this failed chunk into smaller
                    # numbered pieces and verify each independently.
                    new_ceiling = job["ceiling"] // 2
                    if new_ceiling < CHUNK_FLOOR:
                        job["state"] = "held"
                        job["hold_reason"] = "floor-reached"
                    else:
                        pieces = _chunk_text(part_text, new_ceiling)
                        if len(pieces) <= 1:
                            job["state"] = "held"
                            job["hold_reason"] = (
                                "size-limit-unsplittable")
                        else:
                            job["remaining"] = (
                                pieces + job["remaining"][1:])
                            job["parts_total"] = (
                                job["parts_sent"] +
                                len(job["remaining"]))
                            receipt({"kind": "DELIVER_SPLIT",
                                     "job": job["job"], "k": k,
                                     "from": job["ceiling"],
                                     "to": new_ceiling,
                                     "pieces": len(pieces)})
                            job["ceiling"] = new_ceiling
                    if job["state"] == "held":
                        job["updated"] = time.strftime(
                            "%Y-%m-%dT%H:%M:%S+03:00")
                        _delivery_save(job)
                        receipt({"kind": "DELIVER_HELD",
                                 "job": job["job"],
                                 "reason": job["hold_reason"],
                                 "chunk_state": chunk_state,
                                 "part_index": k,
                                 "part_sha256": hashlib.sha256(
                                     part_text.encode(
                                         "utf-8")).hexdigest(),
                                 "part_text": part_text})
                        return
                    _delivery_save(job)
                    time.sleep(2)
                    continue
                if kind == "definite" and \
                        job["retries"].get(k, 0) < 1:
                    # Definite rejection, evidence the chunk was not
                    # accepted: retry this same chunk ONCE.
                    job["retries"][k] = job["retries"].get(k, 0) + 1
                    receipt({"kind": "DELIVER_RETRY",
                             "job": job["job"], "k": k,
                             "reason": resp.get("reason"),
                             "sha256": hashlib.sha256(
                                 part_text.encode("utf-8")).hexdigest(),
                             "attempt": job["retries"][k]})
                    _delivery_save(job)
                    time.sleep(2)
                    continue
                # Ambiguous, or the one retry already failed: stop
                # and report UNKNOWN with the exact chunk, the error
                # and the message copy. Never blind-retry.
                job["state"] = "held"
                job["hold_reason"] = "%s:%s" % (
                    resp.get("status"), resp.get("reason"))
                job["updated"] = time.strftime(
                    "%Y-%m-%dT%H:%M:%S+03:00")
                _delivery_save(job)
                receipt({"kind": "DELIVER_HELD", "job": job["job"],
                         "reason": job["hold_reason"],
                         "chunk_state": chunk_state,
                         "part_index": k,
                         "part_sha256": hashlib.sha256(
                             part_text.encode("utf-8")).hexdigest(),
                         "part_text": part_text})
                return
            claim = resp.get("respondent_claimed")
            if claim and not job.get("respondent_claimed"):
                job["respondent_claimed"] = claim
            job["remaining"].pop(0)
            job["parts_sent"] = k
            job["last_sent_text"] = marker + part_text
            job["bands"].append(band)
            job["walls"].append(int(wall))
            job["updated"] = time.strftime("%Y-%m-%dT%H:%M:%S+03:00")
            # Adapt down only: a slow part (>2x running median) or an
            # unbound anchor shrinks the ceiling for the remainder.
            walls = job["walls"]
            med = sorted(walls)[len(walls) // 2]
            slow = wall > 2 * max(med, 20)
            if slow and len(job["remaining"]) > 0:
                new_ceiling = int(job["ceiling"] * 0.7)
                if new_ceiling < CHUNK_FLOOR:
                    job["floor_hits"] = job.get("floor_hits", 0) + 1
                    if job["floor_hits"] >= 2:
                        job["state"] = "held"
                        job["hold_reason"] = "floor-reached"
                        _delivery_save(job)
                        return
                else:
                    rest = "\n\n".join(job["remaining"])
                    job["remaining"] = _chunk_text(rest, new_ceiling)
                    receipt({"kind": "DELIVER_ADAPT",
                             "job": job["job"],
                             "from": job["ceiling"], "to": new_ceiling,
                             "after_part": k})
                    job["ceiling"] = new_ceiling
            _delivery_save(job)
            time.sleep(2)
        job["state"] = "sent"
        _delivery_save(job)
        if job.get("expect"):
            last = job.get("last_sent_text") or ""
            w = exchange({"pkg": job["pkg"], "text": last,
                          "send": False, "wait_only": True,
                          "expect": job.get("expect"),
                          "patience_s": job.get("patience_s"),
                          "xchg": job["job"]})
            job["wait"] = {"status": w.get("status"),
                           "reason": w.get("reason"),
                           "reply": w.get("reply"),
                           "reply_chars": w.get("reply_chars")}
        job["state"] = "done"
        job["updated"] = time.strftime("%Y-%m-%dT%H:%M:%S+03:00")
        _delivery_save(job)
        receipt({"kind": "DELIVER_DONE", "job": job["job"],
                 "parts": job["parts_sent"], "bands": job["bands"],
                 "chunk_states": job.get("chunk_states"),
                 "unverified_parts": job.get("unverified_parts", 0),
                 "wait_status": (job.get("wait") or {}).get("status")})
    except Exception as e:
        job["state"] = "held"
        job["hold_reason"] = "exc:%s" % e
        _delivery_save(job)
    finally:
        _delivery_ctx.pop(job["job"], None)
        with _delivery_lock:
            if _delivery_active.get("job") == job["job"]:
                _delivery_active["job"] = None


_delivery_ctx = {}


def _delivery_start(job):
    with _delivery_lock:
        if _delivery_active.get("job"):
            return None
        _delivery_active["job"] = job["job"]
    entry, _ah = _atlas_entry(job["pkg"])
    _delivery_ctx[job["job"]] = {
        "entry": entry,
        "win_pkg": (entry or {}).get("window_pkg") or job["pkg"]}
    _deliveries[job["job"]] = job
    _delivery_save(job)
    threading.Thread(target=_delivery_run, args=(job,),
                     daemon=True).start()
    return job["job"]


# ---- Stage 4: /status cache - the supervisor's health probe must
# never queue behind exchange work on the service channel (the
# stage-3 named cause). A refresher thread owns the channel calls;
# /status answers from memory and reports the cache age.
_status_cache = {"ts": 0.0, "wedge": {"state": "indeterminate"},
                 "epoch": None}


def _status_refresher():
    while True:
        try:
            st = call("com.qebas.kbdriver.STATUS", "status", {},
                      timeout=2.0)
            if not st or not st.get("ok"):
                wedge = {"state": "indeterminate"}
            else:
                streak = int(st.get("root_null_streak") or 0)
                evc = int(st.get("ev_count") or 0)
                pkg_now = st.get("pkg") or ""
                if streak >= 5 and evc > 0 and pkg_now:
                    wedge = {"state": "anomaly",
                             "signature": "events-grow-nodes-zero",
                             "root_null_streak": streak,
                             "ev_count": evc, "pkg": pkg_now}
                else:
                    wedge = {"state": "ok", "root_null_streak": streak,
                             "ev_count": evc}
            er = call("com.qebas.kbdriver.EPOCH_GET", "any", {},
                      timeout=3.0)
            _status_cache["wedge"] = wedge
            _status_cache["epoch"] = (er or {}).get("epoch")
            _status_cache["ts"] = time.time()
        except Exception:
            pass
        time.sleep(4)


_last_reply_sha = [""]


def exchange(spec):
    with _exchange_lock:
        return _exchange(spec)


def _exchange(spec):
    t0 = time.time()
    t0_str = time.strftime("%Y-%m-%dT%H:%M:%S+03:00")
    pkg = spec.get("pkg", "")
    text = spec.get("text", "")
    send = bool(spec.get("send", False))
    rec = {"pkg": pkg, "chars": len(text),
           "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
           "send": send}
    if send and _recon.get("quarantined"):
        receipt({"kind": "EXCHANGE_REFUSED", "reason": "quarantine",
                 "pkg": pkg, "sha256": rec["sha256"],
                 "quarantined_jobs": sorted(_recon["quarantined"].keys())})
        return {"status": "refused", "reason": "quarantine",
                "quarantined_jobs": sorted(_recon["quarantined"].keys())}
    if spec.get("xchg"):
        rec["xchg"] = spec["xchg"]
    _lastjob(phase="exchange", pkg=pkg, sha256=rec["sha256"],
             chars=rec["chars"], send=send)
    modified_a11y = None
    restore_to = None
    screen_guard = None
    paste_saved = {"text": None}

    def done(status, **kw):
        rec["status"] = status
        rec["ms"] = int((time.time() - t0) * 1000)
        rec.update(kw)
        if rec.get("send"):
            armed_job = _recon_close(rec["sha256"], t0_str)
            if armed_job and "armed_job" not in rec:
                rec["armed_job"] = armed_job
        receipt(rec)
        _lastjob(phase="idle",
                 last_outcome={"status": status, "pkg": pkg,
                               "sha256": rec["sha256"],
                               "reason": kw.get("reason"),
                               "ms": rec["ms"]})
        out = {"status": status, **kw}
        if rec.get("respondent_claimed"):
            out["respondent_claimed"] = rec["respondent_claimed"]
        return out

    try:
        # Banking gate: never run inside the bank room.
        if os.path.exists(BANK_FLAG):
            return done("aborted", reason="bank-mode")
        if any(s in pkg.lower() for s in NEVER_SUBSTR):
            return done("aborted", reason="never-list")
        if pkg not in ALLOW:
            return done("aborted", reason="not-allowlisted")

        # Atlas resolution: the package a caller names may be the
        # atlas package (e.g. the Bard app) while its window lives
        # under another package (the Google app). All foreground,
        # focus, send and extraction work below targets the WINDOW
        # package; launches go through the atlas package.
        entry, atlas_hash = _atlas_entry(pkg)
        win_pkg = (entry or {}).get("window_pkg") or pkg
        launch_pkg = (entry or {}).get("package") or pkg
        pat_ms = int((entry or {}).get("patience_s") or 120) * 1000
        rec["window_pkg"] = win_pkg
        rec["atlas"] = {"id": (entry or {}).get("id"),
                        "status": (entry or {}).get("status")
                        if entry else "missing-defaults",
                        "hash": atlas_hash}

        # On-demand enable: leave the list exactly as found.
        current = a11y_get()
        if SVC not in current:
            modified_a11y = current
            a11y_put((current + ":" + SVC) if current else SVC,
                     via_verb=False)
            rec["svc_on_demand"] = True
        st = service_up()
        if not st:
            return done("aborted", reason="service-unavailable")
        if not st.get("ok"):
            # The service holds a token ours does not match (its
            # private store survived something ours did not).
            return done("aborted", reason="auth-mismatch")

        fg = st.get("pkg", "")
        if any(s in fg.lower() for s in NEVER_SUBSTR):
            return done("aborted", reason="sensitive-foreground")
        # The owner's app, captured before anything moves: every exit
        # from here on restores it in the finally block. fg passed the
        # sensitive check above, so restoring to it is safe.
        if fg and fg not in (win_pkg, launch_pkg, "com.termux"):
            restore_to = fg
        # Screen guard: an exchange (plus a long generated answer) can
        # outlast the owner's screen timeout; hold the display awake
        # and restore his exact timeout afterwards. Settings go via
        # rish - plain Termux settings access throws.
        try:
            cur_to = rish("settings get system screen_off_timeout").strip()
            if cur_to.isdigit() and int(cur_to) < 600000:
                rish("settings put system screen_off_timeout 600000")
                screen_guard = int(cur_to)
                rec["screen_guard_from"] = screen_guard
        except Exception:
            screen_guard = None
        # Owner-touch admission gate (Kimi Q6d), hardened per
        # Aragon Q5 + Claude FIX-1106 Q4: a 12-second quiet gap
        # AND no input-method window up (a visible IME means he is
        # mid-typing even between taps), up to 30 s, instead of
        # yanking the screen mid-use or mid-read.
        if not spec.get("urgent"):
            tw0 = time.time()
            while True:
                lt = int(st.get("last_touch_ms") or 0)
                idle = int(time.time() * 1000) - lt
                if (not lt or idle >= 12000) \
                        and not st.get("ime_present"):
                    break
                if time.time() - tw0 > 30:
                    break
                time.sleep(2)
                st2 = call("com.qebas.kbdriver.STATUS", "status",
                           {}, timeout=2.0)
                if st2 and st2.get("ok"):
                    st = st2
            rec["touch_wait_ms"] = int((time.time() - tw0) * 1000)
        # The epoch fences every actuating verb from here on; fetch
        # it AFTER the touch gate so it is as fresh as possible.
        er = call("com.qebas.kbdriver.EPOCH_GET", "any", {})
        epoch = (er or {}).get("epoch")
        if epoch is None:
            return done("aborted", reason="no-epoch")
        rec["epoch"] = epoch
        if fg != win_pkg:
            launch_app(launch_pkg, epoch)
            time.sleep(1.5)
            st = call("com.qebas.kbdriver.STATUS", "status", {})
            if not st or st.get("pkg") != win_pkg:
                return done("aborted", reason="cannot-foreground")
        if not st.get("focused"):
            # Cold start: tap the composer through the service's
            # own model - CLICK_PATH on the digest's last EditText
            # node (in a conversation the composer is the only one).
            # The old road (shell uiautomator dump + rish input tap)
            # was doubly rish-walled, and the dump's transient
            # UiAutomation collides with the live service binding
            # (KB-A/KB-K Q1) - it is what made cold starts abort
            # no-focused-field while the composer sat visible.
            dg = call("com.qebas.kbdriver.DIGEST", win_pkg,
                      {"since": 0, "wait_ms": 0}, timeout=20.0)
            nodes = ((dg or {}).get("digest") or {}).get("nodes") or []
            edits = [n[0] for n in nodes if "EditText" in str(n[1])]
            if edits:
                call("com.qebas.kbdriver.CLICK_PATH", win_pkg,
                     {"path": edits[-1], "expect": "",
                      "epoch": int(epoch)}, timeout=12.0)
                time.sleep(0.8)
                st = call("com.qebas.kbdriver.STATUS", "status", {})
            if not st or not st.get("focused"):
                return done("aborted", reason="no-focused-field")

        # Stage 6: respondent claim, read from the live tree after
        # foregrounding and BEFORE anything is set or sent. A caller
        # that requires a named respondent is gated here.
        claim = _respondent_claim(win_pkg, entry)
        rec["respondent_claimed"] = claim
        if spec.get("expect_respondent") and \
                claim != spec["expect_respondent"]:
            return done("aborted", reason="respondent-mismatch",
                        respondent_claimed=claim)
        phases = {}
        # v2 Fix 1: explicit focused-field check before anything
        # is typed. The cold-start tap above may have re-focused
        # the composer; this verifies the result instead of
        # assuming it. Skipped for wait-only passes (no typing).
        if not spec.get("wait_only"):
            fok, fdetail = _focus_check(win_pkg)
            rec["focus_check"] = fdetail
            if not fok:
                return done("aborted", reason=fdetail["code"],
                            phases=phases, focus=fdetail)
        if spec.get("wait_only"):
            # Stage 4 split: the send already happened in /send; this
            # pass runs only the extraction below.
            pass
        elif send and spec.get("path") == "split":
            # Stage 4 daemon-side verified send: SET_TEXT, GET_TEXT,
            # verdict engine, SEND_ARMED - the send/wait split at the
            # service-verb level. Returns as soon as the send is
            # decided; the reply is harvested by a separate /wait.
            # Stage 7: with "paste": true the text enters via the
            # clipboard instead (flagged surfaces only).
            # v2 Fix 2: snapshot the chip nodes BEFORE the text
            # enters the composer, so the verdict can tell a fresh
            # chip for this chunk from a stale one.
            _pre_chip = _chip_snapshot(win_pkg)
            pre_chip_paths = _pre_chip[0] if _pre_chip else None
            t_ph = time.time()
            if spec.get("paste"):
                if not (entry or {}).get("paste_allowed"):
                    return done("aborted", reason="paste-not-enabled",
                                phases=phases)
                perr = _paste_commit(win_pkg, launch_pkg, epoch, text,
                                     rec, paste_saved)
                if perr:
                    return done("aborted", reason=perr, phases=phases)
                phases["paste_ms"] = int((time.time() - t_ph) * 1000)
            else:
                r = call_text("com.qebas.kbdriver.SET_TEXT", win_pkg,
                              text, fields={"epoch": int(epoch)})
                if not r or not r.get("ok"):
                    return done("aborted", reason="set-text-failed",
                                phases=phases)
            g = call("com.qebas.kbdriver.GET_TEXT", win_pkg, {})
            verdict = _send_verdict(win_pkg, text, g, spec,
                            pre_chip_paths=pre_chip_paths)
            verdict["via"] = "paste" if spec.get("paste") else "set"
            if spec.get("paste") and \
                    verdict.get("band") == "sent-with-error-unmeasured" \
                    and verdict.get("readback_chars") == 0:
                # The paste landed as NOTHING (no chip, no text):
                # a landing failure, not a fidelity drift - the
                # distinct stage-7 code, and never armed.
                verdict["band"] = "hold"
                verdict["code"] = "paste-mismatch"
            phases["verdict_ms"] = int((time.time() - t_ph) * 1000)
            rec["verdict"] = {k: v for k, v in verdict.items()
                              if k != "readback_copy"}
            if verdict.get("readback_copy"):
                rec["verdict"]["readback_copy"] = verdict["readback_copy"]
            if verdict["band"] == "hold":
                call("com.qebas.kbdriver.CLEAR", win_pkg,
                     {"epoch": int(epoch)})
                return done("aborted",
                            reason="verify-" + str(verdict.get(
                                "code", "held")),
                            phases=phases, verdict=rec["verdict"])
            t_ph = time.time()
            r = call_text("com.qebas.kbdriver.SEND_ARMED", win_pkg, text,
                          timeout=15.0,
                          fields={"epoch": int(epoch)})
            phases["send_ms"] = int((time.time() - t_ph) * 1000)
            if not r or not r.get("ok"):
                return done("aborted",
                            reason=(r or {}).get("reason", "send-failed"),
                            phases=phases, verdict=rec["verdict"])
            aj = _recon_close(rec["sha256"], t0_str)
            if aj:
                rec["armed_job"] = aj
            xchg = "xchg-%d" % int(time.time() * 1000)
            _xchg[xchg] = {"pkg": pkg, "text": text,
                           "sha256": rec["sha256"], "ts": t0_str,
                           "wait_outcome": None}
            rec["xchg"] = xchg
            return done("sent", verified=(verdict["band"] == "clean"),
                        verdict=rec["verdict"], job_id=xchg,
                        phases=phases)
        elif send:
            # Composite (v4.0): set + hash-verify + Send in ONE trip
            # inside the service. The verify discipline is identical;
            # the dead air between typing and sending is gone.
            t_ph = time.time()
            r = call_text("com.qebas.kbdriver.SEND_VERIFIED", win_pkg, text,
                          timeout=30.0,
                          fields={"epoch": int(epoch)})
            phases["send_ms"] = int((time.time() - t_ph) * 1000)
            if not r or not r.get("ok"):
                return done("aborted",
                            reason=(r or {}).get("reason", "send-failed"),
                            phases=phases)
            if spec.get("wait") is False:
                # Send-only (intermediate parts): no extraction.
                return done("sent", verified=True, phases=phases)
        else:
            r = call_text("com.qebas.kbdriver.SET_TEXT", win_pkg, text,
                          fields={"epoch": int(epoch)})
            if not r or not r.get("ok"):
                return done("aborted", reason="set-text-failed")
            r = call("com.qebas.kbdriver.GET_TEXT", win_pkg, {})
            want = hashlib.sha256(text.encode("utf-8")).hexdigest()
            if not r or r.get("sha256") != want:
                call("com.qebas.kbdriver.CLEAR", win_pkg,
                     {"epoch": int(epoch)})
                return done("aborted", reason="verify-mismatch")
            return done("ok", verified=True, phases=phases)
        # Atlas gate: on surfaces whose copy road is unmapped or known
        # destructive (extraction_allowed false), a successful send
        # ends the job - no anchor hunt, no QUIET_COPY. The reply is
        # simply not harvested; the receipt says why.
        if entry is not None and entry.get("extraction_allowed") is False:
            return done("ok", verified=True, reply="",
                        extraction="gated-by-atlas", phases=phases)
        # Extraction, validated (v3.4): WAIT_QUIET can settle during a
        # pause in a long generation, when the bottom-most Copy control
        # still belongs to the PREVIOUS reply - the clipboard then
        # returns the old answer and v3.3 happily reported it as new
        # (the EL-1105 election exchange, 2026-11-05). A candidate is
        # accepted only if it is non-empty, differs from the last
        # reply when it is long, and contains the caller's "expect"
        # marker when one was given. Otherwise wait and copy again;
        # after 3 attempts the exchange aborts as extract-stale
        # instead of lying.
        expect = spec.get("expect") or None
        # Anchor (Kimi Q3): locate my own sent message; QUIET_COPY
        # will only accept a Copy control below it, so the previous
        # reply's control is ineligible by construction. The marker /
        # changed-hash validation below stays as the backstop.
        t_ph = time.time()
        ra = call_text("com.qebas.kbdriver.FIND_ANCHOR", win_pkg, text,
                       timeout=15.0, fields={})
        phases["anchor_ms"] = int((time.time() - t_ph) * 1000)
        anchor_bottom = -1
        if ra and ra.get("ok") and ra.get("bottom") is not None:
            anchor_bottom = int(ra["bottom"])
        rec["anchor"] = "bound" if anchor_bottom >= 0 else "unbound"
        reply = None
        cand = ""
        attempts = 0
        t_ph = time.time()
        while attempts < 3:
            attempts += 1
            qc_job = new_job("quiet_copy")
            r = call("com.qebas.kbdriver.QUIET_COPY", win_pkg,
                     {"quiet_ms": 2000, "max_ms": pat_ms,
                      "descs": "Copy message,Copy",
                      "anchor_bottom": anchor_bottom,
                      "epoch": int(epoch),
                      "anchor_b64": base64.b64encode(
                          text.encode("utf-8")).decode()},
                     timeout=pat_ms / 1000.0 + 10.0, job=qc_job,
                     stall_watch=True)
            if not r or not r.get("ok"):
                return done("aborted",
                            reason=(r or {}).get("reason", "extract-timeout"),
                            phases=phases)
            time.sleep(0.4)
            # Clipboard reads are empty while Termux is backgrounded.
            launch_app("com.termux", epoch)
            time.sleep(1.1)
            cand = sh("termux-clipboard-get") or ""
            # Validation is string work - it does not need the target
            # back in front. v3.4 returned to the target here for a
            # foreground check left over from the design that ENDED
            # at the target; with the owner's restore in the finally
            # block, that stop was pure overhead (an extra window
            # switch in front of him). The target is re-foregrounded
            # only when another copy attempt is actually needed.
            cand_sha = hashlib.sha256(cand.encode("utf-8")).hexdigest()
            same_as_last = cand_sha == _last_reply_sha[0] and len(cand) > 200
            expect_missing = bool(expect) and expect not in cand
            if cand and not same_as_last and not expect_missing:
                reply = cand
                _last_reply_sha[0] = cand_sha
                break
            rec.setdefault("extract_retries", []).append(
                {"attempt": attempts, "chars": len(cand),
                 "same_as_last": bool(same_as_last),
                 "expect_missing": bool(expect_missing)})
            if attempts < 3:
                launch_app(launch_pkg, epoch)
                time.sleep(1.0)
                st = call("com.qebas.kbdriver.STATUS", "status", {})
                if not st or st.get("pkg") != win_pkg:
                    return done("aborted", reason="foreground-changed",
                                reply=cand)
                time.sleep(4)
        phases["extract_ms"] = int((time.time() - t_ph) * 1000)
        if reply is None:
            return done("aborted", reason="extract-stale", reply=cand,
                        extract_attempts=attempts, phases=phases)
        return done("ok", verified=True, reply=reply,
                    reply_chars=len(reply), extract_attempts=attempts,
                    phases=phases)
    finally:
        epi = {"kind": "exchange-epilogue"}
        if screen_guard is not None:
            try:
                rish("settings put system screen_off_timeout %d" % screen_guard)
                back = rish("settings get system screen_off_timeout").strip()
                epi["screen_guard_restored"] = (back == str(screen_guard))
            except Exception:
                epi["screen_guard_restored"] = False
        if paste_saved.get("text") is not None:
            # Stage 7 residue duty: the owner's clipboard goes back
            # exactly as found, whatever the send's outcome was.
            try:
                launch_app("com.termux", epoch)
                tmp = os.path.join(HOME, "kb_paste_tmp.txt")
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(paste_saved["text"])
                sh("termux-clipboard-set < " + tmp)
                os.remove(tmp)
                receipt({"kind": "CLIP_RESTORED",
                         "chars": len(paste_saved["text"])})
            except Exception:
                receipt({"kind": "CLIP_RESTORE_FAILED"})
            paste_saved["text"] = None
        if restore_to:
            # Restore only a foreground WE put there (the target, or
            # Termux from the clipboard detour). If the owner has
            # already moved somewhere himself, leave his screen alone.
            try:
                # Foreground from the service's own model over the
                # channel - the old rish dumpsys read died with the
                # bridge and left the restore decision blind
                # (drill 2026-11-06 21:31: left-as-found with an
                # empty name while rish was dead).
                st_now = call("com.qebas.kbdriver.STATUS", "status", {})
                cur_pkg = (st_now or {}).get("pkg", "")
                if cur_pkg in ("com.termux", win_pkg, launch_pkg):
                    launch_app(restore_to)
                    epi["restored_fg"] = restore_to
                else:
                    epi["restored_fg"] = "left-as-found:" + cur_pkg
            except Exception:
                pass
        if len(epi) > 1:
            receipt(epi)
        if modified_a11y is not None:
            a11y_put(modified_a11y, via_verb=True)


class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def do_POST(self):
        n = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(n) if n else b""
        try:
            data = json.loads(body.decode("utf-8")) if body else {}
        except Exception:
            data = {}
        if self.path == "/armed":
            # The service's write-ahead marker, posted synchronously
            # BEFORE a send clicks (Claude FIX-1106 Q1). Landing it
            # in the receipts means a restarted daemon can still
            # tell a half-done exchange from idle.
            if data.get("t") != TOKEN and not _auth_ok(self):
                out = {"ok": False, "reason": "auth"}
            else:
                _armed[data.get("job")] = data
                receipt({"kind": "EXCHANGE_ARMED",
                         "job": data.get("job"),
                         "seq": data.get("seq"),
                         "text_hash": data.get("text_hash")})
                _lastjob(phase="send_armed", job=data.get("job"),
                         seq=data.get("seq"),
                         text_hash=data.get("text_hash"))
                _recon_armed(data.get("job"), data.get("text_hash"))
                out = {"ok": True}
        elif self.path == "/progress":
            if data.get("t") != TOKEN and not _auth_ok(self):
                out = {"ok": False, "reason": "auth"}
            else:
                if data.get("job"):
                    _progress[data["job"]] = time.time()
                out = {"ok": True}
        elif self.path == "/result":
            # The service stamps its posts with the token once one is
            # configured; before that, posts are accepted (bootstrap).
            if _svc_token_active[0] and data.get("t") != TOKEN \
                    and not _auth_ok(self):
                out = {"ok": False, "reason": "auth"}
            else:
                job = data.get("job")
                if job:
                    with _jobs_lock:
                        ev = _jobs.setdefault(job,
                                              {"event": threading.Event(),
                                               "result": None})
                        ev["result"] = data
                        ev["event"].set()
                out = {"ok": True}
        elif not _auth_ok(self):
            payload = json.dumps({"ok": False, "reason": "auth"}).encode()
            self.send_response(403)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        elif self.path == "/epoch/bump":
            reason = str(data.get("reason", "bump"))[:40]
            r = call("com.qebas.kbdriver.EPOCH_BUMP", "any",
                     {"reason": reason})
            out = {"epoch": (r or {}).get("epoch")}
        elif self.path == "/act":
            # Epoch-fenced primitives for the plan executor. The
            # service itself refuses a stale epoch; the daemon adds
            # the standing gates (bank flag, never-list, allowlist).
            pkg = data.get("pkg", "")
            kind = data.get("kind", "")
            epoch = data.get("epoch")
            if os.path.exists(BANK_FLAG):
                out = {"ok": False, "reason": "bank-mode"}
            elif any(s in pkg.lower() for s in NEVER_SUBSTR):
                out = {"ok": False, "reason": "never-list"}
            elif pkg not in ALLOW:
                out = {"ok": False, "reason": "not-allowlisted"}
            elif epoch is None:
                out = {"ok": False, "reason": "no-epoch"}
            elif kind == "tap":
                desc = str(data.get("desc", ""))
                max_ms = int(data.get("max_ms", 15000))
                r = call("com.qebas.kbdriver.WAIT_TAP", pkg,
                         {"desc": desc, "max_ms": max_ms,
                          "epoch": int(epoch)},
                         timeout=max_ms / 1000.0 + 10.0)
                out = {"ok": bool(r and r.get("ok")),
                       "reason": (r or {}).get("reason")}
            elif kind == "set_text":
                text = data.get("text", "")
                b64 = base64.b64encode(text.encode("utf-8")).decode()
                r = call("com.qebas.kbdriver.SET_TEXT", pkg,
                         {"b64": b64, "epoch": int(epoch)})
                if not r or not r.get("ok"):
                    out = {"ok": False,
                           "reason": (r or {}).get("reason", "set-failed")}
                else:
                    g = call("com.qebas.kbdriver.GET_TEXT", pkg, {})
                    want = hashlib.sha256(text.encode("utf-8")).hexdigest()
                    ok = bool(g and g.get("sha256") == want)
                    out = {"ok": ok, "verified": ok,
                           "reason": None if ok else "verify-mismatch"}
            elif kind == "send_armed":
                # v5.0: the second half of the split send. The
                # composer must already hold exactly this text; the
                # service posts ARMED, then clicks. Journalled by
                # the executor like any other act.
                text = data.get("text", "")
                b64 = base64.b64encode(text.encode("utf-8")).decode()
                r = call("com.qebas.kbdriver.SEND_ARMED", pkg,
                         {"b64": b64, "epoch": int(epoch)}, timeout=15.0)
                out = {"ok": bool(r and r.get("ok")),
                       "reason": (r or {}).get("reason"),
                       "sha256": (r or {}).get("sha256")}
            elif kind == "setting_get":
                r = call("com.qebas.kbdriver.SETTING_GET", pkg,
                         {"key": str(data.get("key", ""))}, timeout=12.0)
                out = {"ok": bool(r and r.get("ok")),
                       "value": (r or {}).get("text"),
                       "reason": (r or {}).get("reason")}
            elif kind == "setting_put":
                f = {"key": str(data.get("key", "")),
                     "epoch": int(epoch)}
                if data.get("delete"):
                    f["delete"] = 1
                else:
                    f["value_b64"] = base64.b64encode(
                        str(data.get("value", "")).encode(
                            "utf-8")).decode()
                r = call("com.qebas.kbdriver.SETTING_PUT", pkg, f,
                         timeout=12.0)
                out = {"ok": bool(r and r.get("ok")),
                       "reason": (r or {}).get("reason")}
            elif kind == "tap_xy":
                x = int(data.get("x", -1))
                y = int(data.get("y", -1))
                dur = int(data.get("dur", 80))
                r = call("com.qebas.kbdriver.GESTURE", pkg,
                         {"x": x, "y": y, "dur": dur,
                          "epoch": int(epoch)}, timeout=12.0)
                out = {"ok": bool(r and r.get("ok")),
                       "reason": (r or {}).get("reason")}
            elif kind == "get_text":
                g = call("com.qebas.kbdriver.GET_TEXT", pkg, {})
                if not g or not g.get("ok"):
                    out = {"ok": False,
                           "reason": (g or {}).get("reason", "get-failed")}
                else:
                    out = {"ok": True, "sha256": g.get("sha256"),
                           "chars": g.get("chars")}
            elif kind == "tap_path":
                path = str(data.get("path", ""))
                expect = str(data.get("expect", ""))
                r = call("com.qebas.kbdriver.CLICK_PATH", pkg,
                         {"path": path, "expect": expect,
                          "epoch": int(epoch)},
                         timeout=12.0)
                out = {"ok": bool(r and r.get("ok")),
                       "reason": (r or {}).get("reason")}
            elif kind == "scroll":
                direction = "down" if data.get("dir") == "down" else "up"
                px = int(data.get("px", 600))
                r = call("com.qebas.kbdriver.SCROLL", pkg,
                         {"dir": direction, "px": px,
                          "epoch": int(epoch)}, timeout=12.0)
                out = {"ok": bool(r and r.get("ok")),
                       "reason": (r or {}).get("reason")}
            elif kind == "global":
                which = "home" if data.get("which") == "home" else "back"
                r = call("com.qebas.kbdriver.GLOBAL", pkg,
                         {"which": which, "epoch": int(epoch)},
                         timeout=12.0)
                out = {"ok": bool(r and r.get("ok")),
                       "reason": (r or {}).get("reason")}
            else:
                out = {"ok": False, "reason": "bad-kind"}
        elif self.path == "/recon_ack":
            if not _auth_ok(self):
                out = {"ok": False, "reason": "auth"}
            else:
                job = data.get("job")
                verdict = str(data.get("verdict", ""))[:60]
                with _recon_lock:
                    hit = job in (_recon.get("quarantined") or {})
                    if hit:
                        _recon["quarantined"].pop(job, None)
                        _recon_save()
                if hit:
                    receipt({"kind": "RECONCILED_VERDICT", "job": job,
                             "verdict": verdict})
                out = {"ok": hit, "job": job,
                       "quarantine_remaining":
                           len(_recon.get("quarantined") or {})}
        elif self.path == "/deliver":
            # Stage 5 resident delivery: accept the whole text, run
            # it as a background job, return the job id at once.
            if not _auth_ok(self):
                out = {"status": "error", "reason": "auth"}
            else:
                text = data.get("text", "")
                pkg = data.get("pkg", "")
                entry, _ah = _atlas_entry(pkg)
                # v2 Fix 3: caller > atlas chunk_chars > per-app
                # default > 2400; hard cap CHUNK_CAP (2554).
                # Shortcut/web-surface calibration is out of scope.
                ceiling = int(data.get("ceiling") or
                              (entry or {}).get("chunk_chars") or
                              CHUNK_DEFAULTS.get(pkg) or 2400)
                ceiling = max(CHUNK_FLOOR, min(CHUNK_CAP, ceiling))
                ceiling_source = ("caller" if data.get("ceiling")
                                  else "atlas"
                                  if (entry or {}).get("chunk_chars")
                                  else "app-default"
                                  if pkg in CHUNK_DEFAULTS
                                  else "default")
                job = {"job": "dlv-%d" % int(time.time() * 1000),
                       "pkg": pkg, "state": "running",
                       "ceiling": ceiling,
                       "ceiling_source": ceiling_source,
                       "expect_respondent": data.get(
                           "expect_respondent"),
                       "respondent_claimed": None,
                       "parts_sent": 0,
                       "remaining": _chunk_text(text, ceiling),
                       "bands": [], "walls": [], "floor_hits": 0,
                       "retries": {}, "chunk_states": [],
                       "unverified_parts": 0,
                       "critical": data.get("critical") or [],
                       "paste": bool(data.get("paste")),
                       "policy": data.get("policy"),
                       "expect": data.get("expect"),
                       "patience_s": data.get("patience_s"),
                       "last_sent_text": None,
                       "created": time.strftime(
                           "%Y-%m-%dT%H:%M:%S+03:00"),
                       "updated": time.strftime(
                           "%Y-%m-%dT%H:%M:%S+03:00")}
                job["parts_total"] = len(job["remaining"])
                started = _delivery_start(job)
                if started is None:
                    out = {"status": "refused",
                           "reason": "delivery-active",
                           "job": _delivery_active.get("job")}
                else:
                    out = {"status": "accepted", "job_id": job["job"],
                           "parts": job["parts_total"],
                           "ceiling": ceiling,
                           "ceiling_source": ceiling_source}
        elif self.path == "/deliver_status":
            if not _auth_ok(self):
                out = {"status": "error", "reason": "auth"}
            else:
                job = _deliveries.get(data.get("job_id") or "")
                if job is None:
                    out = {"status": "error", "reason": "unknown-job"}
                else:
                    out = {"status": job["state"], "job_id": job["job"],
                           "pkg": job["pkg"],
                           "respondent_claimed": job.get(
                               "respondent_claimed"),
                           "ceiling_source": job.get("ceiling_source"),
                           "parts_sent": job["parts_sent"],
                           "parts_total": job.get("parts_total"),
                           "parts_remaining": len(job["remaining"]),
                           "bands": job["bands"],
                           "chunk_states": job.get("chunk_states"),
                           "unverified_parts": job.get(
                               "unverified_parts", 0),
                           "ceiling": job["ceiling"],
                           "hold_reason": job.get("hold_reason"),
                           "wait": job.get("wait")}
        elif self.path == "/deliver_resume":
            # Explicit-order resume of an interrupted/held job whose
            # remaining parts were never sent. Never automatic.
            if not _auth_ok(self):
                out = {"status": "error", "reason": "auth"}
            else:
                job = _deliveries.get(data.get("job_id") or "")
                if job is None:
                    out = {"status": "error", "reason": "unknown-job"}
                elif job["state"] not in ("interrupted", "held"):
                    out = {"status": "error",
                           "reason": "not-resumable:" + job["state"]}
                elif not job["remaining"]:
                    out = {"status": "error", "reason": "nothing-left"}
                else:
                    job["state"] = "running"
                    job.pop("hold_reason", None)
                    started = _delivery_start(job)
                    out = {"status": "resumed" if started else "refused",
                           "job_id": job["job"],
                           "reason": None if started
                           else "delivery-active"}
        elif self.path == "/send":
            # Stage 4 split send: daemon-side verified send that
            # returns when the send is decided (job_id keys the
            # later /wait). No extraction happens here.
            if not _auth_ok(self):
                out = {"status": "error", "reason": "auth"}
            else:
                spec = {"pkg": data.get("pkg", ""),
                        "text": data.get("text", ""), "send": True,
                        "path": "split",
                        "policy": data.get("policy"),
                        "critical": data.get("critical") or [],
                        "paste": bool(data.get("paste")),
                        "expect_respondent": data.get(
                            "expect_respondent")}
                if data.get("urgent"):
                    spec["urgent"] = True
                try:
                    out = exchange(spec)
                except Exception as e:
                    out = {"status": "error", "reason": "exc:%s" % e}
        elif self.path == "/wait":
            # Stage 4 split wait: harvest the reply for a /send job.
            # Idempotent - a completed wait returns its stored
            # outcome without re-extracting.
            if not _auth_ok(self):
                out = {"status": "error", "reason": "auth"}
            else:
                job = _xchg.get(data.get("job_id") or "")
                if job is None:
                    out = {"status": "error", "reason": "unknown-job"}
                elif job.get("wait_outcome") is not None:
                    out = job["wait_outcome"]
                else:
                    spec = {"pkg": job["pkg"], "text": job["text"],
                            "send": False, "wait_only": True,
                            "expect": data.get("expect"),
                            "patience_s": data.get("patience_s"),
                            "xchg": data.get("job_id")}
                    if data.get("urgent"):
                        spec["urgent"] = True
                    try:
                        out = exchange(spec)
                    except Exception as e:
                        out = {"status": "error",
                               "reason": "exc:%s" % e}
                    job["wait_outcome"] = out
        elif self.path == "/exchange":
            try:
                out = exchange(data)
            except Exception as e:
                out = {"status": "error", "reason": "exc:%s" % e}
        elif self.path == "/tap":
            # One instruction per choice: the service watches for the
            # labelled node event-side and taps it the moment it
            # appears — nothing crosses the tunnel per look or tap.
            pkg = data.get("pkg", "")
            desc = data.get("desc", "")
            max_ms = int(data.get("max_ms", 60000))
            if os.path.exists(BANK_FLAG):
                out = {"status": "aborted", "reason": "bank-mode"}
            elif any(s in pkg.lower() for s in NEVER_SUBSTR):
                out = {"status": "aborted", "reason": "never-list"}
            elif pkg not in ALLOW:
                out = {"status": "aborted", "reason": "not-allowlisted"}
            else:
                er = call("com.qebas.kbdriver.EPOCH_GET", "any", {})
                ep = (er or {}).get("epoch")
                if ep is None:
                    out = {"status": "aborted", "reason": "no-epoch"}
                else:
                    r = call("com.qebas.kbdriver.WAIT_TAP", pkg,
                             {"desc": desc, "max_ms": max_ms,
                              "epoch": int(ep)},
                             timeout=max_ms / 1000.0 + 10.0)
                    if r and r.get("ok"):
                        out = {"status": "ok", "tapped": desc}
                    else:
                        out = {"status": "aborted",
                               "reason": (r or {}).get("reason", "no-result")}
        else:
            out = {"error": "unknown path"}
        payload = json.dumps(out, ensure_ascii=False).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def do_GET(self):
        if self.path.startswith("/next"):
            # v5.0 channel: the service long-polls for commands.
            # The token rides in the X-KB-Token header.
            if not _auth_ok(self):
                payload = json.dumps({"ok": False,
                                      "reason": "auth"}).encode()
                self.send_response(403)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
                return
            cmd = None
            deadline = time.time() + 25.0
            with _chan["cond"]:
                _chan["poller_seen"] = time.time()
                while time.time() < deadline:
                    if _chan["queue"]:
                        cmd = _chan["queue"].pop(0)
                        break
                    _chan["poller_seen"] = time.time()
                    _chan["cond"].wait(1.0)
            if cmd is None:
                self.send_response(204)
                self.send_header("Content-Length", "0")
                self.end_headers()
                return
            payload = json.dumps(cmd, ensure_ascii=False).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if self.path.startswith(("/shot", "/epoch", "/digest")) \
                and not _auth_ok(self):
            payload = json.dumps({"ok": False, "reason": "auth"}).encode()
            self.send_response(403)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if self.path.startswith("/shot"):
            # Phase 4 escalation: capture the screen so the remote
            # side can SEE a stuck state the tree cannot express.
            # Never inside bank mode or a never-list foreground.
            if os.path.exists(BANK_FLAG):
                out = {"ok": False, "reason": "bank-mode"}
            else:
                st = call("com.qebas.kbdriver.STATUS", "shot", {})
                fg = (st or {}).get("pkg", "")
                if any(s in fg.lower() for s in NEVER_SUBSTR):
                    out = {"ok": False, "reason": "sensitive-foreground"}
                else:
                    # v5.0.5: the service captures its own screen
                    # (takeScreenshot) - no rish screencap, no
                    # /sdcard staging file.
                    er = call("com.qebas.kbdriver.EPOCH_GET", "any", {})
                    ep = (er or {}).get("epoch")
                    if ep is None:
                        out = {"ok": False, "reason": "no-epoch"}
                    else:
                        r = call("com.qebas.kbdriver.SCREENSHOT", "shot",
                                 {"epoch": int(ep)}, timeout=25.0)
                        if r and r.get("ok") and r.get("text"):
                            out = {"ok": True, "pkg": fg,
                                   "png_b64": r["text"],
                                   "bytes": r.get("chars", 0)}
                        else:
                            out = {"ok": False,
                                   "reason": (r or {}).get(
                                       "reason", "shot-failed")}
            payload = json.dumps(out).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if self.path.startswith("/epoch"):
            r = call("com.qebas.kbdriver.EPOCH_GET", "any", {})
            out = {"epoch": (r or {}).get("epoch")}
            payload = json.dumps(out).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if self.path.startswith("/digest"):
            from urllib.parse import urlparse, parse_qs
            q = parse_qs(urlparse(self.path).query)
            try:
                since = int(q.get("since", ["-1"])[0])
            except Exception:
                since = -1
            try:
                wait_ms = int(q.get("wait_ms", ["0"])[0])
            except Exception:
                wait_ms = 0
            wait_ms = max(0, min(wait_ms, 120000))
            if os.path.exists(BANK_FLAG):
                out = {"status": "aborted", "reason": "bank-mode"}
            else:
                r = call("com.qebas.kbdriver.DIGEST", "any",
                         {"since": since, "wait_ms": wait_ms},
                         timeout=wait_ms / 1000.0 + 20.0)
                if not r or not r.get("ok"):
                    out = {"status": "aborted", "reason": "no-result"}
                else:
                    dg = r.get("digest") or {}
                    if any(s in (dg.get("pkg") or "").lower()
                           for s in NEVER_SUBSTR):
                        out = {"seq": r.get("seq"), "changed": r.get("changed"),
                               "refused": "sensitive-foreground"}
                    else:
                        out = {"seq": r.get("seq"), "changed": r.get("changed"),
                               "hash": r.get("hash"), "digest": dg}
            payload = json.dumps(out, ensure_ascii=False).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        # /status stays open for health checks but reports no
        # content - only counters and the wedge state (Kimi Q5 L0):
        # ANOMALY when events flow yet the model stays empty for a
        # real foreground; INDETERMINATE when the probe itself fails.
        # Stage 4: answered from the refresher thread's cache - no
        # channel calls on this path, so the supervisor's probe can
        # never be wedged by exchange work (stage-3 named cause).
        wedge = _status_cache["wedge"]
        out = {"service": "kb_driver", "port": PORT, "version": 5.0,
               "build": "v2-2026-11-12",
               "allow": sorted(ALLOW), "wedge": wedge,
               "epoch_live": _status_cache["epoch"],
               "status_cache_age_s": round(
                   time.time() - _status_cache["ts"], 1)
               if _status_cache["ts"] else None,
               "holders": _holders_view(),
               "channel": {"fresh": _channel_fresh(),
                           "poller_age_s": round(
                               time.time() - _chan["poller_seen"], 1)
                           if _chan["poller_seen"] else None,
                           "queued": len(_chan["queue"])}}
        _deaths = _tail_jsonl(DEATHS)
        out["last_death"] = _deaths[-1] if _deaths else None
        out["last_job"] = _read_lastjob()
        out["unreconciled_armed"] = {
            "count": len(_recon.get("quarantined") or {}) +
                     len(_recon.get("open") or {}),
            "jobs": sorted((_recon.get("quarantined") or {}).keys())[:10]}
        out["quarantine"] = {
            "count": len(_recon.get("quarantined") or {}),
            "jobs": sorted((_recon.get("quarantined") or {}).keys())}
        out["deliveries"] = {
            "active": _delivery_active.get("job"),
            "held": sorted(j for j, jb in _deliveries.items()
                           if jb.get("state") in ("held", "interrupted"))}
        payload = json.dumps(out).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)


if __name__ == "__main__":
    _recon_boot()
    _delivery_boot()
    threading.Thread(target=_status_refresher, daemon=True).start()
    threading.Thread(target=_holder_thread, daemon=True).start()
    ThreadingHTTPServer(("127.0.0.1", PORT), H).serve_forever()
