package com.qebas.kbdriver;

import android.accessibilityservice.AccessibilityService;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.accessibilityservice.GestureDescription;
import android.content.IntentFilter;
import android.graphics.Rect;
import android.os.Bundle;
import android.util.Base64;
import android.util.Log;
import android.view.accessibility.AccessibilityEvent;
import android.view.accessibility.AccessibilityNodeInfo;
import android.view.accessibility.AccessibilityWindowInfo;

import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.List;

/**
 * KB Driver service v3 (keyboard-driver project, 2026-11-05).
 * Broadcast verbs against a named package's window:
 *   SET_TEXT / CLEAR / PASTE / GET_TEXT - the focused editable node
 *   STATUS     - foreground package + focused field state
 *   CLICK_NODE - ACTION_CLICK the bottom-most node whose
 *                content-description contains a given substring
 *   WAIT_QUIET - watch the window text in-process until it is
 *                unchanged for quiet_ms (or max_ms elapses)
 * Results are POSTed to the loopback daemon (127.0.0.1:8773/result)
 * and mirrored to logcat tag KBDRV.
 */
public class KbService extends AccessibilityService {
    private static final String TAG = "KBDRV";
    public static final String ACT_SET = "com.qebas.kbdriver.SET_TEXT";
    public static final String ACT_CLEAR = "com.qebas.kbdriver.CLEAR";
    public static final String ACT_PASTE = "com.qebas.kbdriver.PASTE";
    public static final String ACT_GET = "com.qebas.kbdriver.GET_TEXT";
    public static final String ACT_STATUS = "com.qebas.kbdriver.STATUS";
    public static final String ACT_CLICK = "com.qebas.kbdriver.CLICK_NODE";
    public static final String ACT_WAIT = "com.qebas.kbdriver.WAIT_QUIET";
    public static final String ACT_WAIT_TAP = "com.qebas.kbdriver.WAIT_TAP";
    public static final String ACT_DIGEST = "com.qebas.kbdriver.DIGEST";
    public static final String ACT_SCROLL = "com.qebas.kbdriver.SCROLL";
    public static final String ACT_EPOCH_GET = "com.qebas.kbdriver.EPOCH_GET";
    public static final String ACT_EPOCH_BUMP = "com.qebas.kbdriver.EPOCH_BUMP";
    public static final String ACT_CLICK_PATH = "com.qebas.kbdriver.CLICK_PATH";
    public static final String ACT_GLOBAL = "com.qebas.kbdriver.GLOBAL";
    public static final String ACT_LAUNCH = "com.qebas.kbdriver.LAUNCH";
    public static final String ACT_GESTURE = "com.qebas.kbdriver.GESTURE";
    public static final String ACT_SCREENSHOT = "com.qebas.kbdriver.SCREENSHOT";
    public static final String ACT_SETTING_PUT = "com.qebas.kbdriver.SETTING_PUT";
    public static final String ACT_SETTING_GET = "com.qebas.kbdriver.SETTING_GET";
    public static final String ACT_SET_TOKEN = "com.qebas.kbdriver.SET_TOKEN";
    public static final String ACT_SEND_VERIFIED = "com.qebas.kbdriver.SEND_VERIFIED";
    public static final String ACT_QUIET_COPY = "com.qebas.kbdriver.QUIET_COPY";
    public static final String ACT_FIND_ANCHOR = "com.qebas.kbdriver.FIND_ANCHOR";
    // v5.0 (Aragon review + Claude FIX-1106): SEND_ARMED is the
    // second half of the split send - set_and_verify (SET_TEXT with
    // its journal entry) and send_armed are separate acts, and every
    // send posts a write-ahead ARMED marker before it may click.
    public static final String ACT_SEND_ARMED = "com.qebas.kbdriver.SEND_ARMED";
    private static final String RESULT_URL = "http://127.0.0.1:8773/result";
    private static final String NEXT_URL = "http://127.0.0.1:8773/next";
    private static final String ARMED_URL = "http://127.0.0.1:8773/armed";
    private static final String PROGRESS_URL = "http://127.0.0.1:8773/progress";

    // v4.5 (Kimi evaluation): per-install auth token persisted in the
    // app's private files; actuating verbs must carry the token, the
    // CURRENT epoch (absence now refuses - v4.4 treated a missing
    // epoch as a pass), and a strictly increasing sequence number.
    private volatile String authToken = null;
    private volatile long lastSeq = 0;
    private volatile long lastTouchMs = 0;
    private volatile int rootNullStreak = 0;
    // v5.0: my own dispatchGesture taps can fire
    // TOUCH_INTERACTION_START on some builds; touches within this
    // window of a self gesture are masked so the driver cannot
    // revoke or abort itself (Claude FIX-1106 Q4 caveat).
    private volatile long lastSelfGestureMs = 0;
    // v5.0: the sequence high-water mark is PERSISTED (Aragon Q6:
    // an in-memory counter resets when the service process dies).
    // One counter serves the broadcast gate and the channel dedup.
    private volatile long seqHwm = -1;
    private final java.util.Map<Long, String> resultCache =
            java.util.Collections.synchronizedMap(
                    new java.util.LinkedHashMap<Long, String>() {
                        @Override protected boolean removeEldestEntry(
                                java.util.Map.Entry<Long, String> e) {
                            return size() > 64;
                        }
                    });
    private final java.util.concurrent.BlockingQueue<String> outbox =
            new java.util.concurrent.LinkedBlockingQueue<>();
    private final ThreadLocal<Long> cmdSeqTl = new ThreadLocal<>();
    private final java.util.concurrent.ExecutorService chanExec =
            java.util.concurrent.Executors.newSingleThreadExecutor();
    private volatile String currentJob = null;
    private volatile boolean channelRunning = false;
    private volatile long channelLastOkMs = 0;

    private synchronized long seqHwm() {
        if (seqHwm < 0) {
            try {
                java.io.File f = new java.io.File(getFilesDir(), "seqhwm");
                if (f.exists()) {
                    byte[] b = java.nio.file.Files.readAllBytes(f.toPath());
                    seqHwm = Long.parseLong(new String(b,
                            StandardCharsets.UTF_8).trim());
                } else {
                    seqHwm = 0;
                }
            } catch (Exception e) {
                seqHwm = 0;
            }
            lastSeq = seqHwm;
        }
        return seqHwm;
    }

    private synchronized void seqAdvance(long s) {
        if (s > seqHwm()) {
            seqHwm = s;
            lastSeq = s;
            try {
                java.io.FileOutputStream out = new java.io.FileOutputStream(
                        new java.io.File(getFilesDir(), "seqhwm"));
                out.write(Long.toString(s).getBytes(StandardCharsets.UTF_8));
                out.flush();
                out.getFD().sync();
                out.close();
            } catch (Exception ignored) { }
        }
    }

    private void tokenLoad() {
        try {
            java.io.File f = new java.io.File(getFilesDir(), "authtoken");
            if (f.exists()) {
                byte[] b = java.nio.file.Files.readAllBytes(f.toPath());
                String t = new String(b, StandardCharsets.UTF_8).trim();
                if (!t.isEmpty()) authToken = t;
            }
        } catch (Exception ignored) { }
    }

    private void tokenSave(String t) {
        try {
            java.io.File f = new java.io.File(getFilesDir(), "authtoken");
            java.nio.file.Files.write(f.toPath(),
                    t.getBytes(StandardCharsets.UTF_8));
            authToken = t;
        } catch (Exception ignored) { }
    }

    private boolean tokenOk(Intent in) {
        String t = authToken;
        if (t == null) return true;
        return t.equals(in.getStringExtra("t"));
    }

    /** Full gate. Read verbs need the token once one is configured;
     *  actuating verbs additionally need a present, current epoch and
     *  a fresh sequence number. Refusals are reported, never silent. */
    private boolean gate(Intent in, String job, String mode, String target,
                         boolean actuating) {
        if (!tokenOk(in)) {
            report(job, false, mode, target, 0, "", null, "auth");
            return false;
        }
        if (actuating) {
            if (!in.hasExtra("epoch")) {
                report(job, false, mode, target, 0, "", null, "no-epoch");
                return false;
            }
            if (!epochOk(in, job, mode, target)) return false;
            long seq = in.getLongExtra("seq", -1);
            if (seq <= seqHwm()) {
                report(job, false, mode, target, 0, "", null, "replay");
                return false;
            }
            seqAdvance(seq);
        }
        return true;
    }

    private final BroadcastReceiver receiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context ctx, Intent in) {
            final Intent copy = new Intent(in);
            new Thread(() -> handle(copy)).start();
        }
    };

    // --- EPOCH (v4.1): a durable counter fencing every act. The
    // service is the authority: it persists the epoch, bumps it
    // itself on owner touch, and refuses any act whose epoch extra
    // is present and stale. A zombie executor with an old epoch is
    // impotent even while it is still running.
    private volatile long epoch = -1;

    private synchronized long epochGet() {
        if (epoch < 0) {
            try {
                java.io.File f = new java.io.File(getFilesDir(), "epoch");
                if (f.exists()) {
                    java.io.FileInputStream in = new java.io.FileInputStream(f);
                    byte[] b = new byte[24];
                    int n = in.read(b);
                    in.close();
                    epoch = Long.parseLong(new String(b, 0, Math.max(n, 0),
                            StandardCharsets.UTF_8).trim());
                } else {
                    epoch = 0;
                }
            } catch (Exception e) {
                epoch = 0;
            }
        }
        return epoch;
    }

    private synchronized long epochBump(String reason) {
        long e = epochGet() + 1;
        epoch = e;
        try {
            java.io.FileOutputStream out = new java.io.FileOutputStream(
                    new java.io.File(getFilesDir(), "epoch"));
            out.write(Long.toString(e).getBytes(StandardCharsets.UTF_8));
            out.flush();
            out.getFD().sync();
            out.close();
        } catch (Exception ignored) { }
        Log.i(TAG, "epoch bumped to " + e + " (" + reason + ")");
        return e;
    }

    /** True when the intent carries no epoch, or a current one. */
    private boolean epochOk(Intent in, String job, String mode, String target) {
        if (!in.hasExtra("epoch")) return true;
        long want = in.getLongExtra("epoch", -1);
        if (want == epochGet()) return true;
        report(job, false, mode, target, 0, "", null, "stale-epoch");
        return false;
    }

    /** v5.0.9 (step 4 phase 3): the settings fence. Only the keys
     *  the driver itself legitimately owns may be read or written
     *  through the SETTING verbs - the accessibility list it joins
     *  and leaves, its master switch, and its own probe keys. The
     *  WRITE path runs on the one-time WRITE_SECURE_SETTINGS grant
     *  (development protection level, pm grant), never on Shizuku. */
    private boolean settingKeyAllowed(String k) {
        return k != null && (k.equals("enabled_accessibility_services")
                || k.equals("accessibility_enabled")
                || k.startsWith("kb_driver_"));
    }

    /** v5.0.3 (step 4 phase 2): foreground an app from inside the
     *  service - getLaunchIntentForPackage + NEW_TASK - replacing the
     *  daemon's monkey-via-rish launches, so foregrounding no longer
     *  needs the shell bridge at all. */
    private void launchApp(String job, String target, String lp) {
        try {
            Intent li = getPackageManager().getLaunchIntentForPackage(lp);
            if (li == null) {
                report(job, false, "launch", target, 0, "", null,
                        "no-launch-intent");
                return;
            }
            li.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
            startActivity(li);
            report(job, true, "launch", target, 0, "", null, null);
        } catch (Exception e) {
            report(job, false, "launch", target, 0, "", null, "exc:" + e);
        }
    }

    /** v5.0.5 (step 4 phase 2): the screen through the service -
     *  AccessibilityService.takeScreenshot (API 30+) instead of the
     *  daemon's rish screencap. The PNG travels back base64 in the
     *  result's text field; secure windows fail typed, never silent. */
    private void takeShot(final String job, final String target) {
        try {
            java.util.concurrent.Executor exec = r -> new Thread(r).start();
            takeScreenshot(android.view.Display.DEFAULT_DISPLAY, exec,
                    new TakeScreenshotCallback() {
                        @Override
                        public void onSuccess(ScreenshotResult res) {
                            try {
                                android.hardware.HardwareBuffer hb =
                                        res.getHardwareBuffer();
                                android.graphics.Bitmap bmp =
                                        android.graphics.Bitmap.wrapHardwareBuffer(
                                                hb, res.getColorSpace());
                                android.graphics.Bitmap copy = bmp.copy(
                                        android.graphics.Bitmap.Config.ARGB_8888,
                                        false);
                                bmp.recycle();
                                hb.close();
                                java.io.ByteArrayOutputStream bos =
                                        new java.io.ByteArrayOutputStream();
                                copy.compress(
                                        android.graphics.Bitmap.CompressFormat.PNG,
                                        100, bos);
                                copy.recycle();
                                byte[] raw = bos.toByteArray();
                                String b64 = Base64.encodeToString(
                                        raw, Base64.NO_WRAP);
                                // NOT report(): jsonStr caps strings
                                // at 20000 chars (a text-era guard)
                                // and would silently truncate the
                                // image. Base64's alphabet is
                                // JSON-safe, so it is concatenated
                                // raw - the cap stays for all text.
                                String body = "{\"job\":" + jsonStr(job)
                                        + ",\"ok\":true,\"mode\":\"screenshot\""
                                        + ",\"pkg\":" + jsonStr(target)
                                        + ",\"chars\":" + raw.length
                                        + ",\"sha256\":\"\""
                                        + ",\"text\":\"" + b64 + "\"}";
                                Log.i(TAG, "result ok=true mode=screenshot pkg="
                                        + target + " chars=" + raw.length);
                                post(body);
                            } catch (Exception e) {
                                report(job, false, "screenshot", target, 0,
                                        "", null, "encode:" + e);
                            }
                        }

                        @Override
                        public void onFailure(int errorCode) {
                            report(job, false, "screenshot", target, 0, "",
                                    null, "shot-failed:" + errorCode);
                        }
                    });
        } catch (Exception e) {
            report(job, false, "screenshot", target, 0, "", null, "exc:" + e);
        }
    }

    private void epochReport(String job, long value) {
        try {
            post("{\"job\":" + jsonStr(job) + ",\"ok\":true,\"mode\":\"epoch\""
                    + ",\"epoch\":" + value + "}");
        } catch (Exception ignored) { }
    }

    private void handle(Intent in) {
        String action = in.getAction();
        String target = in.getStringExtra("pkg");
        String job = in.getStringExtra("job");
        if (ACT_SET_TOKEN.equals(action)) {
            String t = in.getStringExtra("t");
            if (t == null || t.isEmpty()) {
                report(job, false, "set_token", target, 0, "", null, "no-token");
                return;
            }
            if (authToken == null || authToken.equals(t)) {
                tokenSave(t);
                report(job, true, "set_token", target, 0, "", null, null);
            } else {
                report(job, false, "set_token", target, 0, "", null, "auth");
            }
            return;
        }
        if (ACT_EPOCH_GET.equals(action)) {
            if (!tokenOk(in)) {
                report(job, false, "epoch", target, 0, "", null, "auth");
                return;
            }
            epochReport(job, epochGet());
            return;
        }
        if (ACT_EPOCH_BUMP.equals(action)) {
            // A bump changes state: full gate, but the epoch extra is
            // meaningless for the bump itself, so check token + seq
            // by hand rather than via gate().
            if (!tokenOk(in)) {
                report(job, false, "epoch", target, 0, "", null, "auth");
                return;
            }
            long bseq = in.getLongExtra("seq", -1);
            if (bseq > 0) seqAdvance(bseq);
            String reason = in.getStringExtra("reason");
            epochReport(job, epochBump(reason == null ? "bump" : reason));
            return;
        }
        if (ACT_GLOBAL.equals(action)) {
            if (!gate(in, job, "global", target, true)) return;
            String which = in.getStringExtra("which");
            int ga = "home".equals(which)
                    ? GLOBAL_ACTION_HOME : GLOBAL_ACTION_BACK;
            boolean ok = performGlobalAction(ga);
            report(job, ok, "global", target, 0, "", null,
                    ok ? null : "global-failed");
            return;
        }
        if (ACT_LAUNCH.equals(action)) {
            if (!gate(in, job, "launch", target, true)) return;
            String lp = in.getStringExtra("launch");
            launchApp(job, target, lp == null ? target : lp);
            return;
        }
        if (ACT_GESTURE.equals(action)) {
            if (!gate(in, job, "gesture", target, true)) return;
            int x = (int) in.getLongExtra("x", -1);
            int y = (int) in.getLongExtra("y", -1);
            long dur = in.getLongExtra("dur", 80);
            if (x < 0 || y < 0) {
                report(job, false, "gesture", target, 0, "", null, "no-coords");
                return;
            }
            boolean ok = tapAtDur(x, y, (int) Math.max(30, Math.min(dur, 1500)));
            report(job, ok, "gesture", target, 0, "", null,
                    ok ? null : "gesture-failed");
            return;
        }
        if (ACT_SCREENSHOT.equals(action)) {
            if (!gate(in, job, "screenshot", target, true)) return;
            takeShot(job, target);
            return;
        }
        if (ACT_SETTING_GET.equals(action)) {
            if (!gate(in, job, "setting_get", target, false)) return;
            String key = in.getStringExtra("key");
            if (!settingKeyAllowed(key)) {
                report(job, false, "setting_get", target, 0, "", null,
                        "key-not-allowed");
                return;
            }
            try {
                String v = android.provider.Settings.Secure.getString(
                        getContentResolver(), key);
                report(job, true, "setting_get", target,
                        v == null ? 0 : v.length(), "", v, null);
            } catch (Exception e) {
                report(job, false, "setting_get", target, 0, "", null,
                        "exc:" + e);
            }
            return;
        }
        if (ACT_SETTING_PUT.equals(action)) {
            if (!gate(in, job, "setting_put", target, true)) return;
            String key = in.getStringExtra("key");
            if (!settingKeyAllowed(key)) {
                report(job, false, "setting_put", target, 0, "", null,
                        "key-not-allowed");
                return;
            }
            String v = null;
            if (!in.hasExtra("delete")) {
                String b64 = in.getStringExtra("value_b64");
                v = b64 == null ? "" : new String(
                        Base64.decode(b64, Base64.DEFAULT),
                        StandardCharsets.UTF_8);
            }
            try {
                boolean ok = android.provider.Settings.Secure.putString(
                        getContentResolver(), key, v);
                report(job, ok, "setting_put", target,
                        v == null ? 0 : v.length(), "", null,
                        ok ? null : "put-false");
            } catch (Exception e) {
                report(job, false, "setting_put", target, 0, "", null,
                        "exc:" + e);
            }
            return;
        }
        if (ACT_CLICK_PATH.equals(action)) {
            if (!gate(in, job, "click_path", target, true)) return;
            String path = in.getStringExtra("path");
            String expect = in.getStringExtra("expect");
            clickPath(job, target, path == null ? "" : path,
                    expect == null ? "" : expect);
            return;
        }
        if (ACT_SCROLL.equals(action)) {
            if (!gate(in, job, "scroll", target, true)) return;
            String dir = in.getStringExtra("dir");
            int px = (int) in.getLongExtra("px", 600);
            scroll(job, target, "down".equals(dir), Math.max(200, Math.min(px, 1200)));
            return;
        }
        if (ACT_STATUS.equals(action)) {
            if (!gate(in, job, "status", target, false)) return;
            status(job);
            return;
        }
        if (ACT_WAIT.equals(action)) {
            if (!gate(in, job, "wait_quiet", target, false)) return;
            long quiet = in.getLongExtra("quiet_ms", 2000);
            long max = in.getLongExtra("max_ms", 90000);
            waitQuiet(job, target, quiet, max);
            return;
        }
        if (ACT_WAIT_TAP.equals(action)) {
            if (!gate(in, job, "wait_tap", target, true)) return;
            String desc = in.getStringExtra("desc");
            long max = in.getLongExtra("max_ms", 60000);
            armWatch(job, target, desc == null ? "" : desc, max);
            return;
        }
        if (ACT_DIGEST.equals(action)) {
            if (!gate(in, job, "digest", target, false)) return;
            long since = in.getLongExtra("since", -1);
            long wait = in.getLongExtra("wait_ms", 0);
            digest(job, since, wait);
            return;
        }
        if (ACT_SEND_VERIFIED.equals(action)) {
            if (!gate(in, job, "send_verified", target, true)) return;
            sendVerified(job, target, in);
            return;
        }
        if (ACT_SEND_ARMED.equals(action)) {
            if (!gate(in, job, "send_armed", target, true)) return;
            sendArmed(job, target, in);
            return;
        }
        if (ACT_QUIET_COPY.equals(action)) {
            if (!gate(in, job, "quiet_copy", target, true)) return;
            quietCopy(job, target, in);
            return;
        }
        if (ACT_FIND_ANCHOR.equals(action)) {
            if (!gate(in, job, "find_anchor", target, false)) return;
            findAnchor(job, target, in);
            return;
        }
        AccessibilityNodeInfo node;
        if (ACT_CLICK.equals(action)) {
            if (!gate(in, job, "click_node", target, true)) return;
            String desc = in.getStringExtra("desc");
            node = findByDesc(target, desc == null ? "" : desc);
            if (node == null) {
                report(job, false, "click_node", target, 0, "", null, "no-node");
                return;
            }
            boolean ok = node.performAction(AccessibilityNodeInfo.ACTION_CLICK);
            String via = "action";
            if (!ok) {
                // Compose action rows often expose no clickable node:
                // tap the node's screen bounds with a real gesture.
                Rect r = new Rect();
                node.getBoundsInScreen(r);
                ok = tapAt((r.left + r.right) / 2, (r.top + r.bottom) / 2);
                via = "gesture";
            }
            report(job, ok, "click_node", target, 0, "", null, ok ? null : "click-failed-" + via);
            return;
        }
        if (!gate(in, job, modeOf(action), target, !ACT_GET.equals(action))) return;
        node = findTargetNode(target);
        if (node == null) {
            report(job, false, modeOf(action), target, 0, "", null, "no-node");
            return;
        }
        try {
            if (ACT_GET.equals(action)) {
                // Read-after-write lag: a node snapshot can hold
                // the pre-set text briefly after SET_TEXT. Re-find
                // and re-read until two reads agree (<= ~1 s).
                String s = textOf(node);
                for (int i = 0; i < 5; i++) {
                    try { Thread.sleep(200); } catch (Exception e) { }
                    AccessibilityNodeInfo n2 = findTargetNode(target);
                    if (n2 == null) break;
                    String s2 = textOf(n2);
                    if (s2.equals(s)) break;
                    s = s2;
                }
                report(job, true, "get_text", target, s.length(), sha256(s), s, null);
            } else if (ACT_PASTE.equals(action)) {
                boolean ok = node.performAction(AccessibilityNodeInfo.ACTION_PASTE);
                String s = textOf(node);
                report(job, ok, "paste", target, s.length(), sha256(s), null, null);
            } else {
                String b64 = in.getStringExtra("b64");
                String payload = ACT_CLEAR.equals(action) ? "" :
                        (b64 == null ? "" : new String(
                                Base64.decode(b64, Base64.DEFAULT), StandardCharsets.UTF_8));
                Bundle args = new Bundle();
                args.putCharSequence(
                        AccessibilityNodeInfo.ACTION_ARGUMENT_SET_TEXT_CHARSEQUENCE, payload);
                boolean ok = node.performAction(AccessibilityNodeInfo.ACTION_SET_TEXT, args);
                report(job, ok, ACT_CLEAR.equals(action) ? "clear" : "set_text",
                        target, payload.length(), sha256(payload), null, null);
            }
        } catch (Exception e) {
            report(job, false, modeOf(action), target, 0, "", null, "exc:" + e);
        }
    }

    /** v4.5 composite: SET_TEXT + read-back hash verify + Send click
     *  in ONE trip (Kimi Q4). The verify discipline is unchanged -
     *  the field is cleared and the verb refuses on mismatch - it
     *  just runs where the hands are, without two broadcast round
     *  trips of dead air between typing and sending. */
    private void sendVerified(String job, String target, Intent in) {
        // v5.0 (Aragon Q3/Q5 + Claude FIX-1106 Q1/Q4): two owner-
        // touch checkpoints (before set, before the click) - after
        // the ARMED marker, never abort. A verify mismatch no longer
        // clears the field: if the owner is typing in the same
        // composer, the field may hold his words, not ours. And the
        // click is preceded by the synchronous ARMED write-ahead
        // marker; without it, no click may fire.
        long touch0 = lastTouchMs;
        String b64 = in.getStringExtra("b64");
        String payload = b64 == null ? "" : new String(
                Base64.decode(b64, Base64.DEFAULT), StandardCharsets.UTF_8);
        AccessibilityNodeInfo node = findTargetNode(target);
        if (node == null) {
            report(job, false, "send_verified", target, 0, "", null, "no-node");
            return;
        }
        if (lastTouchMs > touch0) {
            String cur0 = textOf(node);
            report(job, false, "send_verified", target, cur0.length(),
                    sha256(cur0), null, "aborted-touch");
            return;
        }
        try {
            Bundle args = new Bundle();
            args.putCharSequence(
                    AccessibilityNodeInfo.ACTION_ARGUMENT_SET_TEXT_CHARSEQUENCE,
                    payload);
            boolean okSet = node.performAction(
                    AccessibilityNodeInfo.ACTION_SET_TEXT, args);
            // The node just acted on is a stale snapshot: re-find
            // the field and poll briefly for the app to apply.
            String back = "";
            for (int i = 0; i < 10; i++) {
                AccessibilityNodeInfo n2 = findTargetNode(target);
                if (n2 != null) {
                    back = textOf(n2);
                }
                if (sha256(back).equals(sha256(payload))) break;
                try { Thread.sleep(100); }
                catch (InterruptedException e) { break; }
            }
            if (!okSet || !sha256(back).equals(sha256(payload))) {
                // v5.0.2 diagnostics (KB-A/KB-K consult step 1): on a
                // verify mismatch, capture WHY before reporting: a
                // delayed re-read (async race?), the first differing
                // index + slices (normalization?), the read lengths
                // (truncation at a fixed ceiling?), and whether a
                // canonicalized comparison (NFC, CRLF->LF, trailing
                // whitespace stripped) would have matched.
                String back300 = back;
                try { Thread.sleep(300); }
                catch (InterruptedException e) { }
                AccessibilityNodeInfo n3 = findTargetNode(target);
                if (n3 != null) back300 = textOf(n3);
                int fd = firstDiff(payload, back);
                String diag = "set_ok=" + okSet
                        + " sent_len=" + payload.length()
                        + " read_len=" + back.length()
                        + " read_len_300=" + back300.length()
                        + " first_diff=" + fd
                        + " sent_at=" + sliceEsc(payload, fd)
                        + " read_at=" + sliceEsc(back, fd)
                        + " canon_match=" + sha256(canon(payload))
                                .equals(sha256(canon(back)));
                Log.i(TAG, "verify-diag " + diag);
                report(job, false, "send_verified", target, back.length(),
                        sha256(back), diag, "verify-mismatch");
                return;
            }
            if (lastTouchMs > touch0) {
                report(job, false, "send_verified", target, back.length(),
                        sha256(back), null, "aborted-touch");
                return;
            }
            AccessibilityNodeInfo send = findByDesc(target, "Send");
            if (send == null) {
                report(job, false, "send_verified", target, payload.length(),
                        sha256(back), null, "no-send-control");
                return;
            }
            if (!postArmed(job, in.getLongExtra("seq", -1), sha256(payload))) {
                report(job, false, "send_verified", target, payload.length(),
                        sha256(back), null, "armed-post-failed");
                return;
            }
            boolean ok = send.performAction(AccessibilityNodeInfo.ACTION_CLICK);
            if (!ok) {
                Rect r = new Rect();
                send.getBoundsInScreen(r);
                ok = tapAt((r.left + r.right) / 2, (r.top + r.bottom) / 2);
            }
            report(job, ok, "send_verified", target, payload.length(),
                    sha256(back), null, ok ? null : "click-failed");
        } catch (Exception e) {
            report(job, false, "send_verified", target, 0, "", null, "exc:" + e);
        }
    }

    /** v5.0: the second half of the split send (Claude FIX-1106
     *  Q1/Q2). The composer must already hold exactly the expected
     *  text - set there by a separately journalled set_text - and
     *  the click is preceded by the ARMED write-ahead marker and
     *  guarded by the owner-touch checkpoint. Recovery can then
     *  judge a dangling send_armed from composer + transcript
     *  evidence instead of guessing. */
    private void sendArmed(String job, String target, Intent in) {
        long touch0 = lastTouchMs;
        String b64 = in.getStringExtra("b64");
        String payload = b64 == null ? "" : new String(
                Base64.decode(b64, Base64.DEFAULT), StandardCharsets.UTF_8);
        AccessibilityNodeInfo node = findTargetNode(target);
        if (node == null) {
            report(job, false, "send_armed", target, 0, "", null, "no-node");
            return;
        }
        String back = textOf(node);
        if (!sha256(back).equals(sha256(payload))) {
            report(job, false, "send_armed", target, back.length(),
                    sha256(back), null, "not-armed-text-mismatch");
            return;
        }
        if (lastTouchMs > touch0) {
            report(job, false, "send_armed", target, back.length(),
                    sha256(back), null, "aborted-touch");
            return;
        }
        AccessibilityNodeInfo send = findByDesc(target, "Send");
        if (send == null) {
            report(job, false, "send_armed", target, payload.length(),
                    sha256(back), null, "no-send-control");
            return;
        }
        if (!postArmed(job, in.getLongExtra("seq", -1), sha256(payload))) {
            report(job, false, "send_armed", target, payload.length(),
                    sha256(back), null, "armed-post-failed");
            return;
        }
        try {
            boolean ok = send.performAction(AccessibilityNodeInfo.ACTION_CLICK);
            if (!ok) {
                Rect r = new Rect();
                send.getBoundsInScreen(r);
                ok = tapAt((r.left + r.right) / 2, (r.top + r.bottom) / 2);
            }
            report(job, ok, "send_armed", target, payload.length(),
                    sha256(back), null, ok ? null : "click-failed");
        } catch (Exception e) {
            report(job, false, "send_armed", target, 0, "", null, "exc:" + e);
        }
    }

    /** v4.5 composite: structural settle + Copy click in one trip,
     *  with sent-message anchoring (Kimi Q3): when anchor_bottom is
     *  given, only a Copy control BELOW the owner's sent message is
     *  eligible - the stale-copy failure of 2026-11-05 (the previous
     *  reply's control sat above the new question) is unrepresentable
     *  in this shape. The matched label is returned in text. */
    private void quietCopy(String job, String target, Intent in) {
        long quiet = in.getLongExtra("quiet_ms", 2000);
        long max = in.getLongExtra("max_ms", 120000);
        String descs = in.getStringExtra("descs");
        long anchorBottom = in.getLongExtra("anchor_bottom", -1);
        long start = System.currentTimeMillis();
        long lastProgress = start;
        String lastBody = null;
        long lastChange = start;
        boolean settled = false;
        while (System.currentTimeMillis() - start < max) {
            AccessibilityNodeInfo root = rootOf(target);
            String[] stats = root == null
                    ? new String[]{"", ""} : bodyStats(root);
            String sig = stats[1].isEmpty() ? stats[0] : null;
            if (sig == null) {
                lastChange = System.currentTimeMillis();
                lastBody = null;
            } else if (!sig.equals(lastBody)) {
                lastBody = sig;
                lastChange = System.currentTimeMillis();
            } else if (System.currentTimeMillis() - lastChange >= quiet) {
                settled = true;
                break;
            }
            try { Thread.sleep(400); } catch (InterruptedException e) { return; }
            if (System.currentTimeMillis() - lastProgress >= 5000) {
                lastProgress = System.currentTimeMillis();
                postProgress(job, "settle");
            }
        }
        if (!settled) {
            report(job, false, "quiet_copy", target, 0, "", null, "timeout");
            return;
        }
        String[] list = (descs == null || descs.isEmpty())
                ? new String[]{"Copy message"} : descs.split(",");
        // Anchored search (v4.5.2): the reply's Copy row can sit
        // below the fold for long answers - the app leaves the view
        // at the reply's start, so the row is not even in the tree
        // until the list scrolls. The anchor is re-located by TEXT
        // each round (its recorded bounds go stale the moment the
        // list moves): while the anchor is visible, only a control
        // below it is eligible; once we have scrolled and the
        // anchor has left the top of the tree, any visible control
        // belongs to my reply or later content. The daemon's
        // marker/changed-hash validation remains the backstop.
        String anchorText = "";
        String ab64 = in.getStringExtra("anchor_b64");
        if (ab64 != null) {
            try {
                anchorText = new String(Base64.decode(ab64,
                        Base64.DEFAULT), StandardCharsets.UTF_8);
            } catch (Exception ignored) { }
        }
        long searchDeadline = System.currentTimeMillis() + 25000;
        int scrolls = 0;
        while (true) {
            AccessibilityNodeInfo root = rootOf(target);
            AccessibilityNodeInfo anchorNow = (root == null
                    || anchorText.isEmpty()) ? null
                    : searchText(root, anchorText);
            long anchorNowBottom = -1;
            if (anchorNow != null) {
                Rect ar = new Rect();
                anchorNow.getBoundsInScreen(ar);
                anchorNowBottom = ar.bottom;
            }
            for (String d : list) {
                d = d.trim();
                if (d.isEmpty()) continue;
                AccessibilityNodeInfo node = findByDesc(target, d);
                if (node == null) continue;
                Rect r = new Rect();
                node.getBoundsInScreen(r);
                if (anchorNow != null) {
                    if (r.top < anchorNowBottom - 4) continue;
                } else if (scrolls == 0 && anchorBottom >= 0) {
                    if (r.top < anchorBottom - 4) continue;
                }
                boolean ok = node.performAction(
                        AccessibilityNodeInfo.ACTION_CLICK);
                if (!ok) ok = tapAt((r.left + r.right) / 2,
                        (r.top + r.bottom) / 2);
                if (ok) {
                    report(job, true, "quiet_copy", target, 0, "", d, null);
                    return;
                }
            }
            if (System.currentTimeMillis() - lastProgress >= 5000) {
                lastProgress = System.currentTimeMillis();
                postProgress(job, "search");
            }
            if (System.currentTimeMillis() >= searchDeadline) break;
            if (scrolls < 6) {
                swipeDownInternal(target, 900);
                scrolls++;
            }
            try { Thread.sleep(600); } catch (InterruptedException e) { break; }
        }
        report(job, false, "quiet_copy", target, 0, "", null, "no-copy-control");
    }

    /** v4.5: locate the owner's own sent message in the active
     *  window (exact text match, or 40-char prefix for long texts)
     *  and return its screen bounds - the anchor for quietCopy. */
    private void findAnchor(String job, String target, Intent in) {
        String b64 = in.getStringExtra("b64");
        String want = b64 == null ? "" : new String(
                Base64.decode(b64, Base64.DEFAULT), StandardCharsets.UTF_8);
        AccessibilityNodeInfo root = rootOf(target);
        AccessibilityNodeInfo hit = (root == null || want.isEmpty())
                ? null : searchText(root, want);
        try {
            StringBuilder j = new StringBuilder();
            j.append("{\"job\":").append(jsonStr(job));
            j.append(",\"ok\":").append(hit != null);
            j.append(",\"mode\":\"find_anchor\",\"pkg\":").append(jsonStr(target));
            if (hit != null) {
                Rect r = new Rect();
                hit.getBoundsInScreen(r);
                j.append(",\"top\":").append(r.top);
                j.append(",\"bottom\":").append(r.bottom);
            }
            j.append("}");
            post(j.toString());
        } catch (Exception ignored) { }
    }

    private AccessibilityNodeInfo searchText(AccessibilityNodeInfo n, String want) {
        if (n == null) return null;
        // v5.0.10: never anchor on an editable node. The composer holds
        // the just-typed draft, whose text equals the payload; matching
        // it anchors extraction on the composer instead of the posted
        // bubble (CHFLAP-1107, confirmed 2026-11-07).
        if (!n.isEditable()) {
            String t = textOf(n);
            if (t != null && (t.equals(want) || (want.length() > 40
                    && t.startsWith(want.substring(0, 40))))) return n;
        }
        for (int i = 0; i < n.getChildCount(); i++) {
            AccessibilityNodeInfo h = searchText(n.getChild(i), want);
            if (h != null) return h;
        }
        return null;
    }

    private void status(String job) {
        String fg = "";
        AccessibilityNodeInfo root = getRootInActiveWindow();
        if (root != null && root.getPackageName() != null) {
            fg = root.getPackageName().toString();
        }
        AccessibilityNodeInfo node = fg.isEmpty() ? null : findTargetNode(fg);
        String s = node == null ? "" : textOf(node);
        try {
            StringBuilder j = new StringBuilder();
            j.append("{\"job\":").append(jsonStr(job)).append(",\"ok\":true");
            j.append(",\"mode\":\"status\",\"pkg\":").append(jsonStr(fg));
            j.append(",\"focused\":").append(node != null);
            j.append(",\"chars\":").append(s.length());
            j.append(",\"auth_set\":").append(authToken != null);
            j.append(",\"last_touch_ms\":").append(lastTouchMs);
            j.append(",\"ev_count\":").append(eventCount);
            j.append(",\"root_null_streak\":").append(rootNullStreak);
            boolean ime = false;
            try {
                for (android.view.accessibility.AccessibilityWindowInfo w
                        : getWindows()) {
                    if (w.getType() == android.view.accessibility
                            .AccessibilityWindowInfo.TYPE_INPUT_METHOD) {
                        ime = true;
                        break;
                    }
                }
            } catch (Exception ignored) { }
            j.append(",\"ime_present\":").append(ime);
            j.append(",\"channel_ok\":").append(channelLastOkMs > 0
                    && System.currentTimeMillis() - channelLastOkMs < 30000);
            j.append(",\"seq_hwm\":").append(seqHwm());
            j.append(",\"sha256\":").append(jsonStr(sha256(s))).append("}");
            post(j.toString());
        } catch (Exception ignored) { }
        Log.i(TAG, "status fg=" + fg + " focused=" + (node != null));
    }

    private void waitQuiet(String job, String target, long quietMs, long maxMs) {
        // Quiet = the longest text node (the reply body) unchanged AND
        // no Stop control present. Small volatile nodes (timers,
        // cursors, animated indicators) must not block the settle:
        // the v3.1 whole-tree signature churned for the full 90 s.
        long start = System.currentTimeMillis();
        String lastBody = null;
        long lastChange = start;
        while (System.currentTimeMillis() - start < maxMs) {
            AccessibilityNodeInfo root = rootOf(target);
            String[] stats = root == null ? new String[]{"", ""} : bodyStats(root);
            String sig = stats[1].isEmpty() ? stats[0] : null;
            if (sig == null) {
                lastChange = System.currentTimeMillis();
                lastBody = null;
            } else if (!sig.equals(lastBody)) {
                lastBody = sig;
                lastChange = System.currentTimeMillis();
            } else if (System.currentTimeMillis() - lastChange >= quietMs) {
                report(job, true, "wait_quiet", target, 0, "", null, null);
                return;
            }
            try { Thread.sleep(400); } catch (InterruptedException e) { return; }
        }
        report(job, false, "wait_quiet", target, 0, "", null, "timeout");
    }

    /** {longestText, stopFlag} over the whole tree. */
    private String[] bodyStats(AccessibilityNodeInfo root) {
        StringBuilder longest = new StringBuilder();
        boolean[] stop = new boolean[1];
        scanBody(root, longest, stop, 0);
        return new String[]{longest.toString(), stop[0] ? "stop" : ""};
    }

    private void scanBody(AccessibilityNodeInfo n, StringBuilder longest,
                          boolean[] stop, int depth) {
        if (n == null || depth > 40) return;
        CharSequence t = n.getText();
        if (t != null && t.length() > longest.length()) {
            longest.setLength(0);
            longest.append(t);
        }
        CharSequence d = n.getContentDescription();
        if (d != null && d.toString().toLowerCase().contains("stop")) stop[0] = true;
        for (int i = 0; i < n.getChildCount(); i++) scanBody(n.getChild(i), longest, stop, depth + 1);
    }

    private AccessibilityNodeInfo rootOf(String pkg) {
        AccessibilityNodeInfo active = getRootInActiveWindow();
        if (active != null && (pkg == null || pkg.contentEquals(active.getPackageName()))) {
            return active;
        }
        List<AccessibilityWindowInfo> wins = getWindows();
        if (wins != null) {
            AccessibilityNodeInfo fallback = null;
            for (AccessibilityWindowInfo w : wins) {
                AccessibilityNodeInfo root = w.getRoot();
                if (root == null) continue;
                if (pkg != null && !pkg.contentEquals(root.getPackageName())) continue;
                if (w.isActive() || w.isFocused()) return root;
                if (fallback == null) fallback = root;
            }
            if (fallback != null) return fallback;
        }
        return active;
    }

    private AccessibilityNodeInfo findByDesc(String pkg, String desc) {
        List<AccessibilityNodeInfo> hits = new ArrayList<>();
        AccessibilityNodeInfo root = rootOf(pkg);
        if (root != null) collectByDesc(root, desc.toLowerCase(), hits);
        List<AccessibilityWindowInfo> wins = getWindows();
        if (wins != null) {
            for (AccessibilityWindowInfo w : wins) {
                AccessibilityNodeInfo r = w.getRoot();
                if (r == null || r == root) continue;
                if (pkg != null && !pkg.contentEquals(r.getPackageName())) continue;
                collectByDesc(r, desc.toLowerCase(), hits);
            }
        }
        AccessibilityNodeInfo best = null;
        int bestY = -1;
        Rect r = new Rect();
        for (AccessibilityNodeInfo n : hits) {
            n.getBoundsInScreen(r);
            if (r.top > bestY) { bestY = r.top; best = n; }
        }
        return best;
    }

    private void collectByDesc(AccessibilityNodeInfo n, String desc,
                               List<AccessibilityNodeInfo> hits) {
        if (n == null) return;
        CharSequence d = n.getContentDescription();
        if (d != null && d.toString().toLowerCase().contains(desc)) hits.add(n);
        for (int i = 0; i < n.getChildCount(); i++) collectByDesc(n.getChild(i), desc, hits);
    }

    private boolean tapAt(int x, int y) {
        return tapAtDur(x, y, 60);
    }

    private boolean tapAtDur(int x, int y, int durMs) {
        android.graphics.Path p = new android.graphics.Path();
        p.moveTo(x, y);
        GestureDescription g = new GestureDescription.Builder()
                .addStroke(new GestureDescription.StrokeDescription(p, 0, durMs))
                .build();
        final java.util.concurrent.CountDownLatch latch =
                new java.util.concurrent.CountDownLatch(1);
        final boolean[] completed = new boolean[1];
        lastSelfGestureMs = System.currentTimeMillis();
        boolean dispatched = dispatchGesture(g, new GestureResultCallback() {
            @Override
            public void onCompleted(GestureDescription gestureDescription) {
                completed[0] = true;
                latch.countDown();
            }

            @Override
            public void onCancelled(GestureDescription gestureDescription) {
                latch.countDown();
            }
        }, null);
        if (!dispatched) return false;
        try {
            latch.await(2, java.util.concurrent.TimeUnit.SECONDS);
        } catch (InterruptedException e) {
            return false;
        }
        return completed[0];
    }

    // --- WAIT_TAP: an armed one-shot watcher. Accessibility events
    // fire the moment a window's content changes, so the tap lands
    // within a fraction of a second of the choice appearing - no
    // polling loop, and nothing crosses the tunnel per choice.
    private volatile String watchJob;
    private volatile String watchPkg;
    private volatile String watchDesc;
    private volatile long watchDeadline;
    private volatile boolean watchFired;

    private void armWatch(String job, String pkg, String desc, long maxMs) {
        watchJob = job;
        watchPkg = pkg;
        watchDesc = desc.toLowerCase();
        watchDeadline = System.currentTimeMillis() + maxMs;
        watchFired = false;
        Log.i(TAG, "watch armed desc=" + desc + " pkg=" + pkg);
        new Thread(() -> {
            while (!watchFired && System.currentTimeMillis() < watchDeadline) {
                tryWatch();
                try { Thread.sleep(400); } catch (InterruptedException e) { return; }
            }
            if (!watchFired) {
                watchFired = true;
                report(watchJob, false, "wait_tap", watchPkg, 0, "", null, "timeout");
            }
        }).start();
        tryWatch();
    }

    private synchronized void tryWatch() {
        if (watchFired || watchJob == null) return;
        if (System.currentTimeMillis() > watchDeadline) return;
        AccessibilityNodeInfo node = findByDescOrText(watchPkg, watchDesc);
        if (node == null) return;
        watchFired = true;
        boolean ok = node.performAction(AccessibilityNodeInfo.ACTION_CLICK);
        if (!ok) {
            Rect r = new Rect();
            node.getBoundsInScreen(r);
            ok = tapAt((r.left + r.right) / 2, (r.top + r.bottom) / 2);
        }
        report(watchJob, ok, "wait_tap", watchPkg, 0, "", null,
                ok ? null : "tap-failed");
    }

    /** Match on content-description OR visible text (dialogs use text). */
    private AccessibilityNodeInfo findByDescOrText(String pkg, String needle) {
        AccessibilityNodeInfo byDesc = findByDesc(pkg, needle);
        if (byDesc != null) return byDesc;
        AccessibilityNodeInfo root = rootOf(pkg);
        if (root == null) return null;
        List<AccessibilityNodeInfo> hits = new ArrayList<>();
        collectByText(root, needle, hits);
        AccessibilityNodeInfo best = null;
        int bestY = -1;
        Rect r = new Rect();
        for (AccessibilityNodeInfo n : hits) {
            n.getBoundsInScreen(r);
            if (r.top > bestY) { bestY = r.top; best = n; }
        }
        return best;
    }

    private void collectByText(AccessibilityNodeInfo n, String needle,
                               List<AccessibilityNodeInfo> hits) {
        if (n == null) return;
        CharSequence t = n.getText();
        if (t != null && t.toString().toLowerCase().contains(needle)) hits.add(n);
        for (int i = 0; i < n.getChildCount(); i++) collectByText(n.getChild(i), needle, hits);
    }

    // --- UI DIGEST (v4.0): an event-maintained model of the active
    // window, served in one call. Accessibility events mark the
    // model dirty; a ticker rebuilds it at most every ~200 ms; the
    // sequence number advances only when the content hash changes,
    // so "changed since N" is a content statement, not a clock one.
    private volatile long modelSeq = 0;
    private volatile String modelJson = null;
    private volatile String modelHash = "";
    private volatile boolean modelDirty = true;
    private volatile long lastRefresh = 0;
    private volatile String diagJson = "{}";
    private volatile int lastEventType = -1;
    private volatile long eventCount = 0;
    private volatile long refreshCount = 0;

    private AccessibilityNodeInfo rootOfDiag(StringBuilder dg) {
        AccessibilityNodeInfo active = null;
        try {
            active = getRootInActiveWindow();
        } catch (Exception e) {
            dg.append("\"activeEx\":").append(jsonStr(e.toString())).append(",");
        }
        dg.append("\"activeNull\":").append(active == null).append(",");
        if (active != null) return active;
        List<AccessibilityWindowInfo> wins = null;
        try {
            wins = getWindows();
        } catch (Exception e) {
            dg.append("\"winsEx\":").append(jsonStr(e.toString())).append(",");
        }
        dg.append("\"winCount\":").append(wins == null ? -1 : wins.size()).append(",");
        if (wins != null) {
            StringBuilder wl = new StringBuilder("[");
            AccessibilityNodeInfo fallback = null;
            int shown = 0;
            for (AccessibilityWindowInfo w : wins) {
                AccessibilityNodeInfo root = null;
                String rex = "";
                try {
                    root = w.getRoot();
                } catch (Exception e) {
                    rex = e.toString();
                }
                if (shown < 8) {
                    if (shown > 0) wl.append(",");
                    wl.append("[").append(w.getType()).append(",")
                      .append(root == null).append(",")
                      .append(w.isActive()).append(",")
                      .append(w.isFocused()).append(",")
                      .append(jsonStr(rex)).append("]");
                    shown++;
                }
                if (root == null) continue;
                if (w.isActive() || w.isFocused()) { dg.append("\"wins\":").append(wl).append("]"); return root; }
                if (fallback == null) fallback = root;
            }
            dg.append("\"wins\":").append(wl).append("]");
            return fallback;
        }
        return null;
    }

    private void refreshModel() {
        lastRefresh = System.currentTimeMillis();
        modelDirty = false;
        refreshCount++;
        StringBuilder dg = new StringBuilder("{");
        AccessibilityNodeInfo root = null;
        try {
            root = rootOfDiag(dg);
        } catch (Exception e) {
            dg.append("\"rootEx\":").append(jsonStr(e.toString())).append(",");
        }
        dg.append("\"evType\":").append(lastEventType)
          .append(",\"evCount\":").append(eventCount)
          .append(",\"refresh\":").append(refreshCount).append("}");
        diagJson = dg.toString();
        if (root == null) { rootNullStreak++; return; }
        rootNullStreak = 0;
        String pkg = root.getPackageName() == null ? "" : root.getPackageName().toString();
        StringBuilder nodes = new StringBuilder();
        int[] count = new int[1];
        collectDigest(root, "0", nodes, count);
        String body = "{\"pkg\":" + jsonStr(pkg) + ",\"nodes\":[" + nodes + "]}";
        String h = sha256(body);
        if (!h.equals(modelHash)) {
            modelHash = h;
            modelJson = body;
            modelSeq++;
        }
    }

    private void collectDigest(AccessibilityNodeInfo n, String path,
                               StringBuilder out, int[] count) {
        if (n == null || count[0] >= 160) return;
        if (count[0] > 0) out.append(",");
        count[0]++;
        Rect r = new Rect();
        n.getBoundsInScreen(r);
        String cls = n.getClassName() == null ? "" : n.getClassName().toString();
        int dot = cls.lastIndexOf('.');
        if (dot >= 0) cls = cls.substring(dot + 1);
        StringBuilder flags = new StringBuilder();
        if (n.isClickable()) flags.append("c");
        if (n.isEditable()) flags.append("e");
        if (n.isFocused()) flags.append("f");
        if (n.isScrollable()) flags.append("s");
        if (n.isEnabled()) flags.append("n");
        boolean pw = n.isPassword();
        if (pw) flags.append("p");
        // Password content never leaves the device in a digest.
        String txt = pw ? "" : trunc(textOf(n));
        String dsc = pw ? "" : trunc(n.getContentDescription() == null
                ? "" : n.getContentDescription().toString());
        out.append("[").append(jsonStr(path)).append(",").append(jsonStr(cls))
           .append(",").append(jsonStr(txt))
           .append(",").append(jsonStr(dsc))
           .append(",").append(jsonStr(flags.toString()))
           .append(",").append(r.left).append(",").append(r.top)
           .append(",").append(r.right).append(",").append(r.bottom).append("]");
        for (int i = 0; i < n.getChildCount(); i++) {
            collectDigest(n.getChild(i), path + "." + i, out, count);
        }
    }

    private static String trunc(String s) {
        if (s == null) return "";
        return s.length() > 60 ? s.substring(0, 60) : s;
    }

    private void digest(String job, long since, long waitMs) {
        if (modelJson == null) refreshModel();
        long deadline = System.currentTimeMillis() + Math.min(Math.max(waitMs, 0), 120000);
        while (true) {
            long seq = modelSeq;
            boolean changed = seq != since;
            if (since < 0 || changed || System.currentTimeMillis() >= deadline) {
                try {
                    StringBuilder j = new StringBuilder();
                    j.append("{\"job\":").append(jsonStr(job)).append(",\"ok\":true");
                    j.append(",\"mode\":\"digest\",\"seq\":").append(seq);
                    j.append(",\"changed\":").append(changed);
                    j.append(",\"hash\":").append(jsonStr(modelHash));
                    j.append(",\"diag\":").append(diagJson);
                    j.append(",\"digest\":").append(modelJson == null ? "null" : modelJson);
                    j.append("}");
                    post(j.toString());
                } catch (Exception ignored) { }
                Log.i(TAG, "digest served seq=" + seq + " changed=" + changed);
                return;
            }
            try { Thread.sleep(150); } catch (InterruptedException e) { return; }
        }
    }

    /** Tap the node at a digest index path (v4.2, ASK primitive).
     * The node's live label must still contain the expected text,
     * so a moved or recycled node is refused, never tapped blind. */
    private void clickPath(String job, String pkg, String path, String expect) {
        AccessibilityNodeInfo root = rootOf(pkg);
        AccessibilityNodeInfo node = resolvePath(root, path);
        if (node == null) {
            report(job, false, "click_path", pkg, 0, "", null, "no-node");
            return;
        }
        String hay = (textOf(node) + " "
                + (node.getContentDescription() == null ? ""
                   : node.getContentDescription().toString())).toLowerCase();
        if (!expect.isEmpty() && !hay.contains(expect.toLowerCase())) {
            report(job, false, "click_path", pkg, 0, "", null, "target-moved");
            return;
        }
        boolean ok = node.performAction(AccessibilityNodeInfo.ACTION_CLICK);
        if (!ok) {
            Rect r = new Rect();
            node.getBoundsInScreen(r);
            ok = tapAt((r.left + r.right) / 2, (r.top + r.bottom) / 2);
        }
        report(job, ok, "click_path", pkg, 0, "", null, ok ? null : "tap-failed");
    }

    private AccessibilityNodeInfo resolvePath(AccessibilityNodeInfo root,
                                              String path) {
        if (root == null || path == null || path.isEmpty()) return null;
        String[] parts = path.split("\\.");
        AccessibilityNodeInfo cur = root;
        for (int i = 1; i < parts.length; i++) {
            int idx;
            try {
                idx = Integer.parseInt(parts[i]);
            } catch (Exception e) {
                return null;
            }
            if (cur == null || idx < 0 || idx >= cur.getChildCount()) return null;
            cur = cur.getChild(idx);
        }
        return cur;
    }

    /** Bounded swipe via dispatchGesture (v4.1, plan primitive). */
    private void scroll(String job, String target, boolean down, int px) {
        AccessibilityNodeInfo root = rootOf(target);
        Rect r = new Rect();
        if (root != null) root.getBoundsInScreen(r);
        int x = r.isEmpty() ? 360 : (r.left + r.right) / 2;
        int cy = r.isEmpty() ? 780 : (r.top + r.bottom) / 2;
        int half = px / 2;
        int y0 = down ? cy + half : cy - half;
        int y1 = down ? cy - half : cy + half;
        android.graphics.Path p = new android.graphics.Path();
        p.moveTo(x, y0);
        p.lineTo(x, y1);
        GestureDescription g = new GestureDescription.Builder()
                .addStroke(new GestureDescription.StrokeDescription(p, 0, 250))
                .build();
        final java.util.concurrent.CountDownLatch latch =
                new java.util.concurrent.CountDownLatch(1);
        final boolean[] completed = new boolean[1];
        lastSelfGestureMs = System.currentTimeMillis();
        boolean dispatched = dispatchGesture(g, new GestureResultCallback() {
            @Override
            public void onCompleted(GestureDescription gd) {
                completed[0] = true;
                latch.countDown();
            }

            @Override
            public void onCancelled(GestureDescription gd) {
                latch.countDown();
            }
        }, null);
        boolean ok = false;
        if (dispatched) {
            try {
                latch.await(2, java.util.concurrent.TimeUnit.SECONDS);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            ok = completed[0];
        }
        report(job, ok, "scroll", target, px, "", null, ok ? null : "scroll-failed");
    }

    /** Gesture swipe without a result post (quietCopy's internal
     *  scroll). Same mechanics as the SCROLL verb. */
    private void swipeDownInternal(String target, int px) {
        AccessibilityNodeInfo root = rootOf(target);
        Rect r = new Rect();
        if (root != null) root.getBoundsInScreen(r);
        int x = r.isEmpty() ? 360 : (r.left + r.right) / 2;
        int cy = r.isEmpty() ? 780 : (r.top + r.bottom) / 2;
        int half = px / 2;
        android.graphics.Path p = new android.graphics.Path();
        p.moveTo(x, cy + half);
        p.lineTo(x, cy - half);
        GestureDescription g = new GestureDescription.Builder()
                .addStroke(new GestureDescription.StrokeDescription(p, 0, 250))
                .build();
        final java.util.concurrent.CountDownLatch latch =
                new java.util.concurrent.CountDownLatch(1);
        lastSelfGestureMs = System.currentTimeMillis();
        boolean dispatched = dispatchGesture(g, new GestureResultCallback() {
            @Override
            public void onCompleted(GestureDescription gd) {
                latch.countDown();
            }

            @Override
            public void onCancelled(GestureDescription gd) {
                latch.countDown();
            }
        }, null);
        if (dispatched) {
            try {
                latch.await(2, java.util.concurrent.TimeUnit.SECONDS);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
    }

    private String textOf(AccessibilityNodeInfo node) {
        CharSequence cur = node.getText();
        return cur == null ? "" : cur.toString();
    }

    // v5.0.2 verify diagnostics helpers (ASCII-only source).
    private static int firstDiff(String a, String b) {
        int n = Math.min(a.length(), b.length());
        for (int i = 0; i < n; i++) {
            if (a.charAt(i) != b.charAt(i)) return i;
        }
        return a.length() == b.length() ? -1 : n;
    }

    private static String canon(String s) {
        String t = java.text.Normalizer.normalize(s,
                java.text.Normalizer.Form.NFC);
        t = t.replace("\r\n", "\n").replace('\r', '\n');
        int end = t.length();
        while (end > 0) {
            char c = t.charAt(end - 1);
            if (c == ' ' || c == '\n' || c == '\t') end--;
            else break;
        }
        return t.substring(0, end);
    }

    private static String sliceEsc(String s, int from) {
        if (from < 0) from = 0;
        if (from > s.length()) from = s.length();
        int to = Math.min(s.length(), from + 24);
        StringBuilder sb = new StringBuilder("[");
        for (int i = from; i < to; i++) {
            char c = s.charAt(i);
            if (c == '\n') sb.append("<LF>");
            else if (c == '\r') sb.append("<CR>");
            else if (c == '\t') sb.append("<TAB>");
            else if (c < 0x20 || c == 0x7f) sb.append('?');
            else sb.append(c);
        }
        return sb.append(']').toString();
    }

    private String modeOf(String action) {
        if (ACT_GET.equals(action)) return "get_text";
        if (ACT_PASTE.equals(action)) return "paste";
        if (ACT_CLEAR.equals(action)) return "clear";
        return "set_text";
    }

    private void report(String job, boolean ok, String mode, String pkg, int chars,
                        String sha, String text, String reason) {
        Log.i(TAG, "result ok=" + ok + " mode=" + mode + " pkg=" + pkg
                + " chars=" + chars + (reason == null ? "" : " reason=" + reason));
        try {
            StringBuilder j = new StringBuilder();
            j.append("{");
            j.append("\"job\":").append(jsonStr(job)).append(",");
            j.append("\"ok\":").append(ok).append(",");
            j.append("\"mode\":").append(jsonStr(mode)).append(",");
            j.append("\"pkg\":").append(jsonStr(pkg)).append(",");
            j.append("\"chars\":").append(chars).append(",");
            j.append("\"sha256\":").append(jsonStr(sha));
            if (text != null) j.append(",\"text\":").append(jsonStr(text));
            if (reason != null) j.append(",\"reason\":").append(jsonStr(reason));
            j.append("}");
            post(j.toString());
        } catch (Exception ignored) { }
    }

    private String stamp(String bodyStr) {
        // v4.5: once a token is configured, every post carries it
        // (body stamp + header) so the daemon can refuse forgeries.
        String tok = authToken;
        if (tok != null && bodyStr.startsWith("{")) {
            return "{\"t\":" + jsonStr(tok) + "," + bodyStr.substring(1);
        }
        return bodyStr;
    }

    /** v5.0: results go through an outbox with retries (Claude
     *  FIX-1106 Q2: a dropped connection must not take a result
     *  with it). post() never blocks the verb thread; the poster
     *  retries for up to 30 s. For channel commands the stamped
     *  body is also cached by seq for duplicate re-delivery. */
    private void post(String bodyStr) {
        String stamped = stamp(bodyStr);
        Long s = cmdSeqTl.get();
        if (s != null) resultCache.put(s, stamped);
        outbox.offer(stamped);
    }

    private void postRaw(String url, String bodyStr) throws Exception {
        byte[] body = bodyStr.getBytes(StandardCharsets.UTF_8);
        HttpURLConnection c = (HttpURLConnection) new URL(url).openConnection();
        c.setRequestMethod("POST");
        c.setConnectTimeout(3000);
        c.setReadTimeout(3000);
        c.setDoOutput(true);
        c.setRequestProperty("Content-Type", "application/json");
        String tok = authToken;
        if (tok != null) c.setRequestProperty("X-KB-Token", tok);
        OutputStream os = c.getOutputStream();
        os.write(body);
        os.close();
        int code = c.getResponseCode();
        c.disconnect();
        if (code != 200) throw new Exception("http " + code);
    }

    private void posterLoop() {
        while (true) {
            String body;
            try {
                body = outbox.take();
            } catch (InterruptedException e) {
                return;
            }
            long deadline = System.currentTimeMillis() + 30000;
            int delay = 400;
            while (true) {
                try {
                    postRaw(RESULT_URL, body);
                    break;
                } catch (Exception e) {
                    if (System.currentTimeMillis() > deadline) {
                        Log.w(TAG, "result post gave up after 30 s");
                        break;
                    }
                    try {
                        Thread.sleep(delay);
                    } catch (InterruptedException ie) {
                        return;
                    }
                    delay = Math.min(delay * 2, 3000);
                }
            }
        }
    }

    /** Synchronous post with a hard timeout - used ONLY for the
     *  ARMED write-ahead marker, which must be known to have landed
     *  before the Send click may fire (Claude FIX-1106 Q1). */
    private boolean postSync(String url, String bodyStr, int timeoutMs) {
        String stamped = stamp(bodyStr);
        for (int i = 0; i < 2; i++) {
            try {
                byte[] body = stamped.getBytes(StandardCharsets.UTF_8);
                HttpURLConnection c = (HttpURLConnection) new URL(url).openConnection();
                c.setRequestMethod("POST");
                c.setConnectTimeout(timeoutMs);
                c.setReadTimeout(timeoutMs);
                c.setDoOutput(true);
                c.setRequestProperty("Content-Type", "application/json");
                String tok = authToken;
                if (tok != null) c.setRequestProperty("X-KB-Token", tok);
                OutputStream os = c.getOutputStream();
                os.write(body);
                os.close();
                int code = c.getResponseCode();
                c.disconnect();
                if (code == 200) return true;
            } catch (Exception ignored) { }
        }
        return false;
    }

    private void postFire(String url, String bodyStr) {
        final String stamped = stamp(bodyStr);
        new Thread(() -> {
            try { postRaw(url, stamped); } catch (Exception ignored) { }
        }).start();
    }

    private boolean postArmed(String job, long seq, String hash) {
        String body = "{\"job\":" + jsonStr(job) + ",\"seq\":" + seq
                + ",\"text_hash\":" + jsonStr(hash) + "}";
        return postSync(ARMED_URL, body, 2000);
    }

    private void postProgress(String job, String phase) {
        if (job == null) return;
        postFire(PROGRESS_URL, "{\"job\":" + jsonStr(job)
                + ",\"phase\":" + jsonStr(phase) + "}");
    }

    // --- v5.0 persistent channel (Aragon Q6 / Claude FIX-1106 Q2):
    // the service long-polls the daemon for commands instead of the
    // daemon spawning `am` per command (~1.6 s of process spawn
    // each). Commands carry the same extras a broadcast would; the
    // same handle() runs them; results return via the /result
    // outbox. Delivery is at-least-once; the persisted seq
    // high-water plus the result cache make actuation
    // effectively-once. Broadcast remains for bootstrap, wake-up
    // and fallback under the same gates.
    private void channelLoop() {
        channelRunning = true;
        int backoff = 500;
        while (channelRunning) {
            String tok = authToken;
            if (tok == null) {
                try { Thread.sleep(1000); }
                catch (InterruptedException e) { return; }
                continue;
            }
            HttpURLConnection c = null;
            try {
                c = (HttpURLConnection) new URL(
                        NEXT_URL + "?after=" + seqHwm()).openConnection();
                c.setRequestMethod("GET");
                c.setConnectTimeout(5000);
                c.setReadTimeout(40000);
                c.setRequestProperty("X-KB-Token", tok);
                int code = c.getResponseCode();
                if (code == 200) {
                    java.io.InputStream is = c.getInputStream();
                    java.io.ByteArrayOutputStream bos =
                            new java.io.ByteArrayOutputStream();
                    byte[] buf = new byte[8192];
                    int n;
                    while ((n = is.read(buf)) > 0) bos.write(buf, 0, n);
                    String body = bos.toString("UTF-8");
                    channelLastOkMs = System.currentTimeMillis();
                    backoff = 500;
                    handleChannelCommand(body);
                } else if (code == 204) {
                    channelLastOkMs = System.currentTimeMillis();
                    backoff = 500;
                } else {
                    try { Thread.sleep(backoff); }
                    catch (InterruptedException e) { return; }
                    backoff = Math.min(backoff * 2, 5000);
                }
            } catch (Exception e) {
                try { Thread.sleep(backoff); }
                catch (InterruptedException ie) { return; }
                backoff = Math.min(backoff * 2, 5000);
            } finally {
                if (c != null) c.disconnect();
            }
        }
    }

    private void handleChannelCommand(String body) {
        final String job;
        final Intent in;
        final long cmdSeq;
        try {
            org.json.JSONObject o = new org.json.JSONObject(body);
            job = o.optString("job");
            in = new Intent(o.optString("action"));
            org.json.JSONObject f = o.optJSONObject("fields");
            long s = -1;
            if (f != null) {
                java.util.Iterator<String> keys = f.keys();
                while (keys.hasNext()) {
                    String k = keys.next();
                    Object v = f.get(k);
                    if (v instanceof Number) {
                        in.putExtra(k, ((Number) v).longValue());
                        if ("seq".equals(k)) s = ((Number) v).longValue();
                    } else if (v instanceof Boolean) {
                        in.putExtra(k, ((Boolean) v).booleanValue());
                    } else {
                        in.putExtra(k, String.valueOf(v));
                    }
                }
            }
            cmdSeq = s;
        } catch (Exception e) {
            Log.w(TAG, "channel command parse failed: " + e);
            return;
        }
        if (cmdSeq > 0 && cmdSeq <= seqHwm()) {
            String cached = resultCache.get(cmdSeq);
            if (cached != null) {
                outbox.offer(cached);
            } else {
                post("{\"job\":" + jsonStr(job)
                        + ",\"ok\":false,\"mode\":\"dup\""
                        + ",\"reason\":\"duplicate-no-cache\"}");
            }
            return;
        }
        chanExec.execute(() -> {
            if (cmdSeq > 0) cmdSeqTl.set(cmdSeq);
            currentJob = job;
            try {
                handle(in);
            } finally {
                if (cmdSeq > 0) seqAdvance(cmdSeq);
                cmdSeqTl.remove();
            }
        });
    }

    private static String jsonStr(String s) {
        if (s == null) return "null";
        StringBuilder b = new StringBuilder("\"");
        for (int i = 0; i < s.length() && i < 20000; i++) {
            char ch = s.charAt(i);
            switch (ch) {
                case '"': b.append("\\\""); break;
                case '\\': b.append("\\\\"); break;
                case '\n': b.append("\\n"); break;
                case '\r': b.append("\\r"); break;
                case '\t': b.append("\\t"); break;
                default:
                    if (ch < 0x20) b.append(String.format("\\u%04x", (int) ch));
                    else b.append(ch);
            }
        }
        return b.append("\"").toString();
    }

    private static String sha256(String s) {
        try {
            MessageDigest d = MessageDigest.getInstance("SHA-256");
            byte[] h = d.digest(s.getBytes(StandardCharsets.UTF_8));
            StringBuilder b = new StringBuilder();
            for (byte x : h) b.append(String.format("%02x", x));
            return b.toString();
        } catch (Exception e) {
            return "";
        }
    }

    private AccessibilityNodeInfo findTargetNode(String pkg) {
        List<AccessibilityWindowInfo> wins = getWindows();
        if (wins != null) {
            for (AccessibilityWindowInfo w : wins) {
                AccessibilityNodeInfo root = w.getRoot();
                if (root == null) continue;
                if (pkg != null && !pkg.contentEquals(root.getPackageName())) continue;
                AccessibilityNodeInfo n = findEditable(root);
                if (n != null) return n;
            }
        }
        AccessibilityNodeInfo root = getRootInActiveWindow();
        if (root != null && (pkg == null || pkg.contentEquals(root.getPackageName()))) {
            return findEditable(root);
        }
        return null;
    }

    private AccessibilityNodeInfo findEditable(AccessibilityNodeInfo root) {
        AccessibilityNodeInfo focused = root.findFocus(AccessibilityNodeInfo.FOCUS_INPUT);
        if (focused != null && focused.isEditable()) return focused;
        return traverse(root);
    }

    private AccessibilityNodeInfo traverse(AccessibilityNodeInfo n) {
        if (n == null) return null;
        if (n.isEditable() && n.isFocused()) return n;
        for (int i = 0; i < n.getChildCount(); i++) {
            AccessibilityNodeInfo r = traverse(n.getChild(i));
            if (r != null) return r;
        }
        return null;
    }

    @Override
    protected void onServiceConnected() {
        IntentFilter f = new IntentFilter();
        f.addAction(ACT_SET);
        f.addAction(ACT_CLEAR);
        f.addAction(ACT_PASTE);
        f.addAction(ACT_GET);
        f.addAction(ACT_STATUS);
        f.addAction(ACT_CLICK);
        f.addAction(ACT_WAIT);
        f.addAction(ACT_WAIT_TAP);
        f.addAction(ACT_DIGEST);
        f.addAction(ACT_SCROLL);
        f.addAction(ACT_EPOCH_GET);
        f.addAction(ACT_EPOCH_BUMP);
        f.addAction(ACT_CLICK_PATH);
        f.addAction(ACT_GLOBAL);
        f.addAction(ACT_LAUNCH);
        f.addAction(ACT_GESTURE);
        f.addAction(ACT_SCREENSHOT);
        f.addAction(ACT_SETTING_PUT);
        f.addAction(ACT_SETTING_GET);
        f.addAction(ACT_SET_TOKEN);
        f.addAction(ACT_SEND_VERIFIED);
        f.addAction(ACT_SEND_ARMED);
        f.addAction(ACT_QUIET_COPY);
        f.addAction(ACT_FIND_ANCHOR);
        registerReceiver(receiver, f, Context.RECEIVER_EXPORTED);
        tokenLoad();
        Log.i(TAG, "service connected v5.0 epoch=" + epochGet());
        new Thread(this::posterLoop).start();
        new Thread(this::channelLoop).start();
        new Thread(() -> {
            while (true) {
                try { Thread.sleep(200); } catch (InterruptedException e) { return; }
                if (modelDirty
                        && System.currentTimeMillis() - lastRefresh >= 150) {
                    try { refreshModel(); } catch (Exception ignored) { }
                }
            }
        }).start();
    }

    @Override
    public void onAccessibilityEvent(AccessibilityEvent event) {
        modelDirty = true;
        lastEventType = event.getEventType();
        eventCount++;
        if (event.getEventType()
                == AccessibilityEvent.TYPE_TOUCH_INTERACTION_START
                && System.currentTimeMillis() - lastSelfGestureMs >= 800) {
            // The owner's finger outranks every plan: revoke the
            // current epoch at the actuator itself. Touches within
            // 800 ms of a self-injected gesture are masked - they
            // are the gesture's own echo on some builds, and the
            // driver must not revoke itself (FIX-1106 Q4 caveat).
            lastTouchMs = System.currentTimeMillis();
            epochBump("owner-touch");
        }
        if (watchJob != null && !watchFired) tryWatch();
    }

    @Override
    public void onInterrupt() { }

    @Override
    public void onDestroy() {
        channelRunning = false;
        try { chanExec.shutdownNow(); } catch (Exception ignored) { }
        try { unregisterReceiver(receiver); } catch (Exception ignored) { }
        super.onDestroy();
    }
}
