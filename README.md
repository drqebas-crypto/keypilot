# KB Driver

An Android accessibility-service keyboard driver with a Termux daemon: it sets or
pastes text into the focused field of another app, on command, and reads back what
landed there so a send can be verified instead of assumed.

Two parts, one system:

- `app/` — the Android app (`com.qebas.kbdriver`, KbService 5.0.10). An
  accessibility service that receives broadcast commands (set text, tap, read the
  focused field, take a screenshot) and reports results back over loopback HTTP.
- `daemon/kb_driver.py` — the Python daemon that runs on the phone under Termux.
  It speaks to the service over a loopback HTTP channel (`127.0.0.1:8773`) and
  exposes the send/verify exchange: split a message into parts, arm each send,
  verify the text landed by reading it back, and report an honest verdict
  (verified / staged-unverified / rejected / unknown).

## Security model

- **Per-install token, generated at first run.** The daemon generates a random
  token on first start and stores it in its own private file; the service stores
  its copy in the app's private files. Actuating verbs require the token plus a
  current epoch and a fresh sequence number. No token, key, or credential is
  baked into this source.
- **Loopback only.** The daemon listens on `127.0.0.1:8773` and the service only
  talks to that address. Nothing in this code contacts an external host.
- **No signing key ships with this repo.** `app/build.sh` creates a throwaway
  debug keystore if none exists; the keystore is git-ignored and must never be
  committed. Sign release builds with your own key.
- **Permissions.** The service needs the accessibility service enabled and a
  one-time `pm grant com.qebas.kbdriver android.permission.WRITE_SECURE_SETTINGS`
  (via adb) so it can manage its own accessibility-service membership. It does
  not use Shizuku.

## Build the app

Android SDK with build-tools `34.0.0` and platform `android-34`, then:

```sh
cd app
./build.sh        # aapt2 -> javac -> d8 -> zipalign -> apksigner
```

Produces `app/out/kbdriver.apk`.

## Run the daemon

On the phone, under Termux (the daemon expects the service installed and the
accessibility service enabled):

```sh
python3 kb_driver.py
```

It serves the loopback API on port 8773. See the header comment in
`daemon/kb_driver.py` for the exchange model and the endpoint vocabulary.

## What this is not

This is the driver — the tool — not a product and not a dataset. It contains no
messages, no contacts, no personal data, and no credentials. The staged v2
daemon build (a proposed change set, not the live daemon) is not included here;
the file shipped as `daemon/kb_driver.py` is the live daemon as verified
against the phone on 2026-11-12.
