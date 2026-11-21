#!/bin/bash
# Hand-rolled APK build: aapt2 -> javac -> d8 -> zipalign -> apksigner.
set -e
SDK=$HOME/android-sdk
BT=$SDK/build-tools/34.0.0
AJAR=$SDK/platforms/android-34/android.jar
cd "$(dirname "$0")"
rm -rf out && mkdir -p out/classes out/dex
$BT/aapt2 compile --dir res -o out/res.zip
$BT/aapt2 link -o out/base.apk -I "$AJAR" --manifest AndroidManifest.xml out/res.zip
javac -source 11 -target 11 -cp "$AJAR" -d out/classes src/com/qebas/kbdriver/KbService.java
$BT/d8 --lib "$AJAR" --output out/dex $(find out/classes -name '*.class')
cp out/base.apk out/kbdriver-unsigned.apk
cd out/dex && zip -q ../kbdriver-unsigned.apk classes.dex && cd ../..
$BT/zipalign -f 4 out/kbdriver-unsigned.apk out/kbdriver-aligned.apk
[ -f debug.keystore ] || keytool -genkeypair -keystore debug.keystore -storepass android -keypass android -alias kbdebug -keyalg RSA -keysize 2048 -validity 3650 -dname "CN=KB Driver Debug" > /dev/null 2>&1
$BT/apksigner sign --ks debug.keystore --ks-pass pass:android --key-pass pass:android --out out/kbdriver.apk out/kbdriver-aligned.apk
ls -la out/kbdriver.apk
md5sum out/kbdriver.apk
