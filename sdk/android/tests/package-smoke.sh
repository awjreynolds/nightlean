#!/usr/bin/env bash
set -euo pipefail

if (( $# < 3 || $# > 4 )); then
  echo "usage: bash sdk/android/tests/package-smoke.sh AAR HOST_CONTROL_PLAN NEW_APK [PUBLIC_PROOF_FIXTURE]" >&2
  exit 2
fi
sdk="$(cd "$(dirname "$0")" && pwd)"
android="${ANDROID_SDK_ROOT:?Set ANDROID_SDK_ROOT to the installed Android SDK}"
tool="$android/build-tools/35.0.0"
platform="$android/platforms/android-35/android.jar"
output=$3
if [[ -e "$output" || -L "$output" ]]; then
  echo "Android smoke APK destination already exists: $output" >&2
  exit 1
fi
mkdir -p "$(dirname "$output")"
stage="$(mktemp -d "$(dirname "$output")/.noctium-android-smoke.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
mkdir -p "$stage/assets" "$stage/aar" "$stage/native/lib/arm64-v8a" "$stage/dex"
unzip -q "$1" -d "$stage/aar"
cp "$2" "$stage/assets/plan.json"
if (( $# == 4 )); then
  mkdir "$stage/assets/proof"
  cp "$4/target.json" "$4/srs" "$stage/assets/proof/"
  cp -R "$4/bundle" "$stage/assets/proof/bundle"
fi
cp "$stage/aar/jni/arm64-v8a/libnoctium_jni.so" "$stage/native/lib/arm64-v8a/"
cat > "$stage/AndroidManifest.xml" <<'EOF'
<manifest xmlns:android="http://schemas.android.com/apk/res/android" package="org.noctium.sdk.tests">
  <uses-sdk android:minSdkVersion="24" android:targetSdkVersion="35"/>
  <application android:extractNativeLibs="true" android:label="Noctium witness smoke test"/>
  <instrumentation android:name=".WitnessSmoke" android:targetPackage="org.noctium.sdk.tests"/>
</manifest>
EOF
kotlinc "$sdk/WitnessSmoke.kt" -jvm-target 1.8 -classpath "$platform:$stage/aar/classes.jar" \
    -d "$stage/smoke.jar"
"$tool/d8" --min-api 24 --lib "$platform" --output "$stage/dex" \
    "$stage/smoke.jar" "$stage/aar/classes.jar" "${KOTLIN_HOME:?Set KOTLIN_HOME}/lib/kotlin-stdlib.jar"
"$tool/aapt2" link -I "$platform" --manifest "$stage/AndroidManifest.xml" -A "$stage/assets" -o "$stage/smoke.apk"
(cd "$stage/dex" && zip -q ../smoke.apk classes*.dex)
(cd "$stage/native" && zip -q -r ../smoke.apk lib)
"$tool/zipalign" -f 4 "$stage/smoke.apk" "$stage/aligned.apk"
keytool -genkeypair -keystore "$stage/smoke.p12" -storepass changeit -keypass changeit -alias smoke \
    -dname CN=NoctiumTest -keyalg RSA -validity 1 >/dev/null 2>&1
"$tool/apksigner" sign --ks "$stage/smoke.p12" --ks-pass pass:changeit --out "$stage/signed.apk" "$stage/aligned.apk"
ln "$stage/signed.apk" "$output"
