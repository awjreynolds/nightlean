# Kotlin witness SDK for Android

The Kotlin SDK runs Noctium host-control plans on Android through the existing Rust runtime. The Android archive links one arm64-v8a native library and needs no Node process. Use a worker thread for witness execution.

## Build and import

Install Rust 1.100.0, JDK 21, Kotlin, CMake and the Android NDK. Set `ANDROID_NDK_HOME` to the installed NDK and put `cargo`, `kotlinc`, `python3` and `zip` on your path.

```sh
rustup target add --toolchain 1.100.0 aarch64-linux-android
bash sdk/android/package.sh build/noctium-android.aar
```

Add the AAR to your Android application and link the Kotlin standard library. The archive targets API 24 and newer on arm64 and includes the keep rules for its JNI entrypoints. The build uses the locked ZKIR 3.2.1 Rust runtime and aligns native ELF segments to 16 KiB. [Android NDK build guide](https://developer.android.com/ndk/guides/other_build_systems) · [Android page-size requirements](https://developer.android.com/guide/practices/page-sizes)

## Run a witness

Compile your `noctium_control` declaration with `--emit control`. Pass the emitted plan, invocation inputs and host capability registrations in the Control ABI's UTF-8 begin envelope.

```kotlin
import org.noctium.sdk.WitnessSession

WitnessSession.open(beginEnvelope).use { session ->
    val step = session.advance()
    // Inspect the private host step and dispatch any registered callback.
}
```

On `need_host`, retrieve the separate private request with `privateRequest()`. Pass the exact correlated JSON reply to `resume()` and advance again. Use `typed = false` for a v1 reply. `cancel()` invalidates the pending callback, and `close()` frees the native invocation. `NoctiumFailure.status` carries the native error code. Keep step data, provider arguments and staged writes out of application logs. The app owns the copies it receives as byte arrays. [Control ABI](../../runtime/include/noctium_control.h)

## Run the Android smoke test

Use an arm64 Android emulator. Set `ANDROID_SDK_ROOT` to the SDK with platform 35 and Build Tools 35.0.0, and set `KOTLIN_HOME` to the Kotlin installation. Select your disposable emulator serial with `adb devices`.

```sh
.lake/build/bin/noctium compile tests/WitnessSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit control --output build/android-witness-plans
bash sdk/android/tests/package-smoke.sh build/noctium-android.aar \
  build/android-witness-plans/TypedWitness.scalarHost.control.json build/noctium-witness-smoke.apk
adb -s EMULATOR_SERIAL install build/noctium-witness-smoke.apk
adb -s EMULATOR_SERIAL shell am instrument -w -r org.noctium.sdk.tests/.WitnessSmoke
```

The test passed on the arm64 AOSP Android 35 emulator with Rust 1.100.0, NDK r30, Kotlin 1.9.24 and Temurin 21. The APK returned instrumentation code `-1` after five typed callbacks, a staged private read, rejection of a crossed reply, a result of 14, cancellation and envelope size checks. The tested arm64 AAR measured 2,223,492 bytes. Its three ELF load segments report alignment `0x4000`. Android authenticated proof handoff, transaction submission, durable private-state commit and physical-device execution remain open. [Android instrumentation test](../../sdk/android/tests/WitnessSmoke.kt)
