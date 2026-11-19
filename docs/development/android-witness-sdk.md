# Kotlin witness SDK for Android

The Kotlin SDK runs Noctium host-control plans and generates and verifies proofs on Android through the shared Rust runtime. The Android archive links one arm64-v8a native library and needs no Node process. Use a worker thread for witness execution and local proving.

## Build and import

Install Rust 1.100.0, JDK 21, Kotlin, CMake, Android SDK Platform 35 and the Android NDK. Set `ANDROID_SDK_ROOT` and `ANDROID_NDK_HOME` to their installation directories. Put `cargo`, `kotlinc`, `python3` and `zip` on your path.

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

## Prove a completed witness

Use `NativeWitness.open` for a ledger entrypoint. Provide the native target descriptor with the bundle directory's canonical path, the independently pinned manifest digest, the entrypoint and ledger parameters. Provide the exact bundled control plan, the initial state, the matching SRS bytes and the begin envelope containing the inputs and host context. [Target and proof descriptors](../../runtime/include/noctium_native.h)

```kotlin
import org.noctium.sdk.NativeWitness

NativeWitness.open(targetDescriptor, initialState, srs, controlPlan, beginEnvelope).use { invocation ->
    runCallbacksUntilCompleted(invocation.session)
    invocation.prepareProof(proofDescriptor).use { proof ->
        val publicIntent = proof.proveLocally()
    }
}
```

The application supplies `runCallbacksUntilCompleted`. Successful preparation consumes the target and witness. Proving retains the private preimage in the native runtime and returns the verified public intent projection.

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

Pass a fourth argument to `package-smoke.sh` to include the authenticated proof case. Point it at a directory containing `bundle/` for the scalar typed-witness claim, the matching K7 parameters in `srs`, and its pinned descriptor in `target.json`. The APK copies the bundle into app-private storage and supplies `bundleDirectory`.

The proof APK passed on the arm64 AOSP Android 35 emulator with Rust 1.100.0, NDK r30, Kotlin 1.9.24 and Temurin 21. It completed five typed callbacks, read a staged value, rejected a crossed reply, and generated and verified a K7 proof after producing result 14. It rejected an altered control plan and an incomplete witness. The tested arm64 AAR measured 7,343,061 bytes. Android funding, signing, submission, durable private-state commit and physical-device execution remain open. [Android instrumentation test](../../sdk/android/tests/WitnessSmoke.kt)
