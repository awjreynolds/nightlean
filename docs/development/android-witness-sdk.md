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

## Fund and submit on the development localnet

Build with `bash sdk/android/package.sh --localnet build/noctium-android-localnet.aar` to include the development adapter. The adapter authenticates the pinned development genesis and accepts a loopback endpoint. Use the native header's configuration, transaction descriptor and deployment setup. Supply a funded public development seed to fund a transaction. [Development stack](../../scripts/localnet/README.md) · [Native client interface](../../runtime/include/noctium_native.h)

```kotlin
import org.noctium.sdk.DevelopmentLocalnet
import org.noctium.sdk.DevelopmentTransaction.Command
import org.noctium.sdk.startDevelopmentCall

DevelopmentLocalnet(configuration, developmentSeed).use { adapter ->
    provedWitness.startDevelopmentCall(clientDescriptor).use { call ->
        drive(call, adapter, call.send(Command.PREPARE))
        storeRecoveryContext(call.recoveryContext())
        drive(call, adapter, call.send(Command.SUBMIT))
        observeUntilFinalized(call, adapter)
        drive(call, adapter, call.send(Command.COMMIT))
    }
}
```

The application supplies the driver, storage and finality loop. The driver passes each pending step to `resolve` and approves signing only after inspecting the request. The call takes ownership of the witness's staged private writes. Persist `recoveryContext()` in app-private storage before submitting. Keep the handle until the runtime acknowledges durable state and accepts `close()`. After a restart, open the same journal with `DevelopmentLocalnet(configuration)` and recover with `DevelopmentTransaction.recover(clientDescriptor, context)`. Remove the funding cache, source and DUST digest fields for this recovery-only adapter. Resolve recovery requests, observe a finalized receipt, then send `COMMIT` to acknowledge the private writes. Keep the recovery bytes and private host values out of logs.

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

For the development transaction test, pass `--localnet` to `package-smoke.sh` and use the localnet AAR. Add `localnet/client.json`, `localnet/localnet.json` and `localnet/params/` to the public proof fixture. The parameter directory contains the pinned DUST files and the K13 SRS selected by the DUST circuit. The test replaces the journal and cache paths with app-private paths.

```sh
adb -s EMULATOR_SERIAL reverse tcp:19944 tcp:19944
adb -s EMULATOR_SERIAL shell am instrument -w -r org.noctium.sdk.tests/.DevelopmentSmoke
```

Use the test's loopback endpoint on port 19944 and run funded tests sharing the same development seed serially. Check for instrumentation code `-1` and the transaction and private recovery result.

The default proof APK passed on the arm64 AOSP Android 35 emulator with Rust 1.100.0, NDK r30, Kotlin 1.9.24 and Temurin 21. It completed five typed callbacks, read a staged value, rejected a crossed reply, and generated and verified a K7 proof after producing result 14. It rejected an altered control plan and an incomplete witness. The default AAR measured 7,343,471 bytes. [Witness instrumentation](../../sdk/android/tests/WitnessSmoke.kt)

The development APK funded and finalized deployment at block 29716 and the witness call at block 29719. It rejected an altered signing request and detach during active work. A fresh client and seedless adapter reopened the on-disk journal and recovered the exact sealed transaction bytes. The 1,482 finalized contract-state bytes match both Swift runs by SHA-256. The private value committed after finality. The development AAR measured 19,772,800 bytes. The original K9 one-time claim and physical Android hardware remain separate qualification work. [Public receipts](android-localnet-receipt.json) · [Transaction instrumentation](../../sdk/android/tests/DevelopmentSmoke.kt)
