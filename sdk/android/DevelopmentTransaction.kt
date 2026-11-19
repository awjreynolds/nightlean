package org.noctium.sdk

import org.json.JSONObject

/** The authenticated loopback-only development adapter. Omit the seed for recovery. */
class DevelopmentLocalnet(configuration: ByteArray, developmentSeed: ByteArray = byteArrayOf()) : AutoCloseable {
    private var handle = LocalnetBridge.open(configuration, developmentSeed)

    fun context(): ByteArray = withHandle(LocalnetBridge::context)

    /** Reads a host-private value from the development journal. */
    fun privateValue(namespace: String, key: String): ByteArray = withHandle {
        LocalnetBridge.privateValue(it, JSONObject().put("namespace", namespace).put("key", key).bytes())
    }

    @Synchronized
    internal fun <T> withHandle(action: (Long) -> T): T {
        if (handle == 0L) throw NoctiumFailure(2)
        return action(handle)
    }

    @Synchronized
    override fun close() {
        if (handle != 0L) {
            LocalnetBridge.close(handle)
            handle = 0L
        }
    }
}

/** Starts the proof's retained deployment with an explicit empty or staged journal setup. */
fun NativeProof.startDevelopmentDeployment(descriptor: ByteArray, setup: ByteArray): DevelopmentTransaction =
    withHandle { DevelopmentTransaction(LocalnetBridge.startDeployment(it, descriptor, setup)) }

/** Transfers the completed witness and its staged private writes into the proved call. */
fun NativeProof.startDevelopmentCall(descriptor: ByteArray): DevelopmentTransaction =
    withHandle { DevelopmentTransaction(LocalnetBridge.startFromWitness(it, descriptor)) }

/** Drives the shared native transaction state machine. Run these calls on a worker thread. */
class DevelopmentTransaction internal constructor(private var handle: Long) : AutoCloseable {
    enum class Command { PREPARE, SUBMIT, OBSERVE, COMMIT, CANCEL, DEADLINE, RELOAD }

    companion object {
        fun recover(descriptor: ByteArray, context: ByteArray): DevelopmentTransaction =
            DevelopmentTransaction(LocalnetBridge.recover(descriptor, context))
    }

    @Synchronized
    fun send(command: Command): ByteArray =
        LocalnetBridge.command(activeHandle(), command.name.lowercase().toByteArray(Charsets.UTF_8))

    @Synchronized
    fun advance(): ByteArray = LocalnetBridge.advance(activeHandle())

    /** Resolve the current request. Inspect signing requests before explicitly approving them. */
    @Synchronized
    fun resolve(pending: ByteArray, using: DevelopmentLocalnet, approveSigning: Boolean = false): ByteArray =
        respond(pending) { step, metadata ->
            using.withHandle { adapter ->
                val operation = step.getString("operation")
                if (operation == "funding.native.v1" || (operation == "approval.sign.v1" && approveSigning)) {
                    withEntropy { LocalnetBridge.resolve(activeHandle(), adapter, approveSigning, metadata, it) }
                } else {
                    LocalnetBridge.resolve(activeHandle(), adapter, approveSigning, metadata, null)
                }
            }
        }

    @Synchronized
    fun reportServiceFailure(pending: ByteArray): ByteArray = respond(pending) { _, metadata ->
        LocalnetBridge.resolve(activeHandle(), 0, false, metadata, null)
    }

    /** Store these private bytes securely before submit for process recovery. */
    @Synchronized
    fun recoveryContext(): ByteArray = LocalnetBridge.recoveryContext(activeHandle())

    @Synchronized
    fun finalizedState(): ByteArray = LocalnetBridge.finalizedState(activeHandle())

    @Synchronized
    fun sealedTransaction(): ByteArray = LocalnetBridge.sealedTransaction(activeHandle())

    /** Retains the handle if the runtime refuses to detach unresolved work. */
    @Synchronized
    override fun close() {
        if (handle != 0L) {
            LocalnetBridge.detach(handle)
            handle = 0L
        }
    }

    private fun activeHandle(): Long {
        if (handle == 0L) throw NoctiumFailure(2)
        return handle
    }

    private inline fun respond(pending: ByteArray, action: (JSONObject, ByteArray) -> ByteArray): ByteArray {
        val current = advance()
        if (!current.contentEquals(pending)) throw NoctiumFailure(4)
        val step = JSONObject(current.toString(Charsets.UTF_8))
        if (step.getString("status") != "need_host") throw NoctiumFailure(3)
        val correlation = JSONObject()
        for (key in listOf("abiVersion", "requestId", "operation", "capability", "schema", "profile")) {
            correlation.put(key, step.get(key))
        }
        return action(step, correlation.bytes())
    }
}

private fun JSONObject.bytes(): ByteArray = toString().toByteArray(Charsets.UTF_8)

internal object LocalnetBridge {
    init { System.loadLibrary("noctium_jni") }

    external fun open(configuration: ByteArray, seed: ByteArray): Long
    external fun context(adapter: Long): ByteArray
    external fun privateValue(adapter: Long, query: ByteArray): ByteArray
    external fun close(adapter: Long)
    external fun startDeployment(proof: Long, descriptor: ByteArray, setup: ByteArray): Long
    external fun startFromWitness(proof: Long, descriptor: ByteArray): Long
    external fun recover(descriptor: ByteArray, context: ByteArray): Long
    external fun command(transaction: Long, command: ByteArray): ByteArray
    external fun advance(transaction: Long): ByteArray
    external fun resolve(transaction: Long, adapter: Long, approve: Boolean, metadata: ByteArray, entropy: ByteArray?): ByteArray
    external fun recoveryContext(transaction: Long): ByteArray
    external fun finalizedState(transaction: Long): ByteArray
    external fun sealedTransaction(transaction: Long): ByteArray
    external fun detach(transaction: Long)
}
