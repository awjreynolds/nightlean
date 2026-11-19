package org.noctium.sdk

import java.security.SecureRandom
import org.json.JSONObject

/** Owns an authenticated target and one bound witness session. */
class NativeWitness private constructor(
    private var target: Long,
    val session: WitnessSession,
    private val parameters: ByteArray,
) : AutoCloseable {
    companion object {
        /** Pass the exact control plan bytes held in the authenticated bundle. */
        fun open(
            targetDescriptor: ByteArray, initialState: ByteArray, parameters: ByteArray,
            plan: ByteArray, begin: ByteArray,
        ): NativeWitness {
            val target = withEntropy { Native.targetOpen(targetDescriptor, initialState, parameters, it) }
            try {
                val session = WitnessSession.openBound(target, plan, begin)
                return NativeWitness(target, session, parameters)
            } catch (error: Throwable) {
                Native.targetClose(target)
                throw error
            }
        }
    }

    /** Consumes the completed session and its target on success. */
    @Synchronized
    fun prepareProof(descriptor: ByteArray): NativeProof {
        check(target != 0L) { "Noctium witness target is closed" }
        val proof = session.consume { witness ->
            withEntropy { Native.proofPrepare(target, witness, descriptor, parameters, it) }
        }
        target = 0L
        return NativeProof(proof)
    }

    @Synchronized
    override fun close() {
        session.close()
        if (target != 0L) {
            Native.targetClose(target)
            target = 0L
        }
    }
}

/** A native proof session. Run the synchronous prover on a worker thread. */
class NativeProof internal constructor(private var handle: Long) : AutoCloseable {
    /** Generates and verifies the local proof before returning the public intent projection. */
    @Synchronized
    fun proveLocally(): ByteArray {
        val proof = activeHandle()
        val request = JSONObject(Native.proofAdvance(proof).toString(Charsets.UTF_8))
        check(request.getString("status") == "need_proof") { "Noctium proof is no longer pending" }
        val reply = JSONObject()
        for (key in listOf("abiVersion", "requestId", "operation", "capability", "profile")) {
            reply.put(key, request.get(key))
        }
        val response = withEntropy { Native.proofGenerate(proof, it) }
        return Native.proofAttach(proof, reply.toString().toByteArray(Charsets.UTF_8), response)
    }

    @Synchronized
    fun cancel() = Native.proofCancel(activeHandle())

    @Synchronized
    override fun close() {
        if (handle != 0L) {
            Native.proofClose(handle)
            handle = 0L
        }
    }

    private fun activeHandle(): Long {
        check(handle != 0L) { "Noctium proof session is closed" }
        return handle
    }
}

private val entropySource = SecureRandom()

private inline fun <T> withEntropy(action: (ByteArray) -> T): T {
    val entropy = ByteArray(32)
    try {
        entropySource.nextBytes(entropy)
        return action(entropy)
    } finally {
        entropy.fill(0)
    }
}
