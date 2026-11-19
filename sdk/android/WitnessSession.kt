package org.noctium.sdk

/** A status returned by the native runtime. */
class NoctiumFailure(val status: Int) : IllegalStateException("Noctium status $status")

/** Runs a compiler-emitted host-control plan. Keep all invocation data on your trusted host. */
class WitnessSession private constructor(private var handle: Long) : AutoCloseable {
    companion object {
        /** Takes the Control ABI's UTF-8 JSON envelope with plan, inputs and hostContext. */
        fun open(begin: ByteArray): WitnessSession = WitnessSession(Native.open(begin))
    }

    @Synchronized
    fun advance(): ByteArray = Native.advance(activeHandle())

    /** Pass a canonical correlated reply. Set typed to false for protocol v1. */
    @Synchronized
    fun resume(response: ByteArray, typed: Boolean = true): ByteArray =
        Native.resume(activeHandle(), response, typed)

    /** Returns host-private callback arguments and the staged-write overlay. */
    @Synchronized
    fun privateRequest(): ByteArray = Native.privateRequest(activeHandle())

    @Synchronized
    fun cancel(): ByteArray = Native.cancel(activeHandle())

    @Synchronized
    override fun close() {
        if (handle != 0L) {
            Native.close(handle)
            handle = 0L
        }
    }

    private fun activeHandle(): Long {
        check(handle != 0L) { "Noctium witness session is closed" }
        return handle
    }
}

internal object Native {
    init { System.loadLibrary("noctium_jni") }

    external fun open(begin: ByteArray): Long
    external fun advance(handle: Long): ByteArray
    external fun resume(handle: Long, response: ByteArray, typed: Boolean): ByteArray
    external fun privateRequest(handle: Long): ByteArray
    external fun cancel(handle: Long): ByteArray
    external fun close(handle: Long)
}
