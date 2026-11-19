package org.noctium.sdk.tests

import android.app.Activity
import android.app.Instrumentation
import android.os.Bundle
import java.io.File
import java.util.UUID
import org.json.JSONObject
import org.noctium.sdk.NoctiumFailure
import org.noctium.sdk.NativeWitness
import org.noctium.sdk.WitnessSession

class WitnessSmoke : Instrumentation() {
    override fun onCreate(arguments: Bundle?) {
        super.onCreate(arguments)
        start()
    }

    override fun onStart() {
        val result = Bundle()
        try {
            val proofPassed = runWitness()
            val proofResult = if (proofPassed) "Noctium Android K7 authenticated witness proof passed\n" else ""
            result.putString("stream", "Noctium Android witness passed\n$proofResult")
            finish(Activity.RESULT_OK, result)
        } catch (error: Exception) {
            val status = (error as? NoctiumFailure)?.let { " status ${it.status}" }.orEmpty()
            result.putString("stream", "Noctium Android witness failed: ${error.javaClass.simpleName} " +
                "${error.stackTrace.firstOrNull()}$status\n")
            finish(Activity.RESULT_CANCELED, result)
        }
    }

    private fun runWitness(): Boolean {
        val plan = targetContext.assets.open("plan.json").bufferedReader().use { JSONObject(it.readText()) }
        val attempt = "b".repeat(64)
        val context = JSONObject("""
            {
              "protocolVersion":1,"namespace":"noctium","baseRevision":"fixture-r0",
              "attemptId":"$attempt",
              "capabilities":[
                {"id":"private","namespace":"noctium","keyPrefix":"cache/",
                 "operations":["private_state.read.v1","private_state.stage.v1","private_state.compare_exchange.v1"]},
                {"id":"lookup","namespace":"noctium","keyPrefix":"lookup/","operations":["noctium.lookup.v1"]}
              ],
              "operations":[
                {"operation":"private_state.read.v1","argumentSchema":{"key":"Key"},"resultSchema":"UIntRange<256>"},
                {"operation":"noctium.lookup.v1","argumentSchema":{"seed":"UIntRange<256>"},"resultSchema":"UIntRange<256>"}
              ],
              "providers":[
                {"input":"cache","operation":"private_state.read.v1","capability":"private","arguments":{"key":"cache/last"}},
                {"input":"lookup","operation":"noctium.lookup.v1","capability":"lookup","arguments":{}}
              ],
              "commitCapability":"private","limits":{"requests":64,"writes":64,"privateBytes":65536}
            }
        """.trimIndent())
        val begin = JSONObject().put("abiVersion", 1)
            .put("inputs", JSONObject().put("expected", "14").put("seed", "7"))
            .put("hostContext", context)
        val sourceBegin = JSONObject(begin.toString()).put("plan", plan).bytes()

        WitnessSession.open(sourceBegin).use { completeWitness(it, attempt) }
        WitnessSession.open(sourceBegin).use { session ->
            check(session.advance().json().getString("status") == "need_host")
            check(session.cancel().json().getString("status") == "cancelled")
            expectStatus(3) { session.privateRequest() }
        }
        expectStatus(5) { WitnessSession.open(ByteArray(1024 * 1024 + 1)).close() }

        val proof = targetContext.assets.list("")?.contains("proof") == true
        if (proof) runProof(begin.bytes(), attempt)
        return proof
    }

    private fun completeWitness(session: WitnessSession, attempt: String) {
        for ((index, name) in listOf("cache", "cache", "lookup", "cache", "lookup").withIndex()) {
            val pending = session.advance()
            val step = pending.json()
            check(step.getString("status") == "need_host")
            val request = step.getJSONObject("request")
            check(request.getString("name") == name && !request.has("invocationWrites"))
            val overlay = session.privateRequest().json().getJSONObject("invocationWrites")
            check(overlay.getJSONObject("cache/last").getString("value") == "1")
            val reply = JSONObject().put("protocolVersion", 2).put("attemptId", attempt)
                .put("outcome", "value").put("value", if (name == "cache") "1" else "14")
            for (key in listOf("requestId", "operation", "capability", "schema")) {
                reply.put(key, request.getString(key))
            }
            if (index == 0) {
                reply.put("attemptId", "c".repeat(64))
                expectStatus(4) { session.resume(reply.bytes()) }
                check(session.advance().contentEquals(pending))
                reply.put("attemptId", attempt)
            }
            check(session.resume(reply.bytes()).json().getString("status") == "ready")
        }
        val finished = session.advance().json()
        check(finished.getString("status") == "completed" && finished.getString("result") == "14")
    }

    private fun runProof(begin: ByteArray, attempt: String) {
        val directory = File(targetContext.cacheDir, "proof-${UUID.randomUUID()}")
        check(directory.mkdir())
        try {
            val bundle = File(directory, "bundle")
            copyAsset("proof/bundle", bundle)
            val srs = targetContext.assets.open("proof/srs").use { it.readBytes() }
            val options = targetContext.assets.open("proof/target.json").bufferedReader().use { JSONObject(it.readText()) }
            check(options.getInt("k") == 7)
            val descriptor = JSONObject(options.toString()).put("bundleDirectory", bundle.canonicalPath).bytes()
            val plan = File(bundle, "witness/entrypoint.control.json").readBytes()
            val state = """{"state":{"total":"0"}}""".toByteArray(Charsets.UTF_8)
            val proofDescriptor = options.put("proofServiceCapability", "host.prover")
                .put("maxResponseBytes", 1_048_576).bytes()
            expectStatus(1) {
                NativeWitness.open(descriptor, state, srs, plan + byteArrayOf(10), begin).close()
            }
            NativeWitness.open(descriptor, state, srs, plan, begin).use { invocation ->
                expectStatus(3) { invocation.prepareProof(proofDescriptor).close() }
                completeWitness(invocation.session, attempt)
                invocation.prepareProof(proofDescriptor).use { native ->
                    check(runCatching { invocation.session.advance() }.exceptionOrNull() is IllegalStateException)
                    check(runCatching { invocation.prepareProof(proofDescriptor) }.exceptionOrNull() is IllegalStateException)
                    val proved = native.proveLocally().json()
                    check(proved.getString("status") == "proved")
                    check(!proved.getBoolean("funded") && !proved.getBoolean("submitted"))
                    check(proved.getString("publicIntentHex").isNotEmpty())
                }
            }
        } finally {
            directory.deleteRecursively()
        }
    }

    private fun copyAsset(path: String, destination: File) {
        val assets = targetContext.assets
        val entries = assets.list(path).orEmpty()
        if (entries.isEmpty()) {
            assets.open(path).use { input -> destination.outputStream().use { input.copyTo(it) } }
        } else {
            check(destination.mkdir())
            for (entry in entries) copyAsset("$path/$entry", File(destination, entry))
        }
    }

    private fun expectStatus(status: Int, action: () -> Unit) {
        try {
            action()
        } catch (error: NoctiumFailure) {
            check(error.status == status)
            return
        }
        error("Expected a native status")
    }

    private fun ByteArray.json() = JSONObject(toString(Charsets.UTF_8))
    private fun JSONObject.bytes() = toString().toByteArray(Charsets.UTF_8)
}
