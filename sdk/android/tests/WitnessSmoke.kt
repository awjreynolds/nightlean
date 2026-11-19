package org.noctium.sdk.tests

import android.app.Activity
import android.app.Instrumentation
import android.os.Bundle
import org.json.JSONObject
import org.noctium.sdk.NoctiumFailure
import org.noctium.sdk.WitnessSession

class WitnessSmoke : Instrumentation() {
    override fun onCreate(arguments: Bundle?) {
        super.onCreate(arguments)
        start()
    }

    override fun onStart() {
        val result = Bundle()
        try {
            runWitness()
            result.putString("stream", "Noctium Android witness passed\n")
            finish(Activity.RESULT_OK, result)
        } catch (error: Exception) {
            result.putString("stream", "Noctium Android witness failed: ${error.javaClass.simpleName} " +
                "${error.stackTrace.firstOrNull()}\n")
            finish(Activity.RESULT_CANCELED, result)
        }
    }

    private fun runWitness() {
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
        val begin = JSONObject().put("abiVersion", 1).put("plan", plan)
            .put("inputs", JSONObject().put("expected", "14").put("seed", "7"))
            .put("hostContext", context).bytes()

        WitnessSession.open(begin).use { session ->
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
        WitnessSession.open(begin).use { session ->
            check(session.advance().json().getString("status") == "need_host")
            check(session.cancel().json().getString("status") == "cancelled")
            expectStatus(3) { session.privateRequest() }
        }
        expectStatus(5) { WitnessSession.open(ByteArray(1024 * 1024 + 1)).close() }
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
