package org.noctium.sdk.tests

import java.io.File
import java.security.MessageDigest
import java.util.UUID
import org.json.JSONObject
import org.noctium.sdk.DevelopmentLocalnet
import org.noctium.sdk.DevelopmentTransaction
import org.noctium.sdk.DevelopmentTransaction.Command
import org.noctium.sdk.NativeProof
import org.noctium.sdk.startDevelopmentCall
import org.noctium.sdk.startDevelopmentDeployment

class DevelopmentSmoke : WitnessSmoke() {
    override fun testProof(directory: File): String {
        val fixture = File(directory, "localnet")
        val descriptor = File(fixture, "client.json").readBytes()
        val settings = JSONObject(File(fixture, "localnet.json").readText())
            .put("journalDirectory", File(fixture, "journal").canonicalPath)
            .put("parameterCache", File(fixture, "params").canonicalPath)
        val attempt = attemptId()
        val namespace = "android-witness-${attempt.take(16)}"
        val seed = ByteArray(32).also { it[31] = 1 }
        val recoveryFile = File(fixture, "recovery")
        val development = try {
            DevelopmentLocalnet(settings.bytes(), seed)
        } finally {
            seed.fill(0)
        }
        val claim = File(directory, "synthetic-claim.json")
        if (claim.isFile) {
            return development.use { testClaim(directory, claim, descriptor, it) }
        }
        val (deploymentReceipt, sealed) = development.use { localnet ->
            val ttl = localnet.context().json().getString("blockTime").toLong() + 1800
            val begin = beginEnvelope(attempt, namespace, "r0").bytes()
            prepareProof(directory, begin, attempt, ttl).use { proof ->
                prove(proof)
                val deployment = proof.startDevelopmentDeployment(descriptor, emptySetup("$namespace-deployment"))
                val receipt = deployment.use {
                    val request = it.send(Command.PREPARE)
                    expectStatus(3) { it.close() }
                    drive(it, localnet, request)
                    drive(it, localnet, it.send(Command.SUBMIT))
                    val finalized = observe(it, localnet)
                    check(finalized.getString("event") == "Deploy")
                    check(drive(it, localnet, it.send(Command.COMMIT)).getString("phase") == "Committed")
                    finalized
                }
                val call = proof.startDevelopmentCall(descriptor)
                expectStatus(3) { proof.startDevelopmentCall(descriptor).close() }
                call.use {
                    drive(it, localnet, it.send(Command.PREPARE))
                    val recovery = it.recoveryContext()
                    try {
                        recoveryFile.outputStream().use { output ->
                            output.write(recovery)
                            output.fd.sync()
                        }
                    } finally {
                        recovery.fill(0)
                    }
                    val transaction = it.sealedTransaction()
                    check(localnet.privateValue(namespace, "cache/last").contentEquals("null".toByteArray()))
                    drive(it, localnet, it.send(Command.SUBMIT))
                    receipt to transaction
                }
            }
        }

        for (key in listOf("parameterCache", "parameterSource", "dustSrsSha256")) settings.remove(key)
        val callReceipt = DevelopmentLocalnet(settings.bytes()).use { localnet ->
            val recovery = recoveryFile.readBytes()
            val resumed = try {
                DevelopmentTransaction.recover(descriptor, recovery)
            } finally {
                recovery.fill(0)
            }
            resumed.use {
                drive(it, localnet, it.advance())
                check(it.sealedTransaction().contentEquals(sealed))
                val receipt = observe(it, localnet)
                check(receipt.getString("event") == "Call")
                check(receipt.getString("contractAddress") == deploymentReceipt.getString("contractAddress"))
                val digest = MessageDigest.getInstance("SHA-256").digest(it.finalizedState())
                    .joinToString("") { byte -> "%02x".format(byte) }
                check(digest == "f9b24f4480110e62fe9333e5c3be687073922bd24b0935fbd62c0eb1b699c600")
                check(receipt.getString("contractStateSha256") == digest)
                val committed = drive(it, localnet, it.send(Command.COMMIT))
                check(committed.getString("phase") == "Committed" && committed.getBoolean("privateAcknowledged"))
                check(localnet.privateValue(namespace, "cache/last").json().getString("value") == "14")
                receipt
            }
        }
        val receipts = JSONObject().put("deployment", deploymentReceipt).put("call", callReceipt)
        return "Noctium Android localnet transaction and private recovery passed\n$receipts\n"
    }

    private fun testClaim(
        directory: File, fixture: File, client: ByteArray, localnet: DevelopmentLocalnet,
    ): String {
        val options = JSONObject(File(directory, "target.json").readText())
        check(options.getInt("k") == 9)
        val ttl = localnet.context().json().getString("blockTime").toLong() + 1800
        val descriptor = options.put("ttl", ttl)
            .put("bundleDirectory", File(directory, "bundle").canonicalPath)
            .put("proofServiceCapability", "host.prover").put("maxResponseBytes", 1_048_576).bytes()
        val srs = File(directory, "srs").readBytes()
        val config = fixture.readBytes()
        val altered = config.json()
        check(altered.getJSONObject("inputs").getString("secret") != "0")
        altered.getJSONObject("inputs").put("secret", "0")
        expectStatus(1) { NativeProof.open(descriptor, altered.bytes(), srs).close() }
        val namespace = "android-claim-${attemptId().take(16)}"
        NativeProof.open(descriptor, config, srs).use { proof ->
            prove(proof)
            val deployment = proof.startDevelopmentDeployment(client, emptySetup("$namespace-deploy")).use {
                finalize(it, localnet).also { receipt -> check(receipt.getString("event") == "Deploy") }
            }
            proof.startDevelopmentCall(client, emptySetup("$namespace-call")).use {
                val call = finalize(it, localnet)
                check(call.getString("event") == "Call")
                check(call.getString("contractAddress") == deployment.getString("contractAddress"))
                val finalized = it.finalizedState()
                val digest = MessageDigest.getInstance("SHA-256").digest(finalized)
                    .joinToString("") { byte -> "%02x".format(byte) }
                check(digest == "d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3")
                check(call.getString("contractStateSha256") == digest)
                val receipts = JSONObject().put("deployment", deployment).put("call", call)
                // Only finalized public ledger state is exported for the host replay check.
                val stateHex = finalized.joinToString("") { byte -> "%02x".format(byte) }
                return "Noctium Android K9 private claim passed\n$receipts\nNOCTIUM_PUBLIC_STATE $stateHex\n"
            }
        }
    }

    private fun finalize(transaction: DevelopmentTransaction, adapter: DevelopmentLocalnet): JSONObject {
        drive(transaction, adapter, transaction.send(Command.PREPARE))
        drive(transaction, adapter, transaction.send(Command.SUBMIT))
        val receipt = observe(transaction, adapter)
        check(drive(transaction, adapter, transaction.send(Command.COMMIT)).getString("phase") == "Committed")
        return receipt
    }

    private fun drive(transaction: DevelopmentTransaction, adapter: DevelopmentLocalnet, initial: ByteArray): JSONObject {
        var pending = initial
        repeat(128) {
            val step = pending.json()
            if (step.getString("status") != "need_host") {
                check(step.getString("status") == "step_done")
                return step
            }
            val sign = step.getString("operation") == "approval.sign.v1"
            if (sign) {
                val crossed = JSONObject(step.toString()).put("requestId", "1")
                expectStatus(4) { transaction.resolve(crossed.bytes(), adapter, approveSigning = true) }
            }
            pending = transaction.resolve(pending, adapter, approveSigning = sign)
        }
        error("Development transaction exceeded its host request limit")
    }

    private fun observe(transaction: DevelopmentTransaction, adapter: DevelopmentLocalnet): JSONObject {
        repeat(180) {
            val observed = drive(transaction, adapter, transaction.send(Command.OBSERVE))
            observed.optJSONObject("receipt")?.let { return it }
            Thread.sleep(500)
        }
        error("Development transaction did not finalize")
    }

    private fun emptySetup(namespace: String): ByteArray {
        return JSONObject("""
            {"hostContext":{"protocolVersion":1,"namespace":"$namespace","baseRevision":"r0",
              "attemptId":"${attemptId()}","operations":[],"providers":[],"commitCapability":"store",
              "capabilities":[{"id":"store","namespace":"$namespace","keyPrefix":"fixture/",
                "operations":["private_state.stage.v1","private_state.compare_exchange.v1"]}]},"stages":[]}
        """.trimIndent()).bytes()
    }

    private fun attemptId() = (UUID.randomUUID().toString() + UUID.randomUUID()).replace("-", "")
}
