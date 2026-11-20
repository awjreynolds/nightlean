import init, { AuthenticatedWitness, WitnessSession } from "./noctium_witness.js"
import { resumeLocalnet, submitLocalnet } from "./browser-localnet.js"

type Json = string | number | boolean | null | Json[] | { [key: string]: Json }
type Request = { requestId: string, operation: string, capability: string, schema: string, name: string }
type Step = { status: "ready" | "completed" | "cancelled" | "need_host", result?: Json, request?: Request }

const encoder = new TextEncoder()
const decoder = new TextDecoder()
const encode = (value: unknown) => encoder.encode(JSON.stringify(value))
const parse = <T>(bytes: Uint8Array): T => JSON.parse(decoder.decode(bytes)) as T

function check(condition: unknown, label: string): asserts condition {
    if (!condition) throw new Error(label)
}

function rejects(status: number, run: () => unknown) {
    try {
        run()
    } catch (error) {
        check(error === status, "Unexpected error code")
        return
    }
    throw new Error("Expected native rejection")
}

type Witness = Pick<WitnessSession, "advance" | "privateRequest" | "resume">

function complete(witness: Witness, attemptId: string) {
    for (const [index, name] of ["cache", "cache", "lookup", "cache", "lookup"].entries()) {
        const pending = witness.advance()
        const step = parse<Step>(pending)
        check(step.status === "need_host" && step.request?.name === name, "Unexpected callback")
        check(!Object.hasOwn(step.request, "invocationWrites"), "Public request carries private values")
        const privateRequest = witness.privateRequest()
        try {
            const hidden = parse<{ invocationWrites: Record<string, { value: string }> }>(privateRequest)
            check(hidden.invocationWrites["cache/last"].value === "1", "Wrong staged private value")
        } finally {
            privateRequest.fill(0)
        }
        const { requestId, operation, capability, schema } = step.request
        const reply = { protocolVersion: 2, attemptId, requestId, operation, capability, schema,
            outcome: "value", value: name === "cache" ? "1" : "14" }
        if (index === 0) {
            rejects(4, () => witness.resume(encode({ ...reply, attemptId: "c".repeat(64) }), true))
            check(decoder.decode(witness.advance()) === decoder.decode(pending), "Crossed reply changed request")
        }
        check(parse<Step>(witness.resume(encode(reply), true)).status === "ready", "Reply did not resume")
    }
    const completed = parse<Step>(witness.advance())
    check(completed.status === "completed" && completed.result === "14", "Wrong completion")
}

async function asset(path: string) {
    const response = await fetch(path)
    check(response.ok, "Missing fixture: " + path)
    return new Uint8Array(await response.arrayBuffer())
}

async function prove(begin: Uint8Array, attemptId: string, localnetRun: string | null) {
    const [manifest, target, srs] = await Promise.all([
        asset("./bundle/manifest.json"), asset("./target.json"), asset("./srs"),
    ])
    const options = parse<{ k: number, trustedManifestSha256: string }>(target)
    check(options.k === 7, "Wrong fixture size")
    const inventory = parse<{ entries: { path: string, role: string, sha256: string, size: number }[] }>(manifest)
    const { entries } = inventory
    const payloads = await Promise.all(entries.map(({ path }) => asset("./bundle/" + path)))
    const state = encode({ state: { total: "0" } })
    const start = (files: Uint8Array[]) => new AuthenticatedWitness(target, manifest, files, srs, state, begin)
    const index = entries.findIndex(({ role }) => role === "witnessControl")
    check(index >= 0, "Missing authenticated witness control")
    const changed = payloads[index].slice()
    changed[0] ^= 1
    rejects(1, () => start(payloads.map((value, i) => i === index ? changed : value)).free())
    const digest = async (bytes: Uint8Array<ArrayBuffer>) =>
        Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)),
            byte => byte.toString(16).padStart(2, "0")).join("")
    const bindingIndex = entries.findIndex(({ role }) => role === "witnessBinding")
    check(bindingIndex >= 0, "Missing binding")
    const binding = parse<{ target: { entrypoint: string } }>(payloads[bindingIndex])
    binding.target.entrypoint = "someOtherCall"
    const crossed = encode(binding)
    const entry = entries[bindingIndex]
    entry.sha256 = await digest(crossed)
    entry.size = crossed.byteLength
    const crossedManifest = encoder.encode(JSON.stringify(inventory) + "\n")
    const crossedTarget = encode({ ...options, trustedManifestSha256: await digest(crossedManifest) })
    const crossedFiles = payloads.map((value, i) => i === bindingIndex ? crossed : value)
    rejects(1, () => new AuthenticatedWitness(crossedTarget, crossedManifest, crossedFiles, srs, state, begin).free())
    const witness = start(payloads)
    try {
        rejects(3, () => witness.prepareProof().free())
        complete(witness, attemptId)
        const proof = witness.prepareProof()
        try {
            rejects(3, () => witness.advance())
            const start = performance.now()
            const proved = await proof.proveLocally()
            try {
                const proofMs = Math.round(performance.now() - start)
                const publicIntentBytes = proved.publicIntent().byteLength
                check(publicIntentBytes > 0, "Missing proved public intent")
                const stats = { k: 7, proofMs, publicIntentBytes }
                return localnetRun ? await submitLocalnet(proved, localnetRun, attemptId, stats) : stats
            } finally {
                proved.free()
            }
        } finally {
            proof.free()
        }
    } finally {
        witness.free()
    }
}

async function run() {
    await init()
    const query = new URLSearchParams(location.search)
    const localnetRun = query.has("localnet") ? query.get("runId") : null
    check(!query.has("localnet") || localnetRun, "Missing browser localnet run ID")
    if (localnetRun && query.has("resume")) return resumeLocalnet(localnetRun)
    const fixture = await fetch("./plan.json")
    check(fixture.ok, "Missing compiled fixture")
    const plan: Json = await fixture.json()
    const attemptId = localnetRun
        ? Array.from(crypto.getRandomValues(new Uint8Array(32)), byte => byte.toString(16).padStart(2, "0")).join("")
        : "b".repeat(64)
    const invocation = {
        abiVersion: 1,
        inputs: { expected: "14", seed: "7" },
        hostContext: {
            protocolVersion: 1,
            namespace: "noctium",
            baseRevision: localnetRun ? "r0" : "fixture-r0",
            attemptId,
            capabilities: [
                { id: "private", namespace: "noctium", keyPrefix: "cache/",
                  operations: ["private_state.read.v1", "private_state.stage.v1", "private_state.compare_exchange.v1"] },
                { id: "lookup", namespace: "noctium", keyPrefix: "lookup/", operations: ["noctium.lookup.v1"] },
            ],
            operations: [
                { operation: "private_state.read.v1", argumentSchema: { key: "Key" }, resultSchema: "UIntRange<256>" },
                { operation: "noctium.lookup.v1", argumentSchema: { seed: "UIntRange<256>" }, resultSchema: "UIntRange<256>" },
            ],
            providers: [
                { input: "cache", operation: "private_state.read.v1", capability: "private", arguments: { key: "cache/last" } },
                { input: "lookup", operation: "noctium.lookup.v1", capability: "lookup", arguments: {} },
            ],
            commitCapability: "private",
            limits: { requests: 64, writes: 64, privateBytes: 65536 },
        },
    }
    const begin = encode({ ...invocation, plan })

    const witness = new WitnessSession(begin)
    try {
        complete(witness, attemptId)
        witness.close()
        rejects(2, () => witness.advance())
    } finally {
        witness.free()
    }

    const cancelled = new WitnessSession(begin)
    try {
        check(parse<Step>(cancelled.advance()).status === "need_host", "Missing request")
        check(parse<Step>(cancelled.cancel()).status === "cancelled", "Cancellation failed")
        rejects(3, () => cancelled.privateRequest())
    } finally {
        cancelled.free()
        begin.fill(0)
    }
    rejects(5, () => new WitnessSession(new Uint8Array(1024 * 1024 + 1)))
    const result = { passed: true, callbacks: 5, result: 14 }
    if (!query.has("proof") && !localnetRun) return result
    const source = encode(invocation)
    try {
        const proof = await prove(source, attemptId, localnetRun)
        return "restart" in proof ? proof : { ...result, ...proof }
    } finally {
        source.fill(0)
    }
}

run().then(
    result => self.postMessage(result),
    (error: unknown) => self.postMessage({ passed: false, error: String(error) }),
)
