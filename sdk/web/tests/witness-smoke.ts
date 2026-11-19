import init, { WitnessSession } from "./noctium_witness.js"

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

async function run() {
    await init()
    const fixture = await fetch("./plan.json")
    check(fixture.ok, "Missing compiled fixture")
    const plan: Json = await fixture.json()
    const attemptId = "b".repeat(64)
    const begin = encode({
        abiVersion: 1,
        plan,
        inputs: { expected: "14", seed: "7" },
        hostContext: {
            protocolVersion: 1,
            namespace: "noctium",
            baseRevision: "fixture-r0",
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
    })

    const witness = new WitnessSession(begin)
    try {
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
}

run().then(
    () => self.postMessage({ passed: true, callbacks: 5, result: 14 }),
    (error: unknown) => self.postMessage({ passed: false, error: String(error) }),
)
