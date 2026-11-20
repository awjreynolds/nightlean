import { BrowserClient, type BrowserProvedCall } from "./noctium_witness.js"

const encoder = new TextEncoder()
const decoder = new TextDecoder()
const encode = (value: unknown) => encoder.encode(JSON.stringify(value))
const parse = <T>(bytes: Uint8Array) => JSON.parse(decoder.decode(bytes)) as T
const hex = (bytes: ArrayLike<number>) => Array.from(bytes, byte => byte.toString(16).padStart(2, "0")).join("")
const sha256 = async (bytes: Uint8Array<ArrayBuffer>) =>
    hex(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)))

function check(condition: unknown, message: string): asserts condition {
    if (!condition) throw new Error(message)
}

type Identity = { attemptId: string, transactionId: string, baseRevision: string, journalDigest: string }
type RecordData = { identity: Identity, phase: string, journal: number[], cas?: Cas }
type Cas = { identity: Identity, revision: string, committed: boolean }
type Attempt = { body: string, digest: string, revision: bigint, bytes: Uint8Array, phase: string }
type PrivateState = { revision: bigint, values: Record<string, { value: unknown }> }
type Request = {
    operation: string, requestId: string, hasPrivateArguments: boolean,
    expectedRevision?: string | null, immutableDigest?: string,
}
type Transaction = { transaction: string, expectedState: string, afterHeight: string }
type Receipt = {
    blockHash: string, height: string, contractAddress: string, transactionId: string,
    contractStateSha256: string, event: string,
}
type Status = {
    status: string, phase?: string, busy: boolean, durableAcknowledged?: boolean,
    transactionId?: string, privateCommitted?: boolean, privateAcknowledged?: boolean,
    receipt?: Receipt,
}
type ProofStats = { k: number, proofMs: number, publicIntentBytes: number }
type Checkpoint = {
    recoveryContext: Uint8Array, transactionDigest: string, expectedState: string,
    transactionId: string, deployment: Receipt, proof: ProofStats,
}

const phases: Record<string, string[]> = {
    Prepared: ["Prepared", "Persisted", "Submitted", "Cancelled"],
    Persisted: ["Persisted", "Submitted", "Cancelled"],
    Submitted: ["Submitted", "Uncertain", "Accepted", "Rejected"],
    Uncertain: ["Submitted", "Uncertain", "Accepted", "Rejected"],
    Accepted: ["Accepted", "Committed", "Conflicted"],
    Committed: ["Committed"], Conflicted: ["Conflicted"], Cancelled: ["Cancelled"], Rejected: ["Rejected"],
}

function sameIdentity(left: Identity, right: Identity) {
    return left.attemptId === right.attemptId && left.transactionId === right.transactionId
        && left.baseRevision === right.baseRevision && left.journalDigest === right.journalDigest
}

function result<T>(request: IDBRequest<T>) {
    return new Promise<T>((resolve, reject) => {
        request.onsuccess = () => resolve(request.result)
        request.onerror = () => reject(new Error("IndexedDB request failed"))
    })
}

class Journal {
    private constructor(private db: IDBDatabase) {}

    static async open(runId: string) {
        check(/^[0-9a-f]{32}$/.test(runId), "Missing browser localnet run identity")
        const request = indexedDB.open("noctium-localnet-" + runId, 1)
        request.onupgradeneeded = () => request.result.createObjectStore("journal")
        return new Journal(await result(request))
    }

    close() {
        this.db.close()
    }

    private async access<T>(
        mode: IDBTransactionMode,
        action: (store: IDBObjectStore) => Promise<T>,
    ) {
        const tx = this.db.transaction("journal", mode, { durability: "strict" })
        const finished = new Promise<void>((resolve, reject) => {
            tx.oncomplete = () => resolve()
            tx.onabort = () => reject(new Error("IndexedDB transaction aborted"))
        })
        try {
            const value = await action(tx.objectStore("journal"))
            await finished
            return value
        } catch (error) {
            try { tx.abort() } catch { /* The failed transaction has closed. */ }
            await finished.catch(() => {})
            throw error
        }
    }

    read<T>(key: string): Promise<T | undefined> {
        return this.access("readonly", async store => await result(store.get(key)) as T | undefined)
    }

    async checkpoint(checkpoint: Checkpoint) {
        await this.access("readwrite", async store => { await result(store.add(checkpoint, "checkpoint")) })
    }

    async reply(request: Request, bytes: Uint8Array) {
        if (request.operation === "journal.load.v1") {
            const attempt = await this.read<Attempt>("attempt/" + decoder.decode(bytes))
            check(attempt && await sha256(attempt.bytes.slice()) === attempt.digest, "Invalid stored attempt")
            return { kind: "loaded", revision: attempt.revision.toString(), record: hex(attempt.bytes) }
        }
        const record = parse<RecordData>(bytes)
        const id = "attempt/" + record.identity.attemptId
        const casId = "cas/" + record.identity.attemptId
        const digest = await sha256(bytes.slice())
        return this.access("readwrite", async store => {
            const previous = await result(store.get(id)) as Attempt | undefined
            const cas = await result(store.get(casId)) as Cas | undefined
            if (request.operation === "journal.persist.v1") {
                const body = request.immutableDigest
                check(body && /^[0-9a-f]{64}$/.test(body) && request.expectedRevision !== undefined,
                    "Missing journal version binding")
                const expected = request.expectedRevision === null ? null : BigInt(request.expectedRevision)
                let revision = 1n
                if (previous) {
                    check(previous.body === body && phases[previous.phase]?.includes(record.phase),
                        "Changed immutable journal or illegal phase")
                    if (previous.digest === digest &&
                        (expected === previous.revision || expected === previous.revision - 1n)) {
                        revision = previous.revision
                    } else {
                        check(expected === previous.revision && previous.revision < 2n ** 64n - 1n,
                            "Stale journal revision")
                        revision = previous.revision + 1n
                    }
                } else {
                    check(expected === null && ["Prepared", "Persisted", "Cancelled"].includes(record.phase),
                        "Unexpected first durable phase")
                }
                if (record.phase === "Committed" || record.phase === "Conflicted") {
                    check(cas && record.cas && sameIdentity(cas.identity, record.cas.identity)
                        && cas.revision === record.cas.revision && cas.committed === record.cas.committed,
                    "Unknown private-state receipt")
                }
                await result(store.put({ revision, body, digest, bytes, phase: record.phase }, id))
                return { kind: "persisted", identity: record.identity, recordSha256: digest, revision: revision.toString() }
            }
            check(request.operation === "private_state.compare_exchange.v1", "Unknown journal operation")
            if (cas) {
                check(sameIdentity(cas.identity, record.identity), "Crossed private-state receipt")
                return { kind: "cas", ...cas }
            }
            check(previous?.digest === digest && record.phase === "Accepted", "CAS before durable acceptance")
            const journal = parse<{ namespace: string, writes: PrivateState["values"] }>(Uint8Array.from(record.journal))
            const key = "state/" + journal.namespace
            const state = await result(store.get(key)) as PrivateState | undefined
            const revision = state?.revision ?? 0n
            const committed = record.identity.baseRevision === `r${revision}`
            if (committed) {
                check(revision < 2n ** 64n - 1n, "Private state revision exhausted")
                await result(store.put({ revision: revision + 1n, values: { ...state?.values, ...journal.writes } }, key))
            }
            const receipt = { identity: record.identity, revision: `r${committed ? revision + 1n : revision}`, committed }
            await result(store.add(receipt, casId))
            return { kind: "cas", ...receipt }
        })
    }
}

type DriveOptions = {
    approve: boolean,
    requests?: string[],
    transaction?: (operation: string, transaction: Transaction) => Promise<void>,
}

async function providerReply(operation: string, transaction?: Transaction, bytes?: Uint8Array, approval = false) {
    const response = await fetch("./provider", {
        method: "POST",
        mode: "same-origin",
        redirect: "error",
        cache: "no-store",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ operation, transaction,
            privatePayload: bytes?.byteLength ? hex(bytes) : undefined,
            approved: approval ? true : undefined }),
    })
    check(response.ok, "Localnet provider failed: " + operation)
    return await response.json()
}

async function drive(client: BrowserClient, journal: Journal, options: DriveOptions, command?: string) {
    if (command) client.command(command)
    for (let step = 0; step < 64; step++) {
        const status = parse<Status>(client.poll())
        const metadata = client.request()
        if (!metadata.byteLength) {
            if (!status.busy) return status
            continue
        }
        const request = parse<Request>(metadata)
        options.requests?.push(request.operation)
        const bytes = request.hasPrivateArguments ? client.privateRequest() : new Uint8Array()
        try {
            let reply: unknown
            if (request.operation.startsWith("journal.") || request.operation === "private_state.compare_exchange.v1") {
                reply = await journal.reply(request, bytes)
            } else if (request.operation === "approval.sign.v1" && !options.approve) {
                reply = { kind: "failure" }
            } else {
                const transport = client.transactionRequest()
                const transaction = transport.byteLength ? parse<Transaction>(transport) : undefined
                if (transaction) await options.transaction?.(request.operation, transaction)
                const approval = request.operation === "funding.native.v1" || request.operation === "approval.sign.v1"
                reply = await providerReply(request.operation, transaction, bytes, approval)
            }
            const replyBytes = encode(reply)
            try { client.complete(request.requestId, replyBytes) } finally { replyBytes.fill(0) }
        } finally {
            bytes.fill(0)
        }
    }
    throw new Error("Browser client command exceeded its request bound")
}

function phase(status: Status, expected: string) {
    check(status.status === "step_done" && status.phase === expected, "Expected client phase " + expected)
}

async function descriptor() {
    const response = await fetch("./client.json")
    check(response.ok, "Missing pinned localnet client descriptor")
    return new Uint8Array(await response.arrayBuffer())
}

async function finalized(client: BrowserClient, journal: Journal, options: DriveOptions) {
    const deadline = Date.now() + 90_000
    while (Date.now() < deadline) {
        const status = await drive(client, journal, options, "observe")
        check(status.status === "step_done", "Finality verification failed")
        if (status.receipt) {
            phase(status, "AwaitingCas")
            return status.receipt
        }
        await new Promise(resolve => setTimeout(resolve, 300))
    }
    throw new Error("Timed out waiting for localnet finality")
}

export async function submitLocalnet(proved: BrowserProvedCall, runId: string, attemptId: string, proof: ProofStats) {
    const nativeDescriptor = await descriptor()
    const journal = await Journal.open(runId)
    try {
        const setup = encode({ hostContext: {
            protocolVersion: 1, namespace: "deployment", baseRevision: "r0",
            attemptId: hex(crypto.getRandomValues(new Uint8Array(32))),
            capabilities: [{ id: "setup", namespace: "deployment", keyPrefix: "cache/",
                operations: ["private_state.compare_exchange.v1"] }],
            operations: [], providers: [], commitCapability: "setup",
        }, stages: [] })
        const deploy = proved.startDeploymentClient(nativeDescriptor, setup)
        let deployment: Receipt
        try {
            const approve = { approve: true }
            phase(await drive(deploy, journal, approve, "prepare"), "Prepared")
            phase(await drive(deploy, journal, approve, "submit"), "Submitted")
            deployment = await finalized(deploy, journal, approve)
            check(deployment.event === "Deploy", "Wrong deployment receipt")
            phase(await drive(deploy, journal, approve, "commit"), "Committed")
        } finally {
            deploy.free()
        }

        const call = proved.startCallClient(nativeDescriptor)
        try {
            const requests: string[] = []
            const denied = await drive(call, journal, { approve: false, requests }, "prepare")
            check(denied.status === "step_error" && requests.at(-1) === "approval.sign.v1"
                && !requests.includes("chain.submit.v1") && !requests.includes("private_state.compare_exchange.v1")
                && !await journal.read("attempt/" + attemptId) && !await journal.read("state/noctium"),
            "Declined approval submitted or changed private state")

            const prepared = await drive(call, journal, { approve: true }, "prepare")
            phase(prepared, "Prepared")
            const transactionId = prepared.transactionId
            check(transactionId, "Missing prepared transaction ID")
            const broadcasts: Transaction[] = []
            const recoveryContext = call.recoveryContext()
            try {
                const submitted = await drive(call, journal, {
                    approve: true,
                    transaction: async (operation, binding) => {
                        check(operation === "chain.submit.v1" && broadcasts.length === 0, "Unexpected transaction request")
                        broadcasts.push(binding)
                        await journal.checkpoint({ recoveryContext, transactionId,
                            transactionDigest: await sha256(encoder.encode(binding.transaction)),
                            expectedState: binding.expectedState, deployment, proof })
                    },
                }, "submit")
                phase(submitted, "Submitted")
                check(submitted.transactionId === transactionId && submitted.durableAcknowledged && call.detachable(),
                    "Missing durable submission acknowledgement")
                check(!await journal.read("state/noctium"), "Private state committed before finality")
                const [transaction] = broadcasts
                check(transaction, "Missing broadcast")
                const beforeRestart = await providerReply("chain.observe.v1", transaction)
                check(beforeRestart.kind === "observed" && beforeRestart.status === "pending",
                    "Call finalized before the browser restart checkpoint")
            } finally {
                recoveryContext.fill(0)
            }
        } finally {
            call.free()
        }
        return { restart: true }
    } finally {
        journal.close()
    }
}

export async function resumeLocalnet(runId: string) {
    const nativeDescriptor = await descriptor()
    const journal = await Journal.open(runId)
    try {
        const checkpoint = await journal.read<Checkpoint>("checkpoint")
        check(checkpoint, "Missing durable browser checkpoint")
        let call: BrowserClient
        try {
            call = BrowserClient.recover(nativeDescriptor, checkpoint.recoveryContext)
        } finally {
            checkpoint.recoveryContext.fill(0)
        }
        try {
            const requests: string[] = []
            const observe = {
                approve: false, requests,
                transaction: async (operation: string, binding: Transaction) => {
                    check(operation === "chain.observe.v1"
                        && await sha256(encoder.encode(binding.transaction)) === checkpoint.transactionDigest
                        && binding.expectedState === checkpoint.expectedState, "Recovered transaction changed")
                },
            }
            const restored = await drive(call, journal, observe)
            phase(restored, "Submitted")
            check(restored.transactionId === checkpoint.transactionId && requests[0] === "journal.load.v1",
                "Worker did not recover the submitted attempt")
            const receipt = await finalized(call, journal, observe)
            check(receipt.transactionId === checkpoint.transactionId && receipt.event === "Call"
                && receipt.contractAddress === checkpoint.deployment.contractAddress
                && BigInt(receipt.height) > BigInt(checkpoint.deployment.height)
                && hex(call.receiptState()) === checkpoint.expectedState,
            "Finalized state or receipt identity differs from the proved call")
            check(!await journal.read("state/noctium"), "Private state committed before acceptance handling")
            for (let i = 0; i < 2; i++) {
                const committed = await drive(call, journal, observe, "commit")
                phase(committed, "Committed")
                check(committed.privateCommitted && committed.privateAcknowledged, "Private write was not acknowledged")
                const state = await journal.read<PrivateState>("state/noctium")
                check(state?.revision === 1n && state.values["cache/last"]?.value === "14",
                    "Wrong private-state value or duplicate write")
            }
            check(!requests.includes("chain.submit.v1")
                && requests.filter(operation => operation === "private_state.compare_exchange.v1").length === 1,
            "Restart repeated broadcast or private CAS")
            return { passed: true, callbacks: 5, result: 14, ...checkpoint.proof,
                localnet: { deployment: checkpoint.deployment, receipt, approvalDenied: true,
                    recoveredWithoutReproof: true, pendingBeforeRestart: true, broadcasts: 1, privateCommits: 1, exactState: true } }
        } finally {
            call.free()
        }
    } finally {
        journal.close()
    }
}
