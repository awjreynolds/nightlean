#if NOCTIUM_LOCALNET
import CNoctium
import Foundation

/// The native SDK's loopback-only development adapter. Supply an empty seed for recovery.
public final class DevelopmentLocalnet {
    fileprivate let handle: UInt64

    public init(configuration: Data, developmentSeed: Data = Data()) throws {
        var adapter: UInt64 = 0
        let status = configuration.withBytePointer { config, configSize in
            developmentSeed.withBytePointer { seed, seedSize in
                noctium_localnet_open(config, configSize, seed, seedSize, &adapter)
            }
        }
        try WitnessSession.check(status)
        handle = adapter
    }

    deinit { _ = noctium_localnet_free(handle) }

    public func context() throws -> Data {
        var token: UInt64 = 0
        try WitnessSession.check(noctium_localnet_context(handle, &token))
        return try takeNativeResult(token)
    }

    /// Reads a value from the local development journal. Treat the result as private.
    public func privateValue(namespace: String, key: String) throws -> Data {
        let query = try JSONEncoder().encode(["namespace": namespace, "key": key])
        var token: UInt64 = 0
        let status = query.withBytePointer { bytes, size in
            noctium_localnet_private_value(handle, bytes, size, &token)
        }
        try WitnessSession.check(status)
        return try takeNativeResult(token, privateResult: true)
    }
}

public extension NativeProof {
    func startDevelopmentDeployment(descriptor: Data, setup: Data) throws -> DevelopmentTransaction {
        try startDevelopment(kind: 0, descriptor: descriptor, setup: setup)
    }

    /// Starts a call prepared from explicit inputs. Setup is the host's private journal configuration.
    func startDevelopmentCall(descriptor: Data, setup: Data) throws -> DevelopmentTransaction {
        try startDevelopment(kind: 1, descriptor: descriptor, setup: setup)
    }

    private func startDevelopment(kind: UInt32, descriptor: Data, setup: Data) throws -> DevelopmentTransaction {
        var client: UInt64 = 0
        let status = descriptor.withBytePointer { config, configSize in
            setup.withBytePointer { privacy, privacySize in
                noctium_client_start(handle, kind, config, configSize, privacy, privacySize, &client)
            }
        }
        try WitnessSession.check(status)
        return DevelopmentTransaction(handle: client)
    }

    /// Transfers the staged private writes from the proved witness into the call.
    func startDevelopmentCall(descriptor: Data) throws -> DevelopmentTransaction {
        var client: UInt64 = 0
        let status = descriptor.withBytePointer { bytes, size in
            noctium_client_start_from_witness(handle, bytes, size, &client)
        }
        try WitnessSession.check(status)
        return DevelopmentTransaction(handle: client)
    }
}

/// Drives an existing Rust transaction state machine. Use serially on a worker.
/// Keep the object until work settles and close succeeds, or recover from durable state.
public final class DevelopmentTransaction {
    public enum Command: String {
        case prepare, submit, observe, commit, cancel, deadline, reload
    }

    private struct Correlation: Codable {
        let abiVersion: Int
        let requestId: String
        let operation: String
        let capability: String
        let schema: String
        let profile: String
    }

    private var handle: UInt64?

    fileprivate init(handle: UInt64) { self.handle = handle }

    public static func recover(descriptor: Data, context: Data) throws -> DevelopmentTransaction {
        var client: UInt64 = 0
        let status = descriptor.withBytePointer { config, configSize in
            context.withBytePointer { bytes, size in
                noctium_client_recover(config, configSize, bytes, size, &client)
            }
        }
        try WitnessSession.check(status)
        return DevelopmentTransaction(handle: client)
    }

    deinit {
        if let handle { _ = noctium_client_detach(handle) }
    }

    /// Releases the handle after the runtime confirms it has no unsettled work.
    public func close() throws {
        guard let handle else { return }
        try WitnessSession.check(noctium_client_detach(handle))
        self.handle = nil
    }

    public func send(_ command: Command) throws -> Data {
        try result { client, token in
            Data(command.rawValue.utf8).withBytePointer { bytes, size in
                noctium_client_command(client, bytes, size, token)
            }
        }
    }

    public func advance() throws -> Data {
        try result(noctium_client_advance)
    }

    /// Resolves the exact pending host request. Approve only an inspected signing request.
    public func resolve(
        _ pending: Data, using localnet: DevelopmentLocalnet, approveSigning: Bool = false
    ) throws -> Data {
        try respond(to: pending) { operation, request, reply in
            let approve: UInt32 = approveSigning ? 1 : 0
            if operation == "funding.native.v1" || (operation == "approval.sign.v1" && approveSigning) {
                return try withEntropy { entropy, size in
                    noctium_localnet_resolve(localnet.handle, request, approve, entropy, size, reply)
                }
            }
            return noctium_localnet_resolve(localnet.handle, request, approve, nil, 0, reply)
        }
    }

    public func reportServiceFailure(_ pending: Data) throws -> Data {
        try respond(to: pending) { _, request, reply in noctium_client_service_failure(request, reply) }
    }

    /// Persist these private bytes separately before submitting if you need process recovery.
    public func recoveryContext() throws -> Data {
        try result(noctium_client_recovery_context, privateResult: true)
    }

    public func finalizedState() throws -> Data {
        try result(noctium_client_receipt_state)
    }

    public func sealedTransaction() throws -> Data {
        try result(noctium_client_transaction)
    }

    private func activeHandle() throws -> UInt64 {
        guard let handle else {
            throw WitnessSession.Failure.nativeStatus(Int32(NOCTIUM_NATIVE_INVALID_HANDLE))
        }
        return handle
    }

    private func result(
        _ operation: (UInt64, UnsafeMutablePointer<UInt64>?) -> Int32,
        privateResult: Bool = false
    ) throws -> Data {
        var token: UInt64 = 0
        try WitnessSession.check(operation(try activeHandle(), &token))
        return try takeNativeResult(token, privateResult: privateResult)
    }

    private func respond(
        to pending: Data,
        _ service: (String, UInt64, UnsafeMutablePointer<UInt64>?) throws -> Int32
    ) throws -> Data {
        let client = try activeHandle()
        let correlation = try JSONDecoder().decode(Correlation.self, from: pending)
        let metadata = try JSONEncoder().encode(correlation)
        guard try advance() == pending else {
            throw WitnessSession.Failure.nativeStatus(Int32(NOCTIUM_NATIVE_INVALID_RESPONSE))
        }
        var request: UInt64 = 0
        try WitnessSession.check(noctium_client_request(client, &request))
        defer { _ = noctium_client_service_free(request) }
        var reply: UInt64 = 0
        try WitnessSession.check(service(correlation.operation, request, &reply))
        defer { _ = noctium_client_service_free(reply) }
        return try result { client, token in
            metadata.withBytePointer { bytes, size in
                noctium_client_resume(client, bytes, size, reply, token)
            }
        }
    }
}
#endif
