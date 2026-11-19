import CNoctium
import Foundation
import Security

/// Owns one authenticated native target and its source witness invocation. Use serially.
public final class NativeWitness {
    public let targetInfo: Data
    public let session: WitnessSession

    private let parameters: Data
    private var target: UInt64?

    /// The descriptors and begin envelope use the formats in the native and Control C headers.
    /// Provide the exact witness control bytes retained in the authenticated bundle.
    public init(
        targetDescriptor: Data, initialState: Data, parameters: Data, plan: Data, begin: Data
    ) throws {
        var target: UInt64 = 0
        var result: UInt64 = 0
        try withEntropy { entropy, entropySize in
            let status = targetDescriptor.withBytePointer { descriptor, descriptorSize in
                initialState.withBytePointer { state, stateSize in
                    parameters.withBytePointer { srs, srsSize in
                        noctium_native_witness_target_begin(
                            descriptor, descriptorSize, state, stateSize,
                            srs, srsSize, entropy, entropySize, &target, &result
                        )
                    }
                }
            }
            try WitnessSession.check(status)
        }
        do {
            targetInfo = try takeProofResult(result)
            var control: UInt64 = 0
            let status = plan.withBytePointer { planBytes, planSize in
                begin.withBytePointer { config, configSize in
                    noctium_control_begin_from_native_target(
                        target, planBytes, planSize, config, configSize, &control
                    )
                }
            }
            try WitnessSession.check(status)
            session = WitnessSession(handle: control)
        } catch {
            _ = noctium_native_target_context_free(target)
            throw error
        }
        self.target = target
        self.parameters = parameters
    }

    deinit {
        if let target { _ = noctium_native_target_context_free(target) }
    }

    /// Consumes the target and completed witness session on success.
    public func prepareProof(descriptor: Data) throws -> NativeProof {
        guard let target else {
            throw WitnessSession.Failure.nativeStatus(Int32(NOCTIUM_NATIVE_INVALID_HANDLE))
        }
        let control = try session.activeHandle()
        var proof: UInt64 = 0
        try withEntropy { entropy, entropySize in
            let status = descriptor.withBytePointer { bytes, size in
                parameters.withBytePointer { srs, srsSize in
                    noctium_native_begin_from_witness(
                        bytes, size, target, control, srs, srsSize, entropy, entropySize, &proof
                    )
                }
            }
            try WitnessSession.check(status)
        }
        self.target = nil
        session.markConsumed()
        return NativeProof(handle: proof)
    }
}

/// An authenticated proof session. Local proving runs synchronously on the caller's thread.
public final class NativeProof {
    private let handle: UInt64

    fileprivate init(handle: UInt64) {
        self.handle = handle
    }

    deinit { _ = noctium_native_free(handle) }

    /// Generates and verifies the native proof before returning the public intent projection.
    public func proveLocally() throws -> Data {
        struct Reply: Codable {
            let abiVersion: Int
            let requestId: UInt64
            let operation: String
            let capability: String
            let profile: String
        }
        var result: UInt64 = 0
        try WitnessSession.check(noctium_native_advance(handle, &result))
        let request = try JSONDecoder().decode(Reply.self, from: takeProofResult(result))
        let reply = try JSONEncoder().encode(request)
        var payload: UInt64 = 0
        try WitnessSession.check(noctium_native_private_request(handle, &payload))
        defer { _ = noctium_native_private_free(payload) }
        try withEntropy { entropy, size in
            try WitnessSession.check(noctium_native_local_prove(payload, entropy, size, &result))
        }
        let response = try takeProofResult(result)
        let status = reply.withBytePointer { metadata, metadataSize in
            response.withBytePointer { proof, proofSize in
                noctium_native_resume(handle, metadata, metadataSize, proof, proofSize, &result)
            }
        }
        try WitnessSession.check(status)
        return try takeProofResult(result)
    }

    public func cancel() throws {
        try WitnessSession.check(noctium_native_cancel(handle))
    }
}

private func takeProofResult(_ token: UInt64) throws -> Data {
    try takeResult(
        token, length: noctium_native_result_length, copy: noctium_native_result_copy,
        free: noctium_native_result_free
    )
}

private func withEntropy<T>(_ body: (UnsafePointer<UInt8>?, Int) throws -> T) throws -> T {
    try withUnsafeTemporaryAllocation(of: UInt8.self, capacity: 32) { bytes in
        let pointer = bytes.baseAddress!
        defer { pointer.update(repeating: 0, count: bytes.count) }
        let status = SecRandomCopyBytes(kSecRandomDefault, bytes.count, pointer)
        guard status == errSecSuccess else { throw WitnessSession.Failure.entropyUnavailable(status) }
        return try body(pointer, bytes.count)
    }
}
