import CNoctium
import Foundation

/// An isolated invocation of a compiler-emitted host-control plan.
/// Keep the session and all returned data on your trusted host. Use the session serially.
public final class WitnessSession {
    public enum Failure: Error, Equatable {
        case nativeStatus(Int32)
        case invalidResult
    }

    private let handle: UInt64

    /// Accepts the Control ABI's UTF-8 JSON envelope with plan, inputs and hostContext.
    public init(begin: Data) throws {
        var session: UInt64 = 0
        let status = begin.withUnsafeBytes { bytes in
            noctium_control_begin(bytes.bindMemory(to: UInt8.self).baseAddress, bytes.count, &session)
        }
        try Self.check(status)
        handle = session
    }

    deinit {
        _ = noctium_control_free(handle)
    }

    /// Advances until completion, rejection or a host callback. A pending request
    /// stays pending until a valid reply arrives or the invocation is cancelled.
    public func advance() throws -> Data {
        try result(noctium_control_advance)
    }

    /// Supplies one canonical reply. Select the typed transport for protocol v2.
    public func resume(_ response: Data, typed: Bool) throws -> Data {
        let resume = typed ? noctium_control_resume_typed : noctium_control_resume
        return try result { session, token in
            response.withUnsafeBytes { bytes in
                resume(session, bytes.bindMemory(to: UInt8.self).baseAddress, bytes.count, token)
            }
        }
    }

    /// Reads private callback arguments and invocation-local staged writes.
    public func privateRequest() throws -> Data {
        try result(noctium_control_private_request, privateResult: true)
    }

    @discardableResult
    public func cancel() throws -> Data {
        try result(noctium_control_cancel)
    }

    private static func check(_ status: Int32) throws {
        guard status == NOCTIUM_CONTROL_OK else { throw Failure.nativeStatus(status) }
    }

    private func result(
        _ operation: (UInt64, UnsafeMutablePointer<UInt64>?) -> Int32,
        privateResult: Bool = false
    ) throws -> Data {
        var token: UInt64 = 0
        try Self.check(operation(handle, &token))
        let free = privateResult ? noctium_control_private_free : noctium_control_result_free
        let length = privateResult ? noctium_control_private_length : noctium_control_result_length
        let copy = privateResult ? noctium_control_private_copy : noctium_control_result_copy
        defer { _ = free(token) }
        var count = 0
        try Self.check(length(token, &count))
        var data = Data(count: count)
        var written = 0
        let status = data.withUnsafeMutableBytes { bytes in
            copy(token, bytes.bindMemory(to: UInt8.self).baseAddress, bytes.count, &written)
        }
        try Self.check(status)
        guard written == count else { throw Failure.invalidResult }
        return data
    }
}
