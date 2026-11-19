import CNoctium
import Foundation

/// An isolated invocation of a compiler-emitted host-control plan.
/// Keep the session and all returned data on your trusted host. Use the session serially.
public final class WitnessSession {
    public enum Failure: Error, Equatable {
        case nativeStatus(Int32)
        case invalidResult
        case entropyUnavailable(Int32)
    }

    private var handle: UInt64?

    /// Accepts the Control ABI's UTF-8 JSON envelope with plan, inputs and hostContext.
    public init(begin: Data) throws {
        var session: UInt64 = 0
        let status = begin.withBytePointer { pointer, count in
            noctium_control_begin(pointer, count, &session)
        }
        try Self.check(status)
        handle = session
    }

    init(handle: UInt64) {
        self.handle = handle
    }

    deinit {
        if let handle { _ = noctium_control_free(handle) }
    }

    func activeHandle() throws -> UInt64 {
        guard let handle else { throw Failure.nativeStatus(Int32(NOCTIUM_CONTROL_INVALID_HANDLE)) }
        return handle
    }

    func markConsumed() {
        handle = nil
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
            response.withBytePointer { pointer, count in
                resume(session, pointer, count, token)
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

    static func check(_ status: Int32) throws {
        guard status == NOCTIUM_CONTROL_OK else { throw Failure.nativeStatus(status) }
    }

    private func result(
        _ operation: (UInt64, UnsafeMutablePointer<UInt64>?) -> Int32,
        privateResult: Bool = false
    ) throws -> Data {
        var token: UInt64 = 0
        try Self.check(operation(try activeHandle(), &token))
        return try takeResult(
            token,
            length: privateResult ? noctium_control_private_length : noctium_control_result_length,
            copy: privateResult ? noctium_control_private_copy : noctium_control_result_copy,
            free: privateResult ? noctium_control_private_free : noctium_control_result_free
        )
    }
}

extension Data {
    func withBytePointer<T>(_ body: (UnsafePointer<UInt8>?, Int) throws -> T) rethrows -> T {
        try withUnsafeBytes { bytes in
            try body(bytes.bindMemory(to: UInt8.self).baseAddress, bytes.count)
        }
    }
}

func takeResult(
    _ token: UInt64,
    length: (UInt64, UnsafeMutablePointer<Int>?) -> Int32,
    copy: (UInt64, UnsafeMutablePointer<UInt8>?, Int, UnsafeMutablePointer<Int>?) -> Int32,
    free: (UInt64) -> Int32
) throws -> Data {
    defer { _ = free(token) }
    var count = 0
    try WitnessSession.check(length(token, &count))
    var data = Data(count: count)
    var written = 0
    let status = data.withUnsafeMutableBytes { bytes in
        copy(token, bytes.bindMemory(to: UInt8.self).baseAddress, bytes.count, &written)
    }
    try WitnessSession.check(status)
    guard written == count else { throw WitnessSession.Failure.invalidResult }
    return data
}
