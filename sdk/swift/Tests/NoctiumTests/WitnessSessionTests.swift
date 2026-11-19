import Foundation
import Noctium
import XCTest

final class WitnessSessionTests: XCTestCase {
    func testTypedWitnessAndCancellation() throws {
        let fixture = try XCTUnwrap(
            ProcessInfo.processInfo.environment["NOCTIUM_SWIFT_PLAN"],
            "Set NOCTIUM_SWIFT_PLAN to the compiled TypedWitness.scalarHost.control.json"
        )
        let plan = try decode(Data(contentsOf: URL(fileURLWithPath: fixture)))
        let attemptID = String(repeating: "b", count: 64)
        let context = try decode(Data("""
            {
              "protocolVersion":1,"namespace":"noctium","baseRevision":"fixture-r0",
              "attemptId":"\(attemptID)",
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
            """.utf8))
        let begin = try encode([
            "abiVersion": 1, "plan": plan, "inputs": ["expected": "14", "seed": "7"], "hostContext": context,
        ])
        let session = try WitnessSession(begin: begin)
        for (index, name) in ["cache", "cache", "lookup", "cache", "lookup"].enumerated() {
            let pending = try session.advance()
            let step = try decode(pending)
            XCTAssertEqual(step["status"] as? String, "need_host")
            let request = try XCTUnwrap(step["request"] as? [String: Any])
            XCTAssertEqual(request["name"] as? String, name)
            XCTAssertNil(request["invocationWrites"])
            let privateRequest = try decode(session.privateRequest())
            let writes = try XCTUnwrap(privateRequest["invocationWrites"] as? [String: [String: String]])
            XCTAssertEqual(writes["cache/last"]?["value"], "1")

            var reply = request.filter { ["requestId", "operation", "capability", "schema"].contains($0.key) }
            reply["protocolVersion"] = 2
            reply["attemptId"] = attemptID
            reply["outcome"] = "value"
            reply["value"] = name == "cache" ? "1" : "14"
            if index == 0 {
                var crossed = reply
                crossed["attemptId"] = String(repeating: "c", count: 64)
                XCTAssertThrowsError(try session.resume(encode(crossed), typed: true)) {
                    XCTAssertEqual($0 as? WitnessSession.Failure, .nativeStatus(4))
                }
                XCTAssertEqual(try session.advance(), pending)
            }
            _ = try session.resume(encode(reply), typed: true)
        }
        let finished = try decode(session.advance())
        XCTAssertEqual(finished["status"] as? String, "completed")
        XCTAssertEqual(finished["result"] as? String, "14")

        let cancelled = try WitnessSession(begin: begin)
        _ = try cancelled.advance()
        XCTAssertEqual(try decode(cancelled.cancel())["status"] as? String, "cancelled")
        XCTAssertThrowsError(try cancelled.privateRequest())
    }

    private func decode(_ bytes: Data) throws -> [String: Any] {
        try XCTUnwrap(JSONSerialization.jsonObject(with: bytes) as? [String: Any])
    }

    private func encode(_ value: [String: Any]) throws -> Data {
        try JSONSerialization.data(withJSONObject: value)
    }
}
