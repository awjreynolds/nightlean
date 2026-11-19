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
        var fields = try beginFields(attemptID: attemptID)
        fields["plan"] = plan
        let begin = try encode(fields)
        let session = try WitnessSession(begin: begin)
        try complete(session, attemptID: attemptID)

        let cancelled = try WitnessSession(begin: begin)
        _ = try cancelled.advance()
        XCTAssertEqual(try decode(cancelled.cancel())["status"] as? String, "cancelled")
        XCTAssertThrowsError(try cancelled.privateRequest())
    }

    func testAuthenticatedWitnessProvesLocally() throws {
        guard let directory = ProcessInfo.processInfo.environment["NOCTIUM_SWIFT_PROOF_FIXTURE"] else {
            throw XCTSkip("Set NOCTIUM_SWIFT_PROOF_FIXTURE to the native proof fixture directory")
        }
        let root = URL(fileURLWithPath: directory, isDirectory: true)
        let targetDescriptor = try Data(contentsOf: root.appendingPathComponent("target.json"))
        let descriptor = try decode(targetDescriptor)
        let bundle = try XCTUnwrap(descriptor["bundleDirectory"] as? String)
        let control = URL(fileURLWithPath: bundle).appendingPathComponent("witness/entrypoint.control.json")
        let plan = try Data(contentsOf: control)
        let parameters = try Data(contentsOf: root.appendingPathComponent("srs"))
        let attemptID = String(repeating: "d", count: 64)
        let begin = try encode(beginFields(attemptID: attemptID))
        let state = Data(#"{"state":{"total":"0"}}"#.utf8)
        var options = descriptor
        options.removeValue(forKey: "bundleDirectory")
        options["proofServiceCapability"] = "host.prover"
        options["maxResponseBytes"] = 1_048_576
        let proofDescriptor = try encode(options)

        XCTAssertThrowsError(try NativeWitness(
            targetDescriptor: targetDescriptor, initialState: state, parameters: parameters,
            plan: plan + Data([10]), begin: begin
        ))
        let target = try NativeWitness(
            targetDescriptor: targetDescriptor, initialState: state, parameters: parameters,
            plan: plan, begin: begin
        )
        XCTAssertEqual(try decode(target.targetInfo)["entrypoint"] as? String, "claim")
        XCTAssertThrowsError(try target.prepareProof(descriptor: proofDescriptor)) {
            XCTAssertEqual($0 as? WitnessSession.Failure, .nativeStatus(3))
        }
        try complete(target.session, attemptID: attemptID)
        let proof = try target.prepareProof(descriptor: proofDescriptor)
        XCTAssertThrowsError(try target.session.advance())
        XCTAssertThrowsError(try target.prepareProof(descriptor: proofDescriptor))
        let intent = try decode(proof.proveLocally())
        XCTAssertEqual(intent["status"] as? String, "proved")
        XCTAssertEqual(intent["funded"] as? Bool, false)
        XCTAssertEqual(intent["submitted"] as? Bool, false)
        XCTAssertFalse(try XCTUnwrap(intent["publicIntentHex"] as? String).isEmpty)
    }

    private func beginFields(attemptID: String) throws -> [String: Any] {
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
        return ["abiVersion": 1, "inputs": ["expected": "14", "seed": "7"], "hostContext": context]
    }

    private func complete(_ session: WitnessSession, attemptID: String) throws {
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
    }

    private func decode(_ bytes: Data) throws -> [String: Any] {
        try XCTUnwrap(JSONSerialization.jsonObject(with: bytes) as? [String: Any])
    }

    private func encode(_ value: [String: Any]) throws -> Data {
        try JSONSerialization.data(withJSONObject: value)
    }
}
