import Nightlean.Verification.ScalarParserAgreement

namespace ScalarParserAgreementTests

open Lean
open Nightlean.Backend.Native
open Nightlean.Verification.NativeRelationJson
open Nightlean.Verification.ScalarParserAgreement

private def successfulImmediate (text : String) (number : Nat) : Bool :=
  match Nightlean.Backend.Native.immediate text, decodeImmediate text with
  | .ok produced, .ok decoded => produced == number && decoded == number
  | _, _ => false

#guard successfulImmediate "0x00" 0
#guard successfulImmediate "0x01" 1
#guard successfulImmediate "0x0001" 256

private def rejectedImmediate (text : String) : Bool :=
  match Nightlean.Backend.Native.immediate text, decodeImmediate text with
  | .ok _, _ => false
  | _, .ok _ => false
  | _, _ => true

#guard rejectedImmediate "0x"
#guard rejectedImmediate "0x0100"
#guard rejectedImmediate "0x0A"

private def numberObject : Json := Json.mkObj [("width", toJson (8 : Nat))]

#guard match Nightlean.Backend.Native.natField numberObject "width", naturalField numberObject "width" with
  | .ok producer, .ok decoder => producer == 8 && decoder == 8
  | _, _ => false

example (json : Json) (name : String) (producer decoder : Nat)
    (producerParsed : Nightlean.Backend.Native.natField json name = .ok producer)
    (decoderParsed : naturalField json name = .ok decoder) :
    producer = decoder :=
  natField_naturalField_agree json name producer decoder producerParsed decoderParsed

end ScalarParserAgreementTests
