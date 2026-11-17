import Noctium.Frontend
import Nightlean.Backend.Impact
import Nightlean.Backend.Native
import Nightlean.Backend.Zkir
import Nightlean.Disclosure

open scoped Noctium
open Lean

noctium_circuit issue70Jubjub where
  private sk : JubjubScalar
  private r : JubjubScalar
  private message : JubjubScalar
  public pk : JubjubPoint
  public account : Bytes32
  public publicScalar : JubjubScalar
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let expectedPk : JubjubPoint := jubjubMulGenerator(sk)
  let skNative : Native := jubjubScalarToNative(sk)
  let randomnessNative : Native := jubjubScalarToNative(r)
  assert eq(pk, expectedPk)
  assert eq(eq(skNative, 0), false)
  assert eq(eq(randomnessNative, 0), false)
  assert eq(eq(pk, identity), false)
  let messagePoint : JubjubPoint := jubjubAdd(
    jubjubMulGenerator(message), jubjubMulGenerator(publicScalar))
  let c1 : JubjubPoint := jubjubMulGenerator(r)
  let sharedSecret : JubjubPoint := jubjubMul(pk, r)
  let c2 : JubjubPoint := jubjubAdd(messagePoint, sharedSecret)
  let recovered : JubjubPoint := jubjubAdd(c2, jubjubNeg(jubjubMul(c1, sk)))
  assert eq(recovered, messagePoint)
  output c1x : Native := disclose(jubjubX(c1))
  output c1y : Native := disclose(jubjubY(c1))
  output c2x : Native := disclose(jubjubX(c2))
  output c2y : Native := disclose(jubjubY(c2))
end

noctium_contract Issue70Jubjub where
  tree ciphertexts : Bytes32 => struct Ciphertext4 {
    c1x : Native
    c1y : Native
    c2x : Native
    c2y : Native
  }
  entry encrypt uses issue70Jubjub where
    write ciphertexts[disclose(account)] := fields(
      disclose(c1x), disclose(c1y), disclose(c2x), disclose(c2y))
    read ciphertexts[disclose(account)] as observed
    require eq(observed_c1x, c1x)
    require eq(observed_c1y, c1y)
    require eq(observed_c2x, c2x)
    require eq(observed_c2y, c2y)
  end
end

private def issue70JubjubEntry : Noctium.Entrypoint :=
  match Issue70Jubjub.entrypoints with
  | entrypoint :: _ => entrypoint
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Nightlean.Backend.Zkir.lowerEntrypoint Issue70Jubjub.state issue70JubjubEntry with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

private def issue70JubjubMutation (program : Json) : Json :=
  let instructions := (program.getObjValD "instructions").getArr?.toOption.getD #[]
  let retained := instructions.filter fun instruction =>
    (instruction.getObjValD "op").getStr?.toOption != some "constrain_eq"
  match program.getObj? with
  | .error _ => program
  | .ok object => Json.mkObj ((object.toList.filter (·.1 != "instructions")) ++
      [("instructions", Json.arr retained)])

private def issue70JubjubRoundtripIsRequired : _root_.Bool :=
  match Nightlean.Backend.Native.expectedEntrypoint Issue70Jubjub.state issue70JubjubEntry with
  | .error _ => _root_.Bool.false
  | .ok expected =>
    match Nightlean.Backend.Zkir.lowerEntrypoint Issue70Jubjub.state issue70JubjubEntry with
    | .error _ => _root_.Bool.false
    | .ok program => match Nightlean.Backend.Native.validate expected (issue70JubjubMutation program) with
      | .error _ => _root_.Bool.true
      | .ok _ => _root_.Bool.false

#guard issue70JubjubRoundtripIsRequired

private def issue70JubjubPointMutation (program : Json) : Json :=
  let instructions := (program.getObjValD "instructions").getArr?.toOption.getD #[]
  let retained := instructions.filter fun instruction =>
    !((instruction.getObjValD "op").getStr?.toOption == some "constrain_eq" &&
      ["%input_pk_x", "%input_pk_y"].contains
        ((instruction.getObjValD "a").getStr?.toOption.getD ""))
  match program.getObj? with
  | .error _ => program
  | .ok object => Json.mkObj ((object.toList.filter (·.1 != "instructions")) ++
      [("instructions", Json.arr retained)])

#guard match Nightlean.Backend.Native.expectedEntrypoint Issue70Jubjub.state issue70JubjubEntry,
    Nightlean.Backend.Zkir.lowerEntrypoint Issue70Jubjub.state issue70JubjubEntry with
  | .ok expected, .ok program =>
    match Nightlean.Backend.Native.validate expected (issue70JubjubPointMutation program) with
    | .error _ => _root_.Bool.true
    | .ok _ => _root_.Bool.false
  | _, _ => _root_.Bool.false
