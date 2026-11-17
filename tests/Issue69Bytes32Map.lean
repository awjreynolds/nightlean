import Nightlean.Backend.Impact
import Nightlean.Backend.Zkir
import Nightlean.Frontend

open scoped Nightlean
open Nightlean

nightlean_circuit issue69Bytes32Register where
  public probe : Bytes32
  private account : Bytes32
end

nightlean_contract Issue69Bytes32Map where
  map registered : Bytes32 => Bool
  entry register uses issue69Bytes32Register where
    member registered[probe] as existed
    when eq(existed, true) read registered[probe] as before
    insert registered[disclose(account)] := true
    member registered[probe] as present
    read registered[probe] as marker
    require eq(present, true)
    require eq(marker, true)
  end
end

private def issue69Entry : Entrypoint :=
  match Issue69Bytes32Map.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Impact.lower Issue69Bytes32Map.state issue69Entry with
  | .ok plan => plan.reads.any fun item => item.name == "before" && item.guard.isSome
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint Issue69Bytes32Map.state issue69Entry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def issue69Bytes32CastRejected : Expr .native :=
  .cast .native (.ref (ty := .bytes 32) "account")

#guard match issue69Bytes32CastRejected.validate {} [("account", .bytes 32)] with
  | .error message => message == "byte strings do not support scalar casts"
  | .ok _ => Bool.false

nightlean_circuit issue69Bytes32Equality where
  private left : Bytes32
  private right : Bytes32
  output same : Bool := disclose(eq(left, right))
end

private def withoutRelease {ty : Ty} : Expr ty → Expr ty
  | .disclose _ value => value
  | value => value

#guard match Disclosure.circuit {issue69Bytes32Equality with
    outputs := issue69Bytes32Equality.outputs.map fun item =>
      {item with value := withoutRelease item.value}} with
  | .error diagnostic => diagnostic.message.startsWith "undisclosed private parameter"
  | .ok _ => Bool.false

private def issue69Bytes32NameCollision : Circuit := {
  name := "issue69Bytes32NameCollision"
  inputs := [
    {name := "owner", ty := .bytes 32, visibility := .private},
    {name := "owner_byte_0", ty := .native, visibility := .private}]
}

#guard match issue69Bytes32NameCollision.validate {} with
  | .error diagnostic => diagnostic.message == "input names collide after native byte expansion"
  | .ok _ => Bool.false
