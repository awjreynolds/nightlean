import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit issue43EffectBlocks where
  private choose : Bool
  public wide : Native
end

noctium_contract Issue43EffectBlocks where
  cell left : Native
  cell right : Native
  cell selected : Native
  cell nested : Native
  cell final : Native
  entry update uses issue43EffectBlocks where
    if disclose(choose) then {
      read left as observed
      write selected := observed
      if eq(cast(UInt 3, wide), uint(3)) then {
        write nested := 31
      } else {
        write nested := 32
      }
    } else {
      read right as observed
      write selected := observed
      write nested := 42
    }
    read selected as observedAfter
    write final := observedAfter
  end
end

private def issue43EffectBlockEntry : Entrypoint :=
  match Issue43EffectBlocks.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match issue43EffectBlockEntry.effectGuardAt 0 with
  | some (.letE _ _ (.select _ (.disclose span _) _)) =>
      span.file == "tests/Issue43EffectBlocks.lean" && span.line == 20 && span.column == 8
  | _ => Bool.false

private def issue43EffectBlockContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def issue43EffectBlockState : LedgerState := {
  cells := [
    ("left", .native 11),
    ("right", .native 22),
    ("selected", .native 0),
    ("nested", .native 0),
    ("final", .native 0)]
  maps := []
}

#guard match issue43EffectBlockEntry.run issue43EffectBlockContext
    [("choose", .bool Bool.true), ("wide", .native 3)] issue43EffectBlockState with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.cells.lookup "selected" == some (.native 11) &&
      after.cells.lookup "nested" == some (.native 31) &&
      after.cells.lookup "final" == some (.native 11)
  | .error _ => Bool.false

#guard match issue43EffectBlockEntry.run issue43EffectBlockContext
    [("choose", .bool Bool.false), ("wide", .native 8)] issue43EffectBlockState with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.cells.lookup "selected" == some (.native 22) &&
      after.cells.lookup "nested" == some (.native 42) &&
      after.cells.lookup "final" == some (.native 22)
  | .error _ => Bool.false

private def issue43UndisclosedParentWrite : Entrypoint :=
  {issue43EffectBlockEntry with
    effects := [.writeCell "final" .native (.native 1)]
    effectGuards := [some (.ref "choose" : Expr .bool)]}

#guard match Disclosure.entrypoint issue43UndisclosedParentWrite with
  | .error _ => Bool.true
  | .ok _ => Bool.false

noctium_circuit issue43BranchLocalEscapeRelation where
end

/-- error: unknown Noctium value 'branchLocal' -/
#guard_msgs in
noctium_contract Issue43BranchLocalEscape where
  cell marker : Native
  entry update uses issue43BranchLocalEscapeRelation where
    if true then {
      read marker as branchLocal
    } else {
      write marker := 0
    }
    write marker := branchLocal
  end
end
