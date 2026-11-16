import Nightlean.ScalarPolicy

open Nightlean.ScalarPolicy

private def kindResult (value : Except String Kind) : Option Kind :=
  match value with
  | .ok result => some result
  | .error _ => none

private def kindError (value : Except String Kind) : Option String :=
  match value with
  | .ok _ => none
  | .error message => some message

private def resultValue (value : Except String Value) : Option (Kind × Nat) :=
  match value with
  | .ok result => some (result.kind, result.number)
  | .error _ => none

#guard kindResult (sized 8) == some (.uint 255)
#guard kindResult (sized 0) == some (.uint 0)
#guard kindResult (bounded 511) == some (.uint 510)
#guard kindError (bounded 0) == some "unsigned exclusive bound must be positive"
#guard kindError (sized 249) == some "unsigned width exceeds target maximum"
#guard kindResult (infer .add (.uint 255) (.uint 255)) == some (.uint 510)
#guard kindResult (infer .mul (.uint 255) (.uint 255)) == some (.uint 65025)
#guard kindResult (infer .sub (.uint 255) (.uint 15)) == some (.uint 255)
#guard kindResult (infer .add (.uint maxUint) (.uint 0)) == some (.uint maxUint)
#guard kindResult (infer .mul (.uint maxUint) (.uint 1)) == some (.uint maxUint)
#guard kindError (infer .add (.uint maxUint) (.uint 1)) == some "unsigned type exceeds target maximum"
#guard kindResult (infer .add .native (.uint 255)) == some .native
#guard kindError (infer .mul .bool (.uint 255)) == some "boolean arithmetic requires an explicit cast"
#guard resultValue (evaluate .add ⟨.uint 255, 255⟩ ⟨.uint 255, 255⟩) == some (.uint 510, 510)
#guard resultValue (evaluate .mul ⟨.uint 255, 255⟩ ⟨.uint 255, 255⟩) == some (.uint 65025, 65025)
#guard resultValue (evaluate .sub ⟨.uint 255, 3⟩ ⟨.uint 255, 5⟩) == none
#guard resultValue (evaluate .sub ⟨.native, 0⟩ ⟨.native, 1⟩) == some (.native, Nightlean.Field.modulus - 1)
#guard resultValue (cast ⟨.bool, 1⟩ (.uint 0)) == none
#guard resultValue (cast ⟨.uint 255, 2⟩ .bool) == some (.bool, 1)
#guard resultValue (cast ⟨.native, 256⟩ (.uint 255)) == none
#guard resultValue (cast ⟨.native, 255⟩ (.uint 255)) == some (.uint 255, 255)
#guard resultValue (literal 1) == some (.uint 1, 1)
#guard resultValue (evaluate .add ⟨.uint 255, 256⟩ ⟨.uint 255, 0⟩) == none

example (a b m n : Nat) (ha : a ≤ m) (hb : b ≤ n) : a + b ≤ m + n :=
  addition_range a b m n ha hb
