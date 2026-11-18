import Noctium.Verification.NativeStateJson
open Noctium.Verification.NativeRelation Noctium.Verification.NativeState

example : step (.popeq (boolean false)) ⟨[.cell (field zero)], []⟩ = none := by decide +kernel
example : step (.index 3 false) (initial zero one []) = none := by decide +kernel
example : step (.member) ⟨[.cell (field zero), .map [(zero, zero)]], []⟩ =
    some ⟨[.cell (boolean true)], []⟩ := by decide +kernel
example : step (.insert 2) ⟨[.cell (field one), .cell (field zero), .map []], []⟩ = none := by decide +kernel
example : step (.insert 2) ⟨[.cell (field one), .cell (field zero), .map [],
    .cell (field (scalar 1)), .array [field zero, field one] []], []⟩ = none := by decide +kernel
example : Admitted ⟨21, 1⟩ [] [] := by constructor <;> decide +kernel
example : ¬ Admitted ⟨21, 0⟩ [] [] := by simp [Admitted]
