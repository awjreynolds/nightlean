import Lean

namespace Noctium.Backend.RangeDedup
open Lean

private def key? (instruction : Json) : Option (String × Nat) := do
  let object ← instruction.getObj?.toOption
  guard (object.size == 3)
  let opcode ← (instruction.getObjValAs? String "op").toOption
  guard (opcode == "constrain_bits")
  let operand ← (instruction.getObjValAs? String "val").toOption
  guard (operand.startsWith "%")
  let bits ← (instruction.getObjValAs? Nat "bits").toOption
  pure (operand, bits)

/-- Keep the first unconditional check for each immutable SSA operand and width. -/
def run (instructions : Array Json) : Array Json := Id.run do
  let mut seen : Std.HashSet (String × Nat) := {}
  let mut retained := #[]
  for instruction in instructions do
    if let some key := key? instruction then
      if seen.contains key then continue
      seen := seen.insert key
    retained := retained.push instruction
  return retained

end Noctium.Backend.RangeDedup
