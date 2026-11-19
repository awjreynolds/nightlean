import Lean
import Noctium.ScalarPolicy

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
  guard (0 < bits && bits ≤ ScalarPolicy.maxBits)
  pure (operand, bits)

/-- A prior unconditional check at an equal or narrower width already bounds
the same immutable SSA operand. Retain earlier checks before any narrowing. -/
def run (instructions : Array Json) : Array Json := Id.run do
  let mut widths : Std.HashMap String Nat := {}
  let mut retained := #[]
  for instruction in instructions do
    if let some (operand, bits) := key? instruction then
      if let some prior := widths[operand]? then
        if prior ≤ bits then continue
      widths := widths.insert operand bits
    retained := retained.push instruction
  return retained

end Noctium.Backend.RangeDedup
