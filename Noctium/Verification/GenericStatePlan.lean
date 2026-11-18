import Noctium.Compiler
import Noctium.Verification.GenericStateLowering

namespace Noctium.Verification.GenericStatePlan
open Lean Backend

/-- The complete JSON tree at the compiler's pure native-plan seam. All plan
fields, target identity, state schema, circuit, operation order, reads and
guards remain inside the equality. Byte serialization and file IO are a
separate artifact boundary. -/
def actualTree (profile : TargetProfile) (contractName : Name)
    (state : List StateDecl) (ep : Entrypoint) (plan : Impact.Plan) : Json :=
  Compiler.nativePlanJson profile contractName state
    (Passes.pruneEntrypoint ep) plan

structure Certificate (profile : TargetProfile) (contractName : Name)
    (state : List StateDecl) (ep : Entrypoint)
    (relationJson tree : Json) (plan : Impact.Plan)
    (expected : Native.Expected) : Prop where
  lowered : Zkir.lowerEntrypoint state ep = .ok relationJson
  planAccepted : Impact.lower state (Passes.pruneEntrypoint ep) = .ok plan
  expectedAccepted : Native.expectedEntrypoint state
    (Passes.pruneEntrypoint ep) = .ok expected
  nativeGate : Native.validate expected relationJson = .ok ()
  exactTree : tree = actualTree profile contractName state ep plan

/-- A producer-accepted relation has a certificate for the exact plan tree
computed at the production compiler seam. External plan bytes must be bound
to this tree by a separate parser or artifact attestation. -/
theorem of_lowered (profile : TargetProfile) (contractName : Name)
    (state : List StateDecl) (ep : Entrypoint) (relationJson : Json)
    (lowered : Zkir.lowerEntrypoint state ep = .ok relationJson) :
    ∃ tree plan expected,
      Certificate profile contractName state ep relationJson tree plan expected := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted, nativeGate⟩ :=
    GenericStateLowering.lowerEntrypoint_validated state ep relationJson lowered
  exact ⟨actualTree profile contractName state ep plan, plan, expected,
    ⟨lowered, planAccepted, expectedAccepted, nativeGate, rfl⟩⟩

/-- The accepted JSON tree is exactly the production serializer applied to
the accepted Impact plan. This projection deliberately retains the full tree. -/
theorem exact (certificate : Certificate profile contractName state ep relationJson tree plan expected) :
    tree = Compiler.nativePlanJson profile contractName state
      (Passes.pruneEntrypoint ep) plan := certificate.exactTree

end Noctium.Verification.GenericStatePlan
