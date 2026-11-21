import Noctium.Backend.NativeExpected
import Noctium.Verification.NativeRelation

namespace Noctium.Verification.ScalarTermMeaning

open Backend.Native NativeRelation

/-- Interpret the scalar fragment of a native meaning term. Byte vectors and
unknown operations have no scalar interpretation. -/
def interpret? (hash : Hash) (inputs : Assignment) : Term → Option Scalar
  | .constant value => some (scalar value)
  | .input name => some (inputs name)
  | .unary opcode value => do
    let value ← interpret? hash inputs value
    if opcode == "neg" then some (scalar (Field.modulus - value.val))
    else if opcode == "not" then some (bit (decide (value = zero)))
    else none
  | .binary opcode left right => do
    let left ← interpret? hash inputs left
    let right ← interpret? hash inputs right
    if opcode == "add" then some (scalar (left.val + right.val))
    else if opcode == "mul" then some (scalar (left.val * right.val))
    else if opcode == "test_eq" then some (bit (decide (left = right)))
    else if opcode.startsWith "less_than:" then some (bit (decide (left.val < right.val)))
    else none
  | .select condition yes no => do
    let condition ← interpret? hash inputs condition
    if condition = one then interpret? hash inputs yes
    else interpret? hash inputs no
  | .hash values => do
    let values ← values.mapM (interpret? hash inputs)
    some (hash values)
  | _ => none

/-- A term belongs to the scalar meaning domain only when evaluation succeeds. -/
def Supported (hash : Hash) (inputs : Assignment) (term : Term) : Prop :=
  ∃ value, interpret? hash inputs term = some value

/-- Scalar bounds and assertions are meaningful only when every referenced term
has a scalar interpretation. -/
def Requirements (hash : Hash) (inputs : Assignment) (normalized : Normalized) : Prop :=
  (∀ requirement ∈ normalized.bounds,
    ∃ value, interpret? hash inputs requirement.1 = some value ∧ value.val ≤ requirement.2) ∧
  (∀ term ∈ normalized.assertions, interpret? hash inputs term = some one)

/-- A normalized scalar value carries its checked scalar interpretation and all
partial-operation obligations from normalization. -/
def Represents (hash : Hash) (inputs : Assignment) (normalized : Normalized)
    (value : Scalar) : Prop :=
  Requirements hash inputs normalized ∧ interpret? hash inputs normalized.term = some value

@[simp] theorem interpret_constant (hash : Hash) (inputs : Assignment) (value : Nat) :
    interpret? hash inputs (.constant value) = some (scalar value) := by simp [interpret?]

@[simp] theorem interpret_input (hash : Hash) (inputs : Assignment) (name : String) :
    interpret? hash inputs (.input name) = some (inputs name) := by simp [interpret?]

@[simp] theorem interpret_bytes (hash : Hash) (inputs : Assignment) (values : List Term) :
    interpret? hash inputs (.bytes values) = none := by simp [interpret?]

@[simp] theorem supported_add (hash : Hash) (inputs : Assignment) (left right : Term)
    (leftSupported : Supported hash inputs left) (rightSupported : Supported hash inputs right) :
    Supported hash inputs (.binary "add" left right) := by
  rcases leftSupported with ⟨leftValue, leftMeaning⟩
  rcases rightSupported with ⟨rightValue, rightMeaning⟩
  refine ⟨scalar (leftValue.val + rightValue.val), ?_⟩
  simp [interpret?, leftMeaning, rightMeaning]

theorem represents_constant (hash : Hash) (inputs : Assignment) (value : Nat) :
    Represents hash inputs {term := .constant value} (scalar value) := by
  constructor
  · simp [Requirements]
  · simp

/-- The old Native literal case uses the production normalizer and evaluator,
then discharges its result through the partial scalar relation. -/
theorem native_literal_normalization_sound (ctx : EvalContext) (hash : Hash)
    (inputs : Assignment) (aliases : AliasEnvironment) (value : Nat)
    (contextBound : value < ctx.modulus) (fieldBound : value < Field.modulus) :
    (value < Field.modulus ∧ Expr.eval ctx ([] : EvalEnv) (.native value) = .ok value) ∧
      ∃ normalized, Backend.Native.normalize aliases (.native value) = .ok normalized ∧
        Represents hash inputs normalized (scalar value) := by
  have normal : Backend.Native.normalize aliases (.native value) =
      .ok ({term := .constant value} : Normalized) := by
    simp [Backend.Native.normalize, pure, Except.pure]
  refine ⟨⟨fieldBound, ?_⟩, ⟨{term := .constant value}, normal, ?_⟩⟩
  · simp [Expr.eval, contextBound, pure, Except.pure]
  · exact represents_constant hash inputs value

theorem requirements_join (hash : Hash) (inputs : Assignment)
    (left right : Normalized) (term : Term)
    (leftRequirements : Requirements hash inputs left)
    (rightRequirements : Requirements hash inputs right) :
    Requirements hash inputs
      {term := term, bounds := left.bounds ++ right.bounds,
        assertions := left.assertions ++ right.assertions} := by
  constructor
  · intro requirement member
    rcases List.mem_append.mp member with member | member
    · exact leftRequirements.1 requirement member
    · exact rightRequirements.1 requirement member
  · intro assertion member
    rcases List.mem_append.mp member with member | member
    · exact leftRequirements.2 assertion member
    · exact rightRequirements.2 assertion member

end Noctium.Verification.ScalarTermMeaning
