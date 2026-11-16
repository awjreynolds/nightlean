import Nightlean.Field
import Nightlean.Semantics

namespace Nightlean.Verification.NativeRelation

/-- Canonical BLS12-381 scalar values. Malformed external encodings are outside
this typed relation and require separate decoder/ABI qualification. -/
abbrev Scalar := Fin Field.modulus

def scalar (n : Nat) : Scalar := ⟨n % Field.modulus, Nat.mod_lt _ (by decide)⟩
def zero : Scalar := ⟨0, by decide⟩
def one : Scalar := ⟨1, by decide⟩
def bit (b : _root_.Bool) : Scalar := if b then one else zero

theorem zero_ne_one : zero ≠ one := by decide

theorem bit_canonical (b : _root_.Bool) : (bit b).val = 0 ∨ (bit b).val = 1 := by
  cases b <;> simp [bit, zero, one]

abbrev Assignment := String → Scalar
abbrev Hash := List Scalar → Scalar

inductive Operand where
  | immediate (value : Scalar)
  | reference (name : String)
  deriving Repr, DecidableEq

def Operand.read (witness : Assignment) : Operand → Scalar
  | .immediate value => value
  | .reference name => witness name

inductive Instruction where
  | input (visibility : Visibility) (output : String)
  | boolean (value : Operand)
  | add (a b : Operand) (output : String)
  | mul (a b : Operand) (output : String)
  | neg (a : Operand) (output : String)
  | equal (a b : Operand)
  | testEq (a b : Operand) (output : String)
  | not (a : Operand) (output : String)
  | select (condition a b : Operand) (output : String)
  | hash (inputs : List Operand) (output : String)
  | assert (condition : Operand)
  | impact (guard : Operand) (inputs : List Operand)
  | output (values : List Operand)
  deriving Repr, DecidableEq

/-- Independent field-level instruction constraints. A witness is an arbitrary
assignment, never defined as the output of the source or compiler evaluator. -/
def Instruction.Holds (hash : Hash) (witness : Assignment) : Instruction → Prop
  | .input _ _ => True
  | .boolean value => value.read witness = zero ∨ value.read witness = one
  | .add a b destination => witness destination = scalar ((a.read witness).val + (b.read witness).val)
  | .mul a b destination => witness destination = scalar ((a.read witness).val * (b.read witness).val)
  | .neg a destination => witness destination = scalar (Field.modulus - (a.read witness).val)
  | .equal a b => a.read witness = b.read witness
  | .testEq a b destination => witness destination = bit (decide (a.read witness = b.read witness))
  | .not a destination =>
    (a.read witness = zero ∨ a.read witness = one) ∧
      witness destination = if a.read witness = zero then one else zero
  | .select condition a b destination =>
    (condition.read witness = zero ∨ condition.read witness = one) ∧
      witness destination = if condition.read witness = one then a.read witness else b.read witness
  | .hash values destination => witness destination = hash (values.map (·.read witness))
  | .assert condition => condition.read witness ≠ zero
  | .impact guard _ => guard.read witness = one
  | .output _ => True

structure Program where
  instructions : List Instruction
  outputArity : Nat
  communicationsCommitment : _root_.Bool
  deriving Repr, DecidableEq

/-- Ordered Impact groups are observations, not a model of ledger execution. -/
def Program.groups (program : Program) (witness : Assignment) : List (List Scalar) :=
  program.instructions.filterMap fun instruction => match instruction with
    | .impact _ values => some (values.map (·.read witness))
    | _ => none

def Program.returns (program : Program) (witness : Assignment) : List Scalar :=
  program.instructions.flatMap fun instruction => match instruction with
    | .output values => values.map (·.read witness)
    | _ => []

structure InputStreams where
  publicValues : List Scalar
  privateValues : List Scalar

def Program.inputValues (program : Program) (visibility : Visibility) (witness : Assignment) : List Scalar :=
  program.instructions.filterMap fun instruction => match instruction with
    | .input found destination => if found == visibility then some (witness destination) else none
    | _ => none

/-- The native circuit relation binds ordered input streams and public Impact
values. Standalone Output does not add an authenticated public instance. -/
structure CircuitSatisfies (hash : Hash) (program : Program) (streams : InputStreams) (witness : Assignment)
    (publicGroups : List (List Scalar)) : Prop where
  instructions : ∀ instruction ∈ program.instructions, instruction.Holds hash witness
  publicInputs : program.inputValues .«public» witness = streams.publicValues
  privateInputs : program.inputValues .«private» witness = streams.privateValues
  groups : program.groups witness = publicGroups

/-- Add the host's output observation to circuit satisfaction. This observation
alone carries no authentication guarantee. Public binding needs an Impact group
or a separately qualified communications commitment. -/
structure Satisfies (hash : Hash) (program : Program) (streams : InputStreams) (witness : Assignment)
    (publicGroups : List (List Scalar)) (returns : List Scalar) : Prop where
  instructions : ∀ instruction ∈ program.instructions, instruction.Holds hash witness
  publicInputs : program.inputValues .«public» witness = streams.publicValues
  privateInputs : program.inputValues .«private» witness = streams.privateValues
  groups : program.groups witness = publicGroups
  outputs : program.returns witness = returns

theorem CircuitSatisfies.withObservedReturns {hash : Hash} {program : Program} {streams : InputStreams}
    {witness : Assignment} {publicGroups : List (List Scalar)}
    (sat : CircuitSatisfies hash program streams witness publicGroups) :
    Satisfies hash program streams witness publicGroups (program.returns witness) :=
  ⟨sat.instructions, sat.publicInputs, sat.privateInputs, sat.groups, rfl⟩

theorem Satisfies.circuit {hash : Hash} {program : Program} {streams : InputStreams}
    {witness : Assignment} {publicGroups : List (List Scalar)} {returns : List Scalar}
    (sat : Satisfies hash program streams witness publicGroups returns) :
    CircuitSatisfies hash program streams witness publicGroups :=
  ⟨sat.instructions, sat.publicInputs, sat.privateInputs, sat.groups⟩

/-- Separate implementation agreement. This states the hash function's field
semantics, and assumes neither compiler correctness nor source acceptance. -/
structure HashAgreement (ctx : EvalContext) (hash : Hash) : Prop where
  modulus : ctx.modulus = Field.modulus
  calls : ∀ domain left right : Scalar,
    ctx.poseidon2 domain.val left.val right.val = .ok (hash [domain, left, right]).val

theorem test_eq_assert_sound (a b result : Scalar)
    (test : result = bit (decide (a = b))) (assertion : result ≠ zero) : a = b := by
  by_cases equal : a = b
  · exact equal
  · simp only [equal, decide_false, bit, Bool.false_eq_true, zero] at test
    exact False.elim (assertion test)

theorem scalar_canonical (n : Nat) : (scalar n).val < Field.modulus := (scalar n).isLt

theorem scalar_no_wrap (n : Nat) (bound : n < Field.modulus) : (scalar n).val = n :=
  Nat.mod_eq_of_lt bound

end Nightlean.Verification.NativeRelation
