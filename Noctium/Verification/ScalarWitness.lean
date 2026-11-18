import Noctium.Verification.NativeRelation

namespace Noctium.Verification.ScalarWitness

open NativeRelation

def assign (witness : Assignment) (name : String) (value : Scalar) : Assignment :=
  fun found => if found = name then value else witness found

@[simp] theorem assign_same (witness : Assignment) (name : String) (value : Scalar) :
    assign witness name value name = value := by simp [assign]

@[simp] theorem assign_other (witness : Assignment) (name found : String) (value : Scalar)
    (different : found ≠ name) : assign witness name value found = witness found := by
  simp [assign, different]

def OperandIndependent (name : String) : Operand → Prop
  | .immediate _ => True
  | .reference found => found ≠ name

@[simp] theorem Operand.read_assign (witness : Assignment) (name : String) (value : Scalar)
    (operand : Operand) (independent : OperandIndependent name operand) :
    operand.read (assign witness name value) = operand.read witness := by
  cases operand with
  | immediate _ => rfl
  | reference found =>
    have condition : ¬(found = name) := fun equal => independent equal
    simp [Operand.read, assign, condition]

def operandIdentifiers : Operand → List String
  | .immediate _ => []
  | .reference name => [name]

@[simp] theorem Operand.read_assign_of_not_identifier (witness : Assignment) (name : String)
    (value : Scalar) (operand : Operand)
    (absent : name ∉ operandIdentifiers operand) :
    operand.read (assign witness name value) = operand.read witness := by
  cases operand with
  | immediate _ => rfl
  | reference reference =>
    simp only [operandIdentifiers, List.mem_singleton] at absent
    exact Operand.read_assign witness name value _ (fun equal => absent equal.symm)

def instructionIdentifiers : Instruction → List String
  | .input _ name => [name]
  | .boolean value | .bits value _ => operandIdentifiers value
  | .lessThan left right _ output | .add left right output | .mul left right output
  | .testEq left right output => operandIdentifiers left ++ operandIdentifiers right ++ [output]
  | .neg value output | .not value output => operandIdentifiers value ++ [output]
  | .equal left right => operandIdentifiers left ++ operandIdentifiers right
  | .select condition yes no output =>
    operandIdentifiers condition ++ operandIdentifiers yes ++ operandIdentifiers no ++ [output]
  | .hash values output => values.flatMap operandIdentifiers ++ [output]
  | .assert condition => operandIdentifiers condition
  | .impact guard values => operandIdentifiers guard ++ values.flatMap operandIdentifiers
  | .output values => values.flatMap operandIdentifiers

def InstructionIndependent (name : String) (instruction : Instruction) : Prop :=
  name ∉ instructionIdentifiers instruction

theorem Instruction.Holds.assign_frame (hash : Hash) (witness : Assignment)
    (name : String) (value : Scalar) (instruction : Instruction)
    (independent : InstructionIndependent name instruction) :
    Instruction.Holds hash (assign witness name value) instruction ↔
      Instruction.Holds hash witness instruction := by
  cases instruction with
  | input visibility output => simp [Instruction.Holds]
  | boolean operand =>
    have noOperand : name ∉ operandIdentifiers operand := by
      change name ∉ operandIdentifiers operand at independent
      exact independent
    simp [Instruction.Holds, Operand.read_assign_of_not_identifier, noOperand]
  | bits operand width =>
    have noOperand : name ∉ operandIdentifiers operand := by
      change name ∉ operandIdentifiers operand at independent
      exact independent
    simp [Instruction.Holds, Operand.read_assign_of_not_identifier, noOperand]
  | lessThan left right width output
  | add left right output
  | mul left right output
  | testEq left right output =>
    have noLeft : name ∉ operandIdentifiers left := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    have noRight : name ∉ operandIdentifiers right := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    have noOutput : output ≠ name := by
      intro same
      apply independent
      subst output
      simp [instructionIdentifiers]
    simp [Instruction.Holds, Operand.read_assign_of_not_identifier, noLeft, noRight,
      assign_other, noOutput]
  | neg operand output
  | not operand output =>
    have noOperand : name ∉ operandIdentifiers operand := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    have noOutput : output ≠ name := by
      intro same
      apply independent
      subst output
      simp [instructionIdentifiers]
    simp [Instruction.Holds, Operand.read_assign_of_not_identifier, noOperand,
      assign_other, noOutput]
  | equal left right =>
    have noLeft : name ∉ operandIdentifiers left := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    have noRight : name ∉ operandIdentifiers right := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    simp [Instruction.Holds, Operand.read_assign_of_not_identifier, noLeft, noRight]
  | select condition yes no output =>
    have noCondition : name ∉ operandIdentifiers condition := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    have noYes : name ∉ operandIdentifiers yes := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    have noNo : name ∉ operandIdentifiers no := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    have noOutput : output ≠ name := by
      intro same
      apply independent
      subst output
      simp [instructionIdentifiers]
    simp [Instruction.Holds, Operand.read_assign_of_not_identifier, noCondition, noYes,
      noNo, assign_other, noOutput]
  | hash operands output =>
    have noOutput : output ≠ name := by
      intro same
      apply independent
      subst output
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have noOperands : ∀ operand ∈ operands, name ∉ operandIdentifiers operand := by
      intro operand member used
      apply independent
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨operand, member, used⟩)
    have stable : operands.map (fun operand => operand.read (assign witness name value)) =
        operands.map (fun operand => operand.read witness) := by
      apply List.map_congr_left
      intro operand member
      exact Operand.read_assign_of_not_identifier witness name value operand
        (noOperands operand member)
    simp [Instruction.Holds, assign_other, noOutput, stable]
  | assert operand =>
    have noOperand : name ∉ operandIdentifiers operand := by
      change name ∉ operandIdentifiers operand at independent
      exact independent
    simp [Instruction.Holds, Operand.read_assign_of_not_identifier, noOperand]
  | impact guard operands =>
    have noGuard : name ∉ operandIdentifiers guard := by
      intro member
      apply independent
      simp [instructionIdentifiers, member]
    simp [Instruction.Holds, Operand.read_assign_of_not_identifier, noGuard]
  | output operands => simp [Instruction.Holds]

end Noctium.Verification.ScalarWitness
