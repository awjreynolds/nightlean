import Noctium.Frontend
open scoped Noctium

noctium_circuit arithmeticRelation where
  public expected : Native
  private secret : Native
  let square : Native := mul(secret, secret)
  assert eq(square, expected)
  output result : Native := expected
end

noctium_contract ArithmeticContract where
  cell value : Native
  map seen : Native => Bool
  entry apply uses arithmeticRelation where
    read value as old
    require eq(old, expected)
    absent seen[result]
    insert seen[result] := true
  end
end

#guard arithmeticRelation.inputs.length == 2
#guard ArithmeticContract.entrypoints.length == 1

/-- error: unknown Noctium value 'missing' -/
#guard_msgs in
noctium_circuit unknownValue where
  output result : Native := missing
end

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit wrongType where
  public flag : Bool
  output result : Native := flag
end

/-- error: duplicate Noctium value 'same' -/
#guard_msgs in
noctium_circuit duplicateInput where
  public same : Native
  private same : Native
end

noctium_contract PrivateRelease where
  cell value : Native
  entry leak uses arithmeticRelation where
    write value := disclose(secret)
  end
end

/-- error: absent requires a declared state map -/
#guard_msgs in
noctium_contract WrongStateKind where
  cell value : Native
  entry leak uses arithmeticRelation where
    absent value[expected]
  end
end

#guard arithmeticRelation.inputs.map (·.visibility) == [Noctium.Visibility.public, Noctium.Visibility.private]
#guard arithmeticRelation.span.line == 4

/-- error: duplicate Noctium output 'value' -/
#guard_msgs in
noctium_circuit shadowInput where
  public value : Native
  output value : Native := value
end

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit wrongSelectCondition where
  public value : Native
  output result : Native := select(value, 1, 2)
end

namespace Qualified
noctium_circuit relation where
  public x : Native
  output result : Native := x
end
noctium_contract contractValue where
  entry invoke uses relation where
  end
end
#guard relation.name == "Qualified.relation"
#guard contractValue.name == "Qualified.contractValue"
end Qualified
