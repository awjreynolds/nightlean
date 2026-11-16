import Nightlean.Frontend
open scoped Nightlean

nightlean_circuit boundedRelation where
  public expected : UIntRange 511
  private left : UInt 8
  private right : UInt 8
  let sum : UIntRange 511 := add(left, right)
  assert eq(sum, expected)
  output result : UIntRange 511 := expected
end

nightlean_contract BoundedScalars where
  cell total : UIntRange 511
  entry apply uses boundedRelation where
    read total as old
    require eq(old, 0)
    write total := result
  end
end
