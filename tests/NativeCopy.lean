import Noctium.Frontend
import Noctium.Semantics

open scoped Noctium

noctium_circuit copyInput where
  private amount : Native
  private payload : Bytes32
  public enabled : Bool
  public expected : Native
  let copied : Native := copyValue(amount)
  assert eq(copied, expected)
  assert eq(copyValue(secp256k1Base(2)), secp256k1Base(2))
  output released : Native := disclose(copied)
end

noctium_contract NativeCopy where
  cell stored : Native
  entry store uses copyInput where
    if copyValue(enabled) then {
      write stored := released
    } else {}
    return copiedByte : UInt 8 := disclose(copyValue(byteAt(copyValue(payload), 31)))
    return copiedEnabled : Bool := copyValue(enabled)
  end
end

example (ctx : Noctium.EvalContext) (env : Noctium.EvalEnv) (value : Noctium.Expr ty) :
    (Noctium.Expr.copyValue value).eval ctx env = value.eval ctx env := by
  simp only [Noctium.Expr.eval]

#guard !(Noctium.Disclosure.circuit {
  name := "undisclosedCopy"
  inputs := [{name := "secret", ty := .native, visibility := .private}]
  outputs := [{name := "result", ty := .native, value := .copyValue (.ref "secret")}]
}).isOk
