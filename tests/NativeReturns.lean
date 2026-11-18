import Noctium.Frontend

open scoped Noctium

noctium_circuit returnInput where
  private amount : Native
  public enabled : Bool
end

noctium_contract NativeReturns where
  cell balance : Native
  counter count
  entry readValues uses returnInput where
    read balance as currentBalance
    read count as currentCount
    return balanceValue : Native := currentBalance
    return countValue : UInt 64 := currentCount
    return enabledValue : Bool := enabled
  end
  entry advance uses returnInput arguments [amount] where
    read balance as beforeBalance
    write balance := disclose(add(beforeBalance, amount))
    increment count by 1
    read balance as afterBalance
    read count as afterCount
    return balanceValue : Native := afterBalance
    return countValue : UInt 64 := afterCount
    return enabledValue : Bool := enabled
  end
end

private def nativeReturnsEntry (name : String) : Noctium.Entrypoint :=
  match NativeReturns.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def nativeReturnsPrivateLeak : Noctium.Entrypoint :=
  let ep := nativeReturnsEntry "readValues"
  let leaked : Noctium.Output :=
    {name := "leaked", ty := .native,
      value := (.ref "amount" : Noctium.Expr .native)}
  {ep with returns := [leaked]}

#guard match Noctium.Disclosure.entrypoint
    nativeReturnsPrivateLeak with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def callArgumentSchema (names : List String) (visibility : Noctium.Visibility := .private)
    (ty : Noctium.Ty := .native) : Except Noctium.Diagnostic Unit :=
  ({name := "arguments", circuit := {name := "arguments", inputs := [
      {name := "value", ty, visibility}]}, callInputs := names} : Noctium.Entrypoint).validate
    Noctium.Capabilities.crypto []

#guard (callArgumentSchema ["value"]).isOk
#guard !(callArgumentSchema ["missing"]).isOk
#guard !(callArgumentSchema ["value", "value"]).isOk
#guard !(callArgumentSchema ["value"] .public).isOk
#guard !(callArgumentSchema ["value"] .private (.uint 7)).isOk
