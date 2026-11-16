import Nightlean.Frontend
open scoped Nightlean
open Nightlean.Helpers

/-- Source authoring uses typed declarations, lexical identities and forward calls. -/
def helperScalarProgram : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "relation", parameters := [⟨"expected", .native⟩, ⟨"secret", .native⟩]
     result := .scalar .native
     body := [
       .bind "squared" (.scalar .native) (.call "square" [.ref "secret"]),
       .assert (.eq (.ref "squared") (.ref "expected")),
       .return (some (.ref "expected"))]},
    {id := ⟨0, 1⟩, name := "square", parameters := [⟨"value", .native⟩]
     result := .scalar .native, declaredPure := Bool.true
     body := [.return (some (.binary .mul (.ref "value") (.ref "value")))]}]
  exports := [{name := "scalar", target := ⟨0, 0⟩, inputs := [
    {name := "expected", ty := .native, visibility := .public},
    {name := "secret", ty := .native, visibility := .private}]}]
}

nightlean_helper_circuit helperComposed from helperScalarProgram entry "scalar"

nightlean_circuit helperDirect where
  public expected : Native
  private secret : Native
  assert eq(mul(secret, secret), expected)
  output result : Native := expected
end

nightlean_contract HelperContract where
  cell value : Native
  entry apply uses helperComposed where
    write value := result
  end
end

#guard helperComposed.name == "helperComposed"
#guard helperComposed.inputs.length == 2
#guard HelperContract.entrypoints.length == 1
