import Nightlean.Witness

open Nightlean Nightlean.Helpers

namespace WitnessDisclosure

private def disclosureFailure (result : Except Diagnostic α) : Bool :=
  match result with
  | .ok _ => false
  | .error diagnostic => (diagnostic.message.splitOn "undisclosed private").length > 1

def direct : Program := {
  witnesses := [
    {name := "flag", operation := "noctium.flag.v1", capability := "flag",
      result := .scalar .bool}]
  declarations := [
    {id := ⟨0, 0⟩, name := "root", result := .scalar .bool,
      body := [.return (some (.witnessCall "flag-result" "flag" []))]}]
  exports := [{name := "root", target := ⟨0, 0⟩}]
}

#guard disclosureFailure (Control.compileTypedWithLimits {} direct "root")
#guard !(Witness.compile direct "root").isOk

def disclosed : Program := {direct with declarations := [
  {id := ⟨0, 0⟩, name := "root", result := .scalar .bool,
    body := [.return (some (.disclose {} (.witnessCall "flag-result" "flag" [])))]}]}

#guard (Witness.compile disclosed "root").isOk

def throughHelper : Program := {
  direct with
  declarations := direct.declarations ++ [
    {id := ⟨0, 1⟩, name := "publicRoot", result := .scalar .bool,
      body := [.return (some (.call "root" []))]}]
  exports := [{name := "root", target := ⟨0, 1⟩}]
}

#guard disclosureFailure (Control.compileTypedWithLimits {} throughHelper "root")
#guard !(Witness.compile throughHelper "root").isOk

def guardProgram (condition : Term) : Program := {direct with declarations := [
  {id := ⟨0, 0⟩, name := "root", result := .scalar .bool,
    body := [.branch condition [.return (some (.bool true))] [.return (some (.bool false))]]}]}

-- Disclosing constants inside the branch does not disclose its private guard.
def constantsDisclosed : Program := {direct with declarations := [
  {id := ⟨0, 0⟩, name := "root", result := .scalar .bool,
    body := [.branch (.witnessCall "flag-condition" "flag" [])
      [.return (some (.disclose {} (.bool true)))]
      [.return (some (.disclose {} (.bool false)))]]}]}

#guard disclosureFailure (Control.compileTypedWithLimits {} constantsDisclosed "root")
#guard disclosureFailure (Control.compileTypedWithLimits {} (guardProgram
  (.witnessCall "flag-condition" "flag" [])) "root")

-- The host execution plan admits an explicitly disclosed guard. Native guarded
-- execution has a separate backend gate, so this is not a ledger proof claim.
#guard (Control.compileTypedWithLimits {} (guardProgram
  (.disclose {} (.witnessCall "flag-condition" "flag" []))) "root").isOk

end WitnessDisclosure
