import Nightlean.Backend.Compact
import Nightlean.Claim

open Nightlean
open Nightlean.Backend

private def contains (text needle : String) : Bool := (text.splitOn needle).length > 1
private def fixture : Except String Contract := Claim.contract {}

#guard match fixture >>= Compact.emit with
  | .ok source =>
    contains source "transientHash<Vector<3, Field>>([1 as Field" &&
    contains source "witness w_claim_secret(): Field;" &&
    contains source "constructor(init_acceptedRoot: Field, init_campaignId: Field)" &&
    contains source "const nl_input_root = disclose(nl_arg_root);" &&
    contains source "const nl_input_secret = w_claim_secret();" &&
    contains source "spent.insert(disclose(nl_output_nullifier), disclose(true));" &&
    contains source "return [nl_output_nullifier];" &&
    !contains source "disclose(nl_input_secret)"
  | _ => false
#guard match fixture with
  | .ok c => (Compact.witnessBindings c).map (·.providerName) ==
    ["w_claim_secret", "w_claim_sibling0", "w_claim_sibling1", "w_claim_direction0", "w_claim_direction1"]
  | _ => false
-- Reject source injection rather than escaping or passing through raw text.
#guard match fixture with
  | .ok c => match Compact.emit {c with name := "Bad; export circuit steal"} with
    | .error _ => true | _ => false
  | _ => false
#guard match fixture with
  | .ok c => match Compact.emit {c with state := [⟨"return", .cell .native, {}⟩]} with
    | .error _ => true | _ => false
  | _ => false
-- Witness material is unavailable in public ledger effects.
#guard match fixture with
  | .ok c => match c.entrypoints with
    | [entry] => match Compact.emit {c with entrypoints := [{entry with effects := [
        .writeCell "acceptedRoot" .native (.ref "secret")]}]} with
      | .error _ => true | _ => false
    | _ => false
  | _ => false
-- Map reads need a separately qualified adapter and fail explicitly for now.
#guard match fixture with
  | .ok c => match c.entrypoints with
    | [entry] => match Compact.emit {c with entrypoints := [{entry with effects := [
        .readMap "spent" "wasSpent" .native .bool (.ref "nullifier")]}]} with
      | .error message => contains message "does not yet qualify map reads"
      | _ => false
    | _ => false
  | _ => false
-- Ledger declarations and exported circuits share Compact's global namespace.
#guard match fixture with
  | .ok c => match c.entrypoints with
    | [entry] => match Compact.emit {c with entrypoints := [{entry with name := "spent"}]} with
      | .error message => contains message "global declaration name collision"
      | _ => false
    | _ => false
  | _ => false
