import Nightlean.Frontend
import Nightlean.Semantics

open Lean Elab Command

-- Keep the checked grammar and elaborators shared with the compatibility namespace.
run_cmd do
  let state := Lean.Parser.parserExtension.ext.getState (← getEnv)
  let some entries := state.scopedEntries.map.find? `Nightlean
    | throwError "Noctium frontend could not load its source grammar"
  for entry in entries do
    modifyEnv fun env => Lean.Parser.parserExtension.addScopedEntry env `Noctium entry

namespace Noctium
open Nightlean
open scoped Nightlean

export Nightlean (Ty Expr Circuit Contract Entrypoint Input Output Visibility SourceSpan
  Capabilities StateDecl StateKind LedgerValueType PathKey Effect Value EvalContext
  LedgerState LedgerValue)

namespace Field
export Nightlean.Field (modulus)
end Field

scoped macro "noctium_circuit" name:ident "where" stmts:nlcstmt* "end" : command =>
  `(nightlean_circuit $name where $stmts* end)

scoped macro "noctium_contract" name:ident "where" states:nlstate* entries:nlentry* "end" : command =>
  `(nightlean_contract $name where $states:nlstate* $entries:nlentry* end)

scoped macro "noctium_helper_circuit" name:ident "from" source:ident "entry" entryName:str : command =>
  `(nightlean_helper_circuit $name from $source entry $entryName)

scoped macro "noctium_generic_circuit" name:ident "from" source:ident "entry" entryName:str : command =>
  `(nightlean_generic_circuit $name from $source entry $entryName)

scoped macro "noctium_component_circuit" name:ident "from" source:ident "entry" entryName:str : command =>
  `(nightlean_component_circuit $name from $source entry $entryName)

scoped macro "noctium_control" name:ident "from" source:ident "entry" entryName:str : command =>
  `(nightlean_control $name from $source entry $entryName)

scoped macro "noctium_witness_circuit" name:ident "from" source:ident "entry" entryName:str : command =>
  `(nightlean_witness_circuit $name from $source entry $entryName)

scoped macro "noctium_module" "from" source:ident : command =>
  `(nightlean_module from $source)

scoped macro "noctium_module_contract" name:ident "from" source:ident : command =>
  `(nightlean_module_contract $name from $source)

end Noctium
