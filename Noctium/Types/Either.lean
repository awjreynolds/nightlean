import Noctium.Types.ValueSchema

namespace Noctium.Types.Either

open Noctium

private def scalarSuffix (payloadType : Ty) : Except String String := do
  match payloadType with
  | .native => pure "Native"
  | .bool => pure "Bool"
  | .uint maximum => do
    ScalarPolicy.validate (.uint maximum)
    let bits := maximum.log2 + 1
    if maximum + 1 == 2 ^ bits then
      pure s!"UInt{bits}"
    else
      pure s!"UIntRange{maximum + 1}"
  | _ => throw "Either payloads must be Native, Bool, or UInt scalars"

/-- A stable nominal name for a scalar `Either<L, R>` return schema. -/
def scalarTypeId (contractName : String) (leftType rightType : Ty) : Except String DeclId := do
  let leftSuffix ← scalarSuffix leftType
  let rightSuffix ← scalarSuffix rightType
  let id := s!"{contractName}.EitherLeft{leftSuffix}Right{rightSuffix}"
  unless validDeclId id do throw "invalid scalar Either type id"
  pure id

/-- Compact scalar Either records always order fields as `is_left`, `left`, `right`. -/
def scalarFieldTypes (leftType rightType : Ty) : Except String (List (String × Ty)) := do
  discard (scalarSuffix leftType)
  discard (scalarSuffix rightType)
  pure [("is_left", .bool), ("left", leftType), ("right", rightType)]

def scalarEnvironment (id : DeclId) (leftType rightType : Ty) : Except String CompositeEnv := do
  unless validDeclId id do throw "invalid scalar Either type id"
  let fieldTypes ← scalarFieldTypes leftType rightType
  let environment : CompositeEnv := {
    structures := [{
      id
      fields := fieldTypes.map fun (name, ty) => {name, type := .scalar ty}
    }]
  }
  discard ((compileType environment (.structure id)).mapError (·.message))
  pure environment

def scalarType (id : DeclId) : CompositeType := .structure id

end Noctium.Types.Either
