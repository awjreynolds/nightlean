import Noctium.Types.ValueSchema

namespace Noctium.Types.MerklePath

open Noctium

/-- Compact's canonical nominal declaration for one field-valued Merkle digest. -/
def digestId : DeclId := "MerkleTreeDigest"

/-- Compact's canonical nominal declaration for one Merkle path step. -/
def pathEntryId : DeclId := "MerkleTreePathEntry"

def digestDeclaration : StructDecl := {
  id := digestId
  fields := [{name := "field", type := .scalar .native}]
}

def pathEntryDeclaration : StructDecl := {
  id := pathEntryId
  fields := [
    {name := "sibling", type := .structure digestId},
    {name := "goes_left", type := .scalar .bool}
  ]
}

/-- Build a fixed-size Compact-compatible path structure. The environment includes
the canonical nested digest and path-entry declarations, while preserving caller
declarations for the leaf type. -/
def environment (base : CompositeEnv) (pathId : DeclId) (leaf : CompositeType)
    (depth : Nat) : CompositeEnv :=
  let pathDeclaration : StructDecl := {
    id := pathId
    fields := [
      {name := "leaf", type := leaf},
      {name := "path", type := .vector depth (.structure pathEntryId)}
    ]
  }
  {
    structures := (base.structures ++ [digestDeclaration, pathEntryDeclaration, pathDeclaration]).eraseDups
    enumerations := base.enumerations
  }

def digestType : CompositeType := .structure digestId

def pathEntryType : CompositeType := .structure pathEntryId

def pathType (pathId : DeclId) : CompositeType := .structure pathId

def digestValue (field : Nat) : AggregateValue :=
  .structure digestId [("field", .scalar .native field)]

def pathEntryValue (sibling : Nat) (goesLeft : Bool) : AggregateValue :=
  .structure pathEntryId [
    ("sibling", digestValue sibling),
    ("goes_left", .scalar .bool (if goesLeft then 1 else 0))
  ]

def pathValue (pathId : DeclId) (leaf : AggregateValue)
    (entries : List AggregateValue) : AggregateValue :=
  .structure pathId [("leaf", leaf), ("path", .vector entries)]

end Noctium.Types.MerklePath
