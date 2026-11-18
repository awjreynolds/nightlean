import Noctium.Semantics

namespace Noctium.Claim

/-- These tags are versioned application choices, not Midnight protocol constants. -/
structure Domains where
  leaf : Nat := 1
  node : Nat := 2
  nullifier : Nat := 3
  deriving Repr, BEq

def Domains.validate (d : Domains) : Except String Unit := do
  for value in [d.leaf, d.node, d.nullifier] do
    discard (Field.encode value)
  if d.leaf == d.node || d.leaf == d.nullifier || d.node == d.nullifier then
    throw "claim hash domains must be distinct"

/-- maxDepth is a compiler resource bound, independent of ledger tree types.
The initial tree AST lowerer duplicates subexpressions, so its default bound is
small. A DAG lowerer should qualify larger values before profiles raise it. -/
structure Config where
  depth : Nat := 2
  maxDepth : Nat := 8
  domains : Domains := {}
  deriving Repr

def Config.validate (c : Config) : Except String Unit := do
  c.domains.validate
  if c.depth == 0 then throw "claim Merkle depth must be positive"
  if c.depth > c.maxDepth then throw "claim Merkle depth exceeds compiler profile bound"

private def nativeInput (name : String) (visibility : Visibility) : Input :=
  {name, ty := .native, visibility}

private def boolInput (name : String) (visibility : Visibility) : Input :=
  {name, ty := .bool, visibility}

/-- A binary Merkle parent. direction=true places the sibling on the left. -/
def parent (domain : Nat) (current sibling : Expr .native) (direction : Expr .bool) : Expr .native :=
  .poseidon2 domain (.select direction sibling current) (.select direction current sibling)

/-- Build a fixed-depth path from generic expressions, without claim-specific IR. -/
def merkleRoot (nodeDomain : Nat) (leaf : Expr .native) (depth : Nat) : Expr .native :=
  (List.range depth).foldl (fun current level =>
    parent nodeDomain current (.ref s!"sibling{level}") (.ref s!"direction{level}")) leaf

def relation (c : Config := {}) : Except String Circuit := do
  c.validate
  let publicInputs := [nativeInput "root" .«public», nativeInput "campaign" .«public»,
    nativeInput "suppliedNullifier" .«public»]
  let pathInputs := (List.range c.depth).map fun level => nativeInput s!"sibling{level}" .«private»
  let directions := (List.range c.depth).map fun level => boolInput s!"direction{level}" .«private»
  let leaf := Expr.poseidon2 c.domains.leaf (.ref "secret") (.ref "campaign")
  let computedRoot := merkleRoot c.domains.node leaf c.depth
  let computedNullifier := Expr.poseidon2 c.domains.nullifier (.ref "secret") (.ref "campaign")
  pure {
    name := "claimRelation"
    inputs := publicInputs ++ [nativeInput "secret" .«private»] ++ pathInputs ++ directions
    constraints := [.eq computedRoot (.ref "root"), .eq computedNullifier (.ref "suppliedNullifier")]
    outputs := [⟨"nullifier", .native, .ref "suppliedNullifier", {}⟩]
  }

def contract (c : Config := {}) : Except String Contract := do
  let circuit ← relation c
  pure {
    name := "PrivateClaim"
    state := [{name := "acceptedRoot", kind := .cell .native},
      {name := "campaignId", kind := .cell .native},
      {name := "spent", kind := .map .native .bool}]
    entrypoints := [{
      name := "claim"
      circuit
      effects := [
        .readCell "acceptedRoot" "storedRoot" .native,
        .require (.eq (.ref "storedRoot" : Expr .native) (.ref "root")),
        .readCell "campaignId" "storedCampaign" .native,
        .require (.eq (.ref "storedCampaign" : Expr .native) (.ref "campaign")),
        .requireAbsent "spent" .native (.ref "nullifier"),
        .writeMap "spent" .native .bool (.ref "nullifier") (.bool true)]
    }]
  }

/-- Initial public state is explicit and canonically encoded. -/
def initialState (root campaign : Nat) : Except String LedgerState := do
  discard (Field.encode root)
  discard (Field.encode campaign)
  pure {
    cells := [("acceptedRoot", .native root), ("campaignId", .native campaign)]
    maps := [("spent", [])]
  }

/-- A policy-level spent-set model. No cryptographic assumptions enter this guard. -/
def markSpent (nullifier : Nat) (entries : List (Value × Value)) : List (Value × Value) :=
  (.native nullifier, .bool true) :: entries.filter (fun entry => entry.1 != .native nullifier)

def isSpent (nullifier : Nat) (entries : List (Value × Value)) : Bool :=
  (entries.lookup (.native nullifier)).isSome

/-- Recording a successful claim makes its nullifier unavailable for replay,
independently of the hash oracle and other previously spent nullifiers. -/
theorem marked_isSpent (nullifier : Nat) (entries : List (Value × Value)) :
    isSpent nullifier (markSpent nullifier entries) = true := by
  have selfEq : (Value.native nullifier == Value.native nullifier) = true := by
    change (nullifier == nullifier) = true
    simp
  simp [isSpent, markSpent, List.lookup, selfEq]

end Noctium.Claim
