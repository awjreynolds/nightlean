import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit standaloneMintInputs where
  public domain : Bytes32
  private amount : UInt 64
  public enabled : Bool
  public addSecond : Bool
end

noctium_contract NativeStandaloneMints where
  entry record uses standaloneMintInputs where
    when enabled mintShielded(domain, disclose(amount))
    when addSecond mintShielded(domain, 2)
    when enabled mintUnshielded(domain, disclose(amount))
    when addSecond mintUnshielded(domain, 2)
  end
end

private def standaloneMintDomain : List Nat := List.range 32

private def standaloneMintContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

private def standaloneMintArgs (amount : Nat) (enabled addSecond : _root_.Bool) : EvalEnv := [
  ("domain", .bytes 32 standaloneMintDomain),
  ("amount", .uint (2 ^ 64 - 1) amount),
  ("enabled", .bool enabled),
  ("addSecond", .bool addSecond)
]

private def runStandaloneMint (amount : Nat) (enabled addSecond : _root_.Bool)
    (state : LedgerState := {}) : Except String (EvalEnv × LedgerState) := do
  let some operation := NativeStandaloneMints.entrypoints.find? (·.name == "record")
    | throw "missing standalone mint entrypoint"
  operation.run standaloneMintContext (standaloneMintArgs amount enabled addSecond) state

#guard
  let otherDomain := List.replicate 32 9
  let initial : LedgerState := {
    shieldedMints := [(standaloneMintDomain, 3), (otherDomain, 4)]
    unshieldedMints := [(standaloneMintDomain, 5)]
  }
  match runStandaloneMint 17 Bool.true Bool.true initial with
  | .ok (_, state) =>
    state.shieldedMints == [(standaloneMintDomain, 22), (otherDomain, 4)] &&
    state.unshieldedMints == [(standaloneMintDomain, 24)]
  | .error _ => Bool.false

#guard match runStandaloneMint 19 Bool.false Bool.false {
    shieldedMints := [(standaloneMintDomain, 3)]
    unshieldedMints := [(standaloneMintDomain, 5)]
  } with
  | .ok (_, state) =>
    state.shieldedMints == [(standaloneMintDomain, 3)] &&
    state.unshieldedMints == [(standaloneMintDomain, 5)]
  | .error _ => Bool.false

#guard match runStandaloneMint (2 ^ 64 - 1) Bool.true Bool.false with
  | .ok (_, state) =>
    state.shieldedMints == [(standaloneMintDomain, 2 ^ 64 - 1)] &&
    state.unshieldedMints == [(standaloneMintDomain, 2 ^ 64 - 1)]
  | .error _ => Bool.false

#guard match runStandaloneMint (2 ^ 64 - 1) Bool.true Bool.true with
  | .error message => message.contains "UInt64 sum"
  | .ok _ => Bool.false

private def privateMintEntrypoint (shielded : _root_.Bool) : Entrypoint := {
  name := "privateMintAmount"
  circuit := {name := "privateMintAmount", inputs := [
    {name := "domain", ty := .bytes 32, visibility := .public},
    {name := "amount", ty := .uint (2 ^ 64 - 1), visibility := .private}
  ]}
  effects := [if shielded then
    .mintShielded (.ref "domain") (.ref "amount")
  else
    .mintUnshielded (.ref "domain") (.ref "amount")]
}

#guard match Disclosure.entrypoint (privateMintEntrypoint Bool.true) with
  | .error diagnostic => diagnostic.message.contains "public shielded mint"
  | .ok _ => Bool.false

#guard match Disclosure.entrypoint (privateMintEntrypoint Bool.false) with
  | .error diagnostic => diagnostic.message.contains "public unshielded mint"
  | .ok _ => Bool.false
