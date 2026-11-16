import Nightlean.Backend.Zkir

open Nightlean
open Nightlean.Backend.Zkir

def lowererFixture : Circuit := {
  name := "hash_claim_relation"
  inputs := [
    { name := "secret", ty := .native, visibility := .«private» },
    { name := "root", ty := .native, visibility := .«public» },
    { name := "direction", ty := .bool, visibility := .«private» }]
  constraints := [.eq
    (.poseidon2 256 (.select (.ref "direction") (.ref "secret") (.native 7)) (.native 0))
    (.ref "root")]
  outputs := [{name := "nullifier", ty := .native, value := .poseidon2 2 (.ref "secret") (.native 0)}]
}

def main : IO Unit := do
  unless fieldImmediate 0 == "0x00" && fieldImmediate 256 == "0x0001" do
    throw (IO.userError "noncanonical little-endian field immediate")
  let bad : Circuit := { name := "bad", constraints := [.eq (.ref "missing") (.native 0)] }
  match lowerCircuit bad with
  | .ok _ => throw (IO.userError "unknown reference accepted")
  | .error _ => pure ()
  let noncanonical : Circuit := { name := "noncanonical", constraints := [.eq (.native nativeModulus) (.native 0)] }
  match lowerCircuit noncanonical with
  | .ok _ => throw (IO.userError "noncanonical field constant accepted")
  | .error _ => pure ()
  let hash : Nightlean.Expr .native := .poseidon2 1 (.native 42) (.native 7)
  let shared : Circuit := { name := "shared", constraints := [.eq hash hash] }
  match lowerCircuit shared with
  | .error d => throw (IO.userError d.message)
  | .ok json =>
    unless (json.compress.splitOn "transient_hash").length == 2 do
      throw (IO.userError "shared hash was emitted more than once")
  match lowerCircuit lowererFixture with
  | .error d => throw (IO.userError d.message)
  | .ok json => IO.println json.compress
