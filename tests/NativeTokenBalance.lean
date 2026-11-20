import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit tokenBalanceInputs where
  public color : Bytes32
  public isUnshielded : Bool
  public limit : UInt 128
  public enabled : Bool
  public readExact : Bool
end

noctium_contract NativeTokenBalance where
  cell recorded : UInt 128
  entry inspect uses tokenBalanceInputs where
    when readExact tokenBalance(color, isUnshielded) as amount
    when enabled tokenBalanceLt(color, isUnshielded, limit) as below
    when enabled tokenBalanceGt(color, isUnshielded, limit) as above
    when readExact write recorded := amount
    return exactAmount : UInt 128 := amount
    return belowLimit : Bool := below
    return aboveLimit : Bool := above
  end
end

private def tokenBalanceContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
  unshieldedBalances := [(List.range 32, 17)]
  shieldedBalances := [(List.range 32, 23)]
}

private def tokenBalanceArgs (isUnshielded : _root_.Bool) (enabled readExact : _root_.Bool)
    (limit : Nat := 20) : EvalEnv := [
  ("color", .bytes 32 (List.range 32)),
  ("isUnshielded", .bool isUnshielded),
  ("limit", .uint balanceMaximum limit),
  ("enabled", .bool enabled),
  ("readExact", .bool readExact)
]

private def runTokenBalance (context : EvalContext) (args : EvalEnv) (state : LedgerState) :=
  match NativeTokenBalance.entrypoints with
  | ep :: _ => ep.run context args state
  | [] => Except.error "missing token-balance entrypoint"

#guard match runTokenBalance tokenBalanceContext (tokenBalanceArgs Bool.true Bool.true Bool.true) {
      cells := [("recorded", .uint balanceMaximum 99)]
    } with
  | .ok (outputs, state) => outputs == [
      ("exactAmount", .uint balanceMaximum 17),
      ("belowLimit", .bool Bool.true),
      ("aboveLimit", .bool Bool.false)
    ] && state.cells.lookup "recorded" == some (.uint balanceMaximum 17)
  | .error _ => Bool.false

#guard match runTokenBalance tokenBalanceContext (tokenBalanceArgs Bool.false Bool.true Bool.true) {
      cells := [("recorded", .uint balanceMaximum 99)]
    } with
  | .ok (outputs, state) => outputs == [
      ("exactAmount", .uint balanceMaximum 23),
      ("belowLimit", .bool Bool.false),
      ("aboveLimit", .bool Bool.true)
    ] && state.cells.lookup "recorded" == some (.uint balanceMaximum 23)
  | .error _ => Bool.false

#guard match runTokenBalance tokenBalanceContext (tokenBalanceArgs Bool.true Bool.false Bool.false) {
      cells := [("recorded", .uint balanceMaximum 99)]
    } with
  | .ok (outputs, state) => outputs == [
      ("exactAmount", .uint balanceMaximum 0),
      ("belowLimit", .bool Bool.false),
      ("aboveLimit", .bool Bool.false)
    ] && state.cells.lookup "recorded" == some (.uint balanceMaximum 99)
  | .error _ => Bool.false

#guard match runTokenBalance tokenBalanceContext (tokenBalanceArgs Bool.true Bool.true Bool.true (2 ^ 64)) {} with
  | .error message => message.contains "UInt64 operands"
  | .ok _ => Bool.false

#guard match runTokenBalance {tokenBalanceContext with unshieldedBalances := [(List.range 32, 2 ^ 64)]}
      (tokenBalanceArgs Bool.true Bool.true Bool.false 1) {} with
  | .error message => message.contains "UInt64 operands"
  | .ok _ => Bool.false

#guard match runTokenBalance {tokenBalanceContext with unshieldedBalances := [(List.range 32, balanceMaximum)]}
      (tokenBalanceArgs Bool.true Bool.false Bool.true) {
        cells := [("recorded", .uint balanceMaximum 99)]
      } with
  | .ok (outputs, _) => outputs == [
      ("exactAmount", .uint balanceMaximum balanceMaximum),
      ("belowLimit", .bool Bool.false),
      ("aboveLimit", .bool Bool.false)
    ]
  | .error _ => Bool.false

#guard match runTokenBalance {tokenBalanceContext with unshieldedBalances := []}
      (tokenBalanceArgs Bool.true Bool.true Bool.true 1) {
        cells := [("recorded", .uint balanceMaximum 99)]
      } with
  | .ok (outputs, _) => outputs == [
      ("exactAmount", .uint balanceMaximum 0),
      ("belowLimit", .bool Bool.true),
      ("aboveLimit", .bool Bool.false)
    ]
  | .error _ => Bool.false

#guard
  let privateTag : Entrypoint := {
    name := "privateTag"
    circuit := {name := "privateTag", inputs := [
      {name := "tag", ty := .bool, visibility := .private}
    ]}
    effects := [.readTokenBalance "amount" (.bytes32Literal (List.replicate 32 0))
      (.ref "tag") .exact]
  }
  match Disclosure.entrypoint privateTag with
  | .error diagnostic => diagnostic.message.contains "reaches public token balance read"
  | .ok _ => Bool.false

#guard
  let privateGuard : Entrypoint := {
    name := "privateGuard"
    circuit := {name := "privateGuard", inputs := [
      {name := "enabled", ty := .bool, visibility := .private}
    ]}
    effects := [.readTokenBalance "amount" (.bytes32Literal (List.replicate 32 0))
      (.bool Bool.true) .exact]
    effectGuards := [some (.ref "enabled")]
  }
  match Disclosure.entrypoint privateGuard with
  | .error diagnostic => diagnostic.message.contains "undisclosed private control"
  | .ok _ => Bool.false
