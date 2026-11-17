import Nightlean.ScalarPolicy

namespace Nightlean

structure SourceSpan where
  file : String := ""
  line : Nat := 1
  column : Nat := 1
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Ty where
  | native | bool
  | uint (maximum : Nat)
  | bytes (length : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def Ty.scalarKind : Ty → ScalarPolicy.Kind
  | .native => .native
  | .bool => .bool
  | .uint maximum => .uint maximum
  | .bytes length => .bytes length

def Ty.isBytes : Ty → Bool
  | .bytes _ => true
  | _ => false

end Nightlean
