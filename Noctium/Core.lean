import Noctium.ScalarPolicy

namespace Noctium

namespace Jubjub

/-- Scalar order from the pinned `midnight-curves` Jubjub field. -/
def scalarOrder : Nat :=
  6554484396890773809930967563523245729705921265872317281365359162392183254199

end Jubjub

structure SourceSpan where
  file : String := ""
  line : Nat := 1
  column : Nat := 1
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Ty where
  | native | bool
  | uint (maximum : Nat)
  | bytes (length : Nat)
  /-- Dynamically sized host bytes with the native FAB Compress projection. -/
  | opaqueBytes
  | jubjubScalar | jubjubPoint
  | foreign (kind : Foreign.Kind)
  deriving Repr, BEq, DecidableEq, Inhabited

def Ty.scalarKind : Ty → ScalarPolicy.Kind
  | .native => .native
  | .bool => .bool
  | .uint maximum => .uint maximum
  | .bytes length => .bytes length
  | .opaqueBytes => .opaqueBytes
  | .jubjubScalar => .jubjubScalar
  | .jubjubPoint => .jubjubPoint
  | .foreign kind => .foreign kind

def Ty.isBytes : Ty → Bool
  | .bytes _ => true
  | _ => false

def Ty.isOpaqueBytes : Ty → Bool
  | .opaqueBytes => true
  | _ => false

def Ty.isJubjub : Ty → Bool
  | .jubjubScalar | .jubjubPoint => true
  | _ => false

def Ty.isJubjubScalar : Ty → Bool
  | .jubjubScalar => true
  | _ => false

def Ty.isJubjubPoint : Ty → Bool
  | .jubjubPoint => true
  | _ => false

def Ty.isForeign : Ty → Bool
  | .foreign _ => true
  | _ => false

end Noctium
