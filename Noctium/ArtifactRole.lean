namespace Noctium

inductive ArtifactRole where
  | ledger | standalone | witness | control | specialization | observations | rustBinding
  deriving BEq, Repr

namespace ArtifactRole

def label : ArtifactRole → String
  | .ledger => "ledger"
  | .standalone => "standalone"
  | .witness => "witness"
  | .control => "control"
  | .specialization => "specialization"
  | .observations => "observations"
  | .rustBinding => "rustBinding"

def parse : String → Except String ArtifactRole
  | "ledger" => .ok .ledger
  | "standalone" => .ok .standalone
  | "witness" => .ok .witness
  | "control" => .ok .control
  | "specialization" => .ok .specialization
  | "observations" => .ok .observations
  | name => .error s!"unknown artifact role '{name}'"

def validateSelection (roles : List ArtifactRole) (rustBindings : Bool := false) : Except String Unit := do
  if roles.contains .witness && !(roles.contains .ledger || roles.contains .standalone) then
    throw "--emit witness requires --emit ledger or --emit standalone"
  if rustBindings && !roles.isEmpty && !(roles.contains .ledger && roles.contains .witness) then
    throw "--bindings rust requires ledger and witness artifacts"

end ArtifactRole
end Noctium
