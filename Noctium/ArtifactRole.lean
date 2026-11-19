namespace Noctium

inductive ArtifactRole where
  | ledger | standalone | witness | control | specialization | observations
  deriving BEq, Repr

namespace ArtifactRole

def label : ArtifactRole → String
  | .ledger => "ledger"
  | .standalone => "standalone"
  | .witness => "witness"
  | .control => "control"
  | .specialization => "specialization"
  | .observations => "observations"

def parse : String → Except String ArtifactRole
  | "ledger" => .ok .ledger
  | "standalone" => .ok .standalone
  | "witness" => .ok .witness
  | "control" => .ok .control
  | "specialization" => .ok .specialization
  | "observations" => .ok .observations
  | name => .error s!"unknown artifact role '{name}'"

def validateSelection (roles : List ArtifactRole) : Except String Unit := do
  if roles.contains .witness && !(roles.contains .ledger || roles.contains .standalone) then
    throw "--emit witness requires --emit ledger or --emit standalone"

end ArtifactRole
end Noctium
