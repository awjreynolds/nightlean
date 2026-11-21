import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit opaqueCellWriteInputs where
  public nextText : OpaqueString
  public nextBytes : OpaqueBytes
end

noctium_circuit opaqueCellReadInputs where
end

noctium_contract OpaqueCells where
  cell text : OpaqueString
  cell bytes : OpaqueBytes
  entry store uses opaqueCellWriteInputs where
    write text := disclose(nextText)
    write bytes := disclose(nextBytes)
  end
  entry readText uses opaqueCellReadInputs where
    read text as currentText
    return textValue : OpaqueString := disclose(currentText)
  end
  entry readBytes uses opaqueCellReadInputs where
    read bytes as currentBytes
    return bytesValue : OpaqueBytes := disclose(currentBytes)
  end
end

private def opaqueCellEntry (name : String) : Entrypoint :=
  match OpaqueCells.entrypoints.find? (·.name == name) with
  | some value => value
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match OpaqueCells.state with
  | [{name := "text", kind := .cell .opaqueString, ..},
     {name := "bytes", kind := .cell .opaqueBytes, ..}] => Bool.true
  | _ => Bool.false

#guard match OpaqueCells.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueCells.state (opaqueCellEntry "store") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueCells.state (opaqueCellEntry "readText") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueCells.state (opaqueCellEntry "readBytes") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueCells.state (opaqueCellEntry "store") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueCells.state (opaqueCellEntry "readText") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueCells.state (opaqueCellEntry "readBytes") with
  | .ok _ => Bool.true
  | .error _ => Bool.false
