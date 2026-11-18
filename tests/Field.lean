import Noctium.Field

open Noctium.Field

def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def main : IO Unit := do
  for n in [0, 1, 255, 256, modulus - 1] do
    let bytes ← IO.ofExcept (encode n)
    unless bytes.size == 32 do throw (IO.userError "incorrect width")
    let decoded ← IO.ofExcept (decode bytes)
    unless decoded == n do throw (IO.userError "canonical roundtrip failed")
  unless failed (encode modulus) do throw (IO.userError "modulus accepted")
  unless failed (decode ByteArray.empty) do throw (IO.userError "empty encoding accepted")
  unless failed (decode (ByteArray.mk (Array.replicate 32 255))) do
    throw (IO.userError "out-of-field encoding accepted")
  let bytes ← IO.ofExcept (encode 256)
  unless bytes[0]! == 0 && bytes[1]! == 1 do
    throw (IO.userError "encoding is not little-endian")
  IO.println "canonical Native encoding checks passed"
