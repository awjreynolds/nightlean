import Nightlean.Verification.ArtifactBytes
open Lean Nightlean.Verification.ArtifactBytes

example : parse [32, 9, 10, 13, 91, 48, 44, 49, 50, 44, 116, 114, 117, 101, 44, 110, 117, 108, 108, 93, 32] =
    .ok (.arr #[toJson (0 : Nat), toJson (12 : Nat), .bool true, .null]) := by rfl
example : parse [34, 92, 117, 48, 48, 52, 49, 92, 110, 92, 34, 92, 92, 92, 47, 34] =
    .ok (.str "A\n\"\\/") := by rfl
example : parse [123, 34, 120, 34, 58, 49, 125] = .ok (Json.mkObj [("x", toJson (1 : Nat))]) := by rfl

private def rejected (bytes : Bytes) : Bool := match parse bytes with | .error _ => true | .ok _ => false
example : rejected [123, 34, 120, 34, 58, 48, 44, 34, 120, 34, 58, 49, 125] = true := by rfl
example : rejected [48, 49] = true := by rfl
example : rejected [49, 46, 48] = true := by rfl
example : rejected [49, 101, 48] = true := by rfl
example : rejected [45, 49] = true := by rfl
example : rejected [91, 48, 44, 93] = true := by rfl
example : rejected [123, 34, 120, 34, 58, 48, 44, 125] = true := by rfl
example : rejected [34, 10, 34] = true := by rfl
example : rejected [34, 195, 169, 34] = true := by rfl
example : rejected [34, 92, 117, 48, 48, 101, 57, 34] = true := by rfl
example : rejected [239, 187, 191, 123, 125] = true := by rfl
example : rejected [110, 117, 108, 108, 120] = true := by rfl
example : rejected [34, 92, 113, 34] = true := by rfl
example : rejected [34, 92, 117, 100, 56, 48, 48, 34] = true := by rfl
example : rejected [123] = true := by rfl

example : parse [49,56,52,52,54,55,52,52,48,55,51,55,48,57,53,53,49,54,49,53] =
    .ok (toJson (18446744073709551615 : Nat)) := by rfl
example : rejected [49,56,52,52,54,55,52,52,48,55,51,55,48,57,53,53,49,54,49,54] = true := by rfl
example : rejected [123,34,120,34,58,48,44,34,92,117,48,48,55,56,34,58,49,125] = true := by rfl
example : parse (List.replicate (maxBytes + 1) 32) = .error "JSON artifact exceeds qualified byte bound" := by
  have over : (List.replicate (maxBytes + 1) (32 : UInt8)).length > maxBytes := by
    rw [List.length_replicate]
    exact Nat.lt_succ_self _
  unfold parse
  simp only [over, ite_true]
  rfl

example : (parse (List.replicate 64 91 ++ [48] ++ List.replicate 64 93)).toOption.isSome = true := by decide +kernel
example : rejected (List.replicate 65 91 ++ [48] ++ List.replicate 65 93) = true := by decide +kernel

def main (args : List String) : IO UInt32 := do
  for path in args do
    let bytes ← IO.FS.readBinFile path
    match parse bytes.toList with
    | .ok value => IO.println value.compress
    | .error message => IO.eprintln message; return 1
  return 0
