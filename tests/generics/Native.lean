import Noctium.Compiler

open scoped Noctium
open Noctium.Helpers.Specialization

private def genericAddProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "boundedAdd"
    parameters := [⟨"N", .natural⟩]
    values := [
      ("expected", .uint (.multiply (.literal 2) (.parameter "N"))),
      ("left", .uint (.parameter "N")),
      ("right", .uint (.parameter "N"))
    ]
    result := .uint (.multiply (.literal 2) (.parameter "N"))
    body := [
      .bind "sum" (.uint (.multiply (.literal 2) (.parameter "N")))
        (.binary .add (.ref "left") (.ref "right")),
      .assert (.eq (.ref "sum") (.ref "expected")),
      .return (some (.disclose {file := "tests/generics/Native.lean", line := 16, column := 1}
        (.ref "sum")))
    ]
  }]
  exports := [
    ⟨"small", ⟨0, 0⟩, [.natural (.literal 15)], [
      ⟨"expected", .uint (.multiply (.literal 2) (.literal 15)), .public, {}⟩,
      ⟨"left", .uint (.literal 15), .private, {}⟩,
      ⟨"right", .uint (.literal 15), .private, {}⟩
    ], {}⟩,
    ⟨"wide", ⟨0, 0⟩, [.natural (.literal 255)], [
      ⟨"expected", .uint (.multiply (.literal 2) (.literal 255)), .public, {}⟩,
      ⟨"left", .uint (.literal 255), .private, {}⟩,
      ⟨"right", .uint (.literal 255), .private, {}⟩
    ], {}⟩
  ]
}

noctium_generic_circuit genericAddSmall from genericAddProgram entry "small"
noctium_generic_circuit genericAddWide from genericAddProgram entry "wide"
