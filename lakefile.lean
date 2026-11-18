import Lake
open Lake DSL

package noctium where
  version := v!"0.1.0"

@[default_target]
lean_lib Noctium

@[default_target]
lean_exe noctium where
  root := `NoctiumMain
