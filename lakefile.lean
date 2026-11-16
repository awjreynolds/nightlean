import Lake
open Lake DSL

package nightlean where
  version := v!"0.1.0"

@[default_target]
lean_lib Nightlean

@[default_target]
lean_exe nightlean where
  root := `Main
