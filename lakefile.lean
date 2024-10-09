import Lake
open Lake DSL

package "tp_solution" where
  version := v!"0.1.0"

lean_lib «TpSolution» where
  -- add library configuration options here

@[default_target]
lean_exe "tp_solution" where
  root := `Main
