import Lake
open Lake DSL

package «tapl-lean» where
  -- add package configuration options here

lean_lib «TaplLean» where
  -- add library configuration options here

@[default_target]
lean_exe «tapl-lean» where
  root := `Main

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.10.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.10.0"
