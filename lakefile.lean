import Lake
open Lake DSL

package «tapl-lean» where
  -- add package configuration options here

lean_lib «TaplLean» where
  -- add library configuration options here

@[default_target]
lean_exe «tapl-lean» where
  root := `Main
