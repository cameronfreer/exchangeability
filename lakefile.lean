import Lake
open Lake DSL

package «leantest-afp» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «LeantestAfp» where
  -- add library configuration options here

@[default_target]
lean_exe «leantest-afp» where
  root := `Main
