import Lake
open Lake DSL

package «leantest-afp» where
  -- add package configuration options here

lean_lib «LeantestAfp» where
  -- add library configuration options here

@[default_target]
lean_exe «leantest-afp» where
  root := `Main