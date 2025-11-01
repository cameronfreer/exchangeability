import Lake
open Lake DSL

package «exchangeability» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Canonical from git
  "https://github.com/chasenorman/CanonicalLean.git"

lean_lib «Exchangeability» where
  -- add library configuration options here

@[default_target]
lean_exe «exchangeability» where
  root := `Main

lean_lib «DepViz» where
  -- auxiliary tooling for dependency visualization

lean_exe depviz where
  root := `DepViz.Main
  supportInterpreter := true
