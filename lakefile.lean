import Lake
open Lake DSL

package «exchangeability» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

-- require paranoia from git
--   "https://github.com/oOo0oOo/LeanParanoia.git" @ "main"

-- require LeanDepViz from git
--   "https://github.com/cameronfreer/LeanDepViz.git" @ "main"

lean_lib «ForMathlib» where
  -- Lemmas intended for upstream contribution to mathlib

lean_lib «Exchangeability» where
  -- add library configuration options here

@[default_target]
lean_exe «exchangeability» where
  root := `Main

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"