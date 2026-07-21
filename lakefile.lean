import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.30.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.31.0-rc2"

package CliffordProject where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩, ⟨`verso.code.warnLineLength, 120⟩]

@[default_target]
lean_lib CliffordProject where

lean_exe «blueprint-gen» where
  root := `CliffordProjectMain
