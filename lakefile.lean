import Lake
open Lake DSL

package SpectralProof where
  -- Set the source root directory to `lean/`
  srcDir := "lean"

-- Use a known-stable tagged release of mathlib
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0"

@[default_target]
lean_lib SpectralProof

-- Executable entry point for CLI usage: `lake run spectralProof`
lean_exe spectralProof where
  root := `SpectralProof.Main
