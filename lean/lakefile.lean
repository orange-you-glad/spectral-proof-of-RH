import Lake
open Lake DSL

package SpectralProof

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib SpectralProof
