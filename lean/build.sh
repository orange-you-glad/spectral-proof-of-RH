#!/usr/bin/env bash
# Build and test Lean files.
set -euo pipefail

# run from repository root; compute script directory
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
cd "$SCRIPT_DIR"

# Ensure elan in PATH (for Lean version management)
if ! command -v elan &>/dev/null; then
  echo "Installing elan..."
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
  export PATH="$HOME/.elan/bin:$PATH"
fi

# Initialize project if needed
if [ ! -f lakefile.lean ]; then
  echo "Creating lakefile.lean and lean-toolchain..."
  echo "leanprover/lean4:stable" > lean-toolchain
  cat > lakefile.lean <<'EOF_LAKE'
import Lake
open Lake DSL

package SpectralProof

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib SpectralProof
EOF_LAKE
fi

# Download mathlib cache if available (fails gracefully)
lake exe cache get || true

# Build project
lake build

# Typecheck sample file
lake env lean SpectralProof/Test.lean
