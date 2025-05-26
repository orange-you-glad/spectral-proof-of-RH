# === Lean Build + Formal Verification ===

# Default target
.PHONY: all clean lean lean-check

all: lean lean-check

# 🧠 Build Lean project using Lake
lean:
	@echo "🧠 Building Lean formal proof..."
	@lake build

# 🔍 Check for unfinished proofs
lean-check:
	@echo "🔍 Checking for incomplete Lean proofs (sorries)..."
	! grep -r "sorry" SpectralProof/

# 🧼 Clean up generated build artifacts
clean:
	@echo "🧹 Cleaning Lean build outputs..."
	@lake clean
	rm -f lake-manifest.json
	rm -rf build .lake/build
