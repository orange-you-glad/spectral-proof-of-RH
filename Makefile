# File: Makefile

VERSION_FILE = VERSION
VERSION      = $(shell cat $(VERSION_FILE))
MAIN_PDF     = src/main.pdf
FINAL_NAME   = spectral_determinant_RH_equivalence_v$(VERSION).pdf
FINAL_PATH   = docs/$(FINAL_NAME)

.PHONY: all deploy check clean bump bump-minor bump-major

# Full pipeline: validate and release
all: check deploy

# Run all validation tests
check: structure labels proofs

structure:
	@echo "Checking structure..."
	PYTHONPATH=. python3 tests/check_structure.py

labels:
	@echo "Validating labels..."
	PYTHONPATH=. python3 tests/validate_labels.py

proofs:
	@echo "Verifying proof mapping..."
	PYTHONPATH=. python3 tests/check_proofs.py

# Deployment: tag and copy versioned PDF
deploy:
	@echo "Deploying PDF to $(FINAL_PATH)"
	cp $(MAIN_PDF) $(FINAL_PATH)
	@echo "Done."

# Cleanup
clean:
	rm -f docs/spectral_determinant_RH_equivalence_v*.pdf

# Version bumping
bump:
	python3 scripts/bump_version.py patch

bump-minor:
	python3 scripts/bump_version.py minor

bump-major:
	python3 scripts/bump_version.py major
