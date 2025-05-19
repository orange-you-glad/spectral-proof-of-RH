# File: Makefile

VERSION_FILE = VERSION
VERSION      = $(shell cat $(VERSION_FILE))
MAIN_TEX     = src/main.tex
MAIN_PDF     = src/main.pdf
FINAL_NAME   = spectral_determinant_RH_equivalence_v$(VERSION).pdf
FINAL_PATH   = docs/$(FINAL_NAME)

.PHONY: all deploy check clean bump bump-minor bump-major dag-refresh dag-analyze \
        structure labels proofs docs-lint texlog-lint modifications \
        dag checkcites compile pdf stats label_backlinks modularity \
        lint format-check typecheck

# 🚀 Full pipeline: validate and release
all: check deploy

# 🧪 Run all validation tests
check: structure labels proofs docs-lint texlog-lint modifications \
       dag-refresh checkcites dag dag-analyze compile pdf stats \
       label_backlinks modularity \
       lint format-check typecheck

# 📁 Structural integrity checks
structure:
	@echo "🔍 Checking chapter structure..."
	PYTHONPATH=. python3 tests/check_structure.py

labels:
	@echo "🔍 Validating label naming and prefix rules..."
	PYTHONPATH=. python3 tests/validate_labels.py

proofs:
	@echo "🔍 Checking that all formal objects have proofs..."
	PYTHONPATH=. python3 tests/check_proofs.py

# 📚 Lint Markdown and LaTeX logs
docs-lint:
	@echo "🔍 Linting Markdown docs..."
	python3 scripts/docs_lint.py

texlog-lint:
	@echo "🔍 Inspecting LaTeX log..."
	python3 scripts/lint_tex_log.py

# 🔒 DAG policies
modifications:
	@echo "🔍 Checking modifications against DAG policy..."
	python3 scripts/check_modifications.py

dag-refresh:
	@echo "🔁 Regenerating DAG nodes and edges..."
	python3 scripts/generate_dag.py

dag:
	@echo "🔍 Validating DAG node/edge consistency..."
	PYTHONPATH=. python3 dag/dag_audit.py --check

dag-analyze:
	@echo "📊 Analyzing DAG structure and critical paths..."
	python3 scripts/analyze_dot.py

# 🔍 Citation integrity
checkcites:
	@echo "🔍 Running checkcites on main.aux..."
	latexmk -pdf -silent $(MAIN_TEX)
	checkcites -f -v src/main.aux

# 🧱 Compilation & output checks
compile:
	@echo "🔍 Verifying full LaTeX compile from scratch..."
	PYTHONPATH=. python3 tests/check_compile_latexmk.py

pdf:
	@echo "🔍 Verifying PDF output (TOC, length, pagination)..."
	PYTHONPATH=. python3 tests/check_pdf_basics.py

stats:
	@echo "📊 Generating chapter and proof statistics..."
	PYTHONPATH=. python3 tests/generate_chapter_stats.py

label_backlinks:
	@echo "🔍 Checking for reciprocal label usage..."
	PYTHONPATH=. python3 tests/check_label_backlinks.py

modularity:
	@echo "🔍 Verifying environment extraction modularity..."
	PYTHONPATH=. python3 tests/check_all_proofs_extracted.py
	PYTHONPATH=. python3 tests/check_all_remarks_extracted.py
	PYTHONPATH=. python3 tests/check_all_thms_extracted.py
	PYTHONPATH=. python3 tests/check_all_lemmas_extracted.py
	PYTHONPATH=. python3 tests/check_all_defs_extracted.py
	PYTHONPATH=. python3 tests/check_all_props_extracted.py
	PYTHONPATH=. python3 tests/check_all_cors_extracted.py

# 🚢 Deployment
deploy:
	@echo "📤 Deploying PDF to $(FINAL_PATH)"
	cp $(MAIN_PDF) $(FINAL_PATH)
	@echo "✅ Done."

# 🧼 Clean-up
clean:
	rm -f docs/spectral_determinant_RH_equivalence_v*.pdf

# 📦 Version bumping
bump:
	python3 scripts/bump_version.py patch

bump-minor:
	python3 scripts/bump_version.py minor

bump-major:
	python3 scripts/bump_version.py major

# 🧪 Code Quality
lint:
	@echo "🔍 Running Ruff for code linting..."
	ruff .

format-check:
	@echo "🧪 Verifying formatting with Black..."
	black --check .

typecheck:
	@echo "🔍 Running Mypy for type checking..."
	mypy .
