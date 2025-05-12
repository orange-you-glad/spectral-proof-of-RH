# Paths and file names
MAIN_TEX=src/main.tex
PDF_NAME=manuscript
PDF_SRC=src/$(PDF_NAME).pdf
PDF_DEST=docs/$(PDF_NAME).pdf
VERSION_FILE=VERSION

.PHONY: all build clean lint check structure labels proofs metadata deploy \
        bump bump-minor bump-major

# Default: full build and deploy
all: build deploy

build:
	latexmk -pdf -jobname=$(PDF_NAME) -cd $(MAIN_TEX)

clean:
	latexmk -C -cd src/
	rm -rf src/metadata/

lint:
	chktex -q -n1 -n2 -n18 $(MAIN_TEX)

# CI structural checks
check: structure labels proofs

structure:
	python3 scripts/check_structure.py

labels:
	python3 scripts/validate_labels.py

proofs:
	python3 scripts/check_proofs.py

metadata:
	python3 scripts/generate_index.py

deploy: build
	python3 scripts/deploy_pdf.py

# Version bumping
bump:
	python3 scripts/bump_version.py patch

bump-minor:
	python3 scripts/bump_version.py minor

bump-major:
	python3 scripts/bump_version.py major
