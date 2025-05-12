# Root document for build
MAIN=src/main.tex
PDF=manuscript.pdf

.PHONY: all build clean lint check structure labels proofs metadata

# Default target: full build
all: build

build:
	latexmk -pdf -cd $(MAIN)

clean:
	latexmk -C -cd src/
	rm -rf src/metadata/

lint:
	chktex -q -n1 -n2 -n18 $(MAIN)

# Run all CI-level structural checks
check: structure labels proofs

structure:
	python3 scripts/check_structure.py

labels:
	python3 scripts/validate_labels.py

proofs:
	python3 scripts/check_proofs.py

metadata:
	python3 scripts/generate_index.py
