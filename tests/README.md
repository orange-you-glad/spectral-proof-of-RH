# Testing Infrastructure

This directory contains the automated checks that enforce hygiene across the LaTeX
manuscript and any accompanying formal proofs. The goal is to guarantee that every
file follows a predictable convention so the build remains reproducible and easy to
validate.

## Running the suite

All tests are executed with Python's builtin `unittest` module:

```bash
python -m unittest discover -s tests -v
```

CI workflows call this command on every pull request and push. Additional scripts
from `scripts/` are invoked to perform structural checks and will raise an error
on failure.

## Declarative validation rules

The current set of tests enforce the following rules:

1. **Label matching**: Every TeX file under `src/chapters/` whose name begins with
   `thm_`, `lem_`, `def_`, `prop_`, `cor_`, or `rmk_` must contain a `\label{}`
   whose value matches the file name with the underscore replaced by a colon.
2. **Proof mapping**: For each theorem, lemma, proposition, or corollary file,
   a corresponding proof file `prf_<name>.tex` must exist in the `proofs/`
   subdirectory of the same chapter.
3. **Section structure**: Each chapter directory is required to contain a
   driver TeX file matching the directory name, an `intro.tex`, a `summary.tex`,
   and subfolders `defs/`, `lems/`, `thms/`, `props/`, `cors/`, `rems/`, and
   `proofs/`.
4. **File names**: Colon characters are forbidden in file names. Use underscores
   instead. The scripts will report offending names.

Failure to satisfy any rule causes the CI run to fail.

## Lean scaffolding

A light-weight Lean environment will be introduced to formalize core lemmas.
Once present, CI will also invoke `lake build` to make sure the Lean code
compiles. Adding a new theorem to the manuscript will eventually require a
corresponding Lean statement, ensuring the analytic proof and its formal
counterpart evolve together.

This README will be updated as the test suite matures.
