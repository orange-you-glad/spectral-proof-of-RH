## 🧪 Modular LaTeX Proof Integrity Test Suite

This repository enforces strict modularity and logical traceability for all formal proof elements. Your task is to implement a series of Python-based test scripts that verify the structural, referential, and logical consistency of the LaTeX manuscript and associated formal metadata.

### 📁 Location

Place all test scripts in:

```
/tests/
```

Each script should be executable standalone and callable via:

```bash
PYTHONPATH=. python3 tests/<script_name>.py
```

### ✅ Required Scripts and Responsibilities

Each script must:

* Traverse the `src/chapters/` directory
* Parse `.tex` files (skip `summary.tex`, `intro.tex`)
* Check for specific LaTeX environments
* Report any violations clearly (with line number and file path if possible)
* Exit with `sys.exit(1)` if any violation is found

| Script Name                      | Responsibility                                                                     |
| -------------------------------- | ---------------------------------------------------------------------------------- |
| `check_structure.py`             | Ensure each chapter contains `intro.tex`, `summary.tex`, and all subdirs           |
| `validate_labels.py`             | Check that all formal environments have matching `\label{}` with file-derived keys |
| `check_proofs.py`                | Confirm that every theorem/lemma has an associated proof in `proofs/`              |
| `check_unresolved_refs.py`       | Parse all `\ref`, `\cite`, `\eqref` for unresolved or broken links                 |
| `check_unused_citations.py`      | Identify unused `.bib` entries or missing citations                                |
| `check_dag_coherence.py`         | Validate DAG structure: all nodes exist, edges resolve, graph is acyclic           |
| `check_compile_latexmk.py`       | Attempt full clean compile using `latexmk -pdf`, catch and report errors           |
| `check_pdf_basics.py`            | Check output PDF for TOC entries, page number consistency, size limit              |
| `generate_chapter_stats.py`      | Report per-chapter counts of theorems, lemmas, equations, pages                    |
| `check_label_backlinks.py`       | Ensure every `\ref{}` is referenced somewhere meaningful in context                |
| `check_missing_toc.py`           | Ensure all top-level chapters/sections show up in the compiled TOC                 |
| `check_lean_links.py`            | Confirm Lean theorem stubs exist for each LaTeX theorem                            |
| `check_all_remarks_extracted.py` | Ensure all `\begin{remark}` blocks are in `rems/` files                            |
| `check_all_proofs_extracted.py`  | Ensure all `\begin{proof}` blocks live in `proofs/`                                |
| `check_all_thms_extracted.py`    | Ensure all `\begin{theorem}` live in `thms/`                                       |
| `check_all_lemmas_extracted.py`  | Ensure all `\begin{lemma}` live in `lems/`                                         |
| `check_all_defs_extracted.py`    | Ensure all `\begin{definition}` live in `defs/`                                    |
| `check_all_props_extracted.py`   | Ensure all `\begin{proposition}` live in `props/`                                  |
| `check_all_cors_extracted.py`    | Ensure all `\begin{corollary}` live in `cors/`                                     |

### 🔧 Tips for Implementation

* Use `os.walk()` to traverse subfolders
* Use `re` module for LaTeX environment and label detection
* Use `sys.exit(1)` on failure, and print clear filenames and line numbers
* Avoid hardcoding assumptions—read directories dynamically from `src/chapters/`
* Bonus: Add a `--verbose` CLI flag to print more details

### ✅ Example Execution

```bash
make check
```

This will invoke the full test suite before any versioned release.

Let us know in PRs which scripts you've implemented and include example output on pass/failure.
