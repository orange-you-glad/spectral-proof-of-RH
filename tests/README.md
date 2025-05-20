# 🧪 Testing Infrastructure

**Formal Manuscript Hygiene and DAG Audit Suite**

This directory defines the **non-negotiable automated test suite** for maintaining the structural, logical, and spectral hygiene of the manuscript and its Lean formalizations. These checks are not optional: they form the **integrity core** of the entire proof pipeline.

Every rule enforced here supports:

* ✅ **100% structural and logical coverage**
* 🔁 **Full reproducibility and traceability**
* 📐 **Canonical modular conformance**
* 🔒 **Formal soundness under DAG audit invariants**

---

## Usage

All tests are executed via Python’s built-in `unittest` module:

```bash
python -m unittest discover -s tests -v
```

All CI pipelines call this command on **every commit and pull request**.

Additional DAG and metadata checks are run from `dag/` and `scripts/`. Any failure results in an immediate, non-negotiable **build block**.

---

## ✅ Structural and Logical Validation Rules

Every test enforces a **strict invariant**. All failures are **blocking**. Partial passes are disallowed.

### 1. 📎 Label-File Concordance

All LaTeX files under `src/chapters/` with a formal prefix (`thm_`, `lem_`, `def_`, `prop_`, `cor_`, `rmk_`) **must include a `\label{}`** whose value matches the file name, replacing `_` with `:`.

| File                           | Required Label                     |
| ------------------------------ | ---------------------------------- |


| `thm_spectral_equivalence.tex` | `\label{thm:spectral_equivalence}` |


---

### 2. 📜 Proof Presence Enforcement

Each formal object must have a **corresponding proof file**:

| Formal File                    | Required Proof File                   |

| ------------------------------ | ------------------------------------- |

| `thm_spectral_equivalence.tex` | `proofs/prf_spectral_equivalence.tex` |


---

### 3. 📁 Canonical Chapter Directory Shape

Each chapter directory must include:

* `intro.tex` — motivational overview (non-formal)
* `summary.tex` — recap only (no new declarations)
* subdirectories: `defs/`, `lems/`, `thms/`, `props/`, `cors/`, `rems/`, `proofs/`

---

### 4. 🔤 Filename Lexical Discipline

All filenames must follow the pattern:

* **lowercase only**
* **digits and underscores only**
* **no colons, spaces, or symbols**

Examples of disallowed filenames:

* `Thm Spectral.tex`
* `lem:spectrum?.tex`
* `prop-Zeta&Trace.tex`

---

### 5. 🧱 Environment Extraction Enforcement

All formal environments must live in their designated subfolders:

| Environment Type      | Required Directory |
| --------------------- | ------------------ |

| `\begin{theorem}`     | `thms/`            |

| `\begin{lemma}`       | `lems/`            |

| `\begin{definition}`  | `defs/`            |

| `\begin{proposition}` | `props/`           |

| `\begin{corollary}`   | `cors/`            |

| `\begin{remark}`      | `rems/`            |

| `\begin{proof}`       | `proofs/`          |


Any environment found inline will raise a structural hygiene failure.

---

### 6. 🧪 Cross-Reference and Citation Sanity

* All `\ref`, `\cite`, and `\eqref` commands must resolve.
* Unused `.bib` entries are flagged.
* Label backlinks are checked for logical usage symmetry.

---

### 7. 📐 Preamble Consistency *(in progress)*

A preamble consistency agent will soon validate:

* All custom macros (`\lemref{}`, `\specmap{}`, etc.) are defined in a shared source.
* No chapter silently overrides or redefines common notation.

---

## 📊 DAG Audit Layer

**Canonical Proof Dependency Graph**

Logical and spectral inference chains are captured in a strict DAG:

```bash
dag/
├── dag_nodes.json     # Formal object registry
├── dag_edges.json     # Declared dependencies
└── dag_audit.py       # DAG integrity validator
```

### 🧠 Purpose

This layer enforces acyclic, topologically valid inference flows and ensures:

* No circular logic
* All proofs reference only declared upstream nodes
* Spectral equivalence and RH-critical paths are preserved
* File hashes and node labels are consistent and verifiable

### 🔍 DAG Integrity Check

```bash
python dag/dag_audit.py --check
```

---

## 📘 Lean Coherence Gate

When Lean integration is active:

```bash
lake build
```

Each theorem/lemma must have a matching Lean declaration. Compilation without warnings or errors is mandatory. Formal and analytic content must evolve together.

---

## 🔐 Summary

* 💯 No commit or pull request may bypass this test suite.
* 🧩 All formal objects must be traceable from file → label → proof → DAG → Lean.
* 🧠 DAG audit layer guarantees logical and spectral consistency.
* 📏 Structural and lexical hygiene are strictly enforced.

As new invariants are introduced, this README **must be updated**.

**Failure anywhere means failure everywhere.**

**This is not a linter. This is the guardian.**
