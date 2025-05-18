# 🧪 Testing Infrastructure

**Formal Manuscript Hygiene and DAG Audit Suite**

This directory defines the **non-negotiable automated test suite** for maintaining the structural, logical, and spectral hygiene of the manuscript and its Lean formalizations. These checks are not optional: they form the **integrity core** of the entire proof pipeline.

Every rule enforced here supports:

* ✅ **100% structural and logical coverage**
* 🔁 **Full reproducibility and traceability**
* 📐 **Canonical modular conformance**
* 🔒 **Formal soundness under DAG audit invariants**

---

## 🚀 Running the Suite

All tests are executed via Python’s built-in `unittest` module:

```bash
python -m unittest discover -s tests -v
```

All CI pipelines call this command on **every commit and pull request**.

Additional structural and DAG checks are invoked from `scripts/` and `dag/`. Any failure results in an immediate, non-negotiable **build block**.

---

## ✅ Structural and Logical Validation Rules

Every test enforces a **strict invariant**. All failures are **blocking**. Partial passes are disallowed.

### 1. 📎 Label-File Concordance

All LaTeX files under `src/chapters/` with a formal prefix (`thm_`, `lem_`, `def_`, `prop_`, `cor_`, `rmk_`) **must include a `\label{}`** whose value matches the file name, replacing `_` with `:`.

| File                           | Required Label                     |
| ------------------------------ | ---------------------------------- |
| `thm_spectral_equivalence.tex` | `\label{thm:spectral_equivalence}` |

This ensures bi-directional traceability and reference safety.

---

### 2. 📜 Proof Presence Enforcement

Each formal object must have a **corresponding proof file**:

| Formal File                    | Required Proof File                   |
| ------------------------------ | ------------------------------------- |
| `thm_spectral_equivalence.tex` | `proofs/prf_spectral_equivalence.tex` |

Every theorem, lemma, corollary, or proposition must be backed by a uniquely-named, chapter-local proof file.

---

### 3. 📁 Canonical Chapter Directory Shape

Each chapter directory must include:

* `intro.tex` — motivational overview (non-formal)
* `summary.tex` — recap only (no new declarations)
* subdirectories: `defs/`, `lems/`, `thms/`, `props/`, `cors/`, `rems/`, `proofs/`

Missing any of these is a blocking error.

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

Violators are rejected by the test suite and cannot be committed.

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

This checks:

* Acyclicity
* Existence of all nodes
* Hash validation
* Topological ordering of spectral paths

---

### ✳️ Optional: Spectral Path Annotations

Spectral inference objects (e.g. `spec:lsym_trace`) can be tracked and verified for inclusion in RH-equivalence chains:

```json
["spec:lsym_trace", "thm:spectral_equivalence"]
```

---

## 📘 Lean Coherence Gate

When Lean is activated, the test suite additionally requires:

```bash
lake build
```

Each analytic object (`theorem`, `lemma`, etc.) **must be mirrored in Lean**, using a matching name in the formalization.

* All Lean files must compile **without warnings or errors**
* Formal logic and analytic manuscript must evolve **in lockstep**

---

## 🔐 Summary

* 💯 No commit or pull request may bypass this test suite.
* 🧩 All formal objects must be traceable from file → label → proof → Lean.
* 🧠 DAG audit layer ensures logical and spectral soundness.
* 📏 Directory and filename hygiene are strictly enforced.

---

As new invariants are introduced, this README and the test infrastructure **must** be updated. All logic-critical metadata (e.g., spectral node hashes, critical equivalence paths) must be encoded in the DAG layer.

**Failure anywhere means failure everywhere.**

**This is not a linter. This is the guardian.**
