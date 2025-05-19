# 🤖 AGENTS.md — GPT/Codex Agent Roles

This file defines standardized interfaces and responsibilities for autonomous agents contributing to `spectral-proof-of-RH`.

Agents may operate via API, Codex CLI, GitHub PRs, or VS Code integrations. Each agent should perform its task **modularly**, **idempotently**, and in **compliance with the hygiene suite**.

All agents must respect:

- Filename and label conventions
- Structural modularity (e.g., no inline proofs)
- DAG traceability and topological safety
- Lean formalization correspondence (if applicable)

---

## 🧠 Core Agent Roles

| Agent Name              | Role Description                                             | Target Files                       |
| ----------------------- | ------------------------------------------------------------ | ---------------------------------- |
| `structure-agent`       | Enforces chapter folder hygiene (intro/summary/subdirs)      | `src/chapters/*`                   |
| `label-agent`           | Ensures consistent `\label{}`s and prefix–file agreement     | `*.tex`, `validate_labels.py`      |
| `proof-mapper-agent`    | Verifies each lemma/theorem has a `proofs/prf_*.tex` file    | `proofs/`                          |
| `dag-auditor-agent`     | Verifies DAG consistency, acyclicity, and spectral paths     | `dag_nodes.json`, `dag_edges.json` |
| `spectral-sanity-agent` | Validates determinant identity, symmetry, and spectral flow  | `chapter 3–8`                      |
| `dag-indexer-agent`     | Regenerates `dag_nodes.json` and `dag_edges.json` from files | `dag/`, `src/`                     |

---

## 🧼 Hygiene Agents

| Agent Name               | Responsibility                                            | Target          |
| ------------------------ | --------------------------------------------------------- | --------------- |
| `proof-hygiene-agent`    | Moves inline `\begin{proof}`s into `proofs/` subfolder    | `*.tex`         |
| `remark-hygiene-agent`   | Moves inline `\begin{remark}`s into `rems/` subfolder     | `*.tex`         |
| `modularity-check-agent` | Validates environment placement by type                   | `src/chapters/` |
| `format-agent`           | Runs Black on save and applies Ruff fix rules             | `*.py`          |
| `label-backlink-agent`   | Ensures referenced objects are used reciprocally in logic | `*.tex`         |

---

## 📚 Reference & Citation Agents

| Agent Name        | Purpose                                                    | Notes                     |
| ----------------- | ---------------------------------------------------------- | ------------------------- |
| `ref-link-agent`  | Validates `\ref{}`, `\cite{}`, `\eqref{}` from `.aux` file | Uses `checkcites`         |
| `bib-usage-agent` | Detects unused `.bib` entries and uncited references       | Optional via `checkcites` |

---

## 🧘 Lean & Formalization Agents

| Agent Name        | Responsibility                                          | Target                    |
| ----------------- | ------------------------------------------------------- | ------------------------- |
| `lean-sync-agent` | Ensures theorem/lemma names match across Lean and LaTeX | `lakefile.lean`, `*.tex`  |
| `lean-gap-agent`  | Flags theorems without Lean declarations                | `dag_nodes.json`, `lean/` |

---

## 🛠️ Agent Protocols

- All agents must:
  - Log their changes
  - Update or validate `dag_nodes.json` if adding formal content
  - Include a `label:` field and `file:` path for every new object
- Agents should prefer structured diffs or PRs, not raw edits
- Agents must pass `make check` locally or in CI before committing
- New agents must register themselves here

---

## 🧠 Agent Directory Conventions

- `src/chapters/XX_*` — formal content (split into `defs/`, `thms/`, etc.)
- `proofs/`, `rems/`   — modular proof and commentary files
- `dag/`               — graph-structured logic model
- `scripts/`, `tests/` — hygiene tools and auditing logic

---

## 🆕 Adding a New Agent

To register a new agent:

1. Add an entry to this file
2. Declare your scope, files modified, and invariants
3. Add yourself to `.github/CODEOWNERS` if appropriate
4. Ensure your action runs safely under `make check`

---

This `AGENTS.md` defines the trusted interface for AI collaborators. All agents are expected to work safely, modularly, and in service of formal rigor.
