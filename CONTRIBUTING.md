### ✅ `CONTRIBUTING.md`

````markdown
# 🤝 Contributing to `spectral-proof-of-RH`

Welcome! This project builds a formal, spectral operator-theoretic realization of the Riemann Hypothesis. We welcome contributions that enhance structure, readability, correctness, automation, or formalization.

---

## 💻 Preferred Environment: VS Code

We recommend [Visual Studio Code](https://code.visualstudio.com/) for development, with automatic formatting and linting enabled.

### 📦 Required Extensions

- [Python](https://marketplace.visualstudio.com/items?itemName=ms-python.python)
- [Ruff](https://marketplace.visualstudio.com/items?itemName=charliermarsh.ruff)
- [LaTeX Workshop](https://marketplace.visualstudio.com/items?itemName=James-Yu.latex-workshop)

---

## 🔧 Project Setup

```bash
git clone https://github.com/yourname/spectral-proof-of-RH.git
cd spectral-proof-of-RH
python3 -m venv .venv
source .venv/bin/activate
pip install -r scripts/requirements.txt
pip install -r requirements-dev.txt
````

Then open in VS Code:

```bash
code .
```

---

## 🧪 Tests and Verification

All changes must pass the **automated integrity suite**:

```bash
make check
```

This runs:

* Structural checks
* Label/proof validation
* DAG acyclicity
* Citation integrity (via `checkcites`)
* Python linting (`ruff`)
* Type checking (`mypy`)
* Auto-formatting (`black`)
* Full LaTeX build with PDF verification

💡 These are also accessible via `Tasks: Run Task` in VS Code.

---

## 🧼 Code Style and Hygiene

Formatting is handled automatically on save using:

* `black` (code formatter)
* `ruff` (linter + fixer)

Your code will auto-format and lint in VS Code if configured correctly (`.vscode/settings.json` is included).

To manually run:

```bash
make format
make lint
make typecheck
```

---

## 🧾 Task Automation

You can run structured build tasks via:

```bash
make check       # Validate entire repo
make deploy      # Deploy versioned PDF to docs/
make bump        # Increment patch version
```

Or via the VS Code task runner (⇧⌘P → Tasks: Run Task).

---

## 🧠 Codex/GPT Agent Compatibility

This repo supports modular GPT-based automation. All formal objects (lemmas, theorems, etc.) are modularly extracted and traceable via a DAG. When developing agents:

* Respect label and file naming rules (`thm_spectral_identity.tex` → `\label{thm:spectral_identity}`)
* Use `pyproject.toml` for tool configuration
* Update `agents.md` to register new roles

---

## 🧩 Directory Structure

```
src/
  chapters/
    01_foundations/
      intro.tex
      defs/
      lems/
      thms/
      proofs/
      summary.tex
  main.tex
docs/
  spectral_determinant_RH_equivalence_vX.Y.Z.pdf
tests/
  check_structure.py
scripts/
  bump_version.py
.vscode/
  settings.json
  tasks.json
```

---

## 🏁 Submitting a PR

1. Branch from `main`
2. Follow all formatting and DAG rules
3. Pass `make check`
4. Add test cases if you fix bugs
5. Describe your changes in the PR, especially if you're adding a new formal object or DAG node

---

Thank you for helping us build a formally sound, reproducible, and elegant proof system!

```