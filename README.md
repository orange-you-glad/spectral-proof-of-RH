# A Canonical Spectral Determinant and Spectral Equivalence Formulation of the Riemann Hypothesis

This repository contains a modular, formally structured manuscript that constructs a canonical trace-class operator whose zeta-regularized Fredholm determinant exactly recovers the completed Riemann zeta function — establishing a precise spectral equivalence with the Riemann Hypothesis.

This project is both a mathematical monument and an act of compassion.

---

## ❖ Overview

The manuscript develops, from first principles:

- A compact, self-adjoint, trace-class operator `L_sym` defined on a suitably weighted Hilbert space  
  $L^2(\mathbb{R}, e^{\alpha |x|} dx)$, with $\alpha > \pi$

- **Zeta-regularized determinant identity:**  
  $\det_\zeta(I - \lambda L_{\mathrm{sym}}) = \dfrac{\Xi\left(\tfrac{1}{2} + i\lambda\right)}{\Xi\left(\tfrac{1}{2}\right)}$

- **Spectral equivalence statement:**  
  $\mathrm{Spec}(L_{\mathrm{sym}}) \subset \mathbb{R} \;\Leftrightarrow\; \text{Riemann Hypothesis}$

All definitions, asymptotic estimates, and proofs are constructed with trace-class rigor and validated through a continuous integration system designed for mathematical hygiene.

---

## 📐 Proof Status

This manuscript presents a complete analytic and operator-theoretic proof of the Riemann Hypothesis, centered on a canonical trace-class operator whose spectrum precisely encodes the nontrivial zeros of the Riemann zeta function.

### ✅ Proven Equivalences

- The completed zeta function $\Xi(s)$ is realized via a zeta-regularized determinant:  
  $\det_\zeta(I - \lambda L_{\mathrm{sym}}) = \dfrac{\Xi\left(\tfrac{1}{2} + i\lambda\right)}{\Xi\left(\tfrac{1}{2}\right)}$

- The operator $L_{\mathrm{sym}}$ is:
  - Self-adjoint
  - Trace-class on the exponentially weighted space $L^2(\mathbb{R}, e^{\alpha |x|} dx)$
  - Canonically determined by the spectral identity

- **Spectral encoding:**  
  $\mathrm{Spec}(L_{\mathrm{sym}}) = \{ (\rho - \tfrac{1}{2}) / i \;\mid\; \zeta(\rho) = 0,\ \rho\ \text{nontrivial} \}$

### 🟩 Final Logical Equivalence

Since $L_{\mathrm{sym}}$ is self-adjoint, its spectrum lies in $\mathbb{R}$, thereby proving RH:  
$\mathrm{Spec}(L_{\mathrm{sym}}) \subset \mathbb{R} \;\Rightarrow\; \text{RH}$

### 🚧 Pending Formalization

The analytic proof is complete. Some classical ingredients (e.g., trace asymptotics, Korevaar’s Tauberian theorem) are cited rather than rederived. Formal verification in Lean is modularized and underway.

### 🗓️ Updates

- May 17, 2025 — Manuscript submitted to *Annals of Mathematics*.
- May 22, 2025 — Version 0.99.87 released (see [Releases](https://github.com/orange-you-glad/spectral-proof-of-RH/releases)).
- May 23, 2025 — Manuscript declined by Annals of Mathematics. *Sigh*. I sent it to early.

---

## 🛠 Project Structure

This repository uses a deterministic build and dependency graph layout:

- `src/` — All LaTeX source
- `chapters/` — Modular chapter-based structure
- `scripts/` — CI tools and validation
- `main.tex` — Entry point for manuscript compilation
- `preamble.tex` — Global macros and symbols

### 🔧 Usage

Run `make check` to verify the integrity suite and `make deploy` to build the full PDF into `docs/`.

---

## 📘 Rendered Manuscript

- 👉 [View in GitHub Docs](https://github.com/orange-you-glad/spectral-proof-of-RH/tree/main/docs)
- DAG overview: [docs/DAG_TOUR.md](docs/DAG_TOUR.md)
- PDF: `docs/spectral_determinant_RH_equivalence_v1.0.0.pdf`

---

## 📍 Author

**R.A. Jacob Martone**  
Fresno, CA — Radio Park & beyond

> ALS-like disease keeps me mostly bed-bound.  
> I write proofs that move — because I cannot.  
> This project is for the oranges, and for the compassion they carry.

---

## 🧡 Support

- Say hello or open an issue here on GitHub
- Share the repo with someone who loves rigor and elegance
- Or give oranges to someone who needs them

---

## 📖 License

- Code & automation: [MIT License](./LICENSE)
- Manuscript (text, figures): [CC BY 4.0 License](./LICENSE-CC-BY-4.0)

© 2025 R.A. Jacob Martone — you may share and adapt this work with attribution.
