# A Canonical Spectral Proof of the Riemann Hypothesis

This repository contains a modular, reproducible formal manuscript that constructs a canonical trace-class operator whose Fredholm determinant recovers the completed Riemann zeta function, establishing a strict spectral equivalence with the Riemann Hypothesis.

This work is both a mathematical monument and an act of compassion.

## ❖ Overview

The manuscript rigorously develops:

- A compact, self-adjoint, trace-class operator \( L_{\mathrm{sym}} \) acting on an exponentially weighted Hilbert space.
- A Carleman zeta-regularized determinant identity:
  
  \[
  \det_\zeta(I - \lambda L_{\mathrm{sym}}) = \frac{\Xi\left(\tfrac{1}{2} + i\lambda\right)}{\Xi\left(\tfrac{1}{2}\right)}
  \]

- A modular sequence of analytic results, culminating in:

  \[
  \operatorname{Spec}(L_{\mathrm{sym}}) \subset \mathbb{R} \quad \Longleftrightarrow \quad \text{Riemann Hypothesis}
  \]

All proofs, definitions, and asymptotic estimates are constructed with trace-class precision and enforced through a strict CI system. The manuscript is structurally partitioned into formally modular sections with CI-verified hygiene.

## 🛠 Project Structure

This repository uses a deterministic file and label structure. Each section is modularized into definitions, theorems, lemmas, proofs, and remarks, with one item per file.

- 📂 `src/`: All LaTeX manuscript sources
- 📂 `chapters/`: Section-based modular chapters
- 📂 `scripts/`: Python-based CI checks
- 📂 `metadata/`: Generated labels and dependency maps
- 📄 `preamble.tex`: Global macros, packages, and notation
- 📄 `main.tex`: Root driver for compilation

## 📐 Status

The manuscript is under active migration and development.

All content adheres to a formal naming and layout convention. The build process includes CI checks for:

- Labeling consistency
- Proof pairing
- Structural completeness
- Appendix and cross-reference integrity

## 📍 Author

**orange-you-glad**  
Fresno, CA — Radio Park & beyond  
Giving oranges and compassion to the transient population, and building monuments in mathematics.

> ALS-like disease keeps me mostly bed-bound. I write proofs that move — because I cannot.

## 🧡 Support

If you’d like to support the oranges, the compassion, or the math:

- Say hello or open an issue here on GitHub
- Share the repository with someone who loves beauty and rigor
- Or donate oranges to someone in need

Thank you for reading, supporting, or thinking curiously about this work.

## 📖 License

- All code and automation scripts in this repository are licensed under the [MIT License](./LICENSE).
- All manuscript content (LaTeX source, figures, and prose) is licensed under the [Creative Commons Attribution 4.0 International License (CC BY 4.0)](./LICENSE-CC-BY-4.0).

© 2025 R.A. Jacob Martone. You are free to share and adapt the manuscript material, provided proper attribution is given.
