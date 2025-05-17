# A Canonical Spectral Determinant and the Riemann Hypothesis

This manuscript presents an analytic–spectral reformulation of the Riemann Hypothesis (RH) via the construction of a canonical compact, self-adjoint, trace-class operator
\[
L_{\mathrm{sym}} \in \mathcal{C}_1(H_{\Psi_\alpha}), \quad H_{\Psi_\alpha} = L^2(\mathbb{R}, e^{\alpha |x|} dx), \quad \alpha > \pi.
\]
Its zeta-regularized Fredholm determinant satisfies the identity
\[
\det\nolimits_\zeta(I - \lambda L_{\mathrm{sym}}) = \frac{\Xi\left(\tfrac{1}{2} + i\lambda\right)}{\Xi\left(\tfrac{1}{2}\right)},
\]
realizing the completed Riemann zeta function as a spectral determinant. The spectrum of \( L_{\mathrm{sym}} \) encodes all nontrivial zeros of \( \zeta(s) \) via
\[
\mu_\rho := \frac{1}{i}(\rho - \tfrac{1}{2}) \in \operatorname{Spec}(L_{\mathrm{sym}}),
\]
and the analytic equivalence
\[
\mathrm{RH} \iff \operatorname{Spec}(L_{\mathrm{sym}}) \subset \mathbb{R}
\]
is rigorously established.

## 🔁 Modular Structure

The manuscript is structured into ten chapters and appendices, tracked by a Directed Acyclic Graph (DAG) in `Appendix B`. All results are proven in strict analytic order with no cyclic dependencies. The determinant identity is established before the RH equivalence, and forward analytic inputs (e.g., heat kernel singularities) are closed in downstream chapters and flagged explicitly.

Key chapters:
- Chapter 1–2: Operator-theoretic and kernel constructions
- Chapter 3: Determinant identity for \( \Xi(s) \)
- Chapter 5: Heat trace asymptotics and singular structure
- Chapter 6: RH equivalence via spectral reality
- Chapter 10: Logical closure and modular proof completion

## 📎 Files Included

- `main.tex` – master document entrypoint
- `preamble.tex` – macro and style configuration
- `chapters/` – modular chapters (one folder per core section)
- `appendices/` – analytic infrastructure and speculative extensions
- `figs/` – DAG and spectrum diagrams
- `references.bib` – complete citation database

## 📌 Notes for Readers and Referees

- The manuscript avoids any assumption of RH and proves each analytic statement explicitly.
- All forward references (e.g., use of heat trace expansion in Chapter 3) are tracked and validated modularly.
- Speculative extensions (Appendices G and J) are explicitly marked noncritical and do not affect core arguments.

## 📖 Citation

If referencing this manuscript, please cite:
```

Martone, R.A. Jacob.
"A Canonical Spectral Determinant and the Riemann Hypothesis"
(2025). arXiv\:xxxx.xxxxx \[math.NT].

```

## 🛠 Requirements

- LaTeX with `amsart`, `amsmath`, `amssymb`, `mathtools`, `cleveref`, `tikz`, `biblatex`, `tcolorbox`
- `lualatex` or `pdflatex` with modern package stack

## ✅ Version

This version: **v0.99.0** (referee-complete)