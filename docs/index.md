# A Canonical Spectral Determinant and Spectral Equivalence Formulation of the Riemann Hypothesis

This repository contains a formally structured, operator-theoretic manuscript that establishes a canonical spectral encoding of the completed Riemann zeta function. It constructs a compact, self-adjoint, trace-class operator \( L_{\mathrm{sym}} \in \mathcal{C}_1(H_{\Psi_\alpha}) \), where \( H_{\Psi_\alpha} = L^2(\mathbb{R}, e^{\alpha|x|}dx) \), for \( \alpha > \pi \), and proves the determinant identity:
\[
\det\nolimits_{\zeta}(I - \lambda L_{\mathrm{sym}}) = \frac{\Xi\left(\tfrac{1}{2} + i\lambda\right)}{\Xi\left(\tfrac{1}{2}\right)},
\]
realizing the completed zeta function \( \Xi(s) \) as a spectral determinant.

---

## 📘 Read the Manuscript

- [📄 View PDF](./spectral_determinant_RH_equivalence_v0.99.0.pdf)

This identity is proven unconditionally and does not assume RH. The spectral equivalence
\[
\mathrm{RH} \iff \operatorname{Spec}(L_{\mathrm{sym}}) \subset \mathbb{R}
\]
is then rigorously established.

---

## 🔁 Proof Structure

- The proof is **modular** and **acyclic**, with every forward dependency formally tracked and resolved in downstream chapters.
- Analytic preconditions for the determinant (trace-class convergence, heat kernel asymptotics, spectral zeta growth) are established in Chapters 1–5 and Appendix D.
- No use of conjectural number theory or arithmetic assumptions is made.

All dependencies are visualized in the **Directed Acyclic Graph (DAG)** in Appendix B.

---

## 🛠 Project Structure

- `main.tex` — master LaTeX file
- `preamble.tex` — theorem styles and macros
- `chapters/` — modular core chapters 1–10
- `appendices/` — analytic infrastructure and speculative contexts
- `figs/` — includes optional visuals
- `docs/` — finalized compiled manuscript PDF

---

## 🧡 Author

**R.A. Jacob Martone**  
Fresno, California — *Radio Park and beyond*  
*Orange You Glad?*

> Living with ALS-like disease. Mostly bed-bound.  
> I write proofs that move — because I cannot.

---

## 📎 Related Links

- [Source Repository](https://github.com/orange-you-glad/spectral-proof-of-RH)
- [README (Top Level)](../README.md)
- Contact: jacob@orangeyouglad.org
