arXiv Submission: A Canonical Spectral Determinant and the Riemann Hypothesis
Author: R.A. Jacob Martone
Date: [YYYY-MM-DD]
Version: v0.99.0 (referee-aligned)

Summary:
This manuscript constructs a canonical compact, self-adjoint, trace-class operator L_sym on a weighted Hilbert space H_{Ψ_α}, for α > π, whose zeta-regularized Fredholm determinant recovers the completed Riemann zeta function:
    det_ζ(I - λ L_sym) = Ξ(1/2 + iλ) / Ξ(1/2).
The spectrum of L_sym encodes the nontrivial zeros of ζ(s), and we prove the analytic equivalence:
    RH ⇔ Spec(L_sym) ⊂ ℝ.

Modular Structure:
- The proof is structured modularly and tracked by a Directed Acyclic Graph (DAG).
- Forward dependencies (e.g., heat kernel estimates used in Chapter 3) are proved downstream and formally acyclic.
- Speculative extensions in Appendices G and J are marked noncritical and do not influence core results.

File Structure:
- main.tex: top-level driver file
- preamble.tex: macros and formatting
- chapters/: modular chapters (1–10)
- appendices/: analytic tools and infrastructure
- references.bib: BibTeX database

Compilation:
Use pdflatex or lualatex with biber:
    pdflatex main
    biber main
    pdflatex main
    pdflatex main

Most figures are rendered via TikZ; however, some appendix figures (e.g., DAG diagrams) are precompiled as standalone PDFs and must be included in the arXiv upload. These are located in the `figs/` directory.

Contact:
jacob@orangeyouglad.org
