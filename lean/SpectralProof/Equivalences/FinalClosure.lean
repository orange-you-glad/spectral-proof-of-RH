import SpectralProof.Equivalences.RH_iff_SpecReal

noncomputable section

open Complex

namespace SpectralProof.Equivalences

variable {ϕ : ℝ → ℝ}

/--
Final logical closure of the spectral reformulation:
\[
\boxed{\text{GRH for } Λ_π \iff \text{Spec}(L_{\text{sym}}^\varphi) \subset \mathbb{R}}
\]

This equivalence is canonical: the spectrum of `Lsym_π` contains (μ_ρ) for each zero ρ of Λ_π, and
is real if and only if all ρ lie on the critical line Re(ρ) = ½.
-/
theorem GRH_spectral_closure
    (Φ : ℝ → ℂ) (Λπ : ℂ → ℂ)
    (hϕ : ∃ α > π, ∀ x, ϕ x ≥ α * |x|)
    (hΦ_symm : ∀ λ, Φ (-λ) = conj (Φ λ))
    (hΛ_entire : Entire Λπ)
    (hcanonical : ∀ λ, zetaDet ϕ (SpectralProof.Operators.Lsym_pi Φ hϕ) λ
                        = Λπ (1 / 2 + I * λ) / Λπ (1 / 2)) :
    (∀ ρ, Λπ ρ = 0 → ρ.re = 1 / 2)
      ↔ (∀ μ ∈ spectrum (SpectralProof.Operators.Lsym_pi Φ hϕ), μ.im = 0) :=
  GRH_iff_spec_real Φ Λπ hϕ hΦ_symm hΛ_entire hcanonical

end SpectralProof.Equivalences
