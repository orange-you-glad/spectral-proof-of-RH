import SpectralProof.Operators.LsymPi
import SpectralProof.Determinants.CanonicalId
import SpectralProof.Determinants.SpectralMap

noncomputable section

open Complex

namespace SpectralProof.Equivalences

variable {ϕ : ℝ → ℝ}

/--
Generalized Riemann Hypothesis for Λ_π:
All nontrivial zeros lie on the critical line Re(ρ) = ½.
-/
def GRH (Λπ : ℂ → ℂ) : Prop :=
  ∀ ρ : ℂ, Λπ ρ = 0 → ρ.re = 1 / 2

/--
Spectral reality of the canonical operator:
All elements of the spectrum lie on the real axis.
-/
def SpectrumReal (Φ : ℝ → ℂ) (hϕ : ∃ α > π, ∀ x, ϕ x ≥ α * |x|) : Prop :=
  ∀ μ ∈ spectrum (SpectralProof.Operators.Lsym_pi Φ hϕ), μ.im = 0

/--
Main equivalence:
\[
\text{GRH for } Λ_π(s) \iff \text{Spec}(L_{\text{sym}}^\varphi) \subset ℝ
\]
-/
theorem GRH_iff_spec_real
    (Φ : ℝ → ℂ) (Λπ : ℂ → ℂ)
    (hϕ : ∃ α > π, ∀ x, ϕ x ≥ α * |x|)
    (hΦ_symm : ∀ λ, Φ (-λ) = conj (Φ λ))
    (hΛ_entire : Entire Λπ)
    (hcanonical : ∀ λ, zetaDet ϕ (SpectralProof.Operators.Lsym_pi Φ hϕ) λ
                        = Λπ (1 / 2 + I * λ) / Λπ (1 / 2)) :
    GRH Λπ ↔ SpectrumReal Φ hϕ := by
  constructor
  · -- GRH ⇒ spectrum ⊆ ℝ
    intro hGRH
    intro μ hμ
    -- Invert μ to get ρ = ½ + iμ
    let ρ := SpectralProof.Determinants.inverseSpectralMap μ
    have : Λπ ρ = 0 := by
      -- If μ ∈ Spec(L), then det_ζ(I - λL) = 0 ⇒ Λπ(ρ) = 0
      have := hcanonical μ
      rw [SpectralProof.Determinants.zetaDet_def] at this
      rw [this, div_eq_zero_iff] at this
      exact this.1
    specialize hGRH ρ this
    rw [SpectralProof.Determinants.inverseSpectralMap, add_re] at hGRH
    simp only [ofReal_re, ofReal_im, zero_add] at hGRH
    rw [← hGRH, zero_im]
  · -- spectrum ⊆ ℝ ⇒ GRH
    intro hSpec ρ hρ_zero
    let μ := SpectralProof.Determinants.spectralMap ρ
    have : μ ∈ spectrum (SpectralProof.Operators.Lsym_pi Φ hϕ) :=
      SpectralProof.Determinants.zero_maps_to_spectrum Φ Λπ hϕ ρ hρ_zero
    specialize hSpec μ this
    -- ρ = ½ + iμ ⇒ Re(ρ) = ½ iff Im(μ) = 0
    rw [SpectralProof.Determinants.spectralMap, sub_re, ofReal_re, zero_sub,
        neg_re, div_re, ofReal_re, zero_div, zero_sub] at hSpec
    simp only [ofReal_re, div_zero] at hSpec
    field_simp [I_ne_zero] at hSpec
    rw [← hSpec]
    exact rfl

end SpectralProof.Equivalences
