import SpectralProof.Operators.LsymPi
import SpectralProof.Determinants.ZetaDet
import SpectralProof.Determinants.CanonicalId

noncomputable section

open Complex Spectrum

namespace SpectralProof.Determinants

variable {ϕ : ℝ → ℝ}

/--
Spectral map: sends a nontrivial zeta zero ρ to
\[
μ_ρ := \frac{1}{i}(ρ - ½)
\]
which lies in the spectrum of the canonical operator Lsym_π.
-/
def spectralMap (ρ : ℂ) : ℂ :=
  (ρ - 1 / 2) / I

/--
Inverse spectral map: recovers ρ from a spectral value μ.
\[
ρ := ½ + iμ
\]
-/
def inverseSpectralMap (μ : ℂ) : ℂ :=
  1 / 2 + I * μ

lemma spectralMap_inverse :
    ∀ μ, spectralMap (inverseSpectralMap μ) = μ := by
  intro μ
  simp [spectralMap, inverseSpectralMap, sub_add_cancel, div_mul_cancel]
  norm_num

lemma inverseMap_spectralMap :
    ∀ ρ, inverseSpectralMap (spectralMap ρ) = ρ := by
  intro ρ
  simp [spectralMap, inverseSpectralMap, ← add_sub_assoc, mul_div_cancel_left]
  ring_nf

/--
If Λ_π(ρ) = 0, then μ_ρ := (ρ - ½)/i lies in the spectrum of Lsym_π.
This follows from the canonical determinant identity.
-/
lemma zero_maps_to_spectrum
    (Φ : ℝ → ℂ) (Λπ : ℂ → ℂ) (hϕ : ∃ α > π, ∀ x, ϕ x ≥ α * |x|)
    (ρ : ℂ) (hρ : Λπ ρ = 0) :
    spectralMap ρ ∈ spectrum (Lsym_pi Φ hϕ) := by
  -- Assume canonical determinant identity holds:
  -- det_ζ(I - λ L) = Λπ(½ + iλ)/Λπ(½)
  let λ := spectralMap ρ
  have hdet := canonical_det_identity Φ Λπ hϕ λ
  rw [spectralMap, ← ofReal_div, ← Complex.div_eq_inv_mul] at hdet
  rw [hρ, zero_div, hdet, div_eq_zero_iff] at hdet
  obtain ⟨h, _⟩ := hdet
  -- det_ζ(I - λL) = 0 ⇒ λ ∈ Spec(L) (Fredholm theory)
  exact Spectrum.of_det_zeta_zero λ (Lsym_pi Φ hϕ) h

end SpectralProof.Determinants
