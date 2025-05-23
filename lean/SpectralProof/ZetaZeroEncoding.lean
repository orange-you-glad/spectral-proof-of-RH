import Mathlib.Analysis.SpecialFunctions.Zeta
import Mathlib.Analysis.NormedSpace.Spectrum
import SpectralProof.CanonicalOperator
import SpectralProof.DeterminantIdentity

noncomputable section

open Complex Real

namespace SpectralProof

/-- Predicate for a nontrivial zero of the Riemann zeta function. -/
@[simp] def nontrivialZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1

/-- Encoding a zeta zero as an eigenvalue of the canonical operator. -/
@[simp] def mu (ρ : ℂ) : ℂ :=
  (ρ - 1 / 2) / Complex.I

/-- Mapping from nontrivial zeros to eigenvalues. -/
def zeroToEigen (ρ : ℂ) (hρ : nontrivialZetaZero ρ) :
    μ : ℂ := mu ρ :=
  rfl

variable {φ : ℝ → ℂ} {α : ℝ}

/-- Assuming the determinant identity, the spectrum of `Lsym` corresponds exactly
 to the encoded zeros. -/
theorem spectrum_eq_zeros
    (hdet : ∀ λ : ℂ, zetaDet (Lsym φ α) λ =
      (riemannZeta (1 / 2 + Complex.I * λ)) /
      riemannZeta (1 / 2)) :
    {μ | μ ∈ spectrum (Lsym φ α)} =
    {μ | ∃ ρ, nontrivialZetaZero ρ ∧ μ = mu ρ} := by
  -- TODO: use analytic Fredholm theory and determinant identity
  admit

/-- Bijection between zeros and eigenvalues preserving multiplicity. -/
lemma eigen_zero_bijection
    (hdet : ∀ λ : ℂ, zetaDet (Lsym φ α) λ =
      (riemannZeta (1 / 2 + Complex.I * λ)) /
      riemannZeta (1 / 2)) :
    ∀ ρ, nontrivialZetaZero ρ ↔
      (mu ρ) ∈ spectrum (Lsym φ α) := by
  -- TODO: derive from `spectrum_eq_zeros`
  admit

/-- Spectral characterization of the Riemann Hypothesis. -/
lemma rh_iff_real_spectrum
    (hdet : ∀ λ : ℂ, zetaDet (Lsym φ α) λ =
      (riemannZeta (1 / 2 + Complex.I * λ)) /
      riemannZeta (1 / 2)) :
    (∀ ρ, nontrivialZetaZero ρ → ρ.re = 1 / 2) ↔
      (∀ μ ∈ spectrum (Lsym φ α), μ.im = 0) := by
  -- TODO: use `eigen_zero_bijection` to translate statements
  admit

end SpectralProof

