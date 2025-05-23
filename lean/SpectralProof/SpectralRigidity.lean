import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.SelfAdjoint
import SpectralProof.CanonicalOperator
import SpectralProof.DeterminantIdentity

noncomputable section

open Complex

namespace SpectralProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral multiplicity of an eigenvalue of a compact operator. -/
def spectralMultiplicity (T : H →ₗ[ℂ] H) (μ : ℂ) : ℕ := by
  -- TODO: define via generalized eigenspaces
  admit

/--
Uniqueness of the spectral data from the zeta-regularized determinant. If two
compact, self-adjoint, trace-class operators have identical determinant
functions, then their spectra (with multiplicity) coincide.
-/
theorem spectrum_rigidity
    {T₁ T₂ : H →ₗ[ℂ] H}
    (h₁c : CompactOperator T₁) (h₂c : CompactOperator T₂)
    (h₁sa : IsSelfAdjoint T₁) (h₂sa : IsSelfAdjoint T₂)
    (h₁tr : TraceClass ℂ T₁) (h₂tr : TraceClass ℂ T₂)
    (hdet : ∀ λ : ℂ, zetaDet T₁ λ = zetaDet T₂ λ) :
    ∀ μ : ℂ, spectralMultiplicity T₁ μ = spectralMultiplicity T₂ μ := by
  -- TODO: use spectral theorem and canonical product representation
  admit

variable {φ : ℝ → ℂ} {α : ℝ}

/--
Characterization of `L_sym` by its determinant identity. Any compact,
self-adjoint, trace-class operator whose determinant agrees with
`L_sym` has exactly the same spectral data.
-/
lemma Lsym_determined
    (Ξ : ℂ → ℂ)
    (hdetL : ∀ λ : ℂ, zetaDet (Lsym φ α) λ = Ξ (1/2 + Complex.I * λ) / Ξ (1/2))
    {T : Hpsi α →ₗ[ℂ] Hpsi α}
    (hTc : CompactOperator T) (hTsa : IsSelfAdjoint T) (hTtr : TraceClass ℂ T)
    (hdetT : ∀ λ : ℂ, zetaDet T λ = Ξ (1/2 + Complex.I * λ) / Ξ (1/2)) :
    ∀ μ : ℂ, spectralMultiplicity T μ = spectralMultiplicity (Lsym φ α) μ := by
  -- TODO: apply `spectrum_rigidity` to `T` and `L_sym`
  admit

/--
Any operator with the same determinant as `L_sym` is unitarily equivalent to it.
-/
theorem unitary_equiv_Lsym
    (Ξ : ℂ → ℂ)
    (hdetL : ∀ λ : ℂ, zetaDet (Lsym φ α) λ = Ξ (1/2 + Complex.I * λ) / Ξ (1/2))
    {T : Hpsi α →ₗ[ℂ] Hpsi α}
    (hTc : CompactOperator T) (hTsa : IsSelfAdjoint T) (hTtr : TraceClass ℂ T)
    (hdetT : ∀ λ : ℂ, zetaDet T λ = Ξ (1/2 + Complex.I * λ) / Ξ (1/2)) :
    ∃ U : Unitary (Hpsi α), U.conj T = Lsym φ α := by
  -- TODO: deduce unitary equivalence from spectral coincidence
  admit

end SpectralProof

