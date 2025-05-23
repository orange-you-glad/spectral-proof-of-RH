import Mathlib.Analysis.FourierTransform
import Mathlib.MeasureTheory.Function.Lp
import Mathlib.Analysis.NormedSpace.Hilbert
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.SelfAdjoint
import SpectralProof.CanonicalOperator
import SpectralProof.DeterminantIdentity

noncomputable section

open Real Complex MeasureTheory

namespace SpectralProof

/--
Weight associated to an automorphic L-function. The input `ϕ : ℝ → ℝ`
is derived from the log-spectral growth of `Λ(1/2 + i λ, π)`.
-/
def autoWeight (ϕ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (ϕ x)

/-- Measure `exp(ϕ(x)) dx` used to define the weighted space. -/
def autoMeasure (ϕ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => autoWeight ϕ x)

/-- Weighted Hilbert space `H_ϕ = L^2(ℝ, exp(ϕ(x)) dx)`. -/
abbrev Hphi (ϕ : ℝ → ℝ) := Lp ℂ 2 (autoMeasure ϕ)

variable {ϕ : ℝ → ℝ}

/-- Inverse Fourier transform producing the canonical kernel. -/
def autoKernel (Φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ λ : ℝ, Φ λ * Complex.exp (2 * π * Complex.I * λ * x)

/--
Self-adjoint trace-class operator associated to an automorphic L-function.
This abstracts the weighted conjugation of the convolution operator with
kernel `autoKernel`.
-/
def Lsym_pi (Φ : ℝ → ℂ) (ϕ : ℝ → ℝ) :
    Hphi ϕ →ₗ[ℂ] Hphi ϕ := by
  -- TODO: construct the strong limit of the regularized operators
  admit

/-- `L_sym_π` is self-adjoint. -/
lemma Lsym_pi_selfAdjoint (Φ : ℝ → ℂ) (ϕ : ℝ → ℝ) :
    IsSelfAdjoint (Lsym_pi Φ ϕ) := by
  -- TODO: show symmetric kernel and weighted invariance
  admit

/-- `L_sym_π` is trace-class. -/
lemma Lsym_pi_traceClass (Φ : ℝ → ℂ) (ϕ : ℝ → ℝ) :
    TraceClass ℂ (Lsym_pi Φ ϕ) := by
  -- TODO: derive from Hilbert–Schmidt regularization
  admit

variable (Φ : ℝ → ℂ) (Λπ : ℂ → ℂ)

/--
Determinant identity recovering the completed automorphic L-function.
-/
theorem automorphic_det_identity (λ : ℂ) :
    zetaDet (Lsym_pi Φ ϕ) λ = Λπ (1 / 2 + Complex.I * λ) / Λπ (1 / 2) := by
  -- TODO: analytic continuation and canonical product expansion
  admit

/--
Generalized Riemann Hypothesis expressed as reality of the spectrum.
-/
theorem grh_iff_real_spectrum :
    (∀ ρ, Λπ ρ = 0 → ρ.re = 1 / 2) ↔
      (∀ μ ∈ spectrum (Lsym_pi Φ ϕ), μ.im = 0) := by
  -- TODO: relate zeros with eigenvalues via `automorphic_det_identity`
  admit

end SpectralProof

