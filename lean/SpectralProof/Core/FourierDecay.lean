import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpLog
import Mathlib.Analysis.Fourier.PaleyWiener

noncomputable section

open Real Complex MeasureTheory

namespace SpectralProof.Core

/--
Mollified spectral profile:
\[
φ_t(λ) := e^{-tλ^2} Φ(λ)
\]
used to define convolution kernels `k_t`.
-/
def φt (Φ : ℝ → ℂ) (t : ℝ) : ℝ → ℂ :=
  λ λ ↦ Complex.exp (-t * λ^2) * Φ λ

/--
Inverse Fourier transform (distributional) of φ.
Defined with positive exponential convention:
\[
k(x) := \int_{ℝ} φ(λ) e^{2πiλx} dλ
\]
-/
def fourierInv (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, φ t * Complex.exp (2 * π * Complex.I * t * x)

/--
Mollified inverse Fourier transform kernel:
\[
k_t(x) := \widehat{φ_t}(x)
\]
used in canonical convolution operator.
-/
def kt (Φ : ℝ → ℂ) (t : ℝ) : ℝ → ℂ :=
  fourierInv (φt Φ t)

/--
Decay bound for `k_t(x)`. If Φ ∈ PW_π, then `kt Φ t` decays exponentially.
This follows from the Paley–Wiener theorem and mollification.
-/
lemma decay_kt (Φ : ℝ → ℂ) (t : ℝ)
    (hΦ : ∃ A, ∀ λ, ‖Φ λ‖ ≤ A * Real.exp (π * |λ|)) :
    ∃ C b > 0, ∀ x, ‖kt Φ t x‖ ≤ C * Real.exp (-b * |x|) := by
  obtain ⟨A, hΦA⟩ := hΦ
  let φ := φt Φ t
  have bound : ∀ λ, ‖φ λ‖ ≤ A * Real.exp (-t * λ^2 + π * |λ|) := by
    intro λ
    simp only [φt, norm_mul, Complex.norm_eq_abs, abs_exp]
    calc ‖φ λ‖ = Real.exp (-t * λ^2) * ‖Φ λ‖ := by simp
      _ ≤ Real.exp (-t * λ^2) * A * Real.exp (π * |λ|) := by gcongr; exact hΦA λ
      _ = A * Real.exp (-t * λ^2 + π * |λ|) := by ring_nf

  -- Use Paley–Wiener-type decay: since φ is exponentially bounded in frequency,
  -- its inverse Fourier transform decays exponentially in space.
  have : ∃ C b > 0, ∀ x, ‖fourierInv φ x‖ ≤ C * Real.exp (-b * |x|) := by
    apply PaleyWiener.exp_decay_of_L1_bound
    use A
    intro λ
    exact bound λ

  exact this

end SpectralProof.Core
