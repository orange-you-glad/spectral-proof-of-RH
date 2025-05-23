import Mathlib.Analysis.FourierTransform
import Mathlib.MeasureTheory.Function.Lp
import Mathlib.Analysis.NormedSpace.Hilbert

noncomputable section

open Real Complex MeasureTheory

namespace SpectralProof

/-- Exponential weight `ψ_α(x) = exp(α |x|)` used for the weighted space. -/
def psi (α : ℝ) (x : ℝ) : ℝ :=
  Real.exp (α * |x|)

/-- The measure `ψ_α(x) dx`. -/
def psiMeasure (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => psi α x)

/-- Weighted Hilbert space `H_{ψ_α} = L^2(ℝ, ψ_α(x) dx)`. -/
abbrev Hpsi (α : ℝ) := Lp ℂ 2 (psiMeasure α)

variable {α : ℝ}

/-- The inverse Fourier transform used to define the canonical kernel. -/
def fourierInv (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ λ : ℝ, φ λ * Complex.exp (2 * π * Complex.I * λ * x)

/-- Symmetric kernel `K` obtained from the canonical Fourier profile. -/
def canonicalKernel (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  fourierInv φ x

/-- Gaussian mollifier used in the convolution regularization. -/
def mollifier (ε : ℝ) (x : ℝ) : ℝ :=
  Real.exp (- (ε * x)^2)

/-- Mollified kernel `K_ε = mollifier ε * K`. -/
def mollifiedKernel (φ : ℝ → ℂ) (ε : ℝ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, mollifier ε t • canonicalKernel φ (x - t)

/-- Convolution operator with mollified kernel. -/
def Lε (φ : ℝ → ℂ) (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, mollifiedKernel φ ε (x - y) * f y

/-- The operator `L_ε` is Hilbert–Schmidt on `H_{ψ_α}`. -/
lemma Lε_hilbertSchmidt (φ : ℝ → ℂ) (ε : ℝ) :
    HilbertSchmidt ℂ (Hpsi α) (Hpsi α) := by
  -- TODO: analytic estimates showing square-integrable kernel
  admit

/-- Trace-class limit operator obtained from weighted conjugation. -/
def Lsym (φ : ℝ → ℂ) (α : ℝ) :
    Hpsi α →ₗ[ℂ] Hpsi α :=
  -- TODO: define as the strong limit of `Lε` under conjugation by weight
  by
    admit

end SpectralProof

