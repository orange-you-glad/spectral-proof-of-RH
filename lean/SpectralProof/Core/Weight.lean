import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.L2Space

noncomputable section

open Real MeasureTheory ENNReal

namespace SpectralProof.Core

/--
Exponential weight:
\[
Ψ_α(x) := e^{ϕ(x)}
\]
Must satisfy ϕ(x) ≥ α |x| for some α > π to ensure trace-class decay.
-/
def autoWeight (ϕ : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (ϕ x)

/--
Weighted measure:
\[
μ_ϕ := e^{ϕ(x)} dx
\]
Used to define the exponentially weighted Hilbert space.
-/
def autoMeasure (ϕ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ofReal (autoWeight ϕ x))

/--
Exponentially weighted Hilbert space:
\[
H_ϕ := L^2(\mathbb{R}, e^{ϕ(x)} dx)
\]
Used throughout the spectral construction of Lt_π and Lsym_π.
-/
abbrev Hϕ (ϕ : ℝ → ℝ) := Lp ℂ 2 (autoMeasure ϕ)

section WithFixedϕ

variable {ϕ : ℝ → ℝ}

instance : NormedAddCommGroup (Hϕ ϕ) := by infer_instance
instance : InnerProductSpace ℂ (Hϕ ϕ) := by infer_instance
instance : CompleteSpace (Hϕ ϕ) := by infer_instance

end WithFixedϕ

end SpectralProof.Core
