import SpectralProof.Core.FourierDecay
import SpectralProof.Core.Weight
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ExpLog

noncomputable section

open Real Complex MeasureTheory

namespace SpectralProof.Core

variable {ϕ : ℝ → ℝ}

/--
Unweighted convolution kernel:
\[
K_t(x, y) := k_t(x - y)
\]
This is the base kernel before applying exponential weighting.
-/
def Kt (kt : ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun ⟨x, y⟩ ↦ kt (x - y)

/--
Exponentially weighted convolution kernel:
\[
K_t^ϕ(x, y) := K_t(x, y) \cdot e^{ϕ(x)/2} \cdot e^{ϕ(y)/2}
\]
Used to define `Lt_pi` on the weighted Hilbert space `Hϕ`.
-/
def KtWeighted (kt : ℝ → ℂ) (ϕ : ℝ → ℝ) : ℝ × ℝ → ℂ :=
  fun ⟨x, y⟩ ↦ kt (x - y) * Real.exp (ϕ x / 2) * Real.exp (ϕ y / 2)

/--
Measurability of the weighted kernel on ℝ².
Required to show `KtWeighted` is Bochner-integrable.
-/
lemma measurable_KtWeighted (kt : ℝ → ℂ) (ϕ : ℝ → ℝ)
    (hkt : Measurable kt) (hϕ : Measurable ϕ) :
    Measurable (KtWeighted kt ϕ) := by
  apply Measurable.mul
  · exact hkt.comp (measurable_sub.comp ⟨measurable_fst, measurable_snd⟩)
  · apply Measurable.mul
    · exact (continuous_exp.comp (continuous_const.mul (hϕ.comp measurable_fst) continuous_const)).measurable
    · exact (continuous_exp.comp (continuous_const.mul (hϕ.comp measurable_snd) continuous_const)).measurable

end SpectralProof.Core
