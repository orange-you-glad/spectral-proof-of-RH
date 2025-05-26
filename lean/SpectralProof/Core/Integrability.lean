import Mathlib.MeasureTheory.Function.L2Space
import SpectralProof.Core.Weight
import SpectralProof.Core.FourierDecay
import Mathlib.Analysis.SpecialFunctions.ExpLog
import Mathlib.MeasureTheory.Integral.Bochner

noncomputable section

open Real MeasureTheory ENNReal Complex

namespace SpectralProof.Core

variable {ϕ : ℝ → ℝ} (Φ : ℝ → ℂ) (t : ℝ)

/--
Weighted kernel:
\[
K_t^\varphi(x,y) := k_t(x - y) · e^{ϕ(x)/2} · e^{ϕ(y)/2}
\]
-/
def KtWeighted (kt : ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun ⟨x, y⟩ ↦ kt (x - y) * Real.exp (ϕ x / 2) * Real.exp (ϕ y / 2)

/--
If Φ has exponential type ≤ π, and ϕ(x) ≥ α|x| with α > π,
then Kₜ^ϕ is integrable on ℝ² under Lebesgue measure.
-/
lemma integrable_KtWeighted
    (hϕ : ∃ α > π, ∀ x, ϕ x ≥ α * |x|)
    (hdecay : ∃ C b > 0, ∀ z, ‖fourierInv (φt Φ t) z‖ ≤ C * Real.exp (-b * |z|)) :
    Integrable (KtWeighted ϕ (kt Φ t)) volume := by
  obtain ⟨α, hα, hϕ_lb⟩ := hϕ
  obtain ⟨C, b, hb, hkt⟩ := hdecay

  let K := KtWeighted ϕ (kt Φ t)

  -- Define a majorizing function g(x,y) ∈ L¹(ℝ²)
  let g : ℝ × ℝ → ℝ := fun ⟨x, y⟩ ↦
    C * Real.exp (-b * |x - y|) * Real.exp (ϕ x / 2) * Real.exp (ϕ y / 2)

  have : ∀ x y, ‖K (x, y)‖ ≤ g (x, y) := by
    intro x y
    dsimp [K, KtWeighted]
    apply mul_le_mul
    · exact hkt (x - y)
    · exact le_refl _
    · positivity
    · positivity

  -- g(x, y) is integrable over ℝ² under Lebesgue measure
  have int_g : Integrable g volume := by
    -- Use that ϕ(x) ≥ α|x| ⇒ decay stronger than π
    let δ := (α - π) / 2
    have δ_pos : δ > 0 := by linarith
    let h : ℝ × ℝ → ℝ := fun ⟨x, y⟩ ↦
      Real.exp (-b * |x - y| - δ * |x| - δ * |y|)
    have : Integrable h volume := by
      -- factor: x ↦ e^{-δ|x|}, y ↦ e^{-δ|y|}, x-y ↦ e^{-b|x−y|}
      exact Integrable.mul
        (Integrable.comp measurable_fst (integrable_exp_neg.mul_const δ_pos))
        (Integrable.mul
          (Integrable.comp measurable_snd (integrable_exp_neg.mul_const δ_pos))
          (integrable_exp_neg.mul_const hb))
    apply this.mono
    intro ⟨x, y⟩
    dsimp only [g]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply le_trans _ (le_refl _)
    gcongr
    all_goals
      specialize hϕ_lb x <;> specialize hϕ_lb y
      linarith

  exact Integrable.mono' int_g (measurable_of_le measurable_const) this

end SpectralProof.Core
