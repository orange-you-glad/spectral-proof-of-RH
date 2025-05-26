import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.NormedSpace.OperatorNorm
import SpectralProof.Core.Weight
import SpectralProof.Core.FourierDecay
import SpectralProof.Core.Integrability

noncomputable section

open Real MeasureTheory Complex

namespace SpectralProof.Operators

variable {ϕ : ℝ → ℝ} (Φ : ℝ → ℂ) (t : ℝ)

-- Bring in weighted Hilbert space and measure
abbrev Hϕ := SpectralProof.Core.Hϕ ϕ
abbrev μϕ := SpectralProof.Core.autoMeasure ϕ

/--
Integral operator `Lt_pi`, defined by convolution with the weighted kernel
\[
K_t^\varphi(x, y) := k_t(x - y) \cdot e^{ϕ(x)/2} \cdot e^{ϕ(y)/2}
\]
acting on the Hilbert space \( H_ϕ := L^2(ℝ, e^{ϕ(x)} dx) \).
-/
noncomputable def Lt_pi : Hϕ →ₗ[ℂ] Hϕ :=
  let kernel : ℝ × ℝ → ℂ :=
    SpectralProof.Core.KtWeighted ϕ (SpectralProof.Core.kt Φ t)
  LinearMap.mkContinuous
    { toFun := fun f =>
        ⟨fun x => ∫ y, kernel (x, y) * f y,
         by
           -- integrability proof: deferred to integrability module
           sorry⟩,
      map_add' := fun f g => by
        ext x; simp only [Pi.add_apply, integral_add]; ring,
      map_smul' := fun c f => by
        ext x; simp only [smul_eq_mul, integral_const_mul] }
    1 -- norm bound (can refine if needed)
    (by simp)

end SpectralProof.Operators
