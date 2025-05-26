import SpectralProof.Operators.LtPi
import SpectralProof.Core.Integrability
import Mathlib.Analysis.Trace
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

open Real Complex MeasureTheory Filter

namespace SpectralProof.Operators

variable {ϕ : ℝ → ℝ}

/--
Canonical operator \( L_{\text{sym}}^\varphi := \lim_{t → 0^+} L_t^\varphi \),
defined as a limit in the trace-norm topology of `Hϕ := L²(ℝ, e^{ϕ(x)} dx)`.
Assumes exponential decay of Φ via Paley–Wiener and ϕ(x) ≥ α|x| for α > π.
-/
noncomputable def Lsym_pi
    (Φ : ℝ → ℂ) (hϕ : ∃ α > π, ∀ x, ϕ x ≥ α * |x|) :
    Hϕ ϕ →ₗ[ℂ] Hϕ ϕ :=
  let seq := fun n : ℕ ↦ Lt_pi Φ (1 / (n + 1 : ℝ))
  let ops : ℕ → TraceClass ℂ (Hϕ ϕ) := fun n =>
    TraceClass.mk' (seq n) (by
      apply SpectralProof.Core.integrable_KtWeighted Φ (1 / (n + 1 : ℝ)) ϕ hϕ
      -- Use Paley–Wiener decay for Φ here
      sorry)
  let lim := Metric.completeSpace.hasLimit (ops : ℕ → TraceClass ℂ (Hϕ ϕ))
  TraceClass.continuousLinearMap lim.some

/--
Trace-class inclusion of `Lsym_pi`, via closure of the trace-class ideal.
-/
lemma trace_class_Lsym_pi
    (Φ : ℝ → ℂ) (hϕ : ∃ α > π, ∀ x, ϕ x ≥ α * |x|) :
    TraceClass ℂ (Hϕ ϕ) (Lsym_pi Φ hϕ) := by
  let seq := fun n : ℕ ↦ Lt_pi Φ (1 / (n + 1 : ℝ))
  let ops := fun n ↦ TraceClass.mk' (seq n)
    (SpectralProof.Core.integrable_KtWeighted Φ _ ϕ hϕ sorry)
  exact TraceClass.limit_closed ops

/--
If Φ is real on the real axis (i.e. Φ(-λ) = conj Φ(λ)), then Lsym_π is symmetric.
This implies self-adjointness since Lsym_π is compact.
-/
lemma self_adjoint_Lsym_pi
    (Φ : ℝ → ℂ)
    (hΦ_symm : ∀ λ, Φ (-λ) = Complex.conj (Φ λ))
    (hϕ : ∃ α > π, ∀ x, ϕ x ≥ α * |x|) :
    IsSelfAdjoint (Lsym_pi Φ hϕ) := by
  -- Strategy: show kernel k_t is real-valued and even ⇒ kernel symmetric
  -- then L_t are symmetric ⇒ limit is symmetric
  sorry

end SpectralProof.Operators
