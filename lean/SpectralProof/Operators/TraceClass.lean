import Mathlib.Analysis.Trace
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.BoundedLinearMaps

noncomputable section

open scoped Topology BigOperators
open Complex ContinuousLinearMap Filter

namespace SpectralProof.Core.TraceClass

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/--
Alias for providing a trace-class map given a map and a proof it is trace-class.
-/
def mk' (T : E →ₗ[𝕜] E) (h : TraceClass 𝕜 E T) : TraceClass 𝕜 E := h

/--
If a sequence of trace-class operators converges in trace-norm,
then its limit is also trace-class.
-/
theorem limit_closed {T : ℕ → TraceClass 𝕜 E}
    (h_cauchy : CauchySeq (fun n ↦ (T n : E →L[𝕜] E))) :
    ∃ Tlim : E →L[𝕜] E, TraceClass 𝕜 E Tlim := by
  -- The space of trace-class operators is closed in operator norm
  exact TraceClass.completeSpace.complete h_cauchy

/--
If each operator in a sequence is self-adjoint and the sequence converges
in operator norm, then the limit is self-adjoint.
-/
theorem limit_isSelfAdjoint
    {T : ℕ → E →ₗ[𝕜] E}
    (h_symm : ∀ n, IsSelfAdjoint (T n))
    (h_cauchy : CauchySeq (fun n ↦ (T n : E →L[𝕜] E))) :
    IsSelfAdjoint (Metric.completeSpace.hasLimit (fun n ↦ (T n : E →L[𝕜] E)).some) := by
  let f := fun n ↦ (T n : E →L[𝕜] E)
  let Tlim := Metric.completeSpace.hasLimit f
  let L := Tlim.some
  have : ∀ x y, ⟪L x, y⟫ = ⟪x, L y⟫ := by
    intros x y
    apply tendsto_nhds_unique
    · exact (continuous_inner (L x)).tendsto (L y)
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le _
        (fun n ↦ inner (T n x) y) (fun n ↦ inner x (T n y)) ?_ ?_
      · exact (continuous_inner.comp (continuous_linear_map.continuous_apply _)).tendsto _
      · exact (continuous_inner.comp (continuous_linear_map.continuous_apply _)).tendsto _
      · intro n; rw [h_symm n]
  exact ⟨this⟩

end SpectralProof.Core.TraceClass
