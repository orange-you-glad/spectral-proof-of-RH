import Mathlib.Analysis.Trace
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

open Complex Topology

namespace TraceClass

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/--
Builds a trace-class operator from a continuous linear map `T : E →ₗ[𝕜] E`
and a proof that it is in fact trace-class.
-/
def mk' (T : E →ₗ[𝕜] E) (h : TraceClass 𝕜 E T) : TraceClass 𝕜 E := h

/--
If a sequence of trace-class operators `T_n` converges in trace norm,
then the limit is trace-class.
-/
theorem limit_closed {T : ℕ → TraceClass 𝕜 E}
    (hlim : CauchySeq (fun n ↦ (T n : E →L[𝕜] E))) :
    TraceClass 𝕜 E (Metric.completeSpace.hasLimit T).some := by
  exact Metric.completeSpace.complete T hlim

/--
If all operators in a Cauchy sequence are self-adjoint, then the limit is self-adjoint.
-/
theorem limit_isSelfAdjoint
    (T : ℕ → E →ₗ[𝕜] E)
    (h_symm : ∀ n, IsSelfAdjoint (T n)) :
    IsSelfAdjoint ((Metric.completeSpace.hasLimit (fun n ↦ ⟨T n, sorry⟩ : ℕ → TraceClass 𝕜 E)).some) := by
  -- This requires a lemma that the limit of symmetric operators is symmetric,
  -- which follows from the preservation of ⟪Tx, y⟫ = ⟪x, Ty⟫ under trace-norm convergence.
  sorry

end TraceClass
