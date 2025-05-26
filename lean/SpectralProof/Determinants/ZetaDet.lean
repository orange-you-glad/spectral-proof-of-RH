import Mathlib.Analysis.Trace
import Mathlib.Topology.Algebra.InfiniteSum
import Mathlib.Analysis.NormedSpace.OperatorNorm
import SpectralProof.Core.Weight

noncomputable section

open Complex BigOperators Topology

namespace SpectralProof.Determinants

variable {ϕ : ℝ → ℝ}

/--
The `n`-th trace power of a trace-class operator T: Tr(Tⁿ).
Used in the zeta-determinant expansion.
-/
def tracePower (T : Hϕ ϕ →ₗ[ℂ] Hϕ ϕ) (n : ℕ) : ℂ :=
  trace ℂ ((T ^ n : Hϕ ϕ →ₗ[ℂ] Hϕ ϕ))

/--
Zeta-regularized Fredholm determinant of a trace-class operator:
\[
\det_\zeta(I - λ T) = \exp\left(-\sum_{n=1}^\infty \frac{λ^n}{n} \operatorname{Tr}(T^n)\right)
\]
This defines an entire function of order 1, with zeros encoding the spectrum of T.
-/
noncomputable def zetaDet (T : Hϕ ϕ →ₗ[ℂ] Hϕ ϕ) (λ : ℂ) : ℂ :=
  let s : ℕ → ℂ := fun n => (λ ^ n / n) * tracePower T n
  exp (-∑' n, s n)

lemma zetaDet_def (T : Hϕ ϕ →ₗ[ℂ] Hϕ ϕ) (λ : ℂ) :
    zetaDet T λ = exp (-(∑' n, (λ ^ n / n) * tracePower T n)) := rfl

/--
If T is trace-class, then the zeta determinant series converges absolutely.
-/
lemma zetaDet_converges
    {T : Hϕ ϕ →ₗ[ℂ] Hϕ ϕ} (h : TraceClass ℂ (Hϕ ϕ) T) (λ : ℂ) :
    Summable (fun n ↦ (λ ^ n / n) * tracePower T n) := by
  -- Bound |Tr(T^n)| using trace norm
  have h_trace_bound : ∀ n, ‖T ^ n‖₁ ≤ ‖T‖₁ ^ n := by
    intro n; exact TraceClass.norm_pow_le_pow_norm h n

  have h_abs_bound : ∀ n, ‖(λ ^ n / n) * tracePower T n‖ ≤ (‖λ‖ ^ n / n) * ‖T‖₁ ^ n := by
    intro n
    calc
      ‖(λ ^ n / n) * tracePower T n‖
          ≤ (‖λ‖ ^ n / n) * ‖tracePower T n‖ : by
            apply norm_mul_le
      _ ≤ (‖λ‖ ^ n / n) * ‖T ^ n‖₁           : by
            apply mul_le_mul_of_nonneg_left (TraceClass.norm_trace_le _)
            positivity
      _ ≤ (‖λ‖ ^ n / n) * (‖T‖₁ ^ n)         : by
            apply mul_le_mul_of_nonneg_left (h_trace_bound n)
            positivity

  -- Now apply comparison with summable exponential series
  have : Summable (fun n ↦ (‖λ‖ ^ n / n) * (‖T‖₁ ^ n)) := by
    apply summable_of_nonneg_of_le
      (fun n ↦ by positivity)
      (fun n ↦ h_abs_bound n)
    apply summable_mul_right
    exact summable_mul_div_pow_of_lt_one ‖λ‖ ‖T‖₁ zero_lt_one

  exact summable_of_norm_bounded _ this h_abs_bound

end SpectralProof.Determinants
