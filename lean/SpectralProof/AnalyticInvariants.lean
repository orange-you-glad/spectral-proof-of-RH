import Mathlib.Analysis.Trace
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.OperatorNorm

noncomputable section

open Complex

namespace SpectralProof

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/--
For a trace-class operator `T : H →ₗ[ℂ] H`, the `n`-th trace power
is defined as the trace of `T^n`.

This is used in the zeta-regularized Fredholm determinant:
\[
\det_\zeta(I - λ T) = \exp\left(-\sum_{n=1}^\infty \frac{λ^n}{n} \operatorname{Tr}(T^n)\right)
\]
-/
def tracePower (T : H →ₗ[ℂ] H) (n : ℕ) : ℂ :=
  trace ℂ ((T ^ n : H →ₗ[ℂ] H))

end SpectralProof
