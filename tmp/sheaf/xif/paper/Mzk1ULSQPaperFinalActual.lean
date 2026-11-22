/- U-C: unconditional paper identity log s^Q = Sum_{p in V(Q)^dst} log p.

The support positivity hypotheses of `Mzk1ULSQPaperActual.log_sQPaper_eq_sum_log` are
discharged by `Mzk1ULSQPositivity3Actual` (badFPrimeSet_nonzero via
`IsDedekindDomain.mem_primesOverFinset_iff`+`Ideal.ne_bot_of_mem_primesOver`,
differentPlaces_nonzero via `normalizedFactors`/`primeFactors` + differentIdeal != 0).
This is the paper L1436-1501 primorial identity, unconditional.
-/
import tmp.sheaf.xif.paper.Mzk1ULSQPaperActual
import tmp.sheaf.xif.paper.Mzk1ULSQPositivity3Actual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPositivity3Actual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- PROVED (unconditional): log(s^Q) = Sum over V(Q)^dst of log p, the paper
primorial identity with all support positivity discharged. -/
theorem log_sQPaper_eq_sum_log_paper :
    Real.log (sQPaper T) =
      ∑ p ∈ (qSupportPrimes T ∪ dSupportPrimes T ∪ specialPrimes l),
        Real.log (p : ℝ) :=
  log_sQPaper_eq_sum_log T (qSupportPrimes_ne_zero T) (dSupportPrimes_ne_zero T)

end LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperFinalActual
end
