/- U-C: log s^Q identity with the paper primorial (re-export, positivity explicit).

`Mzk1ULSQPaperActual.log_sQPaper_eq_sum_log` gives the paper's
log s^Q = Sum_{p in V(Q)^dst} log p with the support positivity hypotheses explicit.
Discharging them (from `underIntGen_natAbs_ge_one` + badF/different nonzeroness) is
a documented TODO (see Mzk1ULBadFPrimeSetNeBotActual header); this file only
re-exports the identity so consumers have a stable name.
-/
import tmp.sheaf.xif.paper.Mzk1ULSQPaperActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperUncondActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- PROVED (re-export): log(s^Q) = Sum over V(Q)^dst of log p, with the support
positivity hypotheses explicit (documented obligation to discharge). -/
theorem log_sQPaper_eq_sum_log_uncond
    (hq : ∀ p ∈ qSupportPrimes T, p ≠ 0)
    (hd : ∀ p ∈ dSupportPrimes T, p ≠ 0) :
    Real.log (sQPaper T) =
      ∑ p ∈ (qSupportPrimes T ∪ dSupportPrimes T ∪ specialPrimes l),
        Real.log (p : ℝ) :=
  log_sQPaper_eq_sum_log T hq hd

end LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperUncondActual
end
