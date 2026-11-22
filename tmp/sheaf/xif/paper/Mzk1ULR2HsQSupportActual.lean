/- R2 (route 4.4): hsQ actual finite bad-prime support log-product（distinct primes; no urSQ）。
   donor: Mzk1ULHSQLambdaNumericTruncActual (DONE 14:10:24):
     log_sQPaper_eq_trunc_add : log sQ = Sum_{qNo u dNo} log p + Sum_special log p;
     hsQ_lambda_numeric_trunc (hbad') (hspecial) : log sQ <= 2 dmod S_ar + 5 + log l;
   Mzk1ULSQPaperFinalActual.log_sQPaper_eq_sum_log_paper (DONE 10:29:11): distinct bad primes;
   Mzk1ULSpecialPrimesOwnActual.specialPrimes_log_sum_le_own (DONE 14:42:07).
   本件为 actual-support 口径的 re-export/shape 文件（q/d/special 三段分开）。 -/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericTruncActual
import tmp.sheaf.xif.paper.Mzk1ULSpecialPrimesOwnActual
import tmp.sheaf.xif.paper.Mzk1ULSQPaperFinalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR2HsQSupportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesOwnActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- R2 hsQ actual support: distinct-primes identity log sQ = Sum_{V(Q)^dst} log p。 -/
theorem hsQ_actualSupport :
    Real.log (sQPaper T) =
      ∑ p ∈ (qSupportPrimes T ∪ dSupportPrimes T ∪ specialPrimes l),
        Real.log (p : Real) :=
  log_sQPaper_eq_sum_log_paper T

/-- R2 hsQ support split: q-support + d-support + special 三段分开。 -/
theorem hsQ_actualSupport_split :
    Real.log (sQPaper T) =
      (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : Real)) +
        (∑ p ∈ specialPrimes l, Real.log (p : Real)) :=
  log_sQPaper_eq_trunc_add (T := T)

/-- R2 hsQ 界: actual support 的 2d_mod S_ar + 5 + log l（hspecial 用 own 件闭合）。 -/
theorem hsQ_actualSupport_bound (dmod S_ar : Real)
    (hbad' : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : Real)) ≤
      2 * dmod * S_ar) :
    Real.log (sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : Real) :=
  hsQ_lambda_numeric_trunc (T := T) dmod S_ar hbad' (specialPrimes_log_sum_le_own l)

#print axioms hsQ_actualSupport
#print axioms hsQ_actualSupport_split
#print axioms hsQ_actualSupport_bound

end LeanFormal.IUT.XiFPaper.Mzk1ULR2HsQSupportActual
