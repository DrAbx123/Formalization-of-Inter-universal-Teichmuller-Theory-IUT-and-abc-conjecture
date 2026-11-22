/- hsQ trunc alias for consumers (Lead 2026-11-17 ruling: use trunc exact names).

Re-export of david's `Mzk1ULHSQLambdaNumericTruncActual.hsQ_lambda_numeric_trunc`
(DONE 14:10:24) with the special-primes input from
`Mzk1ULSpecialPrimesNumericActual.specialPrimes_log_sum_le`.  The previous global
`Mzk1ULStepVIIIInterfacesActual.hsQ_lambda` has the same shape and stays as alias;
the trunc decomposition avoids double counting the special primes (q^ADiv is defined
away from 2*3*5*l), with constant 5 + log l matching paper L1572.
-/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericTruncActual
import tmp.sheaf.xif.paper.Mzk1ULStepVIIIInterfacesActual
import tmp.sheaf.xif.paper.Mzk1ULSpecialPrimesOwnActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHsQTruncAliasActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIInterfacesActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesOwnActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- the trunc form of the s^Q bound (paper L1572), keeping the hbad' and hspecial
inputs explicit. -/
theorem hsQ_lambda_numeric_trunc' (dmod S_ar : ℝ)
    (hbad' : (∑ p ∈ (qSupportNoSpecial T ∪ dSupportNoSpecial T), Real.log (p : ℝ))
      ≤ 2 * dmod * S_ar)
    (hspecial : (∑ p ∈ Mzk1ULSQPaperActual.specialPrimes l, Real.log (p : ℝ))
      ≤ 5 + Real.log (l.value : ℝ)) :
    Real.log (Mzk1ULSQPaperActual.sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : ℝ) :=
  hsQ_lambda_numeric_trunc T dmod S_ar hbad' hspecial

/-- the trunc s^Q bound with the special-primes input discharged by the no-sorry
own bound (replaces the retired numeric donor). -/
theorem hsQ_lambda_numeric_trunc_own (dmod S_ar : ℝ)
    (hbad' : (∑ p ∈ (qSupportNoSpecial T ∪ dSupportNoSpecial T), Real.log (p : ℝ))
      ≤ 2 * dmod * S_ar) :
    Real.log (Mzk1ULSQPaperActual.sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : ℝ) :=
  hsQ_lambda_numeric_trunc T dmod S_ar hbad' (specialPrimes_log_sum_le_own l)

end LeanFormal.IUT.XiFPaper.Mzk1ULHsQTruncAliasActual
end