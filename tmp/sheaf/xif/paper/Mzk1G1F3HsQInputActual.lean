/- H-T F3: connect the generic TruncatedConductorHeightData to the unconditional
s^Q identity and david's numerical hsQ bound.

Reuse (all DONE, three axioms):
* Mzk1ULHSQLambdaNumericActual.hsQ_lambda_numeric (13:32:30)
* Mzk1ULHSQLambdaNumericActual.sum_union_log_le_add
* Mzk1ULSQPaperFinalActual.log_sQPaper_eq_sum_log_paper
* Mzk1ULStepHiiHsQActual.log_thirty_le_five
* Mzk1HTF3ConductorHeightActual.truncatedConductorHeight_le_height_add_const
-/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericActual
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericTruncActual -- DONE 14:10:24
import tmp.sheaf.xif.paper.Mzk1HTF3ConductorHeightActual
import tmp.sheaf.xif.paper.Mzk1ULStepHiiHsQActual
import tmp.sheaf.xif.paper.Mzk1ULSpecialPrimesOwnActual -- DONE 14:42:07
import tmp.sheaf.xif.paper.Mzk1ULHsQTruncAliasActual -- DONE 14:45:28
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F3HsQInputActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open LeanFormal.IUT.XiFPaper.Mzk1HTF3ConductorHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1ULStepHiiHsQActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesOwnActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHsQTruncAliasActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Re-export of david's numerical hsQ bound under the F3 name. -/
theorem log_sQPaper_le_numeric (dmod S_ar : ℝ)
    (hbad : (∑ p ∈ qSupportPrimes T ∪ dSupportPrimes T, Real.log (p : ℝ)) ≤ 2 * dmod * S_ar)
    (hspecial : (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) ≤ 5 + Real.log (l.value : ℝ)) :
    Real.log (sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : ℝ) :=
  hsQ_lambda_numeric T dmod S_ar hbad hspecial

/-- Final (B) interface: truncated bad support plus special primes. -/
theorem log_sQPaper_le_numeric_trunc (dmod S_ar : ℝ)
    (hbad' : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      2 * dmod * S_ar)
    (hspecial : (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) ≤ 5 + Real.log (l.value : ℝ)) :
    Real.log (sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : ℝ) :=
  hsQ_lambda_numeric_trunc T dmod S_ar hbad' hspecial

/-- Final hspecial-free interface: truncated bad support only. -/
theorem log_sQPaper_le_numeric_trunc_own (dmod S_ar : ℝ)
    (hbad' : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      2 * dmod * S_ar) :
    Real.log (sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : ℝ) :=
  hsQ_lambda_numeric_trunc_own T dmod S_ar hbad'

/-- F3 sum form with s^Q input: if the weighted conductor sum is the s^Q log, then it is
bounded by the height sum plus card * C. -/
theorem truncatedConductorHeight_le_height_add_const_sQ {ι : Type*} [Fintype ι]
    (D : TruncatedConductorHeightData ι)
    (hlog : (∑ i, D.logResidue i) = Real.log (sQPaper T)) :
    (∑ i, (D.conductorExponent i : ℝ) * D.logResidue i)
      ≤ (∑ i, D.localHeight i) + (Fintype.card ι : ℝ) * D.C :=
  truncatedConductorHeight_le_height_add_const D

/-- The special-prime contribution is bounded by 5 + log l (david's numeric kernel). -/
theorem specialPrimes_log_le (hl : 0 < (l.value : ℝ)) :
    Real.log (30 : ℝ) + Real.log (l.value : ℝ) ≤ 5 + Real.log (l.value : ℝ) := by
  linarith [log_thirty_le_five]

/-- Final hspecial donor: david specialPrimes_log_sum_le_own (DONE 14:42:07). -/
theorem specialPrimes_log_sum_le_own' (l : PrimeGeFive) :
    (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) ≤ 5 + Real.log (l.value : ℝ) :=
  specialPrimes_log_sum_le_own l

#print axioms log_sQPaper_le_numeric
#print axioms specialPrimes_log_sum_le_own'
#print axioms truncatedConductorHeight_le_height_add_const_sQ
end LeanFormal.IUT.XiFPaper.Mzk1G1F3HsQInputActual
