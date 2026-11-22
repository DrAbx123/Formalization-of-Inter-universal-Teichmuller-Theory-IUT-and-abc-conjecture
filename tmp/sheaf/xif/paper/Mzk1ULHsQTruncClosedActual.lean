/- hsQ λ 数值界的 hspecial 槽闭合: 用 sophie DONE 14:42:07 的 `specialPrimes_log_sum_le_own`
   实例化 `Mzk1ULHSQLambdaNumericTruncActual.hsQ_lambda_numeric_trunc`，不再需要 hspecial 输入。
   旧 `Mzk1ULSpecialPrimesNumericActual` 作废（probe sorryAx + olean 缺失; Lead 已剪除）。 -/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericTruncActual
import tmp.sheaf.xif.paper.Mzk1ULSpecialPrimesOwnActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHsQTruncClosedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesOwnActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- hspecial 槽已由 own 件闭合: hsQ 数值界只剩 hbad' 一个输入。 -/
theorem hsQ_lambda_numeric_trunc_closed (dmod S_ar : ℝ)
    (hbad' : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      2 * dmod * S_ar) :
    Real.log (sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : ℝ) :=
  hsQ_lambda_numeric_trunc (T := T) dmod S_ar hbad' (specialPrimes_log_sum_le_own l)

#print axioms hsQ_lambda_numeric_trunc_closed

end LeanFormal.IUT.XiFPaper.Mzk1ULHsQTruncClosedActual
