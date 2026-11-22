/- hbad 最终形态与 hsQ 接口对齐（Lead 选项 (B)）：
  s^Q 的支撑 = (qSupport \ special) ∪ (dSupport \ special) ∪ special（三者分解精确，因去掉 special 后与 special 不交）。
  hbad' 只作用在截断 union 上，hspecial 单独加，常数恰为 2dmod Sar + 5 + log l。
  donor: Mzk1ULSQPaperFinalActual.log_sQPaper_eq_sum_log_paper（DONE 10:29:11）;
  Mzk1ULSQPaperActual.{qSupportPrimes,dSupportPrimes,specialPrimes};
  Mzk1ULHSQLambdaNumericActual.sum_union_log_le_add（DONE 13:32:30）。 -/
import tmp.sheaf.xif.paper.Mzk1ULSQPaperFinalActual
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericActual
import tmp.sheaf.xif.paper.Mzk1ULBadFPrimeSetActual
import tmp.sheaf.xif.paper.Mzk1ULSArFmodActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSArFmodActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- q-support 去掉 special primes（paper 的 q^ADiv 定义避开 2·3·5·l）。 -/
noncomputable def qSupportNoSpecial : Finset ℕ :=
  qSupportPrimes T \ specialPrimes l

/-- d-support 去掉 special primes。 -/
noncomputable def dSupportNoSpecial : Finset ℕ :=
  dSupportPrimes T \ specialPrimes l

/-- s^Q 的 log 精确分解: log sQ = log(截断 union) + log(special 和)。 -/
theorem log_sQPaper_eq_trunc_add :
    Real.log (sQPaper T) =
      (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) +
        (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) := by
  rw [log_sQPaper_eq_sum_log_paper T]
  have hun : qSupportPrimes T ∪ dSupportPrimes T ∪ specialPrimes l =
      (qSupportNoSpecial T ∪ dSupportNoSpecial T) ∪ specialPrimes l := by
    unfold qSupportNoSpecial dSupportNoSpecial
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hun]
  have hdisj : Disjoint (qSupportNoSpecial T ∪ dSupportNoSpecial T) (specialPrimes l) := by
    unfold qSupportNoSpecial dSupportNoSpecial
    rw [Finset.disjoint_left]
    intro p hp hps
    simp only [Finset.mem_union, Finset.mem_sdiff] at hp
    rcases hp with (⟨_, hnot⟩ | ⟨_, hnot⟩)
    · exact hnot hps
    · exact hnot hps
  exact Finset.sum_union hdisj

/-- **hsQ λ 数值界（最终接口，(B) 版）**: 截断 union 界 + special 界 ⇒ log sQ ≤ 2dmod Sar+5+log l。 -/
theorem hsQ_lambda_numeric_trunc (dmod S_ar : ℝ)
    (hbad' : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      2 * dmod * S_ar)
    (hspecial : (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) ≤ 5 + Real.log (l.value : ℝ)) :
    Real.log (sQPaper T) ≤ 2 * dmod * S_ar + 5 + Real.log (l.value : ℝ) := by
  rw [log_sQPaper_eq_trunc_add T]
  linarith

/-- **hbad 最终形态**: 两个截断 per-segment 界 ⇒ 截断 union ≤ 2dmod·SAr（无 +5+log l）。 -/
theorem hbad_fmod_trunc (dmod Sar : ℝ)
    (hSar : Sar = Mzk1ULSArFmodActual.SAr_tripodal_Fmod T)
    (hq : (∑ p ∈ qSupportNoSpecial T, Real.log (p : ℝ)) ≤
      dmod * Mzk1ULBadFPrimeSetActual.logConductorFActual T)
    (hd : (∑ p ∈ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      dmod * logDifferentF T.arithmetic.Fmod)
    (hdmod : 0 ≤ dmod) (hSar0 : 0 ≤ Sar) :
    (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      2 * dmod * Sar := by
  have h1 := sum_union_log_le_add (s := qSupportNoSpecial T) (t := dSupportNoSpecial T)
  have h2 : (∑ p ∈ qSupportNoSpecial T, Real.log (p : ℝ)) +
      (∑ p ∈ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      dmod * (Mzk1ULBadFPrimeSetActual.logConductorFActual T + logDifferentF T.arithmetic.Fmod) := by
    linarith
  have h3 : Mzk1ULBadFPrimeSetActual.logConductorFActual T + logDifferentF T.arithmetic.Fmod = Sar := by
    rw [hSar]
    unfold SAr_tripodal_Fmod
    ring
  rw [h3] at h2
  have h4 : dmod * Sar ≤ 2 * dmod * Sar := by nlinarith [hSar0]
  linarith [h1, h2, h4]

#print axioms log_sQPaper_eq_trunc_add
#print axioms hsQ_lambda_numeric_trunc
#print axioms hbad_fmod_trunc

end LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual