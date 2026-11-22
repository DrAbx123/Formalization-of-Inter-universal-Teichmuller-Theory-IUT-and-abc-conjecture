/- hbad 的 F 层目标（Lead 裁 (c) 2026-11-17）:
   SAr_F := logDifferentF (T.arithmetic.F) + logConductorFActual T;
   target: Sum_{qNo u dNo} log p <= 2*d_mod*SAr_F（再 + hspecial 得 paper L1572 形状）;
   q 段: <= d_mod*log f_F;  d 段: <= 2*d_mod*log d_F（2 的松弛由 coeff-2 版允许）;
   F vs Ftpd <=21 是 paper L1411-1425 已证（不是义务）; 只在 F 层喂 hii/D4 时显式记 21，
   与 kurt 的 C3 常数 56 对齐（56 已含 21）。dNo 仍为具名 obligation（sum-level local-support）。
   donor: Mzk1ULPaperLettersActual.logDifferentF（DONE）; Mzk1ULBadFPrimeSetActual.logConductorFActual（DONE）;
   Mzk1ULHSQLambdaNumericTruncActual.{qSupportNoSpecial,dSupportNoSpecial,sum_union_log_le_add}（DONE/在编）。 -/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericTruncActual
import tmp.sheaf.xif.paper.Mzk1ULHbadPaperCoeffActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadFLevelActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- F 层 S_ar = log d_F + log f_F（paper 口径，F vs Ftpd 差 <=21 已由 L1411-1425 证）。 -/
noncomputable def SAr_F : ℝ :=
  logDifferentF (T.arithmetic.F) + logConductorFActual (T := T)

/-- hbad 的 F 层两段界 => 截断 union <= 2*d_mod*SAr_F。 -/
theorem hbad_F_trunc (dmod : ℝ)
    (hq : (∑ p ∈ qSupportNoSpecial T, Real.log (p : ℝ)) ≤ dmod * logConductorFActual (T := T))
    (hd : (∑ p ∈ dSupportNoSpecial T, Real.log (p : ℝ)) ≤ 2 * dmod * logDifferentF (T.arithmetic.F))
    (hdmod : 0 ≤ dmod)
    (hld : 0 ≤ logDifferentF (T.arithmetic.F)) (hlf : 0 ≤ logConductorFActual (T := T)) :
    (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤ 2 * dmod * SAr_F (T := T) := by
  have h1 := sum_union_log_le_add (s := qSupportNoSpecial T) (t := dSupportNoSpecial T)
  have h2 : (∑ p ∈ qSupportNoSpecial T, Real.log (p : ℝ)) +
      (∑ p ∈ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      dmod * logConductorFActual (T := T) + 2 * dmod * logDifferentF (T.arithmetic.F) := by
    linarith
  have h3 : dmod * logConductorFActual (T := T) + 2 * dmod * logDifferentF (T.arithmetic.F) ≤
      2 * dmod * SAr_F (T := T) := by
    unfold SAr_F
    nlinarith [hdmod, hld, hlf]
  linarith [h1, h2, h3]

/-- 合成 paper 形状: 截断 union + hspecial => log sQ <= 2 d_mod SAr_F + 5 + log l。 -/
theorem hsQ_F_paper_shape (dmod : ℝ)
    (hbad : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤ 2 * dmod * SAr_F (T := T))
    (hspecial : (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) ≤ 5 + Real.log (l.value : ℝ)) :
    Real.log (sQPaper T) ≤ 2 * dmod * SAr_F (T := T) + 5 + Real.log (l.value : ℝ) := by
  have hdec := log_sQPaper_eq_trunc_add (T := T)
  linarith

#print axioms hbad_F_trunc
#print axioms hsQ_F_paper_shape

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadFLevelActual