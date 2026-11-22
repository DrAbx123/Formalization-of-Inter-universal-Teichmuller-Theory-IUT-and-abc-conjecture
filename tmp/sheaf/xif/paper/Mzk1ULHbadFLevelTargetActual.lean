/- hbad F 层 target 的显式 Prop 与命名义务（Lead 裁 (c)+(2)）:
   hbad_F_coeff2 dmod := (Sum_{qNo u dNo} log p) <= 2*dmod*SAr_F;
   hbad_F_paper dmod := ... <= 2*dmod*SAr_F + 5 + log l;
   剩余具名义务 (obligation: prop13_local_support) = hbad_F_coeff2 的证明
   （Prop1.3(i) sum-level local support, F 层 differentPlaces/badFPrimeSet）。
   hbad_F_trunc 是本文件的别名目标；hsQ_F_paper_shape 把 hbad_F_paper 接到 log sQ。 -/
import tmp.sheaf.xif.paper.Mzk1ULHbadFLevelActual
import tmp.sheaf.xif.paper.Mzk1ULHbadPaperCoeffActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadFLevelTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHbadFLevelActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **coefficient-2 目标（具名义务 prop13_local_support）**: 截断 union 的 primorial 界。
    这是 paper L1555-1572 / Prop1.3(i) sum-level local support 的 Lean 形式; 未证前作为显式 Prop。 -/
def hbad_F_coeff2 (dmod : ℝ) : Prop :=
  (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤ 2 * dmod * SAr_F (T := T)

/-- paper 形状（含 special 常数; 若把 special 并入则用 hspecial 加）。 -/
def hbad_F_paper (dmod : ℝ) : Prop :=
  (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
    2 * dmod * SAr_F (T := T) + 5 + Real.log (l.value : ℝ)

/-- hbad_F_trunc 的别名：由两段界得 coefficient-2 target。 -/
theorem hbad_F_coeff2_of_trunc (dmod : ℝ)
    (hq : (∑ p ∈ qSupportNoSpecial T, Real.log (p : ℝ)) ≤ dmod * logConductorFActual (T := T))
    (hd : (∑ p ∈ dSupportNoSpecial T, Real.log (p : ℝ)) ≤ 2 * dmod * logDifferentF (T.arithmetic.F))
    (hdmod : 0 ≤ dmod) (hld : 0 ≤ logDifferentF (T.arithmetic.F))
    (hlf : 0 ≤ logConductorFActual (T := T)) :
    hbad_F_coeff2 (T := T) dmod := by
  unfold hbad_F_coeff2
  exact hbad_F_trunc (T := T) dmod hq hd hdmod hld hlf

/-- coefficient-2 target => paper shape（+5+log l 进入; special 由 hspecial 另行）。 -/
theorem hbad_F_paper_of_coeff2 (dmod : ℝ) (h : hbad_F_coeff2 (T := T) dmod) :
    hbad_F_paper (T := T) dmod := by
  unfold hbad_F_coeff2 at h
  unfold hbad_F_paper
  have hlogl : (0 : ℝ) ≤ Real.log (l.value : ℝ) :=
    Real.log_nonneg (by exact_mod_cast l.prime.pos)
  linarith

/-- paper shape => log sQ 的 paper 形状（special 分离版）。 -/
theorem hsQ_F_paper_of_hbad (dmod : ℝ) (h : hbad_F_coeff2 (T := T) dmod)
    (hspecial : (∑ p ∈ specialPrimes l, Real.log (p : ℝ)) ≤ 5 + Real.log (l.value : ℝ)) :
    Real.log (sQPaper T) ≤ 2 * dmod * SAr_F (T := T) + 5 + Real.log (l.value : ℝ) := by
  unfold hbad_F_coeff2 at h
  have hdec := log_sQPaper_eq_trunc_add (T := T)
  linarith

#print axioms hbad_F_coeff2_of_trunc
#print axioms hbad_F_paper_of_coeff2
#print axioms hsQ_F_paper_of_hbad

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadFLevelTargetActual