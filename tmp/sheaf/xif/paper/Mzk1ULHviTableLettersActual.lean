/- U-C Step (viii) (beta) 字典核对: S3014PerLabelBound 与 paper 字母的精确恒等式,
   以及 (R4) exceptional->T 的 donor 转写. 对应 IUT IV L1566-1582 (d_i->D, exc->S/T, q->Q)
   与 L1701-1783 平均前的 per-label/per-collection 恒等式. -/
import tmp.sheaf.xif.paper.S3029StepVAlignmentActual
import tmp.sheaf.xif.paper.S3050StepVQExpansionActual
import tmp.sheaf.xif.paper.Mzk1ULHviTableActual
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHviTableLettersActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual

universe u v w

/-- 字典核对 (q->Q, d_i->D, exc->S/T): 实际 S3014PerLabelBound 的精确纸面字母形式:
(label^2 * (localNormOrder p jValue / (2l)) + sum_i d_i + 1) * log p
  + sum_{i in exc} (3 + log e_i),
其中 lambda_label := label^2 * localNormOrder(p, jValue) / (2l) (paper 的 -lambda 项),
d_i := localNormOrder(p, arithmeticTupleLocalDifferent_i) (paper 的 d_i),
e_i := logShellRamificationExponent_i (paper 的 exceptional e_i). -/
theorem S3014PerLabelBound_eq_paperLetters
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l label : Nat) :
    S3014PerLabelBound places tuple istar jValue exceptional l label =
      (((label : Real) ^ 2 * (localNormOrder p jValue / (2 * (l : Real))) +
          (∑ i, localNormOrder p (arithmeticTupleLocalDifferent places tuple i)) + 1) *
        Real.log (p : Real) +
        ∑ i ∈ exceptional, (3 + Real.log
          (logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real))) := by
  rw [S3029_perLabel_decomposition, S3050_stepVTerm_eq_label_sq_mul_unit]
  unfold S3050Unit S3029DifferentTerm S3029ExceptionalTerm
  push_cast
  ring

/-- exc->T 的 donor 转写 (R4): 若 exceptional 指标满足 p <= el 且
log e_i <= -3 + 4 log el, 则 exceptional 和 <= 4 * |I| * log el (当 p <= el),
这正是 paper 的 T 项 (L1701-1783 的 4(j+1)T 结构). -/
theorem S3014Exceptional_le_R4 {α : Type*} (I Istar : Finset α) (hsub : Istar ⊆ I)
    (e : α -> Real) {p el : Real} (hel : 1 <= el)
    (hR4 : ∀ i ∈ Istar, p <= el ∧ Real.log (e i) <= -3 + 4 * Real.log el) :
    (∑ i ∈ Istar, (3 + Real.log (e i))) <=
      4 * (I.card : Real) * (if p <= el then Real.log el else 0) :=
  LeanFormal.IUT.IUTIV.StepVProcessionAverage.exceptionalSum_le_r4 I Istar hsub e p el hel hR4

#print axioms S3014PerLabelBound_eq_paperLetters
#print axioms S3014Exceptional_le_R4

end LeanFormal.IUT.XiFPaper.Mzk1ULHviTableLettersActual
