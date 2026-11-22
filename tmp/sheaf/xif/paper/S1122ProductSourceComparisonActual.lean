import tmp.sheaf.xif.paper.S1112SourceComparisonProductReductionActual

-- S1122: q_v-product source comparison, exact reduction and counterexample.
-- Global q-pilot is the bad q_v family (sourceBadQAbsLog / globalQAbsLogTotal),
-- NOT q=1/5.  ConcreteSourceComparisonActual/GlobalQPilotObjectActual are read
-- for the reduction; their duplicate PaperQPilotObject module names prevent
-- co-import, so the same actual definitions are used through S1112.
-- The comparison is exactly P.average <= sum_b |log q_b|.
-- Unconditional comparison is FALSE for one allowed bad q close to 1.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1122ProductSourceComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.S1112SourceComparisonProductReductionActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui uG uL uC uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)

/-- Exact arithmetic comparison: P.average <= q_v-product absolute-log sum. -/
def S1122ProductComparison : Prop :=
  P.procession.average ≤ sourceBadQAbsLog I.initial

/-- sourceBadQAbsLog is definitionally the q_v-product absolute-log sum. -/
theorem s1122ProductSum_eq :
    sourceBadQAbsLog I.initial =
      letI := I.initial.bad_finite
      ∑ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)| :=
  sourceBadQAbsLog_eq_qvProductSum (l := l) I.initial

/-- The concrete comparison is exactly the q_v-product comparison. -/
theorem s1122ConcreteComparison_iff_product
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    concreteSourceComparison O P ↔
      S1122ProductComparison (l := l) (I := I) P :=
  qvProductComparison_iff_badQAbsLog O P hO

/-- If the q_v-product sum is smaller than P.average, the comparison fails. -/
theorem s1122NotComparison_of_lt
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hlt : sourceBadQAbsLog I.initial < P.procession.average) :
    ¬ concreteSourceComparison O P :=
  not_concreteSourceComparison_of_lt_badQAbsLog O P hO hlt

/-- NEW counterexample: one allowed bad q = 24/25 gives source sum log(25/24),
which is less than P.average = log 25. This is a q_v product, not q=1/5. -/
theorem s1122ProductComparison_false_one_q_close
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hPavg : P.procession.average = Real.log (25 : Real))
    (hsource : sourceBadQAbsLog I.initial = Real.log ((25 : Real) / 24)) :
    ¬ concreteSourceComparison O P :=
  productComparison_false_single_q_close O P hO hPavg hsource

/-- Exact zero-bad-q obstruction: source sum zero while P.average positive. -/
theorem s1122ProductComparison_false_of_zero
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hzero : sourceBadQAbsLog I.initial = 0)
    (havg : 0 < P.procession.average) :
    ¬ concreteSourceComparison O P := by
  apply s1122NotComparison_of_lt O P hO
  rw [hzero]
  exact havg

/-- Exact gap: comparison fails precisely when the product sum is below
P.average. -/
def S1122ProductComparisonGap : Prop :=
  sourceBadQAbsLog I.initial < P.procession.average

theorem s1122Gap_iff_notComparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    S1122ProductComparisonGap (l := l) (I := I) P ↔
      ¬ concreteSourceComparison O P := by
  constructor
  · intro h
    exact s1122NotComparison_of_lt O P hO h
  · intro h
    by_contra hgap
    apply h
    apply (s1122ConcreteComparison_iff_product O P hO).mpr
    unfold S1122ProductComparison
    unfold S1122ProductComparisonGap at hgap
    linarith

#check s1122ConcreteComparison_iff_product
#check s1122ProductComparison_false_one_q_close
#check s1122ProductComparison_false_of_zero
#check s1122Gap_iff_notComparison

end LeanFormal.IUT.XiFPaper.S1122ProductSourceComparisonActual

end