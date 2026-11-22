import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual

-- S1112: q_v-product source comparison = P.average <= sum_b |log q_b|.
-- Existing reduction reproduced directly; the unconditional product
-- comparison is FALSE for one allowed bad q close to 1.
-- Not the already-refuted single q=1/5 substitution.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1112SourceComparisonProductReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui uG uL uC uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- sourceBadQAbsLog is definitionally the q_v-product absolute-log sum. -/
theorem sourceBadQAbsLog_eq_qvProductSum
    (S : SourceDefinition31Data (l := l)) :
    sourceBadQAbsLog S =
      letI := S.bad_finite
      ∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)| := rfl

/-- Existing reduction: product comparison is exactly the arithmetic
inequality P.average <= sum |log q_b|. -/
theorem qvProductComparison_iff_badQAbsLog
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    concreteSourceComparison O P ↔
      P.procession.average ≤ sourceBadQAbsLog I.initial := by
  unfold concreteSourceComparison
  rw [hO, sourceQPilotSignedLog]
  constructor <;> intro h <;> linarith

/-- If the q_v-product sum is smaller than P.average, the product comparison
fails. -/
theorem not_concreteSourceComparison_of_lt_badQAbsLog
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hlt : sourceBadQAbsLog I.initial < P.procession.average) :
    ¬ concreteSourceComparison O P := by
  intro h
  have hbound := (qvProductComparison_iff_badQAbsLog O P hO).mp h
  linarith

/-- NEW counterexample (not single q=1/5): one actual bad q = 24/25
is allowed (q!=0, |q|<1, q!=1). Then source sum = log(25/24) < log25;
if P.average = log25 the product comparison is false. -/
theorem productComparison_false_single_q_close
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hPavg : P.procession.average = Real.log (25 : Real))
    (hsource : sourceBadQAbsLog I.initial = Real.log ((25 : Real) / 24)) :
    ¬ concreteSourceComparison O P := by
  apply not_concreteSourceComparison_of_lt_badQAbsLog O P hO
  rw [hPavg, hsource]
  have hpos : (0 : Real) < (25 : Real) / 24 := by norm_num
  have hlt : (25 : Real) / 24 < 25 := by norm_num
  have hlog := Real.log_lt_log hpos hlt
  linarith

#check qvProductComparison_iff_badQAbsLog
#check not_concreteSourceComparison_of_lt_badQAbsLog
#check productComparison_false_single_q_close

end LeanFormal.IUT.XiFPaper.S1112SourceComparisonProductReductionActual

end