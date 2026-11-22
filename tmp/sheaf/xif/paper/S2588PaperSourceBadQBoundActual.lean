import tmp.sheaf.xif.paper.S1112SourceComparisonProductReductionActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
universe ua uv upi umon ui uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
namespace LeanFormal.IUT.XiFPaper.S2588PaperSourceBadQBoundActual
open LeanFormal.IUT.XiFPaper.S1112SourceComparisonProductReductionActual
/-- The literal C9 signed-hull bound: the procession average is bounded by
the source bad-q absolute-log sum. -/
def PaperSourceBadQBound (P : PaperSignedHull X label) : Prop :=
  P.procession.average ≤ sourceBadQAbsLog I.initial
/-- `sourceBadQAbsLog` is nonnegative: it is a finite sum of absolute logarithms. -/
theorem sourceBadQAbsLog_nonneg (S : SourceDefinition31Data (l := l)) :
    0 ≤ sourceBadQAbsLog S := by
  rw [sourceBadQAbsLog_eq_qvProductSum (l := l) S]
  exact Finset.sum_nonneg fun b _ ↦ abs_nonneg _
/-- Conditional actual bound: if the procession average is the negative
source bad-q absolute log (the diagonal q-pilot normalization), then the
bound follows from nonnegativity. -/
theorem paperSourceBadQBound_of_average_eq_neg
    (P : PaperSignedHull X label)
    (h : P.procession.average = -sourceBadQAbsLog I.initial) :
    PaperSourceBadQBound (I := I) P := by
  unfold PaperSourceBadQBound
  have hnonneg : 0 ≤ sourceBadQAbsLog I.initial :=
    sourceBadQAbsLog_nonneg I.initial
  linarith
/-- Exact obstruction form: the literal bound is equivalent to the average
inequality itself. -/
theorem paperSourceBadQBound_iff (P : PaperSignedHull X label) :
    PaperSourceBadQBound (I := I) P ↔
      P.procession.average ≤ sourceBadQAbsLog I.initial := Iff.rfl
#check PaperSourceBadQBound
#check sourceBadQAbsLog_nonneg
#check paperSourceBadQBound_of_average_eq_neg
end LeanFormal.IUT.XiFPaper.S2588PaperSourceBadQBoundActual
end
