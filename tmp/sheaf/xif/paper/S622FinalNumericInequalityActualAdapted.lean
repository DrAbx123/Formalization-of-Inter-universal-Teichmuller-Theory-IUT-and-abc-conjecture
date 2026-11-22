import tmp.sheaf.xif.paper.ConcreteSourceComparisonNumericActualAdapted
import tmp.sheaf.xif.paper.ConcreteQMagnitudeSourceComparisonActualAdapted

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S622FinalNumericInequalityActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonNumericActualAdapted
open LeanFormal.IUT.XiFPaper.ConcreteQMagnitudeSourceComparisonActualAdapted
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The final numeric inequality as a Prop. -/
def FinalNumericInequality : Prop :=
  Real.log (5 : Real) *
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) ≤
    sourceBadQAbsLog I.initial

/-- Under the explicit source condition |log q|=log 5 and coefficient > 1, the
final numeric inequality is false.  This is an exact arithmetic refutation, not
a missing proof. -/
theorem not_finalNumericInequality_of_badQAbsLog_eq_log5
    (hbad : sourceBadQAbsLog I.initial = Real.log (5 : Real))
    (hcoeff : 1 < (gaussExponentSum (l := l) : Real) /
      (Fintype.card (SignedLabel l.value) : Real)) :
    ¬ FinalNumericInequality (l := l) (I := I) := by
  unfold FinalNumericInequality
  rw [hbad]
  have hlog : (0 : Real) < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  exact not_le_of_gt (mul_lt_mul_of_pos_left hcoeff hlog)

/-- Exact required source lower bound; if supplied, the numeric inequality
follows immediately. -/
def SourceBadQAbsLogLowerBound : Prop :=
  Real.log (5 : Real) *
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) ≤
    sourceBadQAbsLog I.initial

def SourceBadQAbsLogLowerBoundRequired : Prop :=
  SourceBadQAbsLogLowerBound (l := l) (I := I)

theorem finalNumericInequality_of_sourceBound
    (h : SourceBadQAbsLogLowerBound (l := l) (I := I)) :
    FinalNumericInequality (l := l) (I := I) :=
  h

end LeanFormal.IUT.XiFPaper.S622FinalNumericInequalityActualAdapted

end
