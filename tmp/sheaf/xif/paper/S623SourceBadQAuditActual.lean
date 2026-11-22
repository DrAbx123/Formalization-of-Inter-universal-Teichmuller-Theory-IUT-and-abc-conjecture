import tmp.sheaf.xif.paper.S621ConcreteComparisonMinimalGapActual
import tmp.sheaf.xif.paper.SignedAverageBoundActual

/-! # S623: sourceBadQAbsLog audit and exact lower-bound gap

Actual formula:
  sourceBadQAbsLog S = sum over actual bad places b of |log (q_b)|.
Actual arithmetic lower bounds in the tree:
  * sourceBadQAbsLog_nonneg : 0 <= sourceBadQAbsLog S;
  * sourceBadQAbsLog_pos_of_nonempty : nonempty badPlaces -> 0 < sourceBadQAbsLog S.
There is no uniform positive lower bound for individual |log q_b| (qParameter
is only nonzero and norm < 1), hence no proved comparison with the positive
Gaussian theta average.  The exact missing datum is an actual arithmetic lower
bound average <= sourceBadQAbsLog; it is recorded, not assumed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.Theorem311Source.S623SourceBadQAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonActual
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonInequalityActual
open LeanFormal.IUT.XiFPaper.SignedAverageBoundActual

universe ua upi umon ui uX uLabel
variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)

/-- Expanded actual formula of sourceBadQAbsLog. -/
theorem sourceBadQAbsLog_eq_sum_abs_log
    (S : SourceDefinition31Data l) :
    sourceBadQAbsLog S =
      letI := S.bad_finite
      ∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)| := by
  rfl

/-- Conditional final comparison from the exact arithmetic lower bound. -/
theorem obstacle_of_badQAbsLog_lower_bound
    (h : P.procession.average ≤ sourceBadQAbsLog I.initial) :
    ConcreteSourceComparisonObstacle (l := l) I P :=
  (obstacle_iff_minimalGap (l := l) I P).mpr h

/-- Exact lower-bound datum needed to pass the final comparison. -/
structure SourceBadQAbsLogLowerBoundData where
  bound : Real
  average_le_bound : P.procession.average ≤ bound
  bound_le_source : bound ≤ sourceBadQAbsLog I.initial
  source_bound_actual : Prop

def SourceBadQAbsLogLowerBoundDataRequired : Prop :=
  Nonempty (SourceBadQAbsLogLowerBoundData (l := l) I P)

end LeanFormal.IUT.Theorem311Source.S623SourceBadQAuditActual
end
