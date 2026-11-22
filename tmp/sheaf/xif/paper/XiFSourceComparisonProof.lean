import tmp.sheaf.xif.paper.ThetaLinkFromSource
import tmp.sheaf.xif.paper.QPilotObjectActual

/-! # Deep source-comparison reduction (write-only)

Task-564 attempt.  Target:

    sourceComparison O P, i.e. P.procession.average <= -O.signedQPilotLogVolume.

## Reduction using actual definitions

* `PaperQPilotObjectActual.signedQPilotLogVolume = localSignedLog C3.q =
  Real.log ||q|| < 0`.
* `PaperQPilotObjectActual.qPilotLogMagnitude = -signedQPilotLogVolume =
  localLogMagnitude C3.q = -Real.log ||q||`.
* `PaperSignedHull.signedHullLogVolume = -P.procession.average`.

Therefore the target is exactly the analytic bound

    P.procession.average <= localLogMagnitude C3.q
    (equivalently <= -Real.log ||q||).

## Exact missing analytic bound

No project theorem bounds the finite procession average by the actual q
magnitude.  The available `PaperSignedHull.procession_average_le_hullVolume`
only bounds it by `P.hull.hullVolume`, and there is no theorem
`P.hull.hullVolume <= localLogMagnitude C3.q`.  This is the exact missing
analytic/source comparison; no arbitrary inequality or toy value is added.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SourceComparisonProof

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

universe ua uv upi umon ui uC3 uD3 uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

variable (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I))
variable (P : PaperSignedHull X label)

/-- The q-pilot magnitude is exactly the actual local log magnitude. -/
theorem qPilotLogMagnitude_eq_localLogMagnitude :
    O.qPilotLogMagnitude = localLogMagnitude O.line.C3.q :=
  O.qPilotLogMagnitude_eq_localLogMagnitude

/-- The q-pilot magnitude is the negative actual q log norm: `-log ||q||`. -/
theorem qPilotLogMagnitude_eq_neg_log_norm :
    O.qPilotLogMagnitude = -Real.log ‖O.line.C3.q.q‖ := by
  rw [qPilotLogMagnitude_eq_localLogMagnitude]
  rfl

/-- The target source comparison is exactly the analytic average bound. -/
theorem sourceComparison_iff_average_le_qPilotMagnitude :
    sourceComparison O P ↔ P.procession.average ≤ O.qPilotLogMagnitude := by
  unfold sourceComparison qPilotLogMagnitude
  rfl

/-- The target source comparison is exactly `average <= localLogMagnitude q`. -/
theorem sourceComparison_iff_average_le_localLogMagnitude :
    sourceComparison O P ↔ P.procession.average ≤ localLogMagnitude O.line.C3.q := by
  rw [sourceComparison_iff_average_le_qPilotMagnitude,
    qPilotLogMagnitude_eq_localLogMagnitude]

/-- The target source comparison is exactly `average <= -log ||q||`. -/
theorem sourceComparison_iff_average_le_neg_log_norm :
    sourceComparison O P ↔ P.procession.average ≤ -Real.log ‖O.line.C3.q.q‖ := by
  rw [sourceComparison_iff_average_le_qPilotMagnitude,
    qPilotLogMagnitude_eq_neg_log_norm]

/-- The exact missing analytic bound: the finite procession average is at
most the actual q-pilot log magnitude. -/
def MissingAnalyticBound : Prop :=
  P.procession.average ≤ localLogMagnitude O.line.C3.q

/-- The missing bound is equivalent to the target comparison. -/
theorem sourceComparison_iff_missingAnalyticBound :
    sourceComparison O P ↔ MissingAnalyticBound O P := by
  exact sourceComparison_iff_average_le_localLogMagnitude O P

/-- Supplying the exact analytic bound gives the source comparison. -/
theorem sourceComparison_of_missingAnalyticBound
    (h : MissingAnalyticBound O P) : sourceComparison O P :=
  (sourceComparison_iff_missingAnalyticBound O P).mpr h

/-- And hence the xi-f membership via the actual Theta-link theorem. -/
theorem xiFMembership_of_missingAnalyticBound
    (h : MissingAnalyticBound O P) :
    O.signedQPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  xiFMembership_of_sourceComparison O P
    (sourceComparison_of_missingAnalyticBound O P h)

/-- The available actual bound is only through the finite hull volume. -/
theorem average_le_hullVolume :
    P.procession.average ≤ P.hull.hullVolume :=
  P.procession_average_le_hullVolume

/-- Exact second form of the missing analytic input: the finite hull volume is
at most the actual q-pilot log magnitude. -/
def MissingHullVolumeBound : Prop :=
  P.hull.hullVolume ≤ localLogMagnitude O.line.C3.q

/-- The hull-volume bound suffices for the target comparison. -/
theorem sourceComparison_of_hullVolumeBound
    (h : MissingHullVolumeBound O P) : sourceComparison O P :=
  sourceComparison_of_missingAnalyticBound O P
    (le_trans (average_le_hullVolume O P) h)

/-- The actual signed q-pilot scalar is negative. -/
theorem signedQPilotLogVolume_neg : O.signedQPilotLogVolume < 0 :=
  O.signedQPilotLogVolume_neg

/-- The actual q-pilot magnitude is positive. -/
theorem qPilotLogMagnitude_pos : 0 < O.qPilotLogMagnitude :=
  O.qPilotLogMagnitude_pos

end LeanFormal.IUT.XiFPaper.SourceComparisonProof

end
