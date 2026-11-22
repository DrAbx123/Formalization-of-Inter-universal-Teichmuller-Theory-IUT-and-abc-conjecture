import tmp.sheaf.xif.paper.GlobalThetaPilotHullLogVolumeActual

/-!
# Global Theta-hull versus q-pilot: signed log comparison

The actual global Theta-pilot hull log-volume is

  globalThetaHullLogVolume
    = sum_v Real.log (sourceSetVolume v (sourceHolomorphicHull v ...)).toReal,

and the actual q-pilot signed log-volume is I.qPilotSignedLogVolume.

This file defines the paper's signed Theta-hull log

  thetaHullSignedLogVolume := - globalThetaHullLogVolume,

the q-pilot magnitude

  qPilotMagnitude := - I.qPilotSignedLogVolume,

and the exact comparison proposition

  I.qPilotSignedLogVolume <= - globalThetaHullLogVolume.

The comparison is algebraically equivalent to

  globalThetaHullLogVolume <= qPilotMagnitude.

The actual source does not provide the inequality; it is kept as an explicit
condition and the conditional implication is proved.  No trivial
negative <= positive direction is used and no inequality is fabricated.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Signed Theta-hull log-volume: negative of the global hull log-volume. -/
def thetaHullSignedLogVolume : Real :=
  - globalThetaHullLogVolume (I := I) R n

/-- q-pilot magnitude: negative of the signed q-pilot log-volume. -/
def qPilotMagnitude : Real :=
  - I.qPilotSignedLogVolume

/-- The exact paper-direction comparison. -/
def qPilotThetaHullComparison : Prop :=
  I.qPilotSignedLogVolume <= thetaHullSignedLogVolume (I := I) R n

/-- The comparison is equivalent to the hull log-volume being at most the
q-pilot magnitude. -/
theorem qPilotThetaHullComparison_iff :
    qPilotThetaHullComparison (I := I) R n ↔
      globalThetaHullLogVolume (I := I) R n <= qPilotMagnitude (I := I) := by
  unfold qPilotThetaHullComparison thetaHullSignedLogVolume qPilotMagnitude
  constructor <;> intro h <;> linarith

/-- Exact source condition sufficient for the paper comparison. -/
structure ExactGlobalComparisonCondition where
  hullLogVolume_le_qPilotMagnitude :
    globalThetaHullLogVolume (I := I) R n <= qPilotMagnitude (I := I)

/-- The exact comparison condition as a proposition. -/
def GlobalComparisonCondition : Prop :=
  globalThetaHullLogVolume (I := I) R n <= qPilotMagnitude (I := I)

/-- Conditional proof of the paper comparison from the exact actual condition. -/
theorem qPilotThetaHullComparison_of_condition
    (h : GlobalComparisonCondition (I := I) R n) :
    qPilotThetaHullComparison (I := I) R n :=
  (qPilotThetaHullComparison_iff (I := I) R n).mpr h

/-- The q-pilot magnitude is nonnegative, from the actual signed q-pilot sign. -/
theorem qPilotMagnitude_nonneg : 0 <= qPilotMagnitude (I := I) := by
  unfold qPilotMagnitude
  exact neg_nonneg.mpr (qPilotSignedLogVolume_nonpos (I := I))

/-- The exact condition is equivalent to the paper direction. -/
theorem GlobalComparisonCondition_iff :
    GlobalComparisonCondition (I := I) R n ↔
      qPilotThetaHullComparison (I := I) R n :=
  (qPilotThetaHullComparison_iff (I := I) R n).symm

/-- The actual data available for the comparison: q-pilot magnitude, hull
log-volume and signed hull log. -/
structure GlobalHullQPilotComparisonData where
  qPilotMagnitude : Real
  hullLogVolume : Real
  hullSignedLogVolume : Real
  qPilotMagnitude_eq : qPilotMagnitude = -I.qPilotSignedLogVolume
  hullLogVolume_eq : hullLogVolume =
    globalThetaHullLogVolume (I := I) R n
  hullSignedLogVolume_eq : hullSignedLogVolume = -hullLogVolume

/-- Actual comparison data (no inequality asserted). -/
noncomputable def globalHullQPilotComparisonData :
    GlobalHullQPilotComparisonData (I := I) R n where
  qPilotMagnitude := qPilotMagnitude (I := I)
  hullLogVolume := globalThetaHullLogVolume (I := I) R n
  hullSignedLogVolume := thetaHullSignedLogVolume (I := I) R n
  qPilotMagnitude_eq := rfl
  hullLogVolume_eq := rfl
  hullSignedLogVolume_eq := rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual

end