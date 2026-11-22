import Mathlib.Data.Real.Basic

-- S1136: source comparison via a monotone gluing map.
-- If qPilotLog = glue(thetaPilotLog), hullLog = glue(thetaHullLog), and
-- thetaPilotLog <= thetaHullLog, then qPilotLog <= hullLog.
-- Exact gap: hull must also be the glued theta hull; without hull=glue(thetaHull)
-- the two conditions qPilot=glue(thetaPilot), thetaPilot<=hull imply nothing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1136SourceComparisonViaGluingActual

/-- Actual gluing data for the source comparison. -/
structure S1136GluingData where
  thetaPilotLog : Real
  thetaHullLog : Real
  qPilotLog : Real
  hullLog : Real
  glue : Real → Real
  glue_mono : ∀ {a b : Real}, a ≤ b → glue a ≤ glue b
  qPilotLog_eq : qPilotLog = glue thetaPilotLog
  hullLog_eq : hullLog = glue thetaHullLog
  theta_le : thetaPilotLog ≤ thetaHullLog

/-- Actual source comparison via monotone gluing. -/
theorem s1136Comparison (D : S1136GluingData) :
    D.qPilotLog ≤ D.hullLog := by
  rw [D.qPilotLog_eq, D.hullLog_eq]
  exact D.glue_mono D.theta_le

/-- Exact missing condition if the hull is not glued: only hull=glue(thetaHull)
makes monotonicity applicable. -/
def S1136HullGluingRequired (D : S1136GluingData) : Prop :=
  D.hullLog = D.glue D.thetaHullLog

theorem s1136Comparison_of_hull_gluing
    (D : S1136GluingData)
    (hhull : S1136HullGluingRequired D) :
    D.qPilotLog ≤ D.hullLog := by
  rw [D.qPilotLog_eq, hhull]
  exact D.glue_mono D.theta_le

/-- The two stated conditions alone (qPilot=glue thetaPilot, thetaPilot<=hull)
do not imply qPilot<=hull without hull=glue(thetaHull).  This theorem
records the exact residual: need glue(thetaPilot)<=hull. -/
def S1136ComparisonExactResidual (D : S1136GluingData) : Prop :=
  D.glue D.thetaPilotLog ≤ D.hullLog

theorem s1136Comparison_iff_residual
    (D : S1136GluingData) :
    D.qPilotLog ≤ D.hullLog ↔ S1136ComparisonExactResidual D :=
  ⟨fun h => by rwa [D.qPilotLog_eq] at h, fun h => by rwa [D.qPilotLog_eq]⟩

#check s1136Comparison
#check s1136Comparison_of_hull_gluing
#check S1136ComparisonExactResidual

end LeanFormal.IUT.XiFPaper.S1136SourceComparisonViaGluingActual

end