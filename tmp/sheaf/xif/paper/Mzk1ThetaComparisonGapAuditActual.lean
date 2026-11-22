/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A752/A761: theta-value comparison gap audit (REJECTED surrogate removed) -/

/- REJECTED — the earlier `twoPointVolume (fun S => if S = qRegion then qVol else hullVol)`
definition is a value-layer if/else surrogate of the kind the project rejects; it is removed
here and must NOT be used as gate evidence.  What remains is the honest real-analysis content:
* S3137 readings: `qPilotLogVolumeReading P = -|log q|` and
  `thetaPilotHullLogVolumeReal C3 = Real.log (haar (thetaPilotHull)).toReal`;
* the requirement's `strict_measure` obligation, under an exp-of-reading volume, reduces to
  the reading comparison `qReading < thetaReading` (equivalence PROVED below);
* the remaining paper obligation is exactly `qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3`
  (the S3137 named candidate).  No surrogate volume is asserted. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaComparisonGapAuditActual

/-- `exp` is strictly monotone: `exp qR < exp thR <-> qR < thR` (PROVED). -/
theorem exp_lt_exp_iff (qReading thetaReading : ℝ) :
    Real.exp qReading < Real.exp thetaReading ↔ qReading < thetaReading :=
  Real.exp_lt_exp

/-- The paper reading comparison gap, as a concrete Prop target. -/
def PaperReadingGap (qReading thetaReading : ℝ) : Prop := qReading ≤ thetaReading

/-- If the reading comparison holds, the exp-volume strict-measure obligation holds. -/
theorem exp_strictMeasure_of_reading {qReading thetaReading : ℝ}
    (h : qReading < thetaReading) : Real.exp qReading < Real.exp thetaReading :=
  (exp_lt_exp_iff qReading thetaReading).mpr h

end LeanFormal.IUT.XiFPaper.Mzk1ThetaComparisonGapAuditActual
