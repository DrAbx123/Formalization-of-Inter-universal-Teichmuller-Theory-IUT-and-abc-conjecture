import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConditionalActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2NumericActual

/-! # Mzk1Stage4Gap2ObjectCalibrationActual (stage4 lane; Gap2 object-level calibration)

A677 module: object-level calibration of Gap 2 from the GREEN pieces — the conditional
reduction `gap2_conditional_reduction` and the genuine numeric witness `witness_SNamed`
packaged into a calibrated object (boundary equality case).  The object-level
`corrected_gap2_iff_ABC` is a θ-ABSORPTION equivalence naming only (NOT the remaining named
input; that is the pure arithmetic BadSumWeightBound per A688); this file consumes only
green declarations.  No new mathematics; no conclusion changed.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2ObjectCalibrationActual

open LeanFormal.IUT.Objects
open LeanFormal.IUT.Objects.ABCBridgeGap2
open LeanFormal.IUT.Objects.ABCBridgeGap2Numeric
open LeanFormal.IUT.Objects.ABCBridgeGap2Conditional
open scoped ENNReal

/-- Consumer: the conditional Gap-2 reduction (named estimate + nonneg RHS). -/
theorem stage4_gap2_conditional {regionVolume : ENNReal} {eps weight theta D : Real}
    (hR : 0 ≤ (1 + eps) * weight + theta + D)
    (hS : SNamed regionVolume eps weight theta D) :
    regionVolume.toReal ≤ (1 + eps) * weight + theta + D :=
  gap2_conditional_reduction hR hS

/-- Consumer: the numeric Gap-2 witness bound. -/
theorem stage4_gap2_numeric :
    witnessRegionVolume.toReal ≤ (1 + (1 : Real)) * Real.log 11 + 0 + 0 :=
  witness_real_bound

/-- Object-level calibrated Gap-2 data (the boundary case of the numeric witness). -/
structure Gap2CalibratedObject where
  /-- the region volume. -/
  regionVolume : ENNReal
  /-- the epsilon. -/
  eps : Real
  /-- the arithmetic weight. -/
  weight : Real
  /-- the theta/hull constant. -/
  theta : Real
  /-- the additive constant. -/
  D : Real
  /-- the calibrated bound. -/
  bound : regionVolume.toReal ≤ (1 + eps) * weight + theta + D

/-- The numeric-witness calibrated object. -/
noncomputable def gap2WitnessObject : Gap2CalibratedObject where
  regionVolume := witnessRegionVolume
  eps := 1
  weight := Real.log 11
  theta := 0
  D := 0
  bound := witness_real_bound

/-- Object-level calibration identity: the witness sits exactly on the boundary. -/
theorem stage4_gap2_object_boundary :
    gap2WitnessObject.regionVolume.toReal =
      (1 + gap2WitnessObject.eps) * gap2WitnessObject.weight +
        gap2WitnessObject.theta + gap2WitnessObject.D := by
  unfold gap2WitnessObject witnessRegionVolume
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- Status rows for the object-level calibration chain. -/
def gap2CalibrationRows : List (String × String) :=
  [ ("conditional reduction", "gap2_conditional_reduction (GREEN, consumed)")
  , ("numeric witness", "witness_SNamed + witness_real_bound (GREEN, consumed)")
  , ("object-level calibration", "Gap2CalibratedObject + boundary identity (stage4)")
  , ("θ-absorption equivalence", "corrected_gap2_iff_ABC naming is allowed ONLY for θ absorption; not the named input")
  ]

/-- The Gap2 calibration record has four rows. -/
theorem gap2CalibrationRows_length : gap2CalibrationRows.length = 4 := rfl

#print axioms stage4_gap2_conditional
#print axioms stage4_gap2_numeric
#print axioms stage4_gap2_object_boundary

#check stage4_gap2_conditional
#check stage4_gap2_numeric
#check Gap2CalibratedObject
#check gap2WitnessObject
#check stage4_gap2_object_boundary
#check gap2CalibrationRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2ObjectCalibrationActual
end
