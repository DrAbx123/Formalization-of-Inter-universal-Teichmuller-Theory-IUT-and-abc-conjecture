import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealR9PointMembershipAudit
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: iutiii:IUTIII.HULL.R9_AUDIT_GAP (now built, EXIT0 211113) -> R9 audit downRay/value-form/witness-form + Theorem311Source point membership theorems; HullDeterminantLogVolumeReduction hullLogVolumeRay/mem_hullLogVolumeRay_iff -> paper-layer CONSUMER: identify the R9 down-ray with the H5 hull log-volume ray; record value/witness-form calibration rows. No new math beyond the ray identification; no closure.

# Mzk1R9PointMembershipConsumerActual — R9 down-ray / H5 hull-ray consumer

PROVED:
* `hullLogVolumeRay_eq_downRay`: the H5 hull log-volume ray `hullLogVolumeRay theta`
  (HullDeterminantLogVolumeReduction:501) equals the R9 down-ray `downRay theta`
  (CardHullRealR9PointMembershipAudit:56) — both are `Set.Iic theta`.
* `hullLogVolumeRay_consumer_iff`: membership in the hull ray in R9 form.
ROWS record the R9 value-form/witness-form calibration and the pointwise hull-volume
membership theorems as CONSUMED tree assets (no re-proof here).
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1R9PointMembershipConsumerActual

open LeanFormal.IUT

/-- **PROVED:** the H5 hull log-volume ray equals the R9 down-ray. -/
theorem hullLogVolumeRay_eq_downRay (thetaHullLogVolume : ℝ) :
    hullLogVolumeRay thetaHullLogVolume = downRay thetaHullLogVolume := by
  ext x
  rw [mem_hullLogVolumeRay_iff, mem_downRay_iff_le]

/-- **PROVED:** R9-form membership test for the H5 hull log-volume ray. -/
theorem hullLogVolumeRay_consumer_iff {thetaHullLogVolume lambdaValue : ℝ} :
    lambdaValue ∈ hullLogVolumeRay thetaHullLogVolume ↔ lambdaValue ≤ thetaHullLogVolume := by
  rw [hullLogVolumeRay_eq_downRay, mem_downRay_iff_le]

/-- Row record: proved ray identification vs consumed R9/H5 audit assets. -/
def r9ConsumerRows : List (String × String × String) :=
  [ ("R9 down-ray vs H5 hull log-volume ray", "PROVED", "hullLogVolumeRay_eq_downRay (both Set.Iic theta)")
  , ("R9-form ray membership", "PROVED", "hullLogVolumeRay_consumer_iff")
  , ("R9 value-form vs witness-form calibration", "CONSUMED TREE ASSET", "CardHullRealR9PointMembershipAudit.valueForm_not_witnessForm_calibration (built 211113)")
  , ("R9 value form strictly weaker than witness form", "CONSUMED TREE ASSET", "valueForm_strictly_weaker_than_witnessForm")
  , ("pointwise hull-volume membership forms", "CONSUMED TREE ASSET", "sourceHullVolume_le_iff_pointwise_pointVolume_le / sourceHullVolume_le_iff_points_logDegree_le_toReal") ]

theorem r9ConsumerRows_length : r9ConsumerRows.length = 5 := rfl

#check hullLogVolumeRay_eq_downRay
#check hullLogVolumeRay_consumer_iff
#check r9ConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1R9PointMembershipConsumerActual
end