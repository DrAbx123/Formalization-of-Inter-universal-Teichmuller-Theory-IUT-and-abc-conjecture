/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison

/-! # A524: signed log-volume pilot package (Gogopex signed comparison) -/

noncomputable section

namespace LeanFormal.IUT.Objects.SignedLogVolumePilot

open scoped ENNReal
open Iut.Stage1

/-- Signed log-volume of a region (local copy of the A524 definition). -/
def signedLogVolume {X : Type*} (measure : Set X → ENNReal) (S : Set X) : ℝ :=
  Real.log ((measure S).toReal)

/-- The Gogopex pilot package from signed log-volumes: magnitudes are `-signedLogVolume`,
so the signed comparison `-theta.value ≥ -q.value` is exactly
`signedLogVolume qRegion ≤ signedLogVolume hull`. -/
def stage1ComparisonOfSigned {X : Type*} (measure : Set X → ENNReal)
    {qRegion hull : Set X}
    (hmono : (measure qRegion).toReal ≤ (measure hull).toReal)
    (hq_pos : 0 < (measure qRegion).toReal)
    (hq_neg : signedLogVolume measure qRegion < 0)
    (hh_neg : signedLogVolume measure hull < 0) :
    Stage1Comparison where
  theta := { side := PilotSide.theta, value := -signedLogVolume measure hull }
  q := { side := PilotSide.q, value := -signedLogVolume measure qRegion }
  theta_side := rfl
  q_side := rfl
  q_positive := by
    show 0 < -signedLogVolume measure qRegion
    linarith
  comparison := by
    have hlog : signedLogVolume measure qRegion ≤ signedLogVolume measure hull := by
      unfold signedLogVolume
      exact Real.log_le_log hq_pos hmono
    show -(-signedLogVolume measure hull) ≥ -(-signedLogVolume measure qRegion)
    linarith

end LeanFormal.IUT.Objects.SignedLogVolumePilot
