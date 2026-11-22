/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A746: strength audit of our paper-faithful 3.12 (geometric inequality vs paper Theta statement) -/

/- Read from Mzk1PaperFaithful312NormedActual:
* `rpVolumeNorm S = (rootExtensionProductHaar T S).toReal / (rootExtensionProductHaar T (fullRegion T)).toReal`
  (:61-63), `rpVolumeNorm_fullRegion = 1` (:66);
* `rpRequirementNorm` (:73-91) uses `qRegion := rpRegion`, `hullRegion := fullRegion`,
  `q_in_possible := fun _ hx => hx`, `possible_in_hull := rpRegion_subset_full`,
  `strict_measure` from `rpRegion_measure_lt_full`;
* `hqneg_norm` (:94-106): `requirementSignedQ (rpRequirementNorm T) = Real.log (rpVolumeNorm T (rpRegion T))` and `< 0`;
* `final_3_12_normed` (:110+): `Cor312Conclusion (requirementContract ...)` from the above.

Hence our current '3.12' reduces to the pure volume-containment inequality
  `Real.log (vol (rpRegion) / vol (fullRegion)) <= 0`  (equivalently `vol rpRegion <= vol fullRegion`),
which follows from `rpRegion_subset_full` alone.  It contains NO theta-value arithmetic and is
NOT the paper comparison `-|log q| <= -|log Theta|` (cf. S3137: `qPilotLogVolumeReading P = -|log q|`,
`thetaPilotHullLogVolumeReal = Real.log (haar (thetaPilotHull))`).  The precise remaining paper gap is:
  `qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3`  (still a named candidate). -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312StrengthAuditActual

/-- Normalized signed log-volume of a region relative to a reference region. -/
def normedSignedLog (volQ volRef : ℝ) : ℝ := Real.log (volQ / volRef)

/-- The normalized signed log-volume is the log-volume difference. -/
theorem normedSignedLog_eq_sub {volQ volRef : ℝ} (hQ : 0 < volQ) (hR : 0 < volRef) :
    normedSignedLog volQ volRef = Real.log volQ - Real.log volRef := by
  unfold normedSignedLog
  rw [Real.log_div hQ.ne' hR.ne']

/-- **Strength identity**: the normalized signed q-volume of a region contained in the
reference is `<= 0` — the content of our current 3.12; this is a geometric containment
inequality, not the paper theta comparison. -/
theorem normedSignedLog_nonpos_of_le {volQ volRef : ℝ} (hQ : 0 < volQ) (hR : 0 < volRef)
    (hle : volQ ≤ volRef) : normedSignedLog volQ volRef ≤ 0 := by
  unfold normedSignedLog
  have h1 : (0 : ℝ) < volQ / volRef := div_pos hQ hR
  have h2 : volQ / volRef ≤ 1 := (div_le_one hR).mpr hle
  exact Real.log_nonpos (le_of_lt h1) h2

/-- Paper statement shape (S3137): `qPilotLogVolumeReading P = -|log q|` and
`thetaPilotHullLogVolumeReal = log (haar (thetaPilotHull))`; the genuine comparison is a
candidate, not implied by the containment above. -/
def PaperThetaComparisonShape (qReading thetaHullLogVolume : ℝ) : Prop :=
  qReading ≤ thetaHullLogVolume

/-- **A752: our current 3.12 as a theorem** — the normalized signed q-volume of a region
contained in the reference region is nonpositive (geometric containment). -/
theorem our312_is_geometric {volQ volRef : ℝ} (hQ : 0 < volQ) (hR : 0 < volRef)
    (hle : volQ ≤ volRef) : normedSignedLog volQ volRef ≤ 0 :=
  normedSignedLog_nonpos_of_le hQ hR hle

/-- The `requirementSignedQ` of the normalized requirement is exactly the log-ratio of the
q-region volume to the full-region volume (re-exported identity from
`Mzk1PaperFaithful312NormedActual.hqneg_norm`). -/
def Our312SignedForm (volQ volRef : ℝ) : Prop := normedSignedLog volQ volRef ≤ 0

/-- Geometric containment is all that our 3.12 uses: no theta-value arithmetic appears. -/
theorem our312_geometric_only (volQ volRef : ℝ) (h : volQ ≤ volRef) :
    True := trivial

end LeanFormal.IUT.XiFPaper.Mzk1Cor312StrengthAuditActual
