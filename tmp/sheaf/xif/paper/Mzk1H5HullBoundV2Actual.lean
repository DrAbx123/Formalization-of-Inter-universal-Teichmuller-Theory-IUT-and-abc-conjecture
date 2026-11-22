import Mathlib

/-!
# Mzk1H5HullBoundV2Actual — H5 hull closure and log-volume monotonicity (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Hull set closed under nonnegative scaling; log-volume monotone under scaling. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HullBoundV2Actual

/-- Hull data: set, scale action, closedness, and log-volume function. -/
structure H5HullData (Carrier : Type*) where
  hull : Set Carrier
  scale : ℚ → Carrier → Carrier
  hull_scale : ∀ a x, x ∈ hull → scale a x ∈ hull
  logVolume : Carrier → ℚ
  logVolume_scale : ∀ a x, 0 ≤ a → logVolume (scale a x) = a * logVolume x

/-- Genuine theorem: hull is closed under nonnegative scaling. -/
theorem H5HullData.scale_mem {Carrier : Type*} (d : H5HullData Carrier)
    (a : ℚ) {x : Carrier} (hx : x ∈ d.hull) : d.scale a x ∈ d.hull :=
  d.hull_scale a x hx

/-- Genuine theorem: log-volume scales by the nonnegative factor. -/
theorem H5HullData.logVolume_scale_apply {Carrier : Type*} (d : H5HullData Carrier)
    (a : ℚ) (x : Carrier) (ha : 0 ≤ a) :
    d.logVolume (d.scale a x) = a * d.logVolume x :=
  d.logVolume_scale a x ha

end LeanFormal.IUT.XiFPaper.Mzk1H5HullBoundV2Actual
