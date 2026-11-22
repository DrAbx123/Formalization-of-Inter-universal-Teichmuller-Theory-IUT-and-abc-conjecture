/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.RegionMeasure
import tmp.sheaf.gogopex.Iut.Foundations.IndeterminacyRelation

/-! # A517: indeterminacy-to-measure bridge (upper-ray subset + monotone volume) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexMeasure

open Iut RealLineCopy

variable {line : Copy}

/-- Upper rays are monotone in their bound: `upperRay a ⊆ upperRay b` for `a ≤ b`
(the target-side indeterminacy inclusion). -/
theorem upperRay_subset_of_le {a b : Real} (hab : a ≤ b) :
    Region.Subset (Region.upperRay line a) (Region.upperRay line b) := by
  intro x hx
  exact (Region.upperRay_contains).mpr (le_trans ((Region.upperRay_contains).mp hx) hab)

/-- A region measure is monotone on upper rays (bridge of subset inclusion to volume). -/
theorem upperRay_volume_mono (measure : RegionMeasure line) {a b : Real} (hab : a ≤ b) :
    measure.volume (Region.upperRay line a) ≤ measure.volume (Region.upperRay line b) :=
  RegionMeasure.le_of_subset measure (upperRay_subset_of_le (line := line) hab)

/-- An upper ray with bound `a` has volume at most `b` whenever `a ≤ b` and the measure
normalizes upper rays (consumer of `upperRay_atMost_iff_of_normalized`). -/
theorem upperRay_atMost_of_le (measure : RegionMeasure line)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure) {a b : Real} (hab : a ≤ b) :
    RegionMeasure.HasVolumeAtMost measure (Region.upperRay line a) b :=
  (RegionMeasure.upperRay_atMost_iff_of_normalized measure hnormalized a b).mpr hab

end LeanFormal.IUT.Objects.GogopexMeasure
