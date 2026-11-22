/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.RegionMeasure
import tmp.sheaf.gogopex.Iut.Foundations.IndeterminacyRelation

/-! # A517: hull/at-most bridge objects (common-hull volume bound propagation) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexHullBridge

open Iut RealLineCopy

universe u

variable {line : Copy} {index : Type u}

/-- If the common hull has volume at most `bound`, then every choice region does
(consumer of `atMost_of_subset_of_atMost` + `CommonHull.contains_each`). -/
theorem choice_atMost_of_commonHull_atMost (measure : RegionMeasure line)
    {family : RegionFamily line index} (commonHull : RegionFamily.CommonHull family) {bound : Real}
    (h : RegionMeasure.HasVolumeAtMost measure commonHull.hull bound) (choice : index) :
    RegionMeasure.HasVolumeAtMost measure (family.region choice) bound :=
  RegionMeasure.atMost_of_subset_of_atMost measure (commonHull.contains_each choice) h

/-- If a common region contains the family, its volume bounds each choice region's volume. -/
theorem choice_volume_le_common_of_containedIn (measure : RegionMeasure line)
    {family : RegionFamily line index} {common : Region line}
    (hcommon : family.ContainedIn common) (choice : index) :
    measure.volume (family.region choice) ≤ measure.volume common :=
  RegionMeasure.le_common_of_choice measure hcommon choice

/-- Hull monotonicity in the measure: a larger hull bound gives a weaker at-most bound
for the same desired value (transitivity consumer). -/
theorem atMost_trans (measure : RegionMeasure line) {region : Region line} {a b : Real}
    (ha : RegionMeasure.HasVolumeAtMost measure region a) (hab : a ≤ b) :
    RegionMeasure.HasVolumeAtMost measure region b := le_trans ha hab

end LeanFormal.IUT.Objects.GogopexHullBridge
