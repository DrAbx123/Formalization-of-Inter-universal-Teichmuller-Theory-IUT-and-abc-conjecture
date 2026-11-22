/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.RegionMeasure
import tmp.sheaf.gogopex.Iut.Foundations.IndeterminacyRelation

/-! # A517: hull objects (Gogopex HullOperator/CommonHull consumers) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexHull

open Iut RealLineCopy

universe u

variable {line : Copy}

/-- The hull object: a region together with its hull operator and the measure used for
log-volume comparisons. -/
structure HullObject (line : Copy) where
  /-- The base region. -/
  region : Region line
  /-- The hull operator. -/
  hullOp : HullOperator line
  /-- The region measure. -/
  measure : RegionMeasure line

/-- The base region has volume at most its hull (consumer of `RegionMeasure.le_hull`). -/
theorem HullObject.region_volume_le_hull (D : HullObject line) :
    D.measure.volume D.region ≤ D.measure.volume (D.hullOp.hull D.region) :=
  RegionMeasure.le_hull D.measure D.hullOp D.region

/-- The common-hull object: a region family with a common hull and measure. -/
structure CommonHullObject (line : Copy) (index : Type u) where
  /-- The region family. -/
  family : RegionFamily line index
  /-- The common hull. -/
  commonHull : RegionFamily.CommonHull family
  /-- The region measure. -/
  measure : RegionMeasure line

/-- Every choice region has volume at most the common-hull volume (consumer of
`RegionMeasure.le_commonHull_of_choice`). -/
theorem CommonHullObject.choice_volume_le_commonHull
    (D : CommonHullObject line index) (choice : index) :
    D.measure.volume (D.family.region choice) ≤ D.measure.volume D.commonHull.hull :=
  RegionMeasure.le_commonHull_of_choice D.measure D.commonHull choice

end LeanFormal.IUT.Objects.GogopexHull
