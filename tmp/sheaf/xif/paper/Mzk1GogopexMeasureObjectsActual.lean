/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.RegionMeasure
import tmp.sheaf.gogopex.Iut.Foundations.IndeterminacyRelation

/-! # A517: normalized region-measure objects (Gogopex RegionMeasure consumers) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexMeasure

open Iut RealLineCopy

/-- The normalized measure object: a region measure on a labeled copy together with the
signed-log upper-ray calibration. -/
structure NormalizedMeasureObject (line : Copy) where
  /-- The region measure. -/
  measure : RegionMeasure line
  /-- Upper-ray normalization. -/
  normalized : RegionMeasure.NormalizesUpperRays measure

variable {line : Copy}

/-- The volume of an upper ray is its bound (consumer of the normalization). -/
theorem NormalizedMeasureObject.upperRay_volume (D : NormalizedMeasureObject line)
    (bound : Real) :
    D.measure.volume (Region.upperRay line bound) = bound :=
  RegionMeasure.upperRay_volume_eq_of_normalized D.measure D.normalized bound

/-- Upper-ray volume comparison reduces to bound comparison (consumer). -/
theorem NormalizedMeasureObject.upperRay_le_iff (D : NormalizedMeasureObject line)
    (smallBound largeBound : Real) :
    D.measure.volume (Region.upperRay line smallBound) ≤
        D.measure.volume (Region.upperRay line largeBound) ↔
      smallBound ≤ largeBound :=
  RegionMeasure.upperRay_volume_le_iff_of_normalized D.measure D.normalized
    smallBound largeBound

/-- Volume-at-most for an upper ray reduces to the bound comparison (consumer). -/
theorem NormalizedMeasureObject.upperRay_atMost_iff (D : NormalizedMeasureObject line)
    (regionBound volumeBound : Real) :
    RegionMeasure.HasVolumeAtMost D.measure (Region.upperRay line regionBound) volumeBound ↔
      regionBound ≤ volumeBound :=
  RegionMeasure.upperRay_atMost_iff_of_normalized D.measure D.normalized regionBound volumeBound

end LeanFormal.IUT.Objects.GogopexMeasure
