/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData
import tmp.sheaf.gogopex.Iut.Foundations.RegionMeasure

/-! # A517: SHE-measure objects (Gogopex SHE + region measure glue) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexSheMeasure

open Iut RealLineCopy

universe u v w

variable {source target : Copy} {index : Type u}

/-- The SHE-measure object: simultaneous-holomorphic-expressibility data over a family
together with a region measure on the target copy and a measured region inclusion. -/
structure SHEMeasureObject (family : TransportedRegionFamily source target index) where
  /-- The SHE datum. -/
  datum : QualitativeData.SHEDatum family
  /-- The target region measure. -/
  measure : RegionMeasure target
  /-- A small target region. -/
  small : Region target
  /-- A large target region. -/
  large : Region target
  /-- The small region is contained in the large one. -/
  subset : Region.Subset small large

/-- The object witnesses structured SHE (consumer of `HasStructuredSHE`). -/
theorem SHEMeasureObject.hasStructuredSHE
    {family : TransportedRegionFamily source target index} (D : SHEMeasureObject family) :
    QualitativeData.HasStructuredSHE family :=
  ⟨D.datum⟩

/-- Its measured inclusion gives the log-volume inequality (consumer of
`RegionMeasure.le_of_subset`). -/
theorem SHEMeasureObject.volume_le
    {family : TransportedRegionFamily source target index} (D : SHEMeasureObject family) :
    D.measure.volume D.small ≤ D.measure.volume D.large :=
  RegionMeasure.le_of_subset D.measure D.subset

end LeanFormal.IUT.Objects.GogopexSheMeasure
