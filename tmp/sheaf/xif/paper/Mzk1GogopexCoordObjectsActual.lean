/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.IndeterminacyRelation

/-! # A517: coordinate-region objects (Gogopex Point.coord consumers) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexCoord

open Iut RealLineCopy

variable {line : Copy}

/-- A coordinate region object: a region together with a distinguished point of the copy. -/
structure CoordRegionObject (line : Copy) where
  /-- The region. -/
  region : Region line
  /-- The distinguished point. -/
  point : Point line

/-- The singleton at the distinguished point contains exactly the points with the same
coordinate (consumer of `singleton_contains`). -/
theorem CoordRegionObject.singleton_contains (D : CoordRegionObject line)
    (y : Point line) :
    (Region.singleton D.point).Contains y ↔ y.coord = D.point.coord :=
  Region.singleton_contains

/-- The upper ray at a bound contains exactly the points with coordinate at most the bound
(consumer of `upperRay_contains`). -/
theorem CoordRegionObject.upperRay_contains (D : CoordRegionObject line) (bound : Real)
    (y : Point line) :
    (Region.upperRay line bound).Contains y ↔ y.coord ≤ bound :=
  Region.upperRay_contains

/-- Region inclusion is reflexive (consumer). -/
theorem CoordRegionObject.subset_refl (D : CoordRegionObject line) :
    Region.Subset D.region D.region :=
  Region.subset_refl D.region

end LeanFormal.IUT.Objects.GogopexCoord
