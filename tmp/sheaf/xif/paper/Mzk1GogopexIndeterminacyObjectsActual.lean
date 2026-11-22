/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Foundations.IndeterminacyRelation
import tmp.sheaf.gogopex.Iut.Foundations.RegionMeasure

/-! # A516: O4 indeterminacy objects (Gogopex region/measure consumers) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexIndeterminacy

open Iut RealLineCopy

/-- The indeterminacy object: a labeled copy of the real line together with a region and
its measure (the target-side data of a multiradial algorithm). -/
structure IndeterminacyObject (line : Copy) where
  /-- The target region. -/
  region : Region line
  /-- The target-side region measure. -/
  measure : RegionMeasure line

variable {line : Copy}

/-- Region inclusion is reflexive (consumer of Gogopex `subset_refl`). -/
theorem IndeterminacyObject.subset_refl (D : IndeterminacyObject line) :
    Region.Subset D.region D.region :=
  Region.subset_refl D.region

/-- Region inclusion is transitive (consumer of Gogopex `subset_trans`). -/
theorem IndeterminacyObject.subset_trans (D : IndeterminacyObject line)
    {a b c : Region line} (hab : Region.Subset a b) (hbc : Region.Subset b c) :
    Region.Subset a c :=
  Region.subset_trans hab hbc

/-- Exact equality is an equivalence on regions (consumer of `extEq_refl`). -/
theorem IndeterminacyObject.extEq_refl (D : IndeterminacyObject line) :
    Region.ExtEq D.region D.region :=
  Region.extEq_refl D.region

/-- A singleton region contains its point (consumer of `singleton_contains`). -/
theorem IndeterminacyObject.singleton_contains (x y : RealLineCopy.Point line) :
    (Region.singleton x).Contains y ↔ y.coord = x.coord :=
  Region.singleton_contains

/-- An upper ray contains exactly the points above the bound (consumer of `upperRay_contains`). -/
theorem IndeterminacyObject.upperRay_contains (bound : Real)
    (y : RealLineCopy.Point line) :
    (Region.upperRay line bound).Contains y ↔ y.coord ≤ bound :=
  Region.upperRay_contains

end LeanFormal.IUT.Objects.GogopexIndeterminacy
