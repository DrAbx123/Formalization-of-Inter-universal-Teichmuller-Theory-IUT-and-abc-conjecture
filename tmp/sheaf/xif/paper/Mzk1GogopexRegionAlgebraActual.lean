import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Mzk1GogopexRegionAlgebraActual — region algebra for labeled real-line copies

A524 reference/object module: port of the region object and its basic algebra from the
downloaded Gogopex iut-lean project (Iut/Foundations/IndeterminacyRelation.lean),
abstracted over a coordinate map into Real.  Regions are the region-valued
comparisons used by the indeterminacy/descent interface (Theorem 3.11, 3.12).
Pure definitions + order lemmas; no structural claim.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GogopexRegionAlgebraActual

universe u

/-- A region in a labeled copy with a real coordinate map. -/
structure Region (X : Type u) (coord : X → Real) where
  /-- Membership predicate of the region. -/
  Contains : X → Prop

namespace Region

variable {X : Type u} {coord : X → Real}

/-- Region inclusion, pointwise. -/
def Subset (small large : Region X coord) : Prop :=
  ∀ x, small.Contains x → large.Contains x

/-- Extensional equality of regions. -/
def ExtEq (left right : Region X coord) : Prop :=
  ∀ x, left.Contains x ↔ right.Contains x

/-- The underlying set. -/
def toSet (region : Region X coord) : Set X := {x | region.Contains x}

/-- Region from a set. -/
def ofSet (points : Set X) : Region X coord := { Contains := fun x => x ∈ points }

/-- The singleton region of a point (identified by coordinate). -/
def singleton (x : X) : Region X coord := { Contains := fun y => coord y = coord x }

/-- The signed-log upper ray `coord <= bound` (Gogopex sign convention). -/
def upperRay (bound : Real) : Region X coord :=
  { Contains := fun y => coord y <= bound }

@[simp] theorem singleton_contains {x y : X} :
    ((singleton x : Region X coord)).Contains y ↔ coord y = coord x := Iff.rfl

@[simp] theorem ofSet_contains {points : Set X} {x : X} :
    ((ofSet points : Region X coord)).Contains x ↔ x ∈ points := Iff.rfl

@[simp] theorem upperRay_contains {bound : Real} {x : X} :
    (upperRay bound).Contains x ↔ coord x <= bound := Iff.rfl

theorem subset_refl (r : Region X coord) : Subset r r := fun _ h => h

theorem subset_trans {a b c : Region X coord} (hab : Subset a b) (hbc : Subset b c) :
    Subset a c := fun x hx => hbc x (hab x hx)

theorem extEq_iff_subset_both {a b : Region X coord} :
    ExtEq a b ↔ Subset a b ∧ Subset b a := by
  constructor
  · intro h
    exact ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩
  · rintro ⟨h1, h2⟩ x
    exact ⟨h1 x, h2 x⟩

/-- Upper rays are monotone in the bound. -/
theorem upperRay_mono {b b' : Real} (h : b <= b') :
    Subset (upperRay (coord := coord) b) (upperRay b') :=
  fun _ hx => le_trans hx h

/-- Singleton regions are contained in an upper ray when their coordinate is. -/
theorem singleton_subset_upperRay {x : X} {b : Real} (h : coord x <= b) :
    Subset (singleton x : Region X coord) (upperRay (coord := coord) b) := by
  intro y hy
  rw [upperRay_contains]
  rw [singleton_contains] at hy
  rw [hy]
  exact h

end Region

#check Region
#check Region.Subset
#check Region.ExtEq
#check Region.upperRay
#check Region.subset_trans
#check Region.upperRay_mono
#check Region.singleton_subset_upperRay

end LeanFormal.IUT.XiFPaper.Mzk1GogopexRegionAlgebraActual
end
