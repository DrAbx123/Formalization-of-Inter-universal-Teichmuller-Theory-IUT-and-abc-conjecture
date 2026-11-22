import Mathlib

/-! # Mzk1PencilInterfaceActualAdapted — pencil data interface (D-area paper prerequisite)

Real definitions only (no sorry/axiom): the pencil data used by the Problem D
function-field construction — a degree-d divisor pencil on a curve with a base locus and
the associated finite map to P1.  Recorded as explicit data with its compatibility
predicates; existence is a named input, not asserted.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PencilInterfaceActualAdapted

open CategoryTheory AlgebraicGeometry

attribute [local instance] Classical.decEq

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

/-- Pencil data: a degree, a base locus, two generating members and the induced map to P1. -/
structure PencilData (C : Scheme.{u}) (R : Type u) [CommRing R] where
  degree : Nat
  baseLocus : Set C
  baseLocus_finite : baseLocus.Finite
  member1 : Set C
  member2 : Set C
  member1_finite : member1.Finite
  member2_finite : member2.Finite
  base_subset_member1 : baseLocus ⊆ member1
  base_subset_member2 : baseLocus ⊆ member2
  pencilMap : C -> P1Point Rat
  degree_eq : degree = member1.ncard

/-- Projection: the pencil degree is the cardinality of a member. -/
theorem degree_eq_ncard (M : PencilData C R) : M.degree = M.member1.ncard :=
  M.degree_eq

/-- Projection: the base locus is contained in the first member. -/
theorem baseLocus_subset_member1 (M : PencilData C R) :
    M.baseLocus ⊆ M.member1 :=
  M.base_subset_member1

/-- Named interface: pencil data exists for the curve. -/
def PencilDataInput : Prop := Nonempty (PencilData C R)

/-- Row record. -/
def pencilRows : List (String × String) :=
  [ ("PencilData (degree/baseLocus/members/pencilMap)", "DEFINED"),
    ("PencilDataInput", "NAMED (existence not asserted)") ]

theorem pencilRows_length : pencilRows.length = 2 := rfl

#check PencilData
#check PencilDataInput

end LeanFormal.IUT.XiFPaper.Mzk1PencilInterfaceActualAdapted
end
