import LeanFormal.IUT.IUTII.Frobenioid.Example36SpecEssentialSurjectivity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Foundation F1e: Spec-cover comparison and the exact equivalence card

This file builds on the object-level comparison and essential surjectivity of
`Example36SpecEssentialSurjectivity` (F1b) and isolates the remaining
functor/equivalence content of the Spec-cover correspondence.

Proved here (actual):
* the object map `specCoverObjectMap : (CommAlgCat.FiniteEtale K)ᵒᵖ →
  FiniteEtaleCover (Spec K)` sending `A ↦ finiteEtaleAlgebraCover K A`;
* object-level essential surjectivity of this map, transported from F1b;
* the universal property of the frozen functor card: any functor card over
  the actual object map yields the actual essential surjectivity.

Frozen cards (no inhabitant, no fake functor/equivalence):
* `SpecCoverFunctorCard K`: an actual functor
  `(CommAlgCat.FiniteEtale K)ᵒᵖ ⥤ FiniteEtaleCover (Spec K)` agreeing with
  `specCoverObjectMap` on objects, together with its functor laws and full
  faithfulness;
* `SpecCoverEquivalenceCard K`: a category equivalence between
  `(CommAlgCat.FiniteEtale K)ᵒᵖ` and `FiniteEtaleCover (Spec K)` whose functor
  agrees with the proved object map.

Blocker recorded honestly: `FiniteEtaleCover (Spec K)` is an induced
(object-property) subcategory of `Over (Spec K)`, so a morphism is an
`InducedCategory.Hom` around an `Over.Hom`; constructing the functor on
morphisms requires the induced-category hom API plus the Spec/Gamma triangle
(`Spec.map_comp` with `AlgHom.comp_algebraMap`), which is not developed in this
file.  The functor, its laws, fullness and the equivalence are therefore kept
as explicit unproved card fields, not asserted.

Boundary: field-level Spec/Gamma correspondence only; no curve Pi_1 and no
theta/q-pilot claim.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecEssentialSurjectivity

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverEquivalence

universe u

variable (K : Type u) [Field K]

/-! ## 1. The actual object map -/

/-- The object-level map from finite etale `K`-algebras (opposite) to finite
etale covers of `Spec K`: the F1b construction `A ↦ finiteEtaleAlgebraCover K A`. -/
def specCoverObjectMap :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ → FiniteEtaleCover (specBase K) :=
  fun A => finiteEtaleAlgebraCover K A.unop

@[simp]
theorem specCoverObjectMap_apply (A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) :
    specCoverObjectMap K A = finiteEtaleAlgebraCover K A.unop := rfl

/-- The actual object map is essentially surjective: every finite etale cover
of `Spec K` is isomorphic to the cover of a finite etale `K`-algebra (F1b). -/
theorem specCoverObjectMap_essentially_surjective
    (C : FiniteEtaleCover (specBase K)) :
    ∃ A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ,
      Nonempty (specCoverObjectMap K A ≅ C) := by
  obtain ⟨A, ⟨e⟩⟩ := finiteEtaleAlgebraCover_essentially_surjective C
  exact ⟨Opposite.op A, ⟨e.symm⟩⟩

/-! ## 2. Frozen functor and equivalence cards -/

/-- **Frozen card: the Spec-cover functor.**  An actual functor from finite
etale `K`-algebras (opposite) to finite etale covers of `Spec K`, agreeing with
the proved object map, together with its functor laws and full faithfulness.
No inhabitant is constructed in this file. -/
structure SpecCoverFunctorCard (K : Type u) [Field K] where
  /-- The candidate comparison functor. -/
  functor : (CommAlgCat.FiniteEtale K)ᵒᵖ ⥤ FiniteEtaleCover (specBase K)
  /-- It agrees with the proved object map on objects. -/
  agrees_on_objects : ∀ A : (CommAlgCat.FiniteEtale K)ᵒᵖ,
    functor.obj A = finiteEtaleAlgebraCover K A.unop
  /-- Full faithfulness of the candidate functor. -/
  full_faithful : functor.Full ∧ functor.Faithful

/-- **Frozen card: the category equivalence.**  An equivalence between finite
etale `K`-algebras (opposite) and finite etale covers of `Spec K`, whose
functor agrees with the proved object map.  No inhabitant is constructed. -/
structure SpecCoverEquivalenceCard (K : Type u) [Field K] where
  /-- The candidate category equivalence. -/
  equivalence : (CommAlgCat.FiniteEtale K)ᵒᵖ ≌ FiniteEtaleCover (specBase K)
  /-- It agrees with the proved object map on objects. -/
  agrees_on_objects : ∀ A : (CommAlgCat.FiniteEtale K)ᵒᵖ,
    equivalence.functor.obj A = finiteEtaleAlgebraCover K A.unop

/-- Any inhabited functor card recovers the actual object map. -/
theorem SpecCoverFunctorCard.agrees
    (E : SpecCoverFunctorCard K) (A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) :
    E.functor.obj A = specCoverObjectMap K A := by
  rw [E.agrees_on_objects A]
  rfl

/-- An inhabited functor card yields essential surjectivity of its functor. -/
theorem SpecCoverFunctorCard.essentially_surjective
    (E : SpecCoverFunctorCard K) (C : FiniteEtaleCover (specBase K)) :
    ∃ A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ,
      Nonempty (E.functor.obj A ≅ C) := by
  obtain ⟨A, ⟨e⟩⟩ := specCoverObjectMap_essentially_surjective K C
  exact ⟨A, ⟨(eqToIso (E.agrees_on_objects A)) ≪≫ e⟩⟩

/-- An equivalence card yields the functor card. -/
def SpecCoverEquivalenceCard.toFunctorCard
    (E : SpecCoverEquivalenceCard K) : SpecCoverFunctorCard K where
  functor := E.equivalence.functor
  agrees_on_objects := E.agrees_on_objects
  full_faithful := ⟨inferInstance, inferInstance⟩

end LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverEquivalence
