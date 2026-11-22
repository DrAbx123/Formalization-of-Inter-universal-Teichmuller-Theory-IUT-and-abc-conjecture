import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Etale.Finite

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# F1b: finite etale covers of Spec K are affine and come from finite etale K-algebras

Given a field K, this module proves the cover side of the field Galois
correspondence for the category FiniteEtaleCover (Spec K) built in
Example36EtaleCoverFoundations.lean:

1. Every finite etale cover f : X ⟶ Spec K is affine: IsFinite f gives
   IsAffineHom f (Mathlib's IsFinite extends IsAffineHom), and the target
   Spec K is affine, so isAffine_of_isAffineHom yields IsAffine X.
2. The global sections A = Gamma(X, top) of such a cover carry a finite etale
   K-algebra structure: A is a commutative ring, K acts through
   Gamma(Spec K) ≅ K and f.appTop, the module is finite by
   Scheme.Hom.finite_appTop, and the algebra is etale because f is etale
   (HasRingHomProperty.iff_of_isAffine).
3. The canonical isomorphism X ≅ Spec A (Scheme.isoSpec) is an isomorphism of
   covers C ≅ finiteEtaleAlgebraCover K A, using
   Scheme.isoSpec_hom_naturality and the Gamma-Spec inverse laws.  Hence the
   object map finite etale K-algebra ↦ finite etale cover of Spec K is
   essentially surjective.
4. The full functor/equivalence (finite etale K-algebras)ᵒᵖ ≌ FiniteEtaleCover
   (Spec K) is NOT constructed here; only the object-level comparison on the
   nose is proved.  The exact remaining naturality card is frozen as
   SpecCoverEquivalenceCard: a functor agreeing with finiteEtaleAlgebraCover on
   objects, together with its inverse and unit/counit or, equivalently, a full
   equivalence.  No inhabitant of the card is constructed.

Boundary: no fake equivalence, no functor is asserted to exist; the card is a
named unproved structure.  The curve/geometric D6 side and the G_K-set side of
the Galois correspondence are outside this file.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecEssentialSurjectivity

universe u

variable {K : Type u} [Field K]

/-- The base scheme Spec K as a scheme over K. -/
abbrev specBase (K : Type u) [Field K] : Scheme.{u} :=
  Spec (CommRingCat.of K)

/-! ## 1. Finite etale covers of Spec K are affine -/

/-- Every finite etale cover of Spec K has affine carrier: a finite morphism
into the affine scheme Spec K is affine. -/
theorem finiteEtaleCover_carrier_isAffine (C : FiniteEtaleCover (specBase K)) :
    IsAffine C.carrier := by
  haveI : IsFinite C.structureMap := FiniteEtaleCover.finite_structureMap C
  exact isAffine_of_isAffineHom C.structureMap

/-- The carrier of a finite etale cover of Spec K is affine (instance form). -/
instance finiteEtaleCoverCarrierIsAffine (C : FiniteEtaleCover (specBase K)) :
    IsAffine C.carrier :=
  finiteEtaleCover_carrier_isAffine C

/-! ## 2. Global sections as a finite etale K-algebra -/

/-- The ring of global sections of a finite etale cover of Spec K. -/
abbrev coverSections (C : FiniteEtaleCover (specBase K)) : Type u :=
  Γ(C.carrier, ⊤)

/-- The Gamma-Spec inverse as a ring equivalence: sections of Spec K are K. -/
abbrev sectionsOfSpecEquiv : Γ(Spec (CommRingCat.of K), ⊤) ≃+* CommRingCat.of K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv

/-- The K-algebra structure on the global sections of a finite etale cover:
the structure map on global sections, precomposed with the Gamma-Spec identification
K ≅ Gamma(Spec K, top). -/
def coverSectionsAlgebraMap (C : FiniteEtaleCover (specBase K)) :
    K →+* coverSections C :=
  C.structureMap.appTop.hom.comp (sectionsOfSpecEquiv).symm.toRingHom

/-- The K-algebra structure on the global sections of a finite etale cover. -/
@[reducible] noncomputable def coverSectionsAlgebra (C : FiniteEtaleCover (specBase K)) :
    Algebra K (coverSections C) :=
  (coverSectionsAlgebraMap C).toAlgebra

/-- The global sections of a finite etale cover, as a finite etale K-algebra.
This is the object-level inverse direction of the Spec comparison. -/
noncomputable def coverSectionsFiniteEtale (C : FiniteEtaleCover (specBase K)) :
    CommAlgCat.FiniteEtale K := by
  let A := coverSections C
  let Γ₀ := Γ(Spec (CommRingCat.of K), ⊤)
  let φbase : K →+* Γ₀ := (sectionsOfSpecEquiv).symm.toRingHom
  letI : Algebra K Γ₀ := φbase.toAlgebra
  letI : Algebra Γ₀ A := (C.structureMap.appTop.hom).toAlgebra
  letI : Algebra K A := coverSectionsAlgebra C
  have hΓ₀ : Algebra.Etale K Γ₀ := by
    have e : K ≃ₐ[K] Γ₀ := AlgEquiv.ofRingEquiv (f := (sectionsOfSpecEquiv).symm) (by
      intro x
      rfl)
    exact Algebra.Etale.of_equiv e
  have hEtale : RingHom.Etale (C.structureMap.appTop.hom) :=
    (AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp
      (FiniteEtaleCover.etale_structureMap C)
  have hA : Algebra.Etale Γ₀ A := hEtale
  haveI : IsScalarTower K Γ₀ A :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have hKA : Algebra.Etale K A := Algebra.Etale.comp K Γ₀ A
  have hFinΓ₀ : Module.Finite K Γ₀ :=
    Module.Finite.equiv (AlgEquiv.ofRingEquiv (f := (sectionsOfSpecEquiv).symm) (by
      intro x
      rfl)).toLinearEquiv
  haveI : IsFinite C.structureMap := FiniteEtaleCover.finite_structureMap C
  have hFinA : Module.Finite Γ₀ A := Scheme.Hom.finite_appTop C.structureMap
  have hFin : Module.Finite K A := Module.Finite.trans Γ₀ A
  exact CommAlgCat.FiniteEtale.of K A

/-- The cover attributed to the global sections of C. -/
abbrev coverSectionsCover (C : FiniteEtaleCover (specBase K)) :
    FiniteEtaleCover (specBase K) :=
  finiteEtaleAlgebraCover K (coverSectionsFiniteEtale C)

/-! ## 3. The canonical isomorphism of covers -/

/-- The structure map of the sections cover is Spec of the proved algebra map. -/
theorem coverSectionsCover_structureMap (C : FiniteEtaleCover (specBase K)) :
    (coverSectionsCover C).structureMap =
      Spec.map (CommRingCat.ofHom (coverSectionsAlgebraMap C)) :=
  rfl

/-- The canonical isomorphism of covers: the object-level essential surjectivity. -/
theorem coverSections_iso (C : FiniteEtaleCover (specBase K)) :
    Nonempty (C ≅ coverSectionsCover C) := by
  let A := coverSections C
  letI : Algebra K A := coverSectionsAlgebra C
  let hl : C.carrier ≅ Spec (CommRingCat.of A) := Scheme.isoSpec C.carrier
  have hmap : (coverSectionsCover C).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := rfl
  have hw : hl.hom ≫ (coverSectionsCover C).structureMap = C.structureMap := by
    rw [hmap]
    have halg : (CommRingCat.ofHom (algebraMap K A)) =
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ C.structureMap.appTop := by
      rw [show algebraMap K A = coverSectionsAlgebraMap C from rfl]
      rfl
    rw [halg, Spec.map_comp]
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality C.structureMap, Category.assoc]
    rw [show (Spec (CommRingCat.of K)).isoSpec.hom =
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom from Scheme.isoSpec_Spec_hom _]
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  exact ⟨ObjectProperty.isoMk _ (Over.isoMk hl hw)⟩

/-- Object-level essential surjectivity of the finite etale algebra ↦ cover map. -/
theorem finiteEtaleAlgebraCover_essentially_surjective
    (C : FiniteEtaleCover (specBase K)) :
    ∃ A : CommAlgCat.FiniteEtale K,
      Nonempty (C ≅ finiteEtaleAlgebraCover K A) :=
  ⟨coverSectionsFiniteEtale C, coverSections_iso C⟩

/-- Object-level comparison with (FiniteEtale K)ᵒᵖ: applying the cover
construction to the sections of any cover recovers the cover up to isomorphism. -/
theorem objectLevel_coverSections_roundtrip (C : FiniteEtaleCover (specBase K)) :
    Nonempty (C ≅ finiteEtaleAlgebraCover K (coverSectionsFiniteEtale C)) :=
  coverSections_iso C

/-- The object-level map from covers to finite etale K-algebras (opposite). -/
noncomputable def coverSectionsObjectMap :
    FiniteEtaleCover (specBase K) → (CommAlgCat.FiniteEtale K)ᵒᵖ :=
  fun C => Opposite.op (coverSectionsFiniteEtale C)

/-- The object map cover ↦ sections is a section of the object map
A ↦ finiteEtaleAlgebraCover K A up to isomorphism, on objects. -/
theorem coverSectionsObjectMap_roundtrip (C : FiniteEtaleCover (specBase K)) :
    Nonempty (C ≅ finiteEtaleAlgebraCover K (coverSectionsObjectMap C).unop) :=
  coverSections_iso C

/-- The spec-side essential surjectivity component of the frozen
FieldGaloisCorrespondence of Example36EtaleCoverFoundations is proved here. -/
theorem fieldGaloisCorrespondence_specEssentialSurjectivity (K : Type u) [Field K] :
    ∀ C : FiniteEtaleCover (Spec (CommRingCat.of K)),
      ∃ A : CommAlgCat.FiniteEtale K,
        Nonempty (C ≅ finiteEtaleAlgebraCover K A) :=
  fun C => finiteEtaleAlgebraCover_essentially_surjective C

/-! ## 4. The frozen naturality/equivalence card -/

/-- The exact remaining naturality card of the field Galois correspondence: a
functor from finite etale K-algebras (opposite) to finite etale covers of Spec K,
agreeing with the proved object map finiteEtaleAlgebraCover on objects.  The
object map and essential surjectivity are proved above; the functor and its
functor laws are NOT constructed. -/
structure SpecCoverFunctorCard (K : Type u) [Field K] where
  /-- The candidate comparison functor. -/
  functor : (CommAlgCat.FiniteEtale K)ᵒᵖ ⥤ FiniteEtaleCover (specBase K)
  /-- It agrees with the proved object map on objects. -/
  agrees_on_objects : ∀ A : (CommAlgCat.FiniteEtale K)ᵒᵖ,
    functor.obj A = finiteEtaleAlgebraCover K A.unop

/-- The exact remaining equivalence card: a category equivalence between finite
etale K-algebras (opposite) and finite etale covers of Spec K, whose functor
agrees with the proved object map on objects.  This is the precise gap left by
F1b; no inhabitant is constructed in this file. -/
structure SpecCoverEquivalenceCard (K : Type u) [Field K] where
  /-- The candidate category equivalence. -/
  equivalence : (CommAlgCat.FiniteEtale K)ᵒᵖ ≌ FiniteEtaleCover (specBase K)
  /-- It agrees with the proved object map on objects. -/
  agrees_on_objects : ∀ A : (CommAlgCat.FiniteEtale K)ᵒᵖ,
    equivalence.functor.obj A = finiteEtaleAlgebraCover K A.unop

/-- An equivalence card yields a functor card (the forgetful direction of the
frozen data). -/
def SpecCoverEquivalenceCard.toFunctorCard
    (E : SpecCoverEquivalenceCard K) : SpecCoverFunctorCard K where
  functor := E.equivalence.functor
  agrees_on_objects := E.agrees_on_objects

/-- The essential surjectivity proved in this file is the object-level part of
the frozen equivalence card: any inhabited equivalence card recovers it. -/
theorem SpecCoverEquivalenceCard.essentially_surjective
    (_E : SpecCoverEquivalenceCard K) (C : FiniteEtaleCover (specBase K)) :
    ∃ A : CommAlgCat.FiniteEtale K,
      Nonempty (C ≅ finiteEtaleAlgebraCover K A) :=
  finiteEtaleAlgebraCover_essentially_surjective C

end LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecEssentialSurjectivity