/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1826

# S1826 -- base change preserves pushouts; the last BC condition of S1769

This file proves the single missing input of S1807:

  BCPreservesPullbacks K : PreservesLimitsOfShape WalkingCospan (bc K).op

for every field K, where bc K = CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K).
Equivalently, bc K preserves pushouts (PreservesColimitsOfShape WalkingSpan (bc K)).

## Method

The concrete coherence

  Kbar (x)_K (B (x)_A C) = (Kbar (x)_K B) (x)_{Kbar (x)_K A} (Kbar (x)_K C)

is obtained *without* writing it down: extension of scalars on the ambient category
CommAlgCat K is proved to be left adjoint to restriction of scalars

  extendScalars K Kbar -| restrictScalars K Kbar,

using Mathlib's Algebra.TensorProduct.liftEquivRight for the hom-set equivalence
(an S-algebra map out of S (x)_R B is the same as an R-algebra map out of B), with
the two naturality squares proved on pure tensors.  Hence extendScalars preserves all
colimits (Mathlib's Functor.IsLeftAdjoint instance).

On the other hand, S1745 proves that CommAlgCat.finiteEtale K is closed under pushouts
(IsClosedUnderColimitsOfShape WalkingSpan), so the inclusion of the full subcategory into
CommAlgCat K creates -- and therefore preserves -- WalkingSpan-shaped colimits.  The
general lemma preservesColimitsOfShape_of_restrict then transfers preservation from the
ambient extension of scalars to its restriction bc K to the finite etale subcategories.

Finally bc K preserves pushouts, i.e. (bc K).op preserves pullbacks, using the shape
equivalence WalkingCospan^op ~= WalkingSpan and preservesLimitsOfShape_op.

## Consequences

* bcPreservesPullbacks K : the missing condition BCPreservesPullbacks K of S1807.
* fiberFunctorUnconditional K : the unconditional
  PreGaloisCategory.FiberFunctor (CommAlgCat.FiniteEtale.fiber K Kbar), obtained by
  feeding the four S1807 conditions to S1769.fiberFunctorOf.

No sorry, admit, new axiom or weakened statement occurs in this file.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Adjunction.Limits
import tmp.sheaf.xif.paper.S1745FiniteEtaleLimitsActual
import tmp.sheaf.xif.paper.S1807BaseChangeFiberActual
import tmp.sheaf.xif.paper.S1769FiberFunctorFieldsActual

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1826

/-! ### 1. Extension and restriction of scalars on CommAlgCat -/

section ChangeOfRings

variable {K : Type} [Field K]

/-- The algebraic closure of K. -/
abbrev Kbar (K : Type) [Field K] : Type := AlgebraicClosure K

/-- Extension of scalars A |-> Kbar (x)_K A, as a functor on all commutative K-algebras. -/
noncomputable def extendScalars : CommAlgCat.{0} K ⥤ CommAlgCat.{0} (Kbar K) where
  obj A := CommAlgCat.of (Kbar K) (Kbar K ⊗[K] (A : Type))
  map {A B} f :=
    CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (Kbar K) (Kbar K)) f.hom)
  map_id A := by
    ext x
    simp
  map_comp {A B C} f g := by
    ext x
    simp

/-- Restriction of scalars A |-> A, viewing a Kbar-algebra as a K-algebra. -/
noncomputable def restrictScalars : CommAlgCat.{0} (Kbar K) ⥤ CommAlgCat.{0} K where
  obj A :=
    letI : Algebra K (A : Type) :=
      ((algebraMap (Kbar K) (A : Type)).comp (algebraMap K (Kbar K))).toAlgebra
    letI : IsScalarTower K (Kbar K) (A : Type) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.of K (A : Type)
  map {A B} f :=
    letI : Algebra K (A : Type) :=
      ((algebraMap (Kbar K) (A : Type)).comp (algebraMap K (Kbar K))).toAlgebra
    letI : IsScalarTower K (Kbar K) (A : Type) := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra K (B : Type) :=
      ((algebraMap (Kbar K) (B : Type)).comp (algebraMap K (Kbar K))).toAlgebra
    letI : IsScalarTower K (Kbar K) (B : Type) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.ofHom (f.hom.restrictScalars K)
  map_id A := by
    ext x
    rfl
  map_comp {A B C} f g := by
    ext x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The hom-set equivalence of the adjunction extendScalars -| restrictScalars.
A Kbar-algebra map Kbar (x)_K X -> Y is the same as a K-algebra map X -> Y, by
Mathlib's Algebra.TensorProduct.liftEquivRight. -/
noncomputable def homEquiv (X : CommAlgCat.{0} K) (Y : CommAlgCat.{0} (Kbar K)) :
    (extendScalars.obj X ⟶ Y) ≃ (X ⟶ restrictScalars.obj Y) where
  toFun f :=
    letI : Algebra K (Y : Type) :=
      ((algebraMap (Kbar K) (Y : Type)).comp (algebraMap K (Kbar K))).toAlgebra
    letI : IsScalarTower K (Kbar K) (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.ofHom ((Algebra.TensorProduct.liftEquivRight (R := K) (S := Kbar K)
      (B := (X : Type)) (C := (Y : Type))).symm f.hom)
  invFun g :=
    letI : Algebra K (Y : Type) :=
      ((algebraMap (Kbar K) (Y : Type)).comp (algebraMap K (Kbar K))).toAlgebra
    letI : IsScalarTower K (Kbar K) (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.ofHom ((Algebra.TensorProduct.liftEquivRight (R := K) (S := Kbar K)
      (B := (X : Type)) (C := (Y : Type))) g.hom)
  left_inv f := by
    letI : Algebra K (Y : Type) :=
      ((algebraMap (Kbar K) (Y : Type)).comp (algebraMap K (Kbar K))).toAlgebra
    letI : IsScalarTower K (Kbar K) (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom, Equiv.apply_symm_apply]
  right_inv g := by
    letI : Algebra K (Y : Type) :=
      ((algebraMap (Kbar K) (Y : Type)).comp (algebraMap K (Kbar K))).toAlgebra
    letI : IsScalarTower K (Kbar K) (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
    apply CommAlgCat.hom_ext
    rw [CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom, Equiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **Extension of scalars is left adjoint to restriction of scalars.** The two naturality
squares are checked on pure tensors. -/
noncomputable def adj : extendScalars (K := K) ⊣ restrictScalars (K := K) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      letI : Algebra K (Y : Type) :=
        ((algebraMap (Kbar K) (Y : Type)).comp (algebraMap K (Kbar K))).toAlgebra
      letI : IsScalarTower K (Kbar K) (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
      change CommAlgCat.ofHom (Algebra.TensorProduct.liftEquivRight (R := K) (S := Kbar K)
          (B := (X' : Type)) (C := (Y : Type)) (CommAlgCat.Hom.hom (f ≫ g)))
        = extendScalars.map f ≫ CommAlgCat.ofHom (Algebra.TensorProduct.liftEquivRight (R := K)
            (S := Kbar K) (B := (X : Type)) (C := (Y : Type)) (CommAlgCat.Hom.hom g))
      apply CommAlgCat.hom_ext
      apply (Algebra.TensorProduct.liftEquivRight (R := K) (S := Kbar K)
        (B := (X' : Type)) (C := (Y : Type))).symm.injective
      ext x
      simp [extendScalars, CommAlgCat.hom_comp, AlgHom.comp_apply,
        Algebra.TensorProduct.liftEquivRight_apply, Algebra.TensorProduct.lift_tmul]
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      letI : Algebra K (Y : Type) :=
        ((algebraMap (Kbar K) (Y : Type)).comp (algebraMap K (Kbar K))).toAlgebra
      letI : IsScalarTower K (Kbar K) (Y : Type) := IsScalarTower.of_algebraMap_eq' rfl
      letI : Algebra K (Y' : Type) :=
        ((algebraMap (Kbar K) (Y' : Type)).comp (algebraMap K (Kbar K))).toAlgebra
      letI : IsScalarTower K (Kbar K) (Y' : Type) := IsScalarTower.of_algebraMap_eq' rfl
      change CommAlgCat.ofHom ((Algebra.TensorProduct.liftEquivRight (R := K) (S := Kbar K)
          (B := (X : Type)) (C := (Y' : Type))).symm (CommAlgCat.Hom.hom (f ≫ g)))
        = CommAlgCat.ofHom ((Algebra.TensorProduct.liftEquivRight (R := K) (S := Kbar K)
            (B := (X : Type)) (C := (Y : Type))).symm (CommAlgCat.Hom.hom f)) ≫
          restrictScalars.map g
      apply CommAlgCat.hom_ext
      ext x
      simp [restrictScalars, CommAlgCat.hom_comp, AlgHom.comp_apply,
        Algebra.TensorProduct.liftEquivRight_symm_apply, Algebra.TensorProduct.includeRight_apply]
  }

/-- extendScalars is a left adjoint, hence it preserves all colimits. -/
instance extendScalars_isLeftAdjoint : (extendScalars (K := K)).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩

end ChangeOfRings

/-! ### 2. Transfer of colimit preservation through full subcategories -/

/-- If an ambient functor G : C ⥤ D preserves J-colimits, and the full subcategories
P.FullSubcategory, P'.FullSubcategory create J-colimits, then a functor
F : P.FullSubcategory ⥤ P'.FullSubcategory with P.ι ⋙ G = F ⋙ P'.ι also preserves
J-colimits.

The proof reflects the P'.ι-image of the cocone, rewrites it as the G-image of the
P.ι-image, and uses that both P.ι and G preserve the relevant colimits. -/
lemma preservesColimitsOfShape_of_restrict
    {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty C} {P' : ObjectProperty D}
    (J : Type*) [Category J]
    (G : C ⥤ D) (F : P.FullSubcategory ⥤ P'.FullSubcategory)
    (hFG : P.ι ⋙ G = F ⋙ P'.ι)
    [P.IsClosedUnderColimitsOfShape J] [P'.IsClosedUnderColimitsOfShape J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J G] : PreservesColimitsOfShape J F where
  preservesColimit {K} := by
    refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K) ?_
    apply isColimitOfReflects P'.ι
    have h1 : IsColimit (G.mapCocone (P.ι.mapCocone (colimit.cocone K))) :=
      isColimitOfPreserves G (isColimitOfPreserves P.ι (colimit.isColimit K))
    have h2 : IsColimit ((P.ι ⋙ G).mapCocone (colimit.cocone K)) :=
      IsColimit.ofIsoColimit h1
        (Functor.mapCoconeMapCocone (H := P.ι) (H' := G) (c := colimit.cocone K)).symm
    rw [hFG] at h2
    exact IsColimit.ofIsoColimit h2
      (Functor.mapCoconeMapCocone (H := F) (H' := P'.ι) (c := colimit.cocone K))

/-! ### 3. Base change preserves pushouts -/

section BaseChange

variable {K : Type} [Field K]

/-- The base change functor bc K is the restriction of the ambient extension of scalars. -/
lemma bc_eq_restrict_extendScalars :
    (CommAlgCat.finiteEtale K).ι ⋙ (extendScalars (K := K)) =
      (S1807.bc K) ⋙ (CommAlgCat.finiteEtale (Kbar K)).ι := rfl

/-- **Base change preserves pushouts.** The concrete coherence is hidden in the adjunction
extendScalars -| restrictScalars: extension of scalars is a left adjoint, hence preserves
colimits, and S1745's closure of finite etale algebras under pushouts lets us descend to
the full subcategories. -/
theorem bc_preservesColimitsOfShape_walkingSpan :
    PreservesColimitsOfShape WalkingSpan (S1807.bc K) :=
  preservesColimitsOfShape_of_restrict WalkingSpan (extendScalars (K := K)) (S1807.bc K)
    (bc_eq_restrict_extendScalars (K := K))

/-- **The missing condition of S1807**: (bc K).op preserves pullbacks. -/
theorem bcPreservesPullbacks : S1807.BCPreservesPullbacks K := by
  haveI : PreservesColimitsOfShape WalkingSpan (S1807.bc K) :=
    bc_preservesColimitsOfShape_walkingSpan
  haveI : PreservesColimitsOfShape (WalkingCospanᵒᵖ) (S1807.bc K) :=
    preservesColimitsOfShape_of_equiv walkingCospanOpEquiv.symm (S1807.bc K)
  exact preservesLimitsOfShape_op WalkingCospan (S1807.bc K)

end BaseChange

/-! ### 4. The unconditional fiber functor -/

/-- **The unconditional fiber functor.** All four base change conditions of S1769/S1807 are
now unconditional; feeding them to S1769.fiberFunctorOf yields the fiber functor
F K = CommAlgCat.FiniteEtale.fiber K Kbar with all six fields. -/
theorem fiberFunctorUnconditional (K : Type) [Field K] [PreGaloisCategory (S1769.C K)] :
    PreGaloisCategory.FiberFunctor (S1769.F K) :=
  S1769.fiberFunctorOf K (bcPreservesPullbacks (K := K))
    (S1807.bcPreservesFiniteProducts K) (S1807.bcPreservesEpis K) (S1807.bcPreservesQuotients K)

/-! ### 5. Axiom audit -/

#print axioms S1826.extendScalars
#print axioms S1826.restrictScalars
#print axioms S1826.adj
#print axioms S1826.preservesColimitsOfShape_of_restrict
#print axioms S1826.bc_preservesColimitsOfShape_walkingSpan
#print axioms S1826.bcPreservesPullbacks
#print axioms S1826.fiberFunctorUnconditional

end S1826
