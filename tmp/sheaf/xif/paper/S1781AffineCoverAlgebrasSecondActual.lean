/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual
import tmp.sheaf.xif.paper.S1744Category01AssemblyActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite

/-!
# S1781: the affine cover algebras of the S1726 orbicurve (second attempt)

## Question

S1728 constructs the actual cover category of the S1726 D6 orbicurve

    S1728Cover = OrbicurveFiniteEtaleCover S1726Orbicurve

with the 2-isomorphism-quotient category structure Category.{1,1}, and reduces
the missing Category.{0,1} to a small hom carrier.  This file attempts the
*second* route: identify the cover category with

    (CommAlgCat.FiniteEtale R')^op,     R' = S1726CoordinateRing,

i.e. with the opposite of Mathlib's category of finite etale R'-algebras,
by sending a cover A to the global sections of its affine model.

## What is constructed here, unconditionally

* S1781Sections A = Gamma(S_A), the ring of global sections of the affine
  finite etale model S_A = S1733Model A of a cover.

* S1781Algebra: the actual R'-algebra structure on Gamma(S_A), induced by the
  structure morphism S_A -> Spec R' (transported out of Gamma(Spec R') along
  Mathlib's Scheme.GammaSpecIso).  The algebra structure is not manufactured:
  the structure morphism is the base-change projection of the cover.

* S1781_moduleFinite / S1781_algebraEtale: Gamma(S_A) is a finite etale
  R'-algebra, read off from IsFinite/Etale of the structure morphism through
  Mathlib's affine HasRingHomProperty/HasAffineProperty bridges.

* S1781Obj A : CommAlgCat.FiniteEtale R', the actual object of Mathlib's
  finite etale algebra category attached to a cover.

## The exact obstruction (not faked)

The assignment above is *almost* a functor from S1728Cover to
(CommAlgCat.FiniteEtale R')^op.  What fails is the functor identity law, and
it fails exactly at the missing statement of S1756:

* S1781ModelMap_id_class: the model morphism of the identity cover class is
  S1756's self-endomorphism, S1781ModelMap A A (identity) = S1756End A.
* S1781ModelIdLaw_iff / S1781IdLaw_iff: the identity law at a cover, both in
  model form and in the algebra category, is equivalent to
  S1756End A = identity, i.e. to the representability of that cover source.
* S1781IdLawAll_iff: the assignment satisfies the functor identity law on all
  covers if and only if S1781FirstMissing := S1756FirstMissing holds.
* S1781_noFunctor_without_firstMissing: consequently no functor whose object
  map is the affine cover algebra and whose hom map is the canonical
  assignment S1781Map exists without S1781FirstMissing.

Two further unconditional results:

* S1781_modelMap_ext: the induced algebra morphism determines the model
  morphism (Spec and Gamma are mutually inverse on affine schemes), so the
  assignment is injective on model morphisms; combined with
  S1781ModelMap_congr this is the faithfulness half of the comparison.
* S1781FullnessMissing and S1781EssSurjMissing record exactly what is still
  missing for full faithfulness and essential surjectivity: extension/descent
  of model morphisms over the base, and the construction of an
  EtaleStackBaseChangePresentation for the structure morphism of the spectrum
  of an arbitrary finite etale R'-algebra (no such construction exists in the
  tree; every base-change presentation there is the one attached to an
  already given cover).  S1781EquivalenceTarget records the target as a
  structure; it is not inhabited.

No sorry, no new axiom, no Shrink/ULift/PUnit, and no fake category or
functor is introduced.

## Axiom footprint

Only propext, Classical.choice and Quot.sound; see the #print axioms block at
the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1781AffineCoverAlgebrasSecondActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1744Category01AssemblyActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual

attribute [local instance] S1744Model_isAffine S1744Base_isAffine

/-! ## 1. The global sections of the affine model as a finite etale algebra -/

/-- The ring of global sections of the affine finite etale model of a cover. -/
abbrev S1781Sections (A : S1728Cover) : CommRingCat :=
  (Over.left (S1733Model A)).presheaf.obj (Opposite.op ⊤)

/-- The structure morphism R' -> Gamma(S_A), read out of the base-change
projection S_A -> Spec R' and Mathlib's identification Gamma(Spec R') = R'. -/
noncomputable def S1781StructHom (A : S1728Cover) :
    CommRingCat.of S1726CoordinateRing ⟶ S1781Sections A :=
  (Scheme.ΓSpecIso (CommRingCat.of S1726CoordinateRing)).inv ≫
    (S1733ModelOver A).left.appTop

/-- The same structure morphism as a ring homomorphism. -/
noncomputable def S1781StructRingHom (A : S1728Cover) :
    S1726CoordinateRing →+* S1781Sections A :=
  (S1781StructHom A).hom

/-- The actual R'-algebra structure on the global sections of the model. -/
instance S1781Algebra (A : S1728Cover) : Algebra S1726CoordinateRing (S1781Sections A) :=
  (S1781StructRingHom A).toAlgebra

theorem S1781_algebraMap_eq (A : S1728Cover) :
    algebraMap S1726CoordinateRing (S1781Sections A) = S1781StructRingHom A :=
  RingHom.algebraMap_toAlgebra (S1781StructRingHom A)

/-- The structure morphism of the model is finite, hence Gamma(S_A) is a finite
R'-module. -/
theorem S1781_ringHom_finite (A : S1728Cover) :
    RingHom.Finite (S1781StructRingHom A) := by
  haveI hfin : IsFinite (S1733ModelOver A).left := (S1733Model_finiteEtale A).1
  have h : RingHom.Finite ((S1733ModelOver A).left.appTop).hom :=
    Scheme.Hom.finite_appTop (S1733ModelOver A).left
  exact RingHom.finite_respectsIso.2 ((S1733ModelOver A).left.appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of S1726CoordinateRing)).symm.commRingCatIsoToRingEquiv) h

/-- The structure morphism of the model is etale, hence Gamma(S_A) is an etale
R'-algebra. -/
theorem S1781_ringHom_etale (A : S1728Cover) :
    RingHom.Etale (S1781StructRingHom A) := by
  have h : RingHom.Etale ((S1733ModelOver A).left.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (Q := @RingHom.Etale)).mp
      (S1733Model_finiteEtale A).2
  exact RingHom.Etale.respectsIso.2 ((S1733ModelOver A).left.appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of S1726CoordinateRing)).symm.commRingCatIsoToRingEquiv) h

/-- Gamma(S_A) is a finite R'-module. -/
theorem S1781_moduleFinite (A : S1728Cover) :
    Module.Finite S1726CoordinateRing (S1781Sections A) := by
  have h := S1781_ringHom_finite A
  rw [RingHom.Finite] at h
  exact h

/-- Gamma(S_A) is an etale R'-algebra. -/
theorem S1781_algebraEtale (A : S1728Cover) :
    Algebra.Etale S1726CoordinateRing (S1781Sections A) := by
  have h := S1781_ringHom_etale A
  show RingHom.Etale (algebraMap S1726CoordinateRing (S1781Sections A))
  rw [S1781_algebraMap_eq]
  exact h

/-- **The affine cover algebra of a cover**: the finite etale R'-algebra of
global sections of its affine finite etale model, as an object of Mathlib's
category of finite etale R'-algebras. -/
noncomputable def S1781Obj (A : S1728Cover) : CommAlgCat.FiniteEtale S1726CoordinateRing :=
  letI : Module.Finite S1726CoordinateRing (S1781Sections A) := S1781_moduleFinite A
  letI : Algebra.Etale S1726CoordinateRing (S1781Sections A) := S1781_algebraEtale A
  CommAlgCat.FiniteEtale.of S1726CoordinateRing (S1781Sections A)

/-- The underlying algebra of the attached object is the sections ring. -/
theorem S1781Obj_obj (A : S1728Cover) :
    (S1781Obj A).obj = CommAlgCat.of S1726CoordinateRing (S1781Sections A) := rfl

/-! ## 2. The model morphism of a cover map is a morphism over the base -/

/-- The strong transformation of the affine models attached to a cover map: the
base-change comparison of the source cover, the cover map itself, and S1743's
lift of the target cover. -/
noncomputable def S1781Eta (A B : S1728Cover) (f : S1728CoverMap A B) :
    Pseudofunctor.StrongTrans (S1743Y (S1733Model A)) (S1743Y (S1733Model B)) :=
  Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map) (S1743Lift B)

/-- The model scheme morphism of a cover map, as constructed in S1744. -/
noncomputable def S1781ModelMap (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1733Model A ⟶ S1733Model B :=
  S1744ModelMapOfCoverMap A B f

/-- The model morphism is the 2-Yoneda evaluation of the attached strong
transformation. -/
theorem S1781ModelMap_eq_eval (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1781ModelMap A B f =
      S1742HomOfStrongTrans (F := S1726K) (S1781Eta A B f) := rfl

/-- The unconditional half of the model representability: the lift of the
identity cone, composed with the comparison, is 2-isomorphic to the identity of
the cover source. -/
noncomputable def S1781LiftSection (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)) :=
  (S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A)

/-- The lift of the identity cone projects to the structure map of the
cover. -/
noncomputable def S1781LiftProjection (A : S1728Cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ProjectionMap A)) A.map :=
  (S1743BaseChange A).isPullback.liftToY (S1743Source A) (S1743IdentityCone A)

/-- The model morphism of a cover map commutes with the projections to the
base, up to 2-isomorphism of strong transformations. -/
noncomputable def S1781EtaProjection (A B : S1728Cover) (f : S1728CoverMap A B) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1781Eta A B f) (S1756ProjectionMap B))
      (S1756ProjectionMap A) :=
  (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) f.map)
      (S1743Lift B) (S1756ProjectionMap B)).trans
    ((S1756WhiskerLeftIso _ _ _ (S1781LiftProjection B)).trans
    ((S1756AssociatorIso (S1756ToSource A) f.map B.map).trans
    ((S1756WhiskerLeftIso (S1756ToSource A) _ _ f.commutes).trans
    ((S1743BaseChange A).commutes.trans
      (S1756RightUnitorIso (S1756ProjectionMap A))))))

/-- **The model morphism of a cover map is a morphism over the base**: it
commutes strictly with the structure morphisms to Spec R'. -/
theorem S1781ModelMap_over (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1781ModelMap A B f ≫ S1756Projection B = S1756Projection A := by
  have hcomp := S1743YonedaEval_vcomp (S1733Model A) (S1733Model B)
    S1726AffineOver (S1781Eta A B f) (S1756ProjectionMap B)
  have hcongr : S1743YonedaEval (S1733Model A) S1726AffineOver
      (Pseudofunctor.StrongTrans.vcomp (S1781Eta A B f) (S1756ProjectionMap B)) =
      S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) :=
    S1742HomOfStrongTrans_congr (S1781EtaProjection A B f)
  calc
    S1781ModelMap A B f ≫ S1756Projection B
        = S1743YonedaEval (S1733Model A) (S1733Model B) (S1781Eta A B f) ≫
            S1743YonedaEval (S1733Model B) S1726AffineOver (S1756ProjectionMap B) := by
          rw [S1756YonedaEval_projectionMap B]
          rfl
    _ = S1743YonedaEval (S1733Model A) S1726AffineOver
          (Pseudofunctor.StrongTrans.vcomp (S1781Eta A B f) (S1756ProjectionMap B)) :=
          hcomp.symm
    _ = S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) := hcongr
    _ = S1756Projection A := S1756YonedaEval_projectionMap A

/-! ## 3. The induced R'-algebra homomorphism -/

/-- A morphism of affine models over the base induces a ring homomorphism on
global sections which is R'-linear. -/
theorem S1781Struct_natural (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B)
    (hg : g ≫ S1756Projection B = S1756Projection A) :
    (g.left.appTop).hom.comp (S1781StructRingHom B) = S1781StructRingHom A := by
  have hleft : g.left ≫ (S1756Projection B).left = (S1756Projection A).left :=
    congrArg Over.Hom.left hg
  have h5 : (S1756Projection B).left.appTop ≫ g.left.appTop =
      (S1756Projection A).left.appTop := by
    rw [← Scheme.Hom.comp_appTop]
    exact congrArg Scheme.Hom.appTop hleft
  have h4 : ((S1756Projection A).left.appTop).hom =
      (g.left.appTop).hom.comp ((S1756Projection B).left.appTop).hom := by
    have h6 := congrArg CommRingCat.Hom.hom h5
    rw [CommRingCat.hom_comp] at h6
    exact h6.symm
  show (g.left.appTop).hom.comp ((S1781StructHom B).hom) = (S1781StructHom A).hom
  have h1 : (S1781StructHom B).hom = ((S1756Projection B).left.appTop).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of S1726CoordinateRing)).inv).hom := rfl
  have h2 : (S1781StructHom A).hom = ((S1756Projection A).left.appTop).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of S1726CoordinateRing)).inv).hom := rfl
  rw [h1, h2, h4]
  rfl

/-- The R'-algebra homomorphism of global sections induced by a morphism of
affine models over the base. -/
noncomputable def S1781AlgHomOfModelMap (A B : S1728Cover) (g : S1733Model A ⟶ S1733Model B)
    (hg : g ≫ S1756Projection B = S1756Projection A) :
    S1781Sections B →ₐ[S1726CoordinateRing] S1781Sections A where
  toFun := (g.left.appTop).hom
  map_one' := map_one _
  map_mul' x y := map_mul _ x y
  map_zero' := map_zero _
  map_add' x y := map_add _ x y
  commutes' r := by
    have h := S1781Struct_natural A B g hg
    have h2 := congrArg (fun (f : S1726CoordinateRing →+* S1781Sections A) => f r) h
    simpa [RingHom.comp_apply, S1781_algebraMap_eq] using h2

/-- Two proofs of the base compatibility of the same model morphism give the
same algebra homomorphism. -/
theorem S1781AlgHomOfModelMap_congr (A B : S1728Cover)
    {g₁ g₂ : S1733Model A ⟶ S1733Model B}
    (h₁ : g₁ ≫ S1756Projection B = S1756Projection A)
    (h₂ : g₂ ≫ S1756Projection B = S1756Projection A)
    (hg : g₁ = g₂) :
    S1781AlgHomOfModelMap A B g₁ h₁ = S1781AlgHomOfModelMap A B g₂ h₂ := by
  cases hg
  rfl

/-- The morphism of finite etale R'-algebras attached to a model morphism over
the base, in the contravariant direction. -/
noncomputable def S1781HomOfModelMap (A B : S1728Cover)
    (g : S1733Model A ⟶ S1733Model B)
    (hg : g ≫ S1756Projection B = S1756Projection A) :
    S1781Obj B ⟶ S1781Obj A :=
  letI : Module.Finite S1726CoordinateRing (S1781Sections B) := S1781_moduleFinite B
  letI : Algebra.Etale S1726CoordinateRing (S1781Sections B) := S1781_algebraEtale B
  letI : Module.Finite S1726CoordinateRing (S1781Sections A) := S1781_moduleFinite A
  letI : Algebra.Etale S1726CoordinateRing (S1781Sections A) := S1781_algebraEtale A
  CommAlgCat.FiniteEtale.ofHom (S1781AlgHomOfModelMap A B g hg)

/-- The actual morphism of finite etale R'-algebras attached to a cover map,
in the contravariant direction. -/
noncomputable def S1781HomOfCoverMap (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1781Obj B ⟶ S1781Obj A :=
  S1781HomOfModelMap A B (S1781ModelMap A B f) (S1781ModelMap_over A B f)

/-! ## 4. The assignment on 2-isomorphism classes -/

/-- The model morphism depends only on the 2-isomorphism class of the cover
map: the S1744 action is built from the underlying strong transformation only. -/
theorem S1781ModelMap_congr (A B : S1728Cover) {f g : S1728CoverMap A B}
    (h : S1728CoverMapRel f g) :
    S1781ModelMap A B f = S1781ModelMap A B g := by
  apply S1742HomOfStrongTrans_congr
  exact S1756WhiskerRightIso _ _ (S1743Lift B)
    (S1756WhiskerLeftIso (S1756ToSource A) _ _ h.some)

/-- The induced algebra morphism depends only on the model morphism. -/
theorem S1781HomOfModelMap_congr (A B : S1728Cover)
    {g₁ g₂ : S1733Model A ⟶ S1733Model B}
    (h₁ : g₁ ≫ S1756Projection B = S1756Projection A)
    (h₂ : g₂ ≫ S1756Projection B = S1756Projection A)
    (hg : g₁ = g₂) :
    S1781HomOfModelMap A B g₁ h₁ = S1781HomOfModelMap A B g₂ h₂ := by
  cases hg
  rfl

/-- The induced algebra morphism depends only on the 2-isomorphism class. -/
theorem S1781HomOfCoverMap_congr (A B : S1728Cover) {f g : S1728CoverMap A B}
    (h : S1728CoverMapRel f g) :
    S1781HomOfCoverMap A B f = S1781HomOfCoverMap A B g :=
  S1781HomOfModelMap_congr A B _ _ (S1781ModelMap_congr A B h)

/-- **The class-level assignment** of the second attempt: a 2-isomorphism class
of cover maps acts contravariantly on the attached finite etale algebras. -/
noncomputable def S1781Map (A B : S1728Cover) :
    S1728CoverMapClass A B → (S1781Obj B ⟶ S1781Obj A) :=
  Quot.lift (fun f : S1728CoverMap A B => S1781HomOfCoverMap A B f)
    (fun f g h => S1781HomOfCoverMap_congr A B h)

/-- The class-level assignment is the induced algebra morphism on
representatives. -/
@[simp] theorem S1781Map_mk (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1781Map A B (Quot.mk _ f) = S1781HomOfCoverMap A B f := rfl

/-! ## 5. The induced algebra morphism is injective -/

/-- Two model morphisms over the base which induce the same algebra morphism of
global sections are equal: Spec and Gamma are mutually inverse on affine
schemes, and the model schemes are affine. -/
theorem S1781_modelMap_ext (A B : S1728Cover)
    {g1 g2 : S1733Model A ⟶ S1733Model B}
    (h1 : g1 ≫ S1756Projection B = S1756Projection A)
    (h2 : g2 ≫ S1756Projection B = S1756Projection A)
    (h : S1781HomOfModelMap A B g1 h1 = S1781HomOfModelMap A B g2 h2) :
    g1 = g2 := by
  have halg : S1781AlgHomOfModelMap A B g1 h1 = S1781AlgHomOfModelMap A B g2 h2 :=
    congrArg CommAlgCat.Hom.hom (congrArg (fun m => m.hom) h)
  have hfun : ∀ x, (g1.left.appTop).hom x = (g2.left.appTop).hom x := by
    intro x
    exact AlgHom.congr_fun halg x
  have happ : g1.left.appTop = g2.left.appTop := CommRingCat.hom_ext (RingHom.ext hfun)
  have hspec : Spec.map (g1.left.appTop) = Spec.map (g2.left.appTop) := by rw [happ]
  have hnat1 := Scheme.isoSpec_inv_naturality g1.left
  have hnat2 := Scheme.isoSpec_inv_naturality g2.left
  have hleft : g1.left = g2.left := by
    have h3 : (S1733Model A).left.isoSpec.inv ≫ g1.left =
        (S1733Model A).left.isoSpec.inv ≫ g2.left := by
      rw [← hnat1, ← hnat2, hspec]
    exact (cancel_epi _).mp h3
  exact Comma.hom_ext g1 g2 hleft (Subsingleton.elim _ _)

/-- The identity model morphism induces the identity algebra morphism. -/
theorem S1781HomOfModelMap_id (A : S1728Cover)
    (h : (𝟙 (S1733Model A)) ≫ S1756Projection A = S1756Projection A) :
    S1781HomOfModelMap A A (𝟙 (S1733Model A)) h = 𝟙 (S1781Obj A) := by
  have halg : S1781AlgHomOfModelMap A A (𝟙 (S1733Model A)) h =
      AlgHom.id S1726CoordinateRing (S1781Sections A) := by
    apply AlgHom.ext
    intro x
    show (Over.Hom.left (𝟙 (S1733Model A))).appTop x = x
    rw [show Over.Hom.left (𝟙 (S1733Model A)) = 𝟙 (Over.left (S1733Model A)) from rfl,
      Scheme.Hom.id_appTop]
    rfl
  unfold S1781HomOfModelMap
  rw [halg]
  rfl

/-! ## 6. The functor identity law is exactly the missing statement -/

/-- The strong transformation of the identity cover class is S1756's
self-endomorphism transformation. -/
noncomputable def S1781EtaIdIso (A : S1728Cover) :
    Iso (S1781Eta A A (S1641CoverMapId A))
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) := by
  rw [S1781Eta, S1641CoverMapId_map]
  exact S1756WhiskerRightIso _ _ (S1743Lift A) (S1756RightUnitorIso (S1756ToSource A))

/-- **The model morphism of the identity cover class is S1756's
self-endomorphism.** -/
theorem S1781ModelMap_id_class (A : S1728Cover) :
    S1781ModelMap A A (S1641CoverMapId A) = S1756End A := by
  rw [S1781ModelMap_eq_eval, S1756End]
  exact S1743YonedaEval_congr_iso (S1733Model A) (S1733Model A) (S1781EtaIdIso A)

/-- The identity law of the class-level assignment, in model form. -/
def S1781ModelIdLaw (A : S1728Cover) : Prop :=
  S1781ModelMap A A (S1641CoverMapId A) = 𝟙 (S1733Model A)

/-- **The identity law at a cover is the S1756 missing statement at that
cover.** -/
theorem S1781ModelIdLaw_iff (A : S1728Cover) :
    S1781ModelIdLaw A ↔ S1756End A = 𝟙 (S1733Model A) := by
  unfold S1781ModelIdLaw
  rw [S1781ModelMap_id_class]

/-- The identity law of the class-level assignment, in the algebra category. -/
def S1781IdLaw (A : S1728Cover) : Prop :=
  S1781Map A A (S1728CoverMapClassId A) = 𝟙 (S1781Obj A)

/-- The identity class is represented by the identity cover map. -/
theorem S1781Map_id_class_eq (A : S1728Cover) :
    S1781Map A A (S1728CoverMapClassId A) =
      S1781HomOfCoverMap A A (S1641CoverMapId A) := rfl

/-- The algebra-level identity law is equivalent to the S1756 missing
statement. -/
theorem S1781IdLaw_iff (A : S1728Cover) :
    S1781IdLaw A ↔ S1756End A = 𝟙 (S1733Model A) := by
  have hid : (𝟙 (S1733Model A)) ≫ S1756Projection A = S1756Projection A :=
    Category.id_comp _
  rw [S1781IdLaw, S1781Map_id_class_eq, S1781HomOfCoverMap]
  constructor
  · intro h
    have h1 : S1781HomOfModelMap A A (S1781ModelMap A A (S1641CoverMapId A))
        (S1781ModelMap_over A A (S1641CoverMapId A)) =
        S1781HomOfModelMap A A (𝟙 (S1733Model A)) hid :=
      h.trans (S1781HomOfModelMap_id A hid).symm
    have hm : S1781ModelMap A A (S1641CoverMapId A) = 𝟙 (S1733Model A) :=
      S1781_modelMap_ext A A _ _ h1
    rw [← S1781ModelMap_id_class A]
    exact hm
  · intro h
    have hm : S1781ModelMap A A (S1641CoverMapId A) = 𝟙 (S1733Model A) :=
      (S1781ModelIdLaw_iff A).mpr h
    rw [S1781HomOfModelMap_congr A A (S1781ModelMap_over A A (S1641CoverMapId A)) hid hm]
    exact S1781HomOfModelMap_id A hid

/-! ## 7. The exact missing statements -/

/-- **The exact first missing statement**: every cover source stack is the
representable stack of its affine finite etale model.  Equivalently (S1756),
the base change of the cover map A.map along the identity 1-cell of the base has
the cover source itself as apex. -/
def S1781FirstMissing : Prop := S1756FirstMissing

/-- The identity law of the whole assignment is exactly the first missing
statement. -/
theorem S1781IdLawAll_iff :
    (∀ A : S1728Cover, S1781IdLaw A) ↔ S1781FirstMissing := by
  unfold S1781FirstMissing S1756FirstMissing
  exact forall_congr' (fun A => S1781IdLaw_iff A)

/-- The model form of the identity law, for all covers. -/
theorem S1781ModelIdLawAll_iff :
    (∀ A : S1728Cover, S1781ModelIdLaw A) ↔ S1781FirstMissing := by
  unfold S1781FirstMissing S1756FirstMissing
  exact forall_congr' (fun A => S1781ModelIdLaw_iff A)

/-- Fullness of the comparison: every morphism of affine cover algebras comes
from a cover map.  Equivalently (through Spec/Gamma on the affine models), every
morphism of the affine finite etale models over the base extends to the cover
sources.  This is the geometric extension/descent statement; it is not implied
by S1781FirstMissing alone and is not constructed here. -/
def S1781FullnessMissing : Prop :=
  ∀ (A B : S1728Cover) (g : S1781Obj B ⟶ S1781Obj A), ∃ f : S1728CoverMapClass A B,
    S1781Map A B f = g

/-- Essential surjectivity of the comparison: every finite etale R'-algebra is
the affine cover algebra of a cover.  Constructing it requires an
EtaleStackBaseChangePresentation for the structure morphism of the spectrum of
an arbitrary finite etale R'-algebra, i.e. the general 2-Yoneda/pullback
computation for representable morphisms of etale stacks, which does not exist in
the tree (no construction of an EtaleStackBaseChangePresentation other than the
one attached to an already given cover is available). -/
def S1781EssSurjMissing : Prop :=
  ∀ S : CommAlgCat.FiniteEtale S1726CoordinateRing, ∃ A : S1728Cover,
    Nonempty (S1781Obj A ≅ S)

/-! ### The obstruction: the identity law forces the missing statement -/

/-- **The obstruction theorem**: the class-level assignment satisfies the
functor identity law if and only if every cover source is representable by its
affine finite etale model.  Consequently no functor whose object map is the
affine cover algebra and whose hom map is the canonical assignment S1781Map can
exist without S1781FirstMissing. -/
theorem S1781_noFunctor_without_firstMissing
    (hid : ∀ A : S1728Cover, S1781Map A A (S1728CoverMapClassId A) = 𝟙 (S1781Obj A)) :
    S1781FirstMissing :=
  S1781IdLawAll_iff.mp hid

/-- Contrapositive form: if some cover source is not representable, then the
canonical hom assignment violates the identity law at that cover. -/
theorem S1781_idLaw_fails_of_not_firstMissing (h : ¬ S1781FirstMissing) :
    ∃ A : S1728Cover, S1781Map A A (S1728CoverMapClassId A) ≠ 𝟙 (S1781Obj A) := by
  by_contra hcon
  push Not at hcon
  exact h (S1781_noFunctor_without_firstMissing hcon)

/-- **The exact equivalence target**, recorded as a proposition: a functor from
the actual cover category to the opposite of Mathlib's finite etale algebra
category which is faithful, full and essentially surjective, whose object map is
the affine cover algebra.  The hom map condition is what S1781Map supplies on
each hom class; the missing content is the identity law (S1781FirstMissing), the
fullness statement S1781FullnessMissing and the essential surjectivity statement
S1781EssSurjMissing.  It is recorded, not inhabited. -/
structure S1781EquivalenceTarget where
  /-- A functor with the canonical object map. -/
  functor : S1728Cover ⥤ (CommAlgCat.FiniteEtale S1726CoordinateRing)ᵒᵖ
  /-- The object map is the affine cover algebra. -/
  obj_eq : ∀ A : S1728Cover, Nonempty (functor.obj A ≅ Opposite.op (S1781Obj A))
  /-- Faithful. -/
  faithful : functor.Faithful
  /-- Full. -/
  full : functor.Full
  /-- Essentially surjective. -/
  essSurj : functor.EssSurj

/-! ## 8. Axiom footprint and checks -/

#check S1781Sections
#check S1781StructRingHom
#check S1781_moduleFinite
#check S1781_algebraEtale
#check S1781Obj
#check S1781ModelMap
#check S1781ModelMap_over
#check S1781AlgHomOfModelMap
#check S1781HomOfCoverMap
#check S1781Map
#check S1781_modelMap_ext
#check S1781ModelMap_id_class
#check S1781ModelIdLaw_iff
#check S1781IdLaw_iff
#check S1781FirstMissing
#check S1781IdLawAll_iff
#check S1781ModelIdLawAll_iff
#check S1781FullnessMissing
#check S1781EssSurjMissing
#check S1781EquivalenceTarget

#print axioms S1781StructRingHom
#print axioms S1781_moduleFinite
#print axioms S1781_algebraEtale
#print axioms S1781Obj
#print axioms S1781ModelMap_over
#print axioms S1781AlgHomOfModelMap
#print axioms S1781HomOfCoverMap
#print axioms S1781ModelMap_congr
#print axioms S1781Map
#print axioms S1781_modelMap_ext
#print axioms S1781HomOfModelMap_id
#print axioms S1781ModelMap_id_class
#print axioms S1781IdLaw_iff
#print axioms S1781_noFunctor_without_firstMissing
#print axioms S1781IdLawAll_iff

end LeanFormal.IUT.XiFPaper.S1781AffineCoverAlgebrasSecondActual