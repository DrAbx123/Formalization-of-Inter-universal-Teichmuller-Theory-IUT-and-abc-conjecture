/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1761DMStackSmallnessActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual

/-!
# S1800: the identity finite-type DM atlas of the S1726 orbicurve and identity-groupoid descent

## Question

S1761 proved that the raw finite-etale descent category S1761RawDescent s t is
essentially small for arbitrary schemes U R and maps s t : R -> U, and that
every full subcategory (in particular any cocycle subcategory) is essentially
small.  It also proved the conditional transfer
S1761Cover_essentiallySmall_of_atlasDescent: if the actual cover category is
equivalent to a full subcategory of the raw descent category along a finite-type
DM atlas, then the cover category is essentially small.

The stack of S1726Orbicurve is represented by the affine Weierstrass model
Spec R'.  This file constructs the identity atlas U = R', with atlas point the
identity strong transformation, proves that its self-fibre-product is again R'
with both structure maps equal to the identity, and compares the
identity-groupoid cocycle descent category with the affine finite-etale slice
over R'.

## Results proved unconditionally

* S1800IdentityAtlas : S1761FiniteTypeDMAtlas S1726Orbicurve.stack, hence
  S1800FiniteTypeDMAtlasExistence is discharged for the S1726 orbicurve.
  The atlas is the identity map of the representable stack of Spec R'; its
  two-pullback witness is constructed from the representation of the test
  scheme, and is not assumed.

* The self-fibre-product of the identity atlas is Spec R' itself, and both
  S1761AtlasSelfFiberSource and S1761AtlasSelfFiberTarget are the identity
  map of Spec R'.  This is the precise identity groupoid s = t = id
  presentation.

* The identity cocycle subcategory S1800CocycleSub (raw descent data along
  s = t = id whose descent isomorphism is the identity) is equivalent to the
  affine finite-etale slice S1761FiniteEtaleSlice (Spec R')
  (S1800SliceEquivCocycle).  The equivalence is the skeleton equivalence
  followed by the functor that reads a slice object as its own identity descent
  datum.

* Consequently the sharp identity-groupoid descent statement is equivalent to
  the S1733 cover-slice equivalence (S1800CocycleDescent_iff_sliceDescent),
  and implies the S1761 atlas-descent equivalence
  (S1800IdentityAtlasDescent_of_cocycleDescent).  Hence, assuming the sharp
  identity-groupoid descent, the actual cover category is essentially small
  (S1800Cover_essentiallySmall_of_cocycleDescent) and carries an actual
  Category.{0,1} (S1800Category01_of_cocycleDescent).

## The exact first missing

S1761FiniteTypeDMAtlasExistence is no longer missing for S1726Orbicurve: it is
proved here by the identity atlas.  The remaining statement is
S1761FiniteTypeDMCoverDescent, i.e. the equivalence between the actual cover
category and the cocycle subcategory of raw descent data.  For the identity
atlas its sharp form is exactly the S1733 cover-slice equivalence, which is
equivalent to the source-representability/retraction statement isolated in
S1743/S1756/S1758.  This file does not inhabit that equivalence.

The small raw cover-map data of S1728 is a stronger statement: the
slice/descent equivalence compares 2-isomorphism classes of cover maps, while
S1728SmallRawCoverDataRequired asks for small carriers of raw cover maps.  The
stronger input is the known S1733AffineCoverModelMissing; it is re-exported
conditionally as S1800SmallRawCoverData_of_affineCoverModel, not derived from
the descent equivalence.

## Honest boundary

No sorry, no axiom, no Shrink, ULift, PLift or PUnit, and no fake equivalence.
Every assertion about the identity atlas and the identity cocycle subcategory is
a real construction; the remaining descent equivalence is stated as a
hypothesis and is never inhabited.  The only axioms used are propext,
Classical.choice and Quot.sound; see the #print axioms block at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
open scoped SpecOfNotation
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1761DMStackSmallnessActual
open LeanFormal.IUT.XiFPaper.S1738FiniteTypeSmallnessActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

/-- The base field of the S1726 orbicurve. -/
abbrev S1800K := S1726K

/-- The affine Weierstrass model of the S1726 orbicurve, as a scheme over the base. -/
abbrev S1800U : SchemeOverField S1800K := S1726AffineOver

/-- The underlying scheme of the affine model. -/
abbrev S1800U0 : Scheme.{0} := S1726AffineScheme

/-- The etale stack of the S1726 orbicurve. -/
abbrev S1800X : EtaleStackOverField S1800K := S1726Orbicurve.stack

/-! ## 1. Uniqueness of 2-cells into a representable stack -/

/-- A natural transformation between functors into a discrete category is a
subsingleton. -/
theorem S1800NatTrans_discrete_subsingleton {C : Type*} [Category C] {α : Type}
    (F G : C ⥤ Discrete α) : Subsingleton (F ⟶ G) := by
  constructor
  intro a b
  apply CategoryTheory.NatTrans.ext
  funext X
  exact Subsingleton.elim _ _

/-- Modifications between strong transformations into a representable etale
stack are subsingletons. -/
theorem S1800Modification_subsingleton {W : EtaleStackPseudofunctor S1800K}
    {S : SchemeOverField S1800K} (L L' : W ⟶ S1738R S) :
    Subsingleton (L ⟶ L') := by
  constructor
  intro a b
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro V
  apply CategoryTheory.Cat.Hom₂.ext
  haveI : Subsingleton ((L.app V).toFunctor ⟶ (L'.app V).toFunctor) :=
    S1800NatTrans_discrete_subsingleton _ _
  exact Subsingleton.elim _ _

/-! ## 2. The identity finite-type DM atlas -/

/-- The identity scheme morphism of a scheme over the base, as a representable
map of representable etale stacks. -/
noncomputable def S1800IdRepMap (T : SchemeOverField S1800K) :
    SchemeRepresentableMap (𝟙 T) where
  transformation := Pseudofunctor.StrongTrans.id (S1738R T)
  app_eq := by
    intro V
    apply CategoryTheory.Cat.ext
    apply Discrete.functor_ext
    intro P
    exact Discrete.ext (Category.comp_id P)

/-- The identity strong transformation of the affine model, used as the atlas
point. -/
noncomputable def S1800IdAtlasPoint :
    Pseudofunctor.StrongTrans (S1738R S1800U) S1800X.fiber :=
  Pseudofunctor.StrongTrans.id (S1738R S1800U)

/-- The two-pullback square of the identity base change at an arbitrary test
point. -/
noncomputable def S1800IdSquare (T : SchemeOverField S1800K)
    (q : Pseudofunctor.StrongTrans (S1738R T) S1800X.fiber) :
    EtalePseudofunctorSquare (S1738R T) (S1738R S1800U) (S1738R T)
      (S1738R S1800U) :=
  EtalePseudofunctorSquare.mk q (S1800IdRepMap T).transformation S1800IdAtlasPoint q
    ((Pseudofunctor.StrongTrans.rightUnitor q).trans
      (Pseudofunctor.StrongTrans.leftUnitor q).symm)

/-- The identity square is a genuine two-pullback.  The lift of a cone is its
second leg, and all coherence equations are subsingleton comparisons of
modifications into representable stacks. -/
noncomputable def S1800IdSquareWitness (T : SchemeOverField S1800K)
    (q : Pseudofunctor.StrongTrans (S1738R T) S1800X.fiber) :
    (S1800IdSquare T q).TwoPullbackWitness :=
  { lift := fun _ cone => cone.toY
    liftToX := fun _ cone =>
      (cone.commutes.symm).trans (Pseudofunctor.StrongTrans.rightUnitor cone.toX)
    liftToY := fun _ cone =>
      Pseudofunctor.StrongTrans.rightUnitor cone.toY
    liftTwoCell := fun _ _ _ morphism => morphism.toY
    liftTwoCell_toX := by
      intro W source target morphism
      haveI : Subsingleton
          ((Pseudofunctor.StrongTrans.vcomp source.toY (S1800IdSquare T q).toX) ⟶
            (Pseudofunctor.StrongTrans.vcomp target.toY (S1800IdSquare T q).toX)) :=
        S1800Modification_subsingleton (S := S1800U) _ _
      exact Subsingleton.elim _ _
    liftTwoCell_toY := by
      intro W source target morphism
      haveI : Subsingleton
          ((Pseudofunctor.StrongTrans.vcomp source.toY (S1800IdSquare T q).toY) ⟶
            (Pseudofunctor.StrongTrans.vcomp target.toY (S1800IdSquare T q).toY)) :=
        S1800Modification_subsingleton (S := T) _ _
      exact Subsingleton.elim _ _
    twoCell_ext := by
      intro W first second alpha beta h1 h2
      haveI : Subsingleton (first ⟶ second) :=
        S1800Modification_subsingleton (S := T) _ _
      exact Subsingleton.elim _ _ }

/-- The base-change presentation of the identity atlas at an arbitrary test
scheme and point.  The pullback scheme is the test scheme itself, with identity
projection; this is the identity base change. -/
noncomputable def S1800IdBaseChange (T : SchemeOverField S1800K)
    (q : Pseudofunctor.StrongTrans (S1738R T) S1800X.fiber) :
    EtaleStackBaseChangePresentation
      (source := S1761RepresentableStack S1800U) (target := S1800X)
      (map := S1800IdAtlasPoint) T q where
  pullbackScheme := T
  projection := 𝟙 T
  projectionMap := S1800IdRepMap T
  toSource := q
  commutes :=
    (Pseudofunctor.StrongTrans.rightUnitor q).trans
      (Pseudofunctor.StrongTrans.leftUnitor q).symm
  isPullback := S1800IdSquareWitness T q

/-- The identity strong transformation is 2-isomorphic to the strong
transformation induced by the identity scheme map. -/
noncomputable def S1800MkStrongIdIso (T : SchemeOverField S1800K) :
    Iso (S1738MkStrong T T (𝟙 T)) (Pseudofunctor.StrongTrans.id (S1738R T)) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun a => CategoryTheory.Cat.Hom.isoMk
      (Discrete.natIso (fun P => Discrete.eqToIso (Category.comp_id P.as))))
    (by
      intro a b f
      apply CategoryTheory.Cat.Hom₂.ext
      apply CategoryTheory.NatTrans.ext
      funext X
      apply ULift.ext
      exact Subsingleton.elim _ _)

/-- The identity atlas is surjective: every point of the orbicurve is lifted by
the identity etale cover of its own test scheme. -/
theorem S1800IdAtlasSurjective :
    S1761AtlasSurjective S1800U S1800IdAtlasPoint := by
  intro T q
  refine ⟨T, 𝟙 T, ?_, ?_, q, ?_⟩
  · exact inferInstanceAs (Etale (Over.Hom.left (𝟙 T)))
  · exact inferInstanceAs (Surjective (Over.Hom.left (𝟙 T)))
  · refine ⟨?_⟩
    exact (Pseudofunctor.StrongTrans.rightUnitor q).trans
      ((Pseudofunctor.StrongTrans.leftUnitor q).symm.trans
        (@Bicategory.whiskerRightIso (EtaleStackPseudofunctor S1800K) _
          (S1738R T) (S1738R T) (S1800X.fiber)
          (S1738MkStrong T T (𝟙 T)) (Pseudofunctor.StrongTrans.id (S1738R T))
          (S1800MkStrongIdIso T) q).symm)

/-- The affine Weierstrass model is affine. -/
theorem S1800U_affine : IsAffine S1800U.left := by
  change IsAffine (Spec (CommRingCat.of S1726CoordinateRing))
  infer_instance

/-- The structure morphism Spec R' -> Spec F' is locally of finite type:
R' is a quotient of a polynomial ring in two variables. -/
theorem S1800U_locallyOfFiniteType : LocallyOfFiniteType S1800U.hom := by
  have hft : Algebra.FiniteType S1800K S1726CoordinateRing := by
    haveI : Algebra.FiniteType S1800K (MvPolynomial (Fin 2) S1800K) := inferInstance
    exact Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ S1800K (Ideal.span {S1726AffinePolynomial}))
      (Ideal.Quotient.mkₐ_surjective (R₁ := S1800K) (Ideal.span {S1726AffinePolynomial}))
  have hft' : RingHom.FiniteType (algebraMap S1800K S1726CoordinateRing) :=
    RingHom.finiteType_algebraMap.mpr hft
  exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
    (Q := @RingHom.FiniteType) |>.mpr hft'

/-- The identity finite-type DM atlas of the S1726 orbicurve.  The atlas
scheme is the affine Weierstrass model Spec R', the atlas point is the identity
strong transformation, and the self-fibre-product is Spec R' again. -/
noncomputable def S1800IdentityAtlas : S1761FiniteTypeDMAtlas S1800X where
  U := S1800U
  U_affine := S1800U_affine
  U_locallyOfFiniteType := S1800U_locallyOfFiniteType
  point := S1800IdAtlasPoint
  point_etale :=
    { baseChange := fun T q => S1800IdBaseChange T q
      hasProperty := by
        intro T q
        show Etale (Over.Hom.left (𝟙 T))
        infer_instance }
  point_surjective := S1800IdAtlasSurjective
  selfFiber_affine := by
    change IsAffine S1800U.left
    exact S1800U_affine
  selfFiber_locallyOfFiniteType := by
    change LocallyOfFiniteType S1800U.hom
    exact S1800U_locallyOfFiniteType

/-- S1761FiniteTypeDMAtlasExistence is discharged for the S1726 orbicurve.
The first missing piece named in S1761 is not missing here. -/
theorem S1800FiniteTypeDMAtlasExistence_holds :
    S1761FiniteTypeDMAtlasExistence S1800X :=
  ⟨S1800IdentityAtlas⟩

/-- The self-fibre-product of the identity atlas is the affine model itself. -/
theorem S1800AtlasSelfFiber_eq :
    S1761AtlasSelfFiber S1800IdentityAtlas = S1800U := rfl

/-- The underlying scheme of the self-fibre-product is Spec R'. -/
theorem S1800AtlasSelfFiber_left :
    (S1761AtlasSelfFiber S1800IdentityAtlas).left = S1800U0 := rfl

/-- The first structure map of the identity groupoid is the identity. -/
theorem S1800AtlasSelfFiberSource_eq :
    S1761AtlasSelfFiberSource S1800IdentityAtlas = 𝟙 S1800U0 := rfl

/-- The second structure map of the identity groupoid is the identity. -/
theorem S1800AtlasSelfFiberTarget_eq :
    S1761AtlasSelfFiberTarget S1800IdentityAtlas = 𝟙 S1800U0 := rfl

/-- The identity atlas presents the orbicurve as the quotient of the identity
groupoid Spec R' => Spec R'. -/
theorem S1800Atlas_identityGroupoid :
    S1761AtlasSelfFiberSource S1800IdentityAtlas = 𝟙 S1800U0 ∧
      S1761AtlasSelfFiberTarget S1800IdentityAtlas = 𝟙 S1800U0 :=
  ⟨S1800AtlasSelfFiberSource_eq, S1800AtlasSelfFiberTarget_eq⟩

/-! ## 3. The identity cocycle subcategory and the affine slice -/

/-- The affine finite-etale slice over Spec R'. -/
abbrev S1800Slice : Type 1 := S1761FiniteEtaleSlice S1800U0

/-- The raw descent category of the identity groupoid Spec R' => Spec R'. -/
abbrev S1800RawDescentId : Type 1 :=
  S1761RawDescent (𝟙 S1800U0) (𝟙 S1800U0)

/-- The identity-groupoid cocycle condition: the descent isomorphism on the
self-fibre-product is the identity. -/
abbrev S1800Cocycle : S1800RawDescentId → Prop :=
  fun Y => Y.φ = Iso.refl _

/-- The full subcategory of identity-groupoid cocycle descent data. -/
abbrev S1800CocycleSub : Type 1 := ObjectProperty.FullSubcategory S1800Cocycle

/-- The realization functor from the affine finite-etale slice to schemes over
Spec R': a slice object is an affine scheme with a finite-etale map to the
base. -/
abbrev S1800RealizeSlice : S1800Slice ⥤ Over S1800U0 :=
  MorphismProperty.CostructuredArrow.toOver S1761FiniteEtale Scheme.Spec S1800U0 ⋙
    MorphismProperty.Over.forget S1761FiniteEtale ⊤ S1800U0

instance : S1800RealizeSlice.Faithful := inferInstance
instance : S1800RealizeSlice.Full := inferInstance

/-- The composite realization functor from the skeleton of the slice. -/
abbrev S1800RealizeSkeleton : Skeleton S1800Slice ⥤ Over S1800U0 :=
  (fromSkeleton S1800Slice) ⋙ S1800RealizeSlice

instance : S1800RealizeSkeleton.Full := inferInstance
instance : S1800RealizeSkeleton.Faithful := inferInstance

/-- Sending a skeleton index of the slice to its own identity descent datum. -/
noncomputable def S1800SkeletonToCocycle :
    Skeleton S1800Slice ⥤ S1800CocycleSub where
  obj i := ⟨⟨i, Iso.refl _⟩, rfl⟩
  map {i j} f :=
    ObjectProperty.homMk
      { f := S1800RealizeSkeleton.map f
        commutes := by simp }
  map_id i := by
    apply ObjectProperty.hom_ext
    apply S1761RawDescentHom.ext
    change S1800RealizeSkeleton.map (𝟙 i) = 𝟙 (S1800RealizeSkeleton.obj i)
    exact S1800RealizeSkeleton.map_id i
  map_comp {i j k} f g := by
    apply ObjectProperty.hom_ext
    apply S1761RawDescentHom.ext
    change S1800RealizeSkeleton.map (f ≫ g) =
      S1800RealizeSkeleton.map f ≫ S1800RealizeSkeleton.map g
    exact S1800RealizeSkeleton.map_comp f g

instance : S1800SkeletonToCocycle.Faithful where
  map_injective {i j f g} h := by
    have h2 : (S1800SkeletonToCocycle.map f).hom =
        (S1800SkeletonToCocycle.map g).hom :=
      congrArg (fun k => k.hom) h
    have h3 : S1800RealizeSlice.map ((fromSkeleton S1800Slice).map f) =
        S1800RealizeSlice.map ((fromSkeleton S1800Slice).map g) :=
      congrArg S1761RawDescentHom.f h2
    exact (fromSkeleton S1800Slice).map_injective
      (S1800RealizeSlice.map_injective h3)

instance : S1800SkeletonToCocycle.Full where
  map_surjective {i j} k := by
    let f : i ⟶ j := S1800RealizeSkeleton.preimage k.hom.f
    refine ⟨f, ?_⟩
    apply ObjectProperty.hom_ext
    apply S1761RawDescentHom.ext
    change S1800RealizeSkeleton.map f = k.hom.f
    exact Functor.map_preimage S1800RealizeSkeleton k.hom.f

instance : S1800SkeletonToCocycle.EssSurj where
  mem_essImage Y := by
    let h1 : S1761RawDescentHom
        (⟨Y.obj.V, Iso.refl _⟩ : S1800RawDescentId) Y.obj :=
      { f := 𝟙 _, commutes := by
          rw [Y.property]
          simp }
    let h2 : S1761RawDescentHom Y.obj
        (⟨Y.obj.V, Iso.refl _⟩ : S1800RawDescentId) :=
      { f := 𝟙 _, commutes := by
          rw [Y.property]
          simp }
    let e : (S1800SkeletonToCocycle.obj Y.obj.V).obj ≅ Y.obj :=
      { hom := h1
        inv := h2
        hom_inv_id := by
          apply S1761RawDescentHom.ext
          rfl
        inv_hom_id := by
          apply S1761RawDescentHom.ext
          rfl }
    exact ⟨Y.obj.V, ⟨ObjectProperty.isoMk (P := S1800Cocycle) e⟩⟩

instance : S1800SkeletonToCocycle.IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- The affine finite-etale slice over Spec R' is equivalent to the identity
cocycle descent category. -/
noncomputable def S1800SliceEquivCocycle :
    S1800Slice ≌ S1800CocycleSub :=
  (skeletonEquivalence S1800Slice).symm.trans S1800SkeletonToCocycle.asEquivalence

/-- The inverse equivalence, from identity cocycle descent data to the slice. -/
noncomputable def S1800CocycleEquivSlice :
    S1800CocycleSub ≌ S1800Slice :=
  S1800SliceEquivCocycle.symm

/-- The identity cocycle descent category is essentially small, because it is
equivalent to the affine finite-etale slice. -/
theorem S1800CocycleSub_essentiallySmall :
    EssentiallySmall.{0} S1800CocycleSub := by
  haveI : EssentiallySmall.{0} S1800Slice :=
    S1761AffineFiniteEtaleSlice_essentiallySmall S1800U0
  exact (essentiallySmall_congr S1800SliceEquivCocycle).1 inferInstance

/-! ## 4. Identity-groupoid descent and its relation to the cover-slice comparison -/

/-- The actual cover type of the S1726 orbicurve. -/
abbrev S1800Cover : Type 1 := OrbicurveFiniteEtaleCover S1726Orbicurve

/-- The identity-groupoid cocycle descent statement: the actual cover category
(2-isomorphism quotient) is equivalent to the identity cocycle subcategory of
raw descent data. -/
def S1800CocycleDescent : Prop :=
  Nonempty (@CategoryTheory.Equivalence S1800Cover S1800CocycleSub
    (S1728CoverCategory11 (F := S1800K) (X := S1726Orbicurve)) inferInstance)

/-- The cover-slice statement: the actual cover category is equivalent to the
affine finite-etale slice over Spec R'. -/
def S1800SliceDescent : Prop :=
  Nonempty (@CategoryTheory.Equivalence S1800Cover S1800Slice
    (S1728CoverCategory11 (F := S1800K) (X := S1726Orbicurve)) inferInstance)

/-- The cocycle descent statement is exactly the cover-slice statement: the
cocycle subcategory is equivalent to the slice, so composing with that
equivalence identifies the two comparison problems. -/
theorem S1800CocycleDescent_iff_sliceDescent :
    S1800CocycleDescent ↔ S1800SliceDescent := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans S1800CocycleEquivSlice⟩
  · rintro ⟨e⟩
    exact ⟨e.trans S1800SliceEquivCocycle⟩

/-- The S1733 cover-slice equivalence is the same statement as
S1800SliceDescent. -/
theorem S1800SliceDescent_iff_S1733 :
    S1800SliceDescent ↔ S1733CoverSliceEquivalence :=
  Iff.rfl

/-- The identity-atlas form of S1761FiniteTypeDMCoverDescent. -/
def S1800IdentityAtlasDescent : Prop :=
  S1761AtlasDescentEquiv S1800IdentityAtlas

/-- The sharp identity-groupoid descent implies the S1761 atlas-descent
equivalence for the identity atlas (take the cocycle predicate). -/
theorem S1800IdentityAtlasDescent_of_cocycleDescent
    (h : S1800CocycleDescent) : S1800IdentityAtlasDescent := by
  unfold S1800IdentityAtlasDescent S1761AtlasDescentEquiv
  rw [S1800AtlasSelfFiberSource_eq, S1800AtlasSelfFiberTarget_eq]
  rcases h with ⟨e⟩
  exact ⟨S1800Cocycle, ⟨e⟩⟩

/-- The exact first missing statement after S1800:
S1761FiniteTypeDMCoverDescent for the S1726 orbicurve.  The atlas-existence
half is proved; this is the descent half. -/
def S1800FirstMissing : Prop :=
  S1761FiniteTypeDMCoverDescent S1726Orbicurve

/-- The general S1761 descent theorem at an atlas gives the identity-atlas
instance. -/
theorem S1800FirstMissing.identityAtlas
    (h : S1800FirstMissing) : S1800IdentityAtlasDescent :=
  h S1800IdentityAtlas

/-! ## 5. Conditional smallness, Category.{0,1}, and small raw cover data -/

/-- Assuming the sharp identity-groupoid descent, the actual cover category is
essentially small.  This is the S1761 transfer applied to the identity atlas. -/
theorem S1800Cover_essentiallySmall_of_cocycleDescent
    (h : S1800CocycleDescent) : EssentiallySmall.{0} S1800Cover :=
  S1761Cover_essentiallySmall_of_atlasDescent S1800IdentityAtlas
    (S1800IdentityAtlasDescent_of_cocycleDescent h)

/-- The same conclusion directly from the cover-slice comparison. -/
theorem S1800Cover_essentiallySmall_of_sliceDescent
    (h : S1800SliceDescent) : EssentiallySmall.{0} S1800Cover := by
  rcases h with ⟨e⟩
  haveI : EssentiallySmall.{0} S1800Slice :=
    S1761AffineFiniteEtaleSlice_essentiallySmall S1800U0
  exact (essentiallySmall_congr e).2 inferInstance

/-- A genuine Category.{0,1} on the actual cover type, with homs the slice
homs transported along a cover-slice equivalence. -/
@[reducible] noncomputable def S1800Category01_of_sliceEquiv
    (e : @CategoryTheory.Equivalence S1800Cover S1800Slice
      (S1728CoverCategory11 (F := S1800K) (X := S1726Orbicurve))
      inferInstance) : Category.{0, 1} S1800Cover where
  Hom A B := e.functor.obj A ⟶ e.functor.obj B
  id A := 𝟙 (e.functor.obj A)
  comp f g := f ≫ g
  id_comp := by intro A B f; exact Category.id_comp f
  comp_id := by intro A B f; exact Category.comp_id f
  assoc := by intro A B C D f g h; exact Category.assoc f g h

/-- Assuming the sharp identity-groupoid descent, the actual cover type carries
a genuine Category.{0,1}. -/
theorem S1800Category01_of_cocycleDescent
    (h : S1800CocycleDescent) : Nonempty (Category.{0, 1} S1800Cover) := by
  rcases (S1800CocycleDescent_iff_sliceDescent.mp h) with ⟨e⟩
  exact ⟨S1800Category01_of_sliceEquiv e⟩

/-- The affine cover-model input of S1733: a chosen affine finite-etale model of
every cover, with a bijection between model scheme morphisms and raw cover maps. -/
abbrev S1800AffineCoverModelMissing : Prop := S1733AffineCoverModelMissing

/-- The small raw cover-map data of S1728, conditionally on the stronger
S1733 affine cover-model input.  This is not derived from the slice/descent
equivalence: the latter compares 2-isomorphism classes, not raw cover maps. -/
theorem S1800SmallRawCoverData_of_affineCoverModel
    (h : S1800AffineCoverModelMissing) : S1728SmallRawCoverDataRequired :=
  S1733SmallRawCoverDataRequired_of_firstMissing h

/-- From the affine cover-model input one also gets an actual Category.{0,1} on
the cover type, with homs equivalent to the raw cover maps. -/
theorem S1800Category01_of_affineCoverModel
    (h : S1800AffineCoverModelMissing) :
    Nonempty (Category.{0, 1} S1800Cover) :=
  S1733Category01_of_firstMissing h

/-! ## 6. Checks and axiom audit -/

#check S1800IdentityAtlas
#check S1800FiniteTypeDMAtlasExistence_holds
#check S1800AtlasSelfFiberSource_eq
#check S1800AtlasSelfFiberTarget_eq
#check S1800Atlas_identityGroupoid
#check S1800SliceEquivCocycle
#check S1800CocycleDescent_iff_sliceDescent
#check S1800SliceDescent_iff_S1733
#check S1800IdentityAtlasDescent_of_cocycleDescent
#check S1800FirstMissing
#check S1800FirstMissing.identityAtlas
#check S1800Cover_essentiallySmall_of_cocycleDescent
#check S1800Cover_essentiallySmall_of_sliceDescent
#check S1800Category01_of_cocycleDescent
#check S1800SmallRawCoverData_of_affineCoverModel
#check S1800Category01_of_affineCoverModel

#print axioms S1800IdentityAtlas
#print axioms S1800FiniteTypeDMAtlasExistence_holds
#print axioms S1800AtlasSelfFiberSource_eq
#print axioms S1800AtlasSelfFiberTarget_eq
#print axioms S1800SliceEquivCocycle
#print axioms S1800CocycleSub_essentiallySmall
#print axioms S1800CocycleDescent_iff_sliceDescent
#print axioms S1800IdentityAtlasDescent_of_cocycleDescent
#print axioms S1800Cover_essentiallySmall_of_cocycleDescent
#print axioms S1800Cover_essentiallySmall_of_sliceDescent
#print axioms S1800Category01_of_cocycleDescent
#print axioms S1800SmallRawCoverData_of_affineCoverModel
#print axioms S1800Category01_of_affineCoverModel

end LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual
