/-
# S1743: the actual finite-etale cover category versus the S1733 affine slice

## Question

S1728 built the actual cover category of the S1726 D6 orbicurve as a quotient of
the actual cover maps by 2-isomorphism, with a genuine Category.{1,1}
(S1728ActualCategory11).  S1733 built the essentially small affine finite-etale
slice S1733Slice = P.CostructuredArrow ⊤ Scheme.Spec (Spec R'), with
P = IsFinite inf Etale, and produced for every cover an affine base-change model
S1733Model A finite etale over the base.

This file attacks the comparison asked for by S1743:

  is the 2-iso cover category S1728Cover equivalent to S1733Slice?

## Result

* A genuine object map S1743Object : S1728Cover -> S1733Slice is constructed
  unconditionally: a cover is sent to its identity-point base-change model, made
  explicit as Spec Γ(model) (the model is affine because it is finite over the
  affine base), with the finite-etale structure morphism.  No new model is
  chosen: this is exactly S1733's model, and S1743Object_left/S1743Object_hom
  record the formula.

* The identity-point base-change square is a two-pullback whose right leg is the
  identity.  Its universal property gives, for every cover, a strong
  transformation S1743Lift A from the cover source stack to the representable
  stack of its affine model, together with 2-isomorphisms
  vcomp (S1743Lift A) toSource ≅ id and vcomp (S1743Lift A) projection ≅ A.map
  (S1743ModelSection, S1743Lift_projection).  This is one half of stack
  representability of the cover by its affine finite-etale model, item (a),
  proved unconditionally.

* Item (c) is closed, reusing S1742: the 2-Yoneda comparison for representable
  etale stacks.  Consequences recorded here:
  - S1743SchemeRepresentableMap: the structure SchemeRepresentableMap, which
    S1726/S1733 use as an assumption in every base-change presentation, is
    *constructed* for every scheme morphism;
  - S1743YonedaEval_congr / S1743YonedaClassMap / S1743YonedaFunctor: the
    evaluation at the identity is well defined on modifications and hence on
    2-isomorphism classes, and is a functor to the discrete category of scheme
    morphisms;
  - S1743YonedaEval_vcomp: it is compatible with vertical composition;
  - S1743YonedaClassEquiv: the 2-isomorphism classes of strong transformations
    between two representable etale stacks are *equivalent as a type* to the
    scheme morphisms between them (both round trips proved, via S1742).

* The exact missing statement for the whole comparison is packaged as
  S1743CoverSliceComparison: a functor S1728Cover ⤏ S1733Slice whose object map
  is the explicit model map, which is fully faithful and essentially
  surjective.  Exactly this datum yields S1733's S1733CoverSliceEquivalence, and
  hence EssentiallySmall.{0} S1728Cover and a Category.{0,1} on the actual cover
  type (S1743EssentiallySmall_of_comparison, S1743Category01_of_comparison).

* The two propositions are formally equivalent in the exact form needed:
  S1743SliceFunctorMissing (a fully faithful essentially surjective functor
  S1728Cover ⤏ S1733Slice) is equivalent to S1733's
  S1733CoverSliceEquivalence (S1743SliceFunctorMissing_iff).  Hence nothing is
  weakened: the remaining gap is a functor together with full, faithful and
  essentially-surjective proofs, with the object map already fixed.

## Honest boundary: the two remaining gaps

The equivalence itself is NOT constructed and is not claimed.

(a) S1743SourceRetraction: for every cover A, a strong transformation
    A.source ⟹ Y (S1733Model A) whose composite with the comparison toSource is
    2-isomorphic to the identity.  The other composite is proved here
    (S1743ModelSection).  This is not a consequence of the Yoneda comparison of
    item (c): toSource and its lift have a non-representable *source*, so the
    2-Yoneda equivalence does not see them.  The available TwoPullbackWitness
    supplies only the lift, the two comparison 2-cells and 2-cell
    extensionality, but no inverse 2-cell, so this half is a genuine
    two-categorical statement about the representable base-change square.

(b) S1743SliceFunctorMissing: the functor together with the fully faithful and
    essentially surjective proofs, i.e. cover maps modulo 2-isomorphism must be
    the scheme morphisms between the affine models.  S1733's own proposition is
    exactly this, so the comparison is equivalent to the missing functor.
    Even with (a), (b) needs the transport of (c) across the model comparison,
    because the cover maps in S1728 are strong transformations between arbitrary
    (non-representable) stacks.

No sorry, no axiom, no Shrink/ULift/PUnit, and no fake category is used.  The
only axioms are propext, Classical.choice and Quot.sound.  The target
OrbicurveEtaleFundamentalGroup is not constructed.
-/

import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Quot

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1743CoverSliceActual

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

/-! ## 0. Setting -/

/-- The representable etale stack of a scheme over the S1726 field. -/
noncomputable abbrev S1743Y (S : SchemeOverField S1726K) :
    EtaleStackPseudofunctor S1726K :=
  schemeRepresentableEtalePseudofunctor S1726K S

/-- The source pseudofunctor of a cover. -/
abbrev S1743Source (A : S1728Cover) : EtaleStackPseudofunctor S1726K :=
  A.source.fiber

/-- The representable pseudofunctor of the affine model of a cover. -/
noncomputable abbrev S1743ModelStack (A : S1728Cover) :
    EtaleStackPseudofunctor S1726K :=
  S1743Y (S1733Model A)

/-! ## 1. The object map to the affine finite-etale slice -/

/-- The identity-point base-change presentation of a cover, the presentation
used by S1733. -/
noncomputable def S1743BaseChange (A : S1728Cover) :
    EtaleStackBaseChangePresentation A.map S1726AffineOver S1733BasePoint :=
  A.finiteEtale.baseChange S1726AffineOver S1733BasePoint

/-- The affine model of a cover is an affine scheme: its structure morphism is
finite and the base is the affine S1726 base. -/
theorem S1743Model_isAffine (A : S1728Cover) : IsAffine (S1733Model A).left := by
  haveI : IsAffineHom (S1733ModelOver A).left :=
    (S1733Model_finiteEtale A).1.toIsAffineHom
  haveI : IsAffine (S1726AffineOver).left := inferInstanceAs (IsAffine S1726AffineScheme)
  exact isAffine_of_isAffineHom (S1733ModelOver A).left

/-- The ring whose spectrum is the affine model, as an object of the
costructured-arrow source category. -/
noncomputable abbrev S1743ModelRing (A : S1728Cover) : CommRingCatᵒᵖ :=
  Opposite.op ((S1733Model A).left.presheaf.obj (Opposite.op ⊤))

/-- The structure morphism of the affine model, written from Spec Γ(model). -/
noncomputable def S1743ModelHom (A : S1728Cover) :
    Scheme.Spec.obj (S1743ModelRing A) ⟶ S1733BaseScheme :=
  haveI : IsAffine (S1733Model A).left := S1743Model_isAffine A
  (Scheme.isoSpec (S1733Model A).left).inv ≫ (S1733ModelOver A).left

/-- The structure morphism of the affine model is finite and etale.  Both
properties are taken from the S1733 base-change model and transported along the
canonical affine isomorphism Spec Γ(model) ≅ model. -/
theorem S1743ModelHom_finiteEtale (A : S1728Cover) :
    S1733FiniteEtale (S1743ModelHom A) := by
  haveI hA : IsAffine (S1733Model A).left := S1743Model_isAffine A
  have hfin : IsFinite (S1733ModelOver A).left := (S1733Model_finiteEtale A).1
  have het : Etale (S1733ModelOver A).left := (S1733Model_finiteEtale A).2
  have h1 : IsFinite (S1743ModelHom A) := by
    haveI : IsFinite (S1733ModelOver A).left := hfin
    exact inferInstanceAs (IsFinite ((Scheme.isoSpec (S1733Model A).left).inv ≫
      (S1733ModelOver A).left))
  have h2 : Etale (S1743ModelHom A) := by
    haveI : Etale (S1733ModelOver A).left := het
    exact inferInstanceAs (Etale ((Scheme.isoSpec (S1733Model A).left).inv ≫
      (S1733ModelOver A).left))
  exact ⟨h1, h2⟩

/-- The object map from actual finite-etale covers to the S1733 affine
finite-etale slice: a cover is sent to the affine scheme Spec Γ(model A)
together with its finite-etale structure morphism to the base. -/
noncomputable def S1743Object (A : S1728Cover) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (S1743ModelHom A)
    (S1743ModelHom_finiteEtale A)

@[simp] theorem S1743Object_left (A : S1728Cover) :
    (S1743Object A).left = S1743ModelRing A := rfl

@[simp] theorem S1743Object_hom (A : S1728Cover) :
    (S1743Object A).hom = S1743ModelHom A := rfl

/-! ## 2. The identity-point two-pullback and its lift -/

/-- The two-commutative square of the identity-point base change. -/
noncomputable def S1743Square (A : S1728Cover) :
    EtalePseudofunctorSquare (S1743ModelStack A) (S1743Source A)
      (S1743Y S1726AffineOver) S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (S1743BaseChange A).toSource
    (S1743BaseChange A).projectionMap.transformation A.map S1733BasePoint
    (S1743BaseChange A).commutes

/-- The identity cone over that square: the cover maps to itself and to the base
by its own structure map. -/
noncomputable def S1743IdentityCone (A : S1728Cover) :
    (S1743Square A).Cone (S1743Source A) :=
  { toX := Pseudofunctor.StrongTrans.id (S1743Source A)
    toY := A.map
    commutes :=
      (Pseudofunctor.StrongTrans.leftUnitor A.map).trans
        (Pseudofunctor.StrongTrans.rightUnitor A.map).symm }

/-- The universal property of the identity-point two-pullback, applied to the
identity cone. -/
noncomputable def S1743Lift (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743Source A) (S1743ModelStack A) :=
  (S1743BaseChange A).isPullback.lift (S1743Source A) (S1743IdentityCone A)

/-- The model covers the source: the composite of the lift with the comparison is
2-isomorphic to the identity of the cover source stack.  This is the first half
of stack representability of the cover by its affine finite-etale model. -/
theorem S1743ModelSection (A : S1728Cover) :
    ∃ inv : Pseudofunctor.StrongTrans (S1743Source A) (S1743ModelStack A),
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp inv
        (S1743BaseChange A).toSource)
          (Pseudofunctor.StrongTrans.id (S1743Source A))) :=
  ⟨S1743Lift A,
    ⟨(S1743BaseChange A).isPullback.liftToX (S1743Source A)
      (S1743IdentityCone A)⟩⟩

/-- The lift also commutes with the projections to the base. -/
theorem S1743Lift_projection (A : S1728Cover) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
        (S1743BaseChange A).projectionMap.transformation)
      A.map) :=
  ⟨(S1743BaseChange A).isPullback.liftToY (S1743Source A) (S1743IdentityCone A)⟩

/-- Missing half of item (a).  For every cover, a strong transformation from the
source to the representable stack of its model whose composite with the
comparison in the other order is 2-isomorphic to the identity.  The composite
already proved in S1743ModelSection is the opposite one. -/
def S1743SourceRetraction : Prop :=
  ∀ A : S1728Cover,
    ∃ inv : Pseudofunctor.StrongTrans (S1743Source A) (S1743ModelStack A),
      Nonempty (Iso
        (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource inv)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))

/-- Full stack representability of a cover by its affine model, i.e. item (a). -/
def S1743SourceRepresentable (A : S1728Cover) : Prop :=
  ∃ inv : Pseudofunctor.StrongTrans (S1743Source A) (S1743ModelStack A),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp inv
        (S1743BaseChange A).toSource)
        (Pseudofunctor.StrongTrans.id (S1743Source A))) ∧
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
        (S1743BaseChange A).toSource inv)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))

/-- Item (a) for all covers. -/
def S1743SourceRepresentableAll : Prop := ∀ A : S1728Cover, S1743SourceRepresentable A

/-- Item (a) implies the missing retraction half. -/
theorem S1743SourceRetraction_of_representable
    (h : S1743SourceRepresentableAll) : S1743SourceRetraction := by
  intro A
  obtain ⟨inv, -, h2⟩ := h A
  exact ⟨inv, h2⟩
/-! ## 3. Item (c): the 2-Yoneda comparison for representable stacks (reusing S1742)

S1742 constructed both directions of the 2-Yoneda comparison for representable
etale pseudofunctors.  Its reverse direction S1742HomOfStrongTrans is literally
the evaluation at the identity used below, and its forward direction, its
formula S1742Key and both round trips are reused here to close item (c): the
structure SchemeRepresentableMap is constructed, the evaluation descends to
2-isomorphism classes, is compatible with vertical composition, is essentially
surjective, and the 2-isomorphism classes are equivalent to the scheme
morphisms. -/

/-- The 2-Yoneda evaluation of a strong transformation between representable
etale stacks: apply its component at S to the identity section of S. -/
noncomputable def S1743YonedaEval (S T : SchemeOverField S1726K)
    (L : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T)) : S ⟶ T :=
  ((L.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
    (Discrete.mk (𝟙 S))).as

/-- The evaluation is S1742's reverse direction of the 2-Yoneda comparison. -/
theorem S1743YonedaEval_eq_S1742 (S T : SchemeOverField S1726K)
    (L : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T)) :
    S1743YonedaEval S T L = S1742HomOfStrongTrans (F := S1726K) L := rfl

/-- Every scheme morphism induces a strong transformation of representable etale
stacks, exactly as in S1742. -/
noncomputable def S1743StrongTransOfHom {S T : SchemeOverField S1726K}
    (f : S ⟶ T) : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T) :=
  S1742StrongTransOfHom (F := S1726K) f

/-- The structure SchemeRepresentableMap, which S1726/S1733 use as an
assumption in every base-change presentation, is constructed for every scheme
morphism: S1742's transformation has exactly the required components. -/
noncomputable def S1743SchemeRepresentableMap {S T : SchemeOverField S1726K}
    (f : S ⟶ T) : SchemeRepresentableMap f where
  transformation := S1742StrongTransOfHom (F := S1726K) f
  app_eq := fun U => rfl

/-- S1742's key formula, restated for the S1743 abbreviations: every component of
a representable strong transformation is postcomposition with its evaluation. -/
theorem S1743YonedaEval_app (S T : SchemeOverField S1726K)
    (L : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T))
    (a : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (P : Opposite.unop a.as ⟶ S) :
    ((L.app a).toFunctor.obj (Discrete.mk P)).as = P ≫ S1743YonedaEval S T L :=
  S1742Key (F := S1726K) L a P

/-- A modification between strong transformations of representable etale stacks
does not change the 2-Yoneda evaluation: all components land in discrete
categories, so the modification's component at S has to be an identity arrow. -/
theorem S1743YonedaEval_congr (S T : SchemeOverField S1726K)
    {L L' : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T)} (φ : L ⟶ L') :
    S1743YonedaEval S T L = S1743YonedaEval S T L' :=
  Discrete.eq_of_hom
    ((φ.as.app (LocallyDiscrete.mk (Opposite.op S))).toNatTrans.app
      (Discrete.mk (𝟙 S)))

/-- The same statement on 2-isomorphism classes. -/
theorem S1743YonedaEval_congr_iso (S T : SchemeOverField S1726K)
    {L L' : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T)} (e : L ≅ L') :
    S1743YonedaEval S T L = S1743YonedaEval S T L' :=
  S1743YonedaEval_congr S T e.hom

/-- The 2-Yoneda evaluation is compatible with vertical composition of strong
transformations. -/
theorem S1743YonedaEval_vcomp (S T U : SchemeOverField S1726K)
    (L : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T))
    (L' : Pseudofunctor.StrongTrans (S1743Y T) (S1743Y U)) :
    S1743YonedaEval S U (Pseudofunctor.StrongTrans.vcomp L L') =
      S1743YonedaEval S T L ≫ S1743YonedaEval T U L' := by
  have happ : (Pseudofunctor.StrongTrans.vcomp L L').app
        (LocallyDiscrete.mk (Opposite.op S)) =
      L.app (LocallyDiscrete.mk (Opposite.op S)) ≫
        L'.app (LocallyDiscrete.mk (Opposite.op S)) :=
    Pseudofunctor.StrongTrans.comp_app L L' _
  have hkey := S1742Key (F := S1726K) L' (LocallyDiscrete.mk (Opposite.op S))
    (S1743YonedaEval S T L)
  have hobj : (L.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      (Discrete.mk (𝟙 S)) = Discrete.mk (S1743YonedaEval S T L) := Discrete.mk_as _
  simp only [S1743YonedaEval]
  rw [happ, Cat.Hom.comp_obj, hobj, hkey]
  rfl

/-- The 2-Yoneda evaluation as a functor from strong transformations between
representable etale stacks to the discrete category of scheme morphisms. -/
noncomputable def S1743YonedaFunctor (S T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T) ⥤ Discrete (S ⟶ T) where
  obj L := Discrete.mk (S1743YonedaEval S T L)
  map {_L _L'} φ := eqToHom (congrArg Discrete.mk (S1743YonedaEval_congr S T φ))
  map_id _ := Subsingleton.elim _ _
  map_comp {_ _ _} _ _ := Subsingleton.elim _ _

/-- The induced map on 2-isomorphism classes of strong transformations between
representable etale stacks: the 2-iso quotient maps to scheme morphisms. -/
noncomputable def S1743YonedaClassMap (S T : SchemeOverField S1726K) :
    Quot (fun L L' : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T) =>
      Nonempty (L ≅ L')) → (S ⟶ T) :=
  Quot.lift (S1743YonedaEval S T)
    (fun _ _ h => by
      rcases h with ⟨e⟩
      exact S1743YonedaEval_congr_iso S T e)

/-- The class map is the evaluation on representatives. -/
@[simp] theorem S1743YonedaClassMap_mk (S T : SchemeOverField S1726K)
    (L : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T)) :
    S1743YonedaClassMap S T (Quot.mk _ L) = S1743YonedaEval S T L := rfl

/-- Item (c), essential-surjectivity form: every strong transformation between
representable etale stacks is 2-isomorphic to the transformation induced by a
scheme morphism, namely by its own evaluation. -/
theorem S1743YonedaEssSurj (S T : SchemeOverField S1726K) :
    (S1743YonedaFunctor S T).EssSurj :=
  ⟨fun Y => ⟨S1742StrongTransOfHom (F := S1726K) Y.as,
    ⟨eqToIso (by
      show Discrete.mk (S1743YonedaEval S T (S1742StrongTransOfHom (F := S1726K) Y.as)) = Y
      rw [show S1743YonedaEval S T (S1742StrongTransOfHom (F := S1726K) Y.as) = Y.as from
        S1742HomOfStrongTrans_strongTransOfHom Y.as])⟩⟩⟩

/-- Item (c) in closed form.  The 2-isomorphism classes of strong transformations
between two representable etale stacks are equivalent, as a type, to the scheme
morphisms between them. -/
noncomputable def S1743YonedaClassEquiv (S T : SchemeOverField S1726K) :
    Quot (fun L L' : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T) =>
      Nonempty (L ≅ L')) ≃ (S ⟶ T) where
  toFun := S1743YonedaClassMap S T
  invFun f := Quot.mk _ (S1742StrongTransOfHom (F := S1726K) f)
  left_inv q := by
    induction q using Quot.inductionOn with
    | h L =>
      apply Quot.sound
      exact ⟨S1742StrongTransIsoOfHom (F := S1726K) L⟩
  right_inv f := by
    show S1743YonedaEval S T (S1742StrongTransOfHom (F := S1726K) f) = f
    exact S1742HomOfStrongTrans_strongTransOfHom f

/-! ## 4. The exact missing comparison -/

/-- The exact missing theorem.  A functor from the actual 2-iso cover category to
the S1733 affine finite-etale slice whose object map is the explicit model map
S1743Object, which is fully faithful and essentially surjective.

This is precisely item (b) together with the representability of the object map.
It is not constructed, and no inhabitant is asserted. -/
structure S1743CoverSliceComparison where
  /-- The comparison functor. -/
  functor : S1728Cover ⥤ S1733Slice
  /-- Its object map is the explicit affine model map. -/
  objIso : ∀ A : S1728Cover, Nonempty (functor.obj A ≅ S1743Object A)
  /-- Full and faithful. -/
  fullyFaithful : functor.FullyFaithful
  /-- Essentially surjective: every affine finite-etale scheme over the base is
  the model of a cover. -/
  essSurj : functor.EssSurj

/-- The missing comparison, as a proposition. -/
def S1743CoverSliceComparisonMissing : Prop := Nonempty S1743CoverSliceComparison

/-- The proposition equivalent to S1733's slice-equivalence target: a fully
faithful, essentially surjective functor from the actual cover category to the
affine finite-etale slice. -/
def S1743SliceFunctorMissing : Prop :=
  ∃ F : S1728Cover ⥤ S1733Slice, Nonempty F.FullyFaithful ∧ F.EssSurj

/-- A fully faithful essentially surjective functor is an equivalence. -/
theorem S1743IsEquivalence_of (F : S1728Cover ⥤ S1733Slice)
    (hff : F.FullyFaithful) (h : F.EssSurj) : F.IsEquivalence :=
  ⟨hff.faithful, hff.full, h⟩

/-- The comparison, as stated in S1733, is exactly the missing functor: a fully
faithful essentially surjective functor is the same datum as
S1733CoverSliceEquivalence. -/
theorem S1743SliceFunctorMissing_iff :
    S1743SliceFunctorMissing ↔ S1733CoverSliceEquivalence := by
  constructor
  · rintro ⟨F, ⟨hff⟩, h⟩
    haveI : F.IsEquivalence := S1743IsEquivalence_of F hff h
    exact ⟨F.asEquivalence⟩
  · rintro ⟨e⟩
    exact ⟨e.functor, ⟨e.fullyFaithfulFunctor⟩, inferInstance⟩

/-- The missing comparison yields S1733's slice equivalence. -/
theorem S1743CoverSliceEquivalence_of_comparison
    (d : S1743CoverSliceComparison) : S1733CoverSliceEquivalence := by
  haveI : d.functor.IsEquivalence :=
    S1743IsEquivalence_of d.functor d.fullyFaithful d.essSurj
  exact ⟨d.functor.asEquivalence⟩

/-- Consequently the actual cover category is essentially small, via S1733's
conditional theorem. -/
theorem S1743EssentiallySmall_of_comparison
    (d : S1743CoverSliceComparison) : EssentiallySmall.{0} S1728Cover :=
  S1733EssentiallySmall_of_sliceMissing (S1743CoverSliceEquivalence_of_comparison d)

/-- Consequently the actual cover type carries a genuine Category.{0,1}, via
S1733's conditional theorem.  Its hom types are the model homs, so identifying
them with the actual cover maps is the remaining comparison content. -/
theorem S1743Category01_of_comparison
    (d : S1743CoverSliceComparison) :
    Nonempty (Category.{0, 1} S1728Cover) :=
  S1733Category01_of_sliceMissing (S1743CoverSliceEquivalence_of_comparison d)

/-- The same conclusion from the S1733-shaped missing proposition. -/
theorem S1743EssentiallySmall_of_sliceMissing
    (h : S1733CoverSliceEquivalence) : EssentiallySmall.{0} S1728Cover :=
  S1733EssentiallySmall_of_sliceMissing h

/-! ## 5. What the object map alone gives -/

/-- The object map is injective on its data: two covers with the same slice
object have the same model ring. -/
theorem S1743Object_injective_on_data {A B : S1728Cover}
    (h : S1743Object A = S1743Object B) :
    S1743ModelRing A = S1743ModelRing B := by
  simpa using congrArg (fun x : S1733Slice => x.left) h

/-- The object map lands in affine finite-etale models. -/
theorem S1743Object_isAffineModel (A : S1728Cover) :
    IsAffine (S1733Model A).left ∧ S1733FiniteEtale (S1743ModelHom A) :=
  ⟨S1743Model_isAffine A, S1743ModelHom_finiteEtale A⟩

/-! ## 6. Checks -/

#check S1743Y
#check S1743BaseChange
#check S1743Model_isAffine
#check S1743ModelRing
#check S1743ModelHom
#check S1743ModelHom_finiteEtale
#check S1743Object
#check S1743Object_left
#check S1743Object_hom
#check S1743Square
#check S1743IdentityCone
#check S1743Lift
#check S1743ModelSection
#check S1743Lift_projection
#check S1743SourceRetraction
#check S1743SourceRepresentable
#check S1743SourceRepresentableAll
#check S1743SourceRetraction_of_representable
#check S1743YonedaEval
#check S1743YonedaEval_eq_S1742
#check S1743StrongTransOfHom
#check S1743SchemeRepresentableMap
#check S1743YonedaEval_app
#check S1743YonedaEval_congr
#check S1743YonedaEval_congr_iso
#check S1743YonedaEval_vcomp
#check S1743YonedaFunctor
#check S1743YonedaClassMap
#check S1743YonedaClassMap_mk
#check S1743YonedaEssSurj
#check S1743YonedaClassEquiv
#check S1743CoverSliceComparison
#check S1743CoverSliceComparisonMissing
#check S1743SliceFunctorMissing
#check S1743IsEquivalence_of
#check S1743SliceFunctorMissing_iff
#check S1743CoverSliceEquivalence_of_comparison
#check S1743EssentiallySmall_of_comparison
#check S1743Category01_of_comparison
#check S1743Object_injective_on_data
#check S1743Object_isAffineModel

#print axioms S1743Model_isAffine
#print axioms S1743ModelHom_finiteEtale
#print axioms S1743Object
#print axioms S1743ModelSection
#print axioms S1743Lift_projection
#print axioms S1743SchemeRepresentableMap
#print axioms S1743YonedaEval_app
#print axioms S1743YonedaEval_congr
#print axioms S1743YonedaEval_vcomp
#print axioms S1743YonedaEssSurj
#print axioms S1743YonedaClassEquiv
#print axioms S1743SliceFunctorMissing_iff
#print axioms S1743EssentiallySmall_of_comparison
#print axioms S1743Category01_of_comparison

end LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
