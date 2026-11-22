/-
# S1757: the actual functor from the 2-iso cover category to the affine finite-etale slice

## Question

S1743 constructed the object map S1743Object : S1728Cover -> S1733Slice (a
cover goes to the affine finite-etale model Spec Gamma(model A) of its
identity-point base change, with its finite-etale structure morphism) and, for
every cover A, the strong transformation
S1743Lift A : A.source ==> Y (S1733Model A) from the cover source to the
representable stack of its model, together with the 2-isomorphism
S1743ModelSection A : vcomp (Lift A) toSource ~ id (the cover is a retract of
its model).  S1743 left the comparison functor missing and recorded two gaps.
S1757 was asked to build the functor with the object map S1743Object, whose hom
map is the 2-Yoneda comparison S1743YonedaClassEquiv (2-iso classes of strong
transformations between representable stacks <-> scheme morphisms), and to
prove fully faithfulness and essential surjectivity, or to state the exact
first missing datum.

## Result

The hom-level comparison is *constructed unconditionally*:

* S1757HomEval A B f: for a cover map f : A -> B (a strong transformation
  f.map : A.source ==> B.source, i.e. an actual morphism of the two covers),
  the induced morphism of affine models S1733Model A -> S1733Model B, defined
  as the 2-Yoneda evaluation (S1743YonedaEval, the forward map of
  S1743YonedaClassEquiv) of the composite strong transformation
  toSource A ;; f.map ;; Lift B : Y (model A) ==> Y (model B).
  This is exactly the transfer of the S1742/S1743 2-Yoneda comparison across
  the model comparison that the S1743 report listed as missing.
* S1757HomEval_congr: it only depends on the 2-isomorphism class of f (a chain
  of associator/whiskering 2-isomorphisms plus S1743YonedaEval_congr_iso).
  Hence it descends to S1757Hom : (A --> B) -> (S1743Object A --> S1743Object B)
  on the hom types of the S1728 2-iso cover category.
* S1757YonedaEval_projectionMap / S1757HomEval_over_base: the induced model
  morphism is *over the base*: its composite with the structure morphism of the
  model of B is the structure morphism of the model of A.  This uses
  S1743Lift_projection, the cover map's own comparison 2-cell, and the
  two-pullback square of the identity-point base change.  Consequently
  S1757SliceHom produces an honest morphism of the affine finite-etale slice
  S1743Object A --> S1743Object B, by transporting through the affine
  identification Spec Gamma(model A) ~ model A.
* S1757Hom_comp: multiplicativity is proved unconditionally, using
  S1743ModelSection (the section 2-cell of the lift) and S1743YonedaEval_vcomp.
* S1757Hom_id: unitality holds as soon as the *other* composite
  vcomp (toSource A) (Lift A) ~ id is available, i.e. as soon as the lift is a
  section of the base-change comparison up to 2-isomorphism.

Hence, assuming this single missing 2-cell (S1757LiftSection), the functor
S1757Functor : S1728Cover -> S1733Slice with object map S1743Object is
constructed (S1757Functor_exists), and it is the functor that S1743 recorded
as missing.

## Exact missing

(1) S1757LiftSection: for every cover A,
    vcomp (toSource A) (Lift A) ~ id, a 2-isomorphism between endomorphisms of
    Y (S1733Model A).  Only the opposite composite is available
    (S1743ModelSection, from TwoPullbackWitness.liftToX).  The recorded witness
    supplies lift/liftToX/liftToY/liftTwoCell/twoCell_ext, but no inverse
    2-cell and no one-cell uniqueness, so the retraction half cannot be derived
    from it; this is exactly S1743 gap (a), now in the sharp form needed for
    the functor's unit law.  It implies S1743 SourceRetraction
    (S1757LiftSection.toRetraction).

(2) S1757EssSurjMissing: every affine finite-etale scheme over Spec R' (i.e.
    every object of the S1733 slice) is isomorphic to the model of an actual
    cover -- the paper's extension statement, the converse direction of
    S1743Object.  Nothing in the present definitions constructs covers from
    slice objects; this is geometric content, not a coherence question.

S1757SliceFunctorMissing_of records the precise reduction: (1) plus
faithfulness/fullness of the constructed functor plus (2) yield S1743
SliceFunctorMissing, hence S1733 CoverSliceEquivalence.

No sorry, no axiom, no Shrink/ULift/PUnit is used.  Only genuinely proved
statements are theorems; the two missing data are recorded as def ... : Prop and
are never inhabited.  The functor is *conditional* on (1); it is not claimed
unconditional.
-/

import tmp.sheaf.xif.paper.S1743CoverSliceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1757SliceFunctorActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual

/-! ## 1. The bicategory helpers for strong transformations of etale stacks

These are the associator, whiskering and unitor 2-isomorphisms of the
bicategory of etale-stack pseudofunctors, exposed with
Pseudofunctor.StrongTrans.vcomp in their statements so that they compose with
Iso.trans without typeclass friction. -/

/-- Associator for vertical composition of strong transformations. -/
noncomputable def S1757Assoc {X Y Z W : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans X Y) (g : Pseudofunctor.StrongTrans Y Z)
    (h : Pseudofunctor.StrongTrans Z W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp f g) h)
      (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.vcomp g h)) := by
  letI : Bicategory (EtaleStackPseudofunctor S1726K) := inferInstance
  exact @Bicategory.associator (EtaleStackPseudofunctor S1726K) _ X Y Z W f g h

/-- Left whiskering of strong transformations. -/
noncomputable def S1757WhiskerLeft {X Y Z : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans X Y) {g h : Pseudofunctor.StrongTrans Y Z}
    (e : Iso g h) :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f h) := by
  letI : Bicategory (EtaleStackPseudofunctor S1726K) := inferInstance
  exact @Bicategory.whiskerLeftIso (EtaleStackPseudofunctor S1726K) _ X Y Z f g h e

/-- Right whiskering of strong transformations. -/
noncomputable def S1757WhiskerRight {X Y Z : EtaleStackPseudofunctor S1726K}
    {f g : Pseudofunctor.StrongTrans X Y} (e : Iso f g)
    (h : Pseudofunctor.StrongTrans Y Z) :
    Iso (Pseudofunctor.StrongTrans.vcomp f h) (Pseudofunctor.StrongTrans.vcomp g h) := by
  letI : Bicategory (EtaleStackPseudofunctor S1726K) := inferInstance
  exact @Bicategory.whiskerRightIso (EtaleStackPseudofunctor S1726K) _ X Y Z f g e h

/-- Left unitor of vertical composition. -/
noncomputable def S1757LeftUnitor {X Y : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans X Y) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id X) f) f := by
  letI : Bicategory (EtaleStackPseudofunctor S1726K) := inferInstance
  exact @Bicategory.leftUnitor (EtaleStackPseudofunctor S1726K) _ X Y f

/-- Right unitor of vertical composition. -/
noncomputable def S1757RightUnitor {X Y : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans X Y) :
    Iso (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.id Y)) f := by
  letI : Bicategory (EtaleStackPseudofunctor S1726K) := inferInstance
  exact @Bicategory.rightUnitor (EtaleStackPseudofunctor S1726K) _ X Y f

/-! ## 2. The object map

The object map is S1743's: a cover goes to the affine finite-etale model of its
identity-point base change. -/

/-- The object map of the comparison functor. -/
noncomputable abbrev S1757Object (A : S1728Cover) : S1733Slice := S1743Object A

@[simp] theorem S1757Object_left (A : S1728Cover) :
    (S1757Object A).left = S1743ModelRing A := rfl

@[simp] theorem S1757Object_hom (A : S1728Cover) :
    (S1757Object A).hom = S1743ModelHom A := rfl

/-- The object map lands in affine finite-etale models (S1743). -/
theorem S1757Object_isAffineModel (A : S1728Cover) :
    IsAffine (S1733Model A).left ∧ S1733FiniteEtale (S1743ModelHom A) :=
  S1743Object_isAffineModel A

/-! ## 3. The exact missing 2-cell

This is the datum the construction below is conditional on.  It is never
inhabited here. -/

/-- The missing 2-cell: for every cover, the base-change comparison composed
with the lift of S1743 is 2-isomorphic to the identity of the representable
stack of the model.  This is the retraction direction of stack representability
of a cover by its affine model. -/
def S1757LiftSection : Prop :=
  ∀ A : S1728Cover,
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource (S1743Lift A))
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))

/-- The missing 2-cell implies S1743's retraction statement (with the lift as
the chosen transformation). -/
theorem S1757LiftSection.toRetraction (h : S1757LiftSection) : S1743SourceRetraction :=
  fun A => ⟨S1743Lift A, h A⟩

/-- The available direction (S1743), for reference. -/
noncomputable def S1757Lift_toSource {B : S1728Cover} :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1743Lift B) (S1743BaseChange B).toSource)
      (Pseudofunctor.StrongTrans.id (S1743Source B)) :=
  (S1743BaseChange B).isPullback.liftToX (S1743Source B) (S1743IdentityCone B)

/-! ## 4. The hom-level comparison: a cover map induces a morphism of models -/

/-- The model morphism induced by an actual cover map: the 2-Yoneda evaluation
of toSource ;; f.map ;; Lift. -/
noncomputable def S1757HomEval {A B : S1728Cover} (f : S1728CoverMap A B) :
    S1733Model A ⟶ S1733Model B :=
  S1743YonedaEval (S1733Model A) (S1733Model B)
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource f.map)
      (S1743Lift B))

/-- The induced model morphism only depends on the 2-isomorphism class of the
cover map. -/
theorem S1757HomEval_congr {A B : S1728Cover} {f g : S1728CoverMap A B}
    (h : S1728CoverMapRel f g) : S1757HomEval f = S1757HomEval g := by
  obtain ⟨e⟩ := h
  apply S1743YonedaEval_congr_iso
  exact (S1757Assoc (S1743BaseChange A).toSource f.map (S1743Lift B)).trans
    ((S1757WhiskerLeft (S1743BaseChange A).toSource
        (S1757WhiskerRight e (S1743Lift B))).trans
      (S1757Assoc (S1743BaseChange A).toSource g.map (S1743Lift B)).symm)

/-! ## 5. The induced model morphism is over the base -/

/-- The 2-Yoneda evaluation of the structure morphism of the model is that
morphism. -/
theorem S1757YonedaEval_projectionMap (A : S1728Cover) :
    (S1743YonedaEval (S1733Model A) S1726AffineOver
      ((S1743BaseChange A).projectionMap.transformation)).left
      = (S1733ModelOver A).left := by
  have h := (S1743BaseChange A).projectionMap.app_eq (Opposite.op (S1733Model A))
  have h2 : (S1743YonedaEval (S1733Model A) S1726AffineOver
      ((S1743BaseChange A).projectionMap.transformation))
      = (S1743BaseChange A).projection := by
    show (((S1743BaseChange A).projectionMap.transformation.app
      (LocallyDiscrete.mk (Opposite.op (S1733Model A)))).toFunctor.obj
        (Discrete.mk (𝟙 (S1733Model A)))).as = _
    rw [h]
    rfl
  exact congrArg Over.Hom.left h2

/-- The induced model morphism is over the base. -/
theorem S1757HomEval_over_base {A B : S1728Cover} (f : S1728CoverMap A B) :
    (S1757HomEval f).left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left := by
  obtain ⟨hLB⟩ := S1743Lift_projection B
  let projA : Pseudofunctor.StrongTrans (S1743Y (S1733Model A))
      (S1743Y S1726AffineOver) := (S1743BaseChange A).projectionMap.transformation
  let projB : Pseudofunctor.StrongTrans (S1743Y (S1733Model B))
      (S1743Y S1726AffineOver) := (S1743BaseChange B).projectionMap.transformation
  let L : Pseudofunctor.StrongTrans (S1743Y (S1733Model A)) (S1743Y (S1733Model B)) :=
    Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource f.map)
      (S1743Lift B)
  let EB := S1743YonedaEval (S1733Model B) S1726AffineOver projB
  have hLval : S1757HomEval f = S1743YonedaEval (S1733Model A) (S1733Model B) L := rfl
  have hchain : Iso (Pseudofunctor.StrongTrans.vcomp L projB) projA :=
    (S1757Assoc (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource f.map)
        (S1743Lift B) projB).trans
      ((S1757WhiskerLeft
          (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource f.map) hLB).trans
        ((S1757Assoc (S1743BaseChange A).toSource f.map B.map).trans
          ((S1757WhiskerLeft (S1743BaseChange A).toSource f.commutes).trans
            (((S1743BaseChange A).commutes).trans (S1757RightUnitor projA)))))
  have hv : S1743YonedaEval (S1733Model A) S1726AffineOver
      (Pseudofunctor.StrongTrans.vcomp L projB)
      = S1743YonedaEval (S1733Model A) (S1733Model B) L ≫ EB :=
    S1743YonedaEval_vcomp (S1733Model A) (S1733Model B) S1726AffineOver (L := L) (L' := projB)
  have hc : S1743YonedaEval (S1733Model A) S1726AffineOver
      (Pseudofunctor.StrongTrans.vcomp L projB)
      = S1743YonedaEval (S1733Model A) S1726AffineOver
        ((S1743BaseChange A).projectionMap.transformation) :=
    S1743YonedaEval_congr_iso (S1733Model A) S1726AffineOver hchain
  calc (S1757HomEval f).left ≫ (S1733ModelOver B).left
      = (S1743YonedaEval (S1733Model A) (S1733Model B) L).left ≫ (EB).left := by
        rw [hLval, ← S1757YonedaEval_projectionMap B]
    _ = (S1743YonedaEval (S1733Model A) (S1733Model B) L ≫ EB).left := by
        rw [Over.comp_left]
    _ = (S1743YonedaEval (S1733Model A) S1726AffineOver
          ((S1743BaseChange A).projectionMap.transformation)).left := by rw [← hv, hc]
    _ = (S1733ModelOver A).left := S1757YonedaEval_projectionMap A

/-! ## 6. The composition law of the hom-level comparison -/

/-- The hom-level comparison is multiplicative. -/
theorem S1757HomEval_comp {A B C : S1728Cover}
    (f : S1728CoverMap A B) (g : S1728CoverMap B C) :
    S1757HomEval (S1641CoverMapComp f g) = S1757HomEval f ≫ S1757HomEval g := by
  have hsecB := S1757Lift_toSource (B := B)
  let TA : Pseudofunctor.StrongTrans (S1743Y (S1733Model A)) A.source.fiber :=
    (S1743BaseChange A).toSource
  let TB : Pseudofunctor.StrongTrans (S1743Y (S1733Model B)) B.source.fiber :=
    (S1743BaseChange B).toSource
  let LB : Pseudofunctor.StrongTrans B.source.fiber (S1743Y (S1733Model B)) := S1743Lift B
  let LC : Pseudofunctor.StrongTrans C.source.fiber (S1743Y (S1733Model C)) := S1743Lift C
  let u : Pseudofunctor.StrongTrans (S1743Y (S1733Model A)) B.source.fiber :=
    Pseudofunctor.StrongTrans.vcomp TA f.map
  let v : Pseudofunctor.StrongTrans (S1743Y (S1733Model B)) C.source.fiber :=
    Pseudofunctor.StrongTrans.vcomp TB g.map
  have hLBv : Iso (Pseudofunctor.StrongTrans.vcomp LB v) g.map :=
    (S1757Assoc LB TB g.map).symm.trans
      ((S1757WhiskerRight hsecB g.map).trans (S1757LeftUnitor g.map))
  have hchain : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp u LB)
        (Pseudofunctor.StrongTrans.vcomp v LC))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp TA
          (Pseudofunctor.StrongTrans.vcomp f.map g.map)) LC) :=
    (S1757Assoc u LB (Pseudofunctor.StrongTrans.vcomp v LC)).trans
      ((S1757WhiskerLeft u
          ((S1757Assoc LB v LC).symm.trans (S1757WhiskerRight hLBv LC))).trans
        ((S1757Assoc u g.map LC).symm.trans
          (S1757WhiskerRight (S1757Assoc TA f.map g.map) LC)))
  have hv := S1743YonedaEval_vcomp (S1733Model A) (S1733Model B) (S1733Model C)
    (L := Pseudofunctor.StrongTrans.vcomp u LB)
    (L' := Pseudofunctor.StrongTrans.vcomp v LC)
  have hc := S1743YonedaEval_congr_iso (S1733Model A) (S1733Model C) hchain
  have hL : S1757HomEval (S1641CoverMapComp f g)
      = S1743YonedaEval (S1733Model A) (S1733Model C)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp TA
            (Pseudofunctor.StrongTrans.vcomp f.map g.map)) LC) := rfl
  have hR : S1757HomEval f ≫ S1757HomEval g
      = S1743YonedaEval (S1733Model A) (S1733Model B)
          (Pseudofunctor.StrongTrans.vcomp u LB) ≫
        S1743YonedaEval (S1733Model B) (S1733Model C)
          (Pseudofunctor.StrongTrans.vcomp v LC) := rfl
  rw [hL, hR, ← hv, hc]

/-- The 2-Yoneda evaluation of the identity transformation of a representable
stack is the identity morphism. -/
theorem S1757YonedaEval_id (P : SchemeOverField S1726K) :
    S1743YonedaEval P P (Pseudofunctor.StrongTrans.id (S1743Y P)) = 𝟙 P := rfl

/-- Under the missing section 2-cell, the hom-level comparison sends the
identity cover map to the identity model morphism. -/
theorem S1757HomEval_id (h : S1757LiftSection) (A : S1728Cover) :
    S1757HomEval (S1641CoverMapId A) = 𝟙 (S1733Model A) := by
  obtain ⟨hA⟩ := h A
  have hchain : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource
          (S1641CoverMapId A).map) (S1743Lift A))
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) := by
    have hr : Iso (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource
        (S1641CoverMapId A).map) (S1743BaseChange A).toSource :=
      S1757RightUnitor (S1743BaseChange A).toSource
    exact (S1757WhiskerRight hr (S1743Lift A)).trans hA
  have hc := S1743YonedaEval_congr_iso (S1733Model A) (S1733Model A) hchain
  calc S1757HomEval (S1641CoverMapId A)
      = S1743YonedaEval (S1733Model A) (S1733Model A)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S1743BaseChange A).toSource
            (S1641CoverMapId A).map) (S1743Lift A)) := rfl
    _ = S1743YonedaEval (S1733Model A) (S1733Model A)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) := hc
    _ = 𝟙 (S1733Model A) := S1757YonedaEval_id (S1733Model A)

/-! ## 7. Slice morphisms from model morphisms over the base -/

/-- The canonical affine identification of a model with the spectrum of its
ring, with the instance argument fixed so that it can be used uniformly. -/
noncomputable def S1757ModelIso (A : S1728Cover) :
    (S1733Model A).left ≅ Scheme.Spec.obj (S1743ModelRing A) :=
  @Scheme.isoSpec ((S1733Model A).left) (S1743Model_isAffine A)

/-- The structure morphism of the model, written through that identification. -/
theorem S1757ModelHom_eq (A : S1728Cover) :
    S1743ModelHom A = (S1757ModelIso A).inv ≫ (S1733ModelOver A).left := rfl

/-- The affine transport of a model morphism. -/
noncomputable def S1757Phi {A B : S1728Cover} (e : S1733Model A ⟶ S1733Model B) :
    Scheme.Spec.obj (S1743ModelRing A) ⟶ Scheme.Spec.obj (S1743ModelRing B) :=
  (S1757ModelIso A).inv ≫ e.left ≫ (S1757ModelIso B).hom

/-- The affine transport is compatible with composition of model morphisms. -/
theorem S1757Phi_comp {A B C : S1728Cover}
    (e₁ : S1733Model A ⟶ S1733Model B) (e₂ : S1733Model B ⟶ S1733Model C) :
    S1757Phi (e₁ ≫ e₂) = S1757Phi e₁ ≫ S1757Phi e₂ := by
  simp only [S1757Phi, Over.comp_left, Category.assoc, Iso.hom_inv_id_assoc]

/-- A model morphism which is over the base induces a morphism of the affine
finite-etale slice between the two objects of the comparison. -/
noncomputable def S1757SliceHom {A B : S1728Cover} (e : S1733Model A ⟶ S1733Model B)
    (hbase : e.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left) :
    S1743Object A ⟶ S1743Object B :=
  MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (Scheme.Spec.preimage (S1757Phi e))
    (by trivial) (by
      show Scheme.Spec.map (Scheme.Spec.preimage (S1757Phi e)) ≫ S1743ModelHom B
        = S1743ModelHom A
      rw [Scheme.Spec.map_preimage, S1757ModelHom_eq, S1757ModelHom_eq]
      show S1757Phi e ≫ (S1757ModelIso B).inv ≫ (S1733ModelOver B).left
        = (S1757ModelIso A).inv ≫ (S1733ModelOver A).left
      simp only [S1757Phi, Category.assoc, Iso.hom_inv_id_assoc, hbase])

@[simp] theorem S1757SliceHom_left {A B : S1728Cover} (e : S1733Model A ⟶ S1733Model B)
    (hbase : e.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left) :
    (S1757SliceHom e hbase).left = Scheme.Spec.preimage (S1757Phi e) := rfl

/-- Equal model morphisms give equal slice morphisms. -/
theorem S1757SliceHom_congr {A B : S1728Cover} {e e' : S1733Model A ⟶ S1733Model B}
    (h : e = e')
    (hbase : e.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left)
    (hbase' : e'.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left) :
    S1757SliceHom e hbase = S1757SliceHom e' hbase' := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  show Scheme.Spec.preimage (S1757Phi e) = Scheme.Spec.preimage (S1757Phi e')
  rw [h]

/-- The slice morphism of a composite of model morphisms is the composite of the
slice morphisms. -/
theorem S1757SliceHom_comp {A B C : S1728Cover}
    (e₁ : S1733Model A ⟶ S1733Model B) (e₂ : S1733Model B ⟶ S1733Model C)
    (h1 : e₁.left ≫ (S1733ModelOver B).left = (S1733ModelOver A).left)
    (h2 : e₂.left ≫ (S1733ModelOver C).left = (S1733ModelOver B).left)
    (h12 : (e₁ ≫ e₂).left ≫ (S1733ModelOver C).left = (S1733ModelOver A).left) :
    S1757SliceHom e₁ h1 ≫ S1757SliceHom e₂ h2 = S1757SliceHom (e₁ ≫ e₂) h12 := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  show Scheme.Spec.preimage (S1757Phi e₁) ≫ Scheme.Spec.preimage (S1757Phi e₂)
    = Scheme.Spec.preimage (S1757Phi (e₁ ≫ e₂))
  refine Scheme.Spec.map_injective ?_
  rw [Functor.map_comp, Scheme.Spec.map_preimage, Scheme.Spec.map_preimage,
    Scheme.Spec.map_preimage, S1757Phi_comp]

/-- The affine transport of the identity model morphism is the identity. -/
theorem S1757Phi_one (A : S1728Cover) :
    S1757Phi (𝟙 (S1733Model A)) = 𝟙 (Scheme.Spec.obj (S1743ModelRing A)) := by
  show (S1757ModelIso A).inv ≫ Over.Hom.left (𝟙 (S1733Model A)) ≫ (S1757ModelIso A).hom
    = 𝟙 (Scheme.Spec.obj (S1743ModelRing A))
  rw [Over.id_left, Category.id_comp, Iso.inv_hom_id]

/-- The identity model morphism gives the identity slice morphism. -/
theorem S1757SliceHom_one (A : S1728Cover) :
    S1757SliceHom (𝟙 (S1733Model A)) (by
      show Over.Hom.left (𝟙 (S1733Model A)) ≫ (S1733ModelOver A).left
        = (S1733ModelOver A).left
      rw [Over.id_left, Category.id_comp]) = 𝟙 (S1743Object A) := by
  have hidleft : (MorphismProperty.Comma.id (S1743Object A)).left
      = 𝟙 (S1743ModelRing A) :=
    MorphismProperty.Comma.id_left (S1743Object A)
  apply MorphismProperty.CostructuredArrow.Hom.ext
  show Scheme.Spec.preimage (S1757Phi (𝟙 (S1733Model A)))
    = (MorphismProperty.Comma.id (S1743Object A)).left
  rw [hidleft]
  refine Scheme.Spec.map_injective ?_
  rw [Scheme.Spec.map_preimage, S1757Phi_one, Scheme.Spec.map_id]

/-! ## 8. The hom map on 2-isomorphism classes -/

/-- The hom map of the comparison: a 2-isomorphism class of cover maps is sent
to the slice morphism between the affine models. -/
noncomputable def S1757Hom (A B : S1728Cover) :
    (A ⟶ B) → (S1743Object A ⟶ S1743Object B) :=
  Quot.lift (fun f => S1757SliceHom (S1757HomEval f) (S1757HomEval_over_base f))
    (by
      intro f g hrel
      exact S1757SliceHom_congr (S1757HomEval_congr hrel) _ _)

/-- The hom map is multiplicative. -/
theorem S1757Hom_comp {A B C : S1728Cover} (f : A ⟶ B) (g : B ⟶ C) :
    S1757Hom A C (f ≫ g) = S1757Hom A B f ≫ S1757Hom B C g := by
  induction f using Quot.inductionOn with
  | h f =>
    induction g using Quot.inductionOn with
    | h g =>
      change S1757SliceHom (S1757HomEval (S1641CoverMapComp f g))
          (S1757HomEval_over_base (S1641CoverMapComp f g))
        = S1757SliceHom (S1757HomEval f) (S1757HomEval_over_base f)
          ≫ S1757SliceHom (S1757HomEval g) (S1757HomEval_over_base g)
      have h12 : (S1757HomEval f ≫ S1757HomEval g).left ≫ (S1733ModelOver C).left
          = (S1733ModelOver A).left := by
        rw [Over.comp_left, Category.assoc, S1757HomEval_over_base g,
          S1757HomEval_over_base f]
      exact (S1757SliceHom_congr (S1757HomEval_comp f g)
          (S1757HomEval_over_base (S1641CoverMapComp f g)) h12).trans
        (S1757SliceHom_comp (S1757HomEval f) (S1757HomEval g)
          (S1757HomEval_over_base f) (S1757HomEval_over_base g) h12).symm

/-- The hom map is unital under the missing section 2-cell. -/
theorem S1757Hom_id (h : S1757LiftSection) (A : S1728Cover) :
    S1757Hom A A (𝟙 A) = 𝟙 (S1743Object A) := by
  change S1757SliceHom (S1757HomEval (S1641CoverMapId A))
    (S1757HomEval_over_base (S1641CoverMapId A)) = 𝟙 (S1743Object A)
  exact (S1757SliceHom_congr (S1757HomEval_id h A)
    (S1757HomEval_over_base (S1641CoverMapId A)) _).trans (S1757SliceHom_one A)

/-! ## 9. The comparison functor -/

/-- The comparison functor S1728Cover -> S1733Slice with object map
S1743Object, under the missing section 2-cell. -/
noncomputable def S1757Functor (h : S1757LiftSection) : S1728Cover ⥤ S1733Slice where
  obj := S1743Object
  map := fun {A B} f => S1757Hom A B f
  map_id A := S1757Hom_id h A
  map_comp f g := S1757Hom_comp f g

/-- The functor has the prescribed object map. -/
theorem S1757Functor_obj (h : S1757LiftSection) (A : S1728Cover) :
    (S1757Functor h).obj A = S1743Object A := rfl

/-- Hence, under the missing 2-cell, a functor with the prescribed object map
exists.  Comparing with S1743: this is exactly the functor S1743 recorded as
missing, with its object map fixed definitionally. -/
theorem S1757Functor_exists (h : S1757LiftSection) :
    ∃ F : S1728Cover ⥤ S1733Slice,
      ∀ A : S1728Cover, Nonempty (F.obj A ≅ S1743Object A) :=
  ⟨S1757Functor h, fun A => ⟨Iso.refl (S1743Object A)⟩⟩

/-- Everything except the unit law is available unconditionally: a
multiplicative, object-fixing family of slice morphisms. -/
structure S1757SemifunctorData where
  /-- The object-fixing hom map. -/
  map : ∀ {A B : S1728Cover}, (A ⟶ B) → (S1743Object A ⟶ S1743Object B)
  /-- Multiplicativity. -/
  map_comp : ∀ {A B C : S1728Cover} (f : A ⟶ B) (g : B ⟶ C),
    map (f ≫ g) = map f ≫ map g

/-- The actual semifunctor data, constructed without any hypothesis. -/
noncomputable def S1757SemifunctorDataActual : S1757SemifunctorData where
  map := fun {A B} f => S1757Hom A B f
  map_comp := fun f g => S1757Hom_comp f g

/-! ## 10. The exact remaining gaps and the reduction -/

/-- The missing essential surjectivity: every affine finite-etale scheme over
Spec R' (every object of the S1733 slice) is the affine model of an actual
cover.  This is the paper's extension statement. -/
def S1757EssSurjMissing : Prop :=
  ∀ X : S1733Slice, ∃ A : S1728Cover, Nonempty (S1743Object A ≅ X)

/-- The missing extension statement gives essential surjectivity of the
constructed functor. -/
theorem S1757EssSurj_of (h : S1757LiftSection) (he : S1757EssSurjMissing) :
    (S1757Functor h).EssSurj :=
  ⟨fun X => he X⟩

/-- The precise reduction: the missing 2-cell, full faithfulness of the
constructed functor, and the missing extension statement yield S1743's exact
missing slice functor. -/
theorem S1757SliceFunctorMissing_of (h : S1757LiftSection)
    (hff : (S1757Functor h).FullyFaithful) (he : S1757EssSurjMissing) :
    S1743SliceFunctorMissing :=
  ⟨S1757Functor h, ⟨hff⟩, S1757EssSurj_of h he⟩

/-- Consequently S1733's slice equivalence follows. -/
theorem S1757CoverSliceEquivalence_of (h : S1757LiftSection)
    (hff : (S1757Functor h).FullyFaithful) (he : S1757EssSurjMissing) :
    S1733CoverSliceEquivalence :=
  S1743SliceFunctorMissing_iff.mp (S1757SliceFunctorMissing_of h hff he)

/-- Consequently the actual cover category is essentially small. -/
theorem S1757EssentiallySmall_of (h : S1757LiftSection)
    (hff : (S1757Functor h).FullyFaithful) (he : S1757EssSurjMissing) :
    EssentiallySmall.{0} S1728Cover :=
  S1733EssentiallySmall_of_sliceMissing (S1757CoverSliceEquivalence_of h hff he)

/-- Consequently the actual cover type carries a genuine Category.{0,1}. -/
theorem S1757Category01_of (h : S1757LiftSection)
    (hff : (S1757Functor h).FullyFaithful) (he : S1757EssSurjMissing) :
    Nonempty (Category.{0, 1} S1728Cover) :=
  S1733Category01_of_sliceMissing (S1757CoverSliceEquivalence_of h hff he)

/-! ## 11. Checks -/

#check S1757Object
#check S1757LiftSection
#check S1757LiftSection.toRetraction
#check S1757Lift_toSource
#check S1757HomEval
#check S1757HomEval_congr
#check S1757YonedaEval_projectionMap
#check S1757HomEval_over_base
#check S1757HomEval_comp
#check S1757HomEval_id
#check S1757ModelIso
#check S1757SliceHom
#check S1757SliceHom_comp
#check S1757SliceHom_one
#check S1757Hom
#check S1757Hom_comp
#check S1757Hom_id
#check S1757Functor
#check S1757Functor_obj
#check S1757Functor_exists
#check S1757SemifunctorData
#check S1757SemifunctorDataActual
#check S1757EssSurjMissing
#check S1757EssSurj_of
#check S1757SliceFunctorMissing_of
#check S1757CoverSliceEquivalence_of
#check S1757EssentiallySmall_of
#check S1757Category01_of

#print axioms S1757HomEval_congr
#print axioms S1757YonedaEval_projectionMap
#print axioms S1757HomEval_over_base
#print axioms S1757HomEval_comp
#print axioms S1757HomEval_id
#print axioms S1757SliceHom_comp
#print axioms S1757SliceHom_one
#print axioms S1757Hom_comp
#print axioms S1757Hom_id
#print axioms S1757Functor_exists
#print axioms S1757SemifunctorDataActual
#print axioms S1757EssSurj_of
#print axioms S1757SliceFunctorMissing_of
#print axioms S1757EssentiallySmall_of

end LeanFormal.IUT.XiFPaper.S1757SliceFunctorActual
