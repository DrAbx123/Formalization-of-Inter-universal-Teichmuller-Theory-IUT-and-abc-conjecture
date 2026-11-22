/-
# S1756: representability of the source stack of a finite etale cover

## Question

For `A : S1728Cover = OrbicurveFiniteEtaleCover S1726Orbicurve` the cover datum is

* `A.source : EtaleStackOverField F'` (a category-valued etale stack),
* `A.map : A.source.Hom S1726Orbicurve.stack.fiber`, finite etale in the
  representable sense: for every test scheme `T` and every point
  `point : h_T ⟶ S1726Orbicurve.stack`, `A.finiteEtale.baseChange T point`
  supplies a scheme `pullbackScheme`, a map `projection : pullbackScheme ⟶ T`,
  a 1-cell `toSource : h_pullbackScheme ⟶ A.source`, a 2-commuting square and
  a two-pullback universal property.

Can one construct an affine scheme `S_A` over `Spec R'` with an equivalence
`S_A.stack ≅ A.source`, or does `baseChange` at the identity point of the
(representable, S1726) base already give global representability?

## What is proved here, unconditionally

* `S1756AffineModelDataActual`: for every cover, the identity-point base change
  produces an affine scheme `S1733Model A` over `Spec R'` with finite etale
  structure morphism `S1733ModelOver A`.  This is exactly the object half of
  S1733's `S1733AffineCoverModel`; only its `homEquiv` field is not supplied.

* `S1756ToSource`, `S1756ProjectionMap`, `S1743Lift`: the comparison 1-cell
  `h_{S_A} ⟶ A.source`, the projection 1-cell `h_{S_A} ⟶ h_{Spec R'}`, and a
  lift `A.source ⟶ h_{S_A}` with `lift ≫ toSource ≅ 𝟙` (the counit).
  This is one triangle of an equivalence, and it is unconditional.

* `S1756End`: the resulting self-endomorphism of the model,
  `S1756End A = eval (toSource ≫ lift)`, where `eval` is the 2-Yoneda
  evaluation of S1742/S1743.  It is an endomorphism *over the base*
  (`S1756End_projection`) and it is idempotent (`S1756End_idempotent`), so the
  missing statement is exactly "this idempotent endomorphism is the identity".

* `S1756IsoIffEval`: 2-Yoneda in the sharp form used below: two strong
  transformations between representable etale stacks are 2-isomorphic iff they
  have the same evaluation.  No quotient is involved.

* `S1756End_eq_one_of_retraction` and `S1756Retraction_iff_firstMissing`: the
  existence of *any* one-sided inverse `inv` of `toSource` forces the canonical
  self-endomorphism to be the identity.  The proof is bicategorical
  cancellation: from `u ≫ t ≅ 𝟙` and `t ≫ inv �≅ 𝟙` one gets `t ≫ u ≅ 𝟙`
  (`S1756_unit_iso`).

## The precise first missing statement

`S1756FirstMissing : Prop := ∀ A : S1728Cover, S1756End A = 𝟙 (S1733Model A)`.

It is equivalent (`S1756Unit_iff_end`) to the existence of the missing unit
2-cell `toSource ≫ lift ≅ 𝟙`, i.e. to the second triangle of the equivalence;
and it is equivalent (`S1756Retraction_iff_firstMissing`) to S1743's
`S1743SourceRetraction`.  Given it, `S1756SourceRepresentable_of_end`
produces an actual quasi-equivalence `h_{S_A} ≃ A.source`
(`S1756StackEquiv`), hence representability of the cover source by the affine
finite etale scheme `S_A`.

Thus the whole remaining content of "the cover source is representable by its
affine base-change model" is the single scheme-level equation
`S1756End A = 𝟙`.  This is precisely the 2-categorical statement that the
pullback of `A.map` along the identity 1-cell `𝟙 (h_{Spec R'})` is the source
itself (descent / 2-Yoneda for the non-representable source).  S1742's
2-Yoneda comparison does not apply: it compares strong transformations between
two *representable* stacks, while `A.source` is an arbitrary etale stack and is
not known to be representable before this very statement is proved.

## Refutation / non-refutation

* The claim is not refuted, and no counterexample is constructed; on the
  contrary, `S1756End_eq_one_of_mono` shows that whenever the structure
  morphism `S_A ⟶ Spec R'` is a monomorphism the missing equation holds, so a
  counterexample would need a non-monomorphic finite etale structure morphism.
* The claim is *not* proved either: the available `TwoPullbackWitness` supplies
  the lift, the two comparison 2-cells, the action on cone morphisms and
  2-cell extensionality, but no 2-cell `toSource ≫ lift ≅ 𝟙`, and the existing
  data only pin the self-map down up to the equation `S1756End A ≫ p = p`.
  Adding that unit 2-cell (or the equivalent scheme-level equation) to the
  base-change presentation is exactly the missing input.  No fake equivalence
  is introduced: `S1756SourceRepresentable` is a proposition about a genuine
  `Pseudofunctor.StrongTrans`-based quasi-equivalence, and it is not
  inhabited by this file.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the `#print axioms`
block at the end.  No `sorry`, no new axiom, no `Shrink`, `ULift` or `PUnit`.
-/

import tmp.sheaf.xif.paper.S1743CoverSliceActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual

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

/-! ## 1. The affine finite-etale model, unconditionally -/

/-- The object half of S1733's `S1733AffineCoverModel`: an affine finite etale
scheme over `Spec R'` for every cover, with no hom comparison. -/
structure S1756AffineModelData where
  /-- The affine model of a cover. -/
  model : S1728Cover → SchemeOverField S1726K
  /-- Its structure morphism to the base. -/
  toBase : ∀ A, model A ⟶ S1726AffineOver
  /-- The model is affine. -/
  isAffine : ∀ A, IsAffine (model A).left
  /-- The structure morphism is finite. -/
  isFinite : ∀ A, IsFinite (toBase A).left
  /-- The structure morphism is etale. -/
  isEtale : ∀ A, Etale (toBase A).left

/-- The identity-point base-change model supplies every object-level field of
S1733's missing affine cover model. -/
noncomputable def S1756AffineModelDataActual : S1756AffineModelData where
  model := S1733Model
  toBase := S1733ModelOver
  isAffine := S1743Model_isAffine
  isFinite := fun A => (S1733Model_finiteEtale A).1
  isEtale := fun A => (S1733Model_finiteEtale A).2

/-! ## 2. The 1-cells of the identity-point base change -/

/-- The comparison 1-cell `h_{S_A} ⟶ A.source`, with the model written through
`S1733Model A` so that all following composites are syntactically aligned. -/
noncomputable def S1756ToSource (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743Source A) :=
  (S1743BaseChange A).toSource

/-- The projection 1-cell `h_{S_A} ⟶ h_{Spec R'}` of the base change. -/
noncomputable def S1756ProjectionMap (A : S1728Cover) :
    Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743Y S1726AffineOver) :=
  (S1743BaseChange A).projectionMap.transformation

/-- The structure morphism of the affine model to the base, written through
`S1733Model A` so that it composes syntactically with the self-endomorphism. -/
noncomputable def S1756Projection (A : S1728Cover) : S1733Model A ⟶ S1726AffineOver :=
  (S1743BaseChange A).projection

/-! ## 3. Bicategorical 2-isomorphism calculus -/

/-- Left whiskering of a 2-isomorphism of strong transformations. -/
noncomputable def S1756WhiskerLeftIso {A B C : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans A B) (g g' : Pseudofunctor.StrongTrans B C)
    (e : Iso g g') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f g') := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid : Bicat := B
  let target : Bicat := C
  let fmap : source ⟶ mid := f
  let gmap : mid ⟶ target := g
  let gmap' : mid ⟶ target := g'
  exact @Bicategory.whiskerLeftIso Bicat _ source mid target fmap gmap gmap' e

/-- Right whiskering of a 2-isomorphism of strong transformations. -/
noncomputable def S1756WhiskerRightIso {A B C : EtaleStackPseudofunctor S1726K}
    (f f' : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (e : Iso f f') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f' g) := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid : Bicat := B
  let target : Bicat := C
  let fmap : source ⟶ mid := f
  let fmap' : source ⟶ mid := f'
  let gmap : mid ⟶ target := g
  exact @Bicategory.whiskerRightIso Bicat _ source mid target fmap fmap' e gmap

/-- The associator 2-isomorphism of vertical composition. -/
noncomputable def S1756AssociatorIso {A B C D : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (h : Pseudofunctor.StrongTrans C D) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp f g) h)
      (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.vcomp g h)) := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid1 : Bicat := B
  let mid2 : Bicat := C
  let target : Bicat := D
  let fmap : source ⟶ mid1 := f
  let gmap : mid1 ⟶ mid2 := g
  let hmap : mid2 ⟶ target := h
  exact @Bicategory.associator Bicat _ source mid1 mid2 target fmap gmap hmap

/-- The left unitor 2-isomorphism. -/
noncomputable def S1756LeftUnitorIso {A B : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans A B) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id A) f) f := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  exact @Bicategory.leftUnitor Bicat _ source target fmap

/-- The right unitor 2-isomorphism. -/
noncomputable def S1756RightUnitorIso {A B : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans A B) :
    Iso (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.id B)) f := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  exact @Bicategory.rightUnitor Bicat _ source target fmap

/-- Bicategorical cancellation: if `u` is a right inverse of `t` and some `inv`
is a left inverse of `t`, then `t ≫ u` is 2-isomorphic to the identity. -/
noncomputable def S1756_unit_iso {P Q : EtaleStackPseudofunctor S1726K}
    (t : Pseudofunctor.StrongTrans P Q) (u : Pseudofunctor.StrongTrans Q P)
    (inv : Pseudofunctor.StrongTrans Q P)
    (hu : Iso (Pseudofunctor.StrongTrans.vcomp u t) (Pseudofunctor.StrongTrans.id Q))
    (hinv : Iso (Pseudofunctor.StrongTrans.vcomp t inv) (Pseudofunctor.StrongTrans.id P)) :
    Iso (Pseudofunctor.StrongTrans.vcomp t u) (Pseudofunctor.StrongTrans.id P) := by
  have h1 : Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp t u) (Pseudofunctor.StrongTrans.vcomp t inv))
      (Pseudofunctor.StrongTrans.vcomp t
        (Pseudofunctor.StrongTrans.vcomp u (Pseudofunctor.StrongTrans.vcomp t inv))) :=
    S1756AssociatorIso t u (Pseudofunctor.StrongTrans.vcomp t inv)
  have h2 : Iso (Pseudofunctor.StrongTrans.vcomp t
      (Pseudofunctor.StrongTrans.vcomp u (Pseudofunctor.StrongTrans.vcomp t inv)))
      (Pseudofunctor.StrongTrans.vcomp t
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp u t) inv)) :=
    S1756WhiskerLeftIso t _ _ (S1756AssociatorIso u t inv).symm
  have h3 : Iso (Pseudofunctor.StrongTrans.vcomp t
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp u t) inv))
      (Pseudofunctor.StrongTrans.vcomp t
        (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id Q) inv)) :=
    S1756WhiskerLeftIso t _ _ (S1756WhiskerRightIso _ _ inv hu)
  have h4 : Iso (Pseudofunctor.StrongTrans.vcomp t
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id Q) inv))
      (Pseudofunctor.StrongTrans.vcomp t inv) :=
    S1756WhiskerLeftIso t _ _ (S1756LeftUnitorIso inv)
  have hA : Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp t u) (Pseudofunctor.StrongTrans.vcomp t inv))
      (Pseudofunctor.StrongTrans.id P) :=
    h1.trans (h2.trans (h3.trans (h4.trans hinv)))
  have h5 : Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp t u) (Pseudofunctor.StrongTrans.vcomp t inv))
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp t u)
        (Pseudofunctor.StrongTrans.id P)) :=
    S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp t u) _ _ hinv
  have h6 : Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp t u)
      (Pseudofunctor.StrongTrans.id P)) (Pseudofunctor.StrongTrans.vcomp t u) :=
    S1756RightUnitorIso (Pseudofunctor.StrongTrans.vcomp t u)
  exact (h5.trans h6).symm.trans hA

/-! ## 4. 2-Yoneda evaluation: identities and the projection -/

/-- The 2-Yoneda evaluation of the identity strong transformation is the
identity morphism of the representing scheme. -/
theorem S1756YonedaEval_id (S : SchemeOverField S1726K) :
    S1743YonedaEval S S (Pseudofunctor.StrongTrans.id (S1743Y S)) = 𝟙 S := by
  show (((Pseudofunctor.StrongTrans.id (S1743Y S)).app
    (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj (Discrete.mk (𝟙 S))).as = 𝟙 S
  rw [show (Pseudofunctor.StrongTrans.id (S1743Y S)).app
    (LocallyDiscrete.mk (Opposite.op S)) =
      𝟙 ((S1743Y S).obj (LocallyDiscrete.mk (Opposite.op S))) from rfl]
  rw [Cat.Hom.id_toFunctor]
  rfl

/-- The 2-Yoneda evaluation of a representable strong transformation is its
scheme morphism. -/
theorem S1756YonedaEval_projectionMap (A : S1728Cover) :
    S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) =
      S1756Projection A := by
  show ((((S1743BaseChange A).projectionMap.transformation).app
    (LocallyDiscrete.mk (Opposite.op (S1733Model A)))).toFunctor.obj
      (Discrete.mk (𝟙 (S1733Model A)))).as = (S1743BaseChange A).projection
  rw [(S1743BaseChange A).projectionMap.app_eq (Opposite.op (S1733Model A))]
  rfl

/-- 2-Yoneda, forward direction: equal evaluations of strong transformations
between representable etale stacks give a 2-isomorphism. -/
theorem S1756IsoOfEvalEq (S T : SchemeOverField S1726K)
    (L L' : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T))
    (h : S1743YonedaEval S T L = S1743YonedaEval S T L') : Nonempty (L ≅ L') := by
  have h' : S1742HomOfStrongTrans (F := S1726K) L = S1742HomOfStrongTrans (F := S1726K) L' := by
    simpa only [S1743YonedaEval_eq_S1742] using h
  exact ⟨(S1742StrongTransIsoOfHom (F := S1726K) L).symm.trans
    ((eqToIso (congrArg (fun f => S1742StrongTransOfHom (F := S1726K) f) h')).trans
      (S1742StrongTransIsoOfHom (F := S1726K) L'))⟩

/-- 2-Yoneda in the sharp form used below: for strong transformations between
representable etale stacks, being 2-isomorphic is the same as having equal
2-Yoneda evaluations. -/
theorem S1756IsoIffEval (S T : SchemeOverField S1726K)
    (L L' : Pseudofunctor.StrongTrans (S1743Y S) (S1743Y T)) :
    Nonempty (L ≅ L') ↔ S1743YonedaEval S T L = S1743YonedaEval S T L' :=
  ⟨fun h => by
    rcases h with ⟨e⟩
    exact S1743YonedaEval_congr_iso S T e, fun h => S1756IsoOfEvalEq S T L L' h⟩

/-- The self-endomorphism of the affine model induced by the identity-point base
change: the 2-Yoneda evaluation of `toSource ≫ lift`. -/
noncomputable def S1756End (A : S1728Cover) : S1733Model A ⟶ S1733Model A :=
  S1743YonedaEval (S1733Model A) (S1733Model A)
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))

/-- The self-endomorphism of the model is a morphism over the base scheme.  This
is the only constraint on it that the identity-point base-change square supplies
unconditionally. -/
theorem S1756End_projection (A : S1728Cover) :
    S1756End A ≫ S1756Projection A = S1756Projection A := by
  have hcomp := S1743YonedaEval_vcomp (S1733Model A) (S1733Model A) S1726AffineOver
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
    (S1756ProjectionMap A)
  have hiso : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
        (S1756ProjectionMap A))
      (S1756ProjectionMap A) := by
    have h1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
          (S1756ProjectionMap A))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ProjectionMap A))) :=
      S1756AssociatorIso _ _ _
    have h2 : Iso
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ProjectionMap A)))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) A.map) :=
      S1756WhiskerLeftIso _ _ _ ((S1743BaseChange A).isPullback.liftToY
        (S1743Source A) (S1743IdentityCone A))
    have h3 : Iso
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) A.map)
        (Pseudofunctor.StrongTrans.vcomp (S1756ProjectionMap A) S1733BasePoint) :=
      (S1743BaseChange A).commutes
    have h4 : Iso
        (Pseudofunctor.StrongTrans.vcomp (S1756ProjectionMap A) S1733BasePoint)
        (S1756ProjectionMap A) :=
      S1756RightUnitorIso (S1756ProjectionMap A)
    exact h1.trans (h2.trans (h3.trans h4))
  have heq : S1743YonedaEval (S1733Model A) S1726AffineOver
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
        (S1756ProjectionMap A))
      = S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) :=
    S1743YonedaEval_congr_iso (S1733Model A) S1726AffineOver hiso
  rw [S1756End, ← S1756YonedaEval_projectionMap A, ← hcomp, heq]

/-- The self-endomorphism of the model is idempotent: the missing datum is an
idempotent endomorphism of the affine model over the base. -/
theorem S1756End_idempotent (A : S1728Cover) :
    S1756End A ≫ S1756End A = S1756End A := by
  have hu : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)) :=
    (S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A)
  have hcomp := S1743YonedaEval_vcomp (S1733Model A) (S1733Model A) (S1733Model A)
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
  have hiso : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)))
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) := by
    have h1 : Iso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
          (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
            (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)))) :=
      S1756AssociatorIso _ _ _
    have h2 : Iso
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp (S1743Lift A)
            (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
            (S1743Lift A))) :=
      S1756WhiskerLeftIso _ _ _
        (S1756AssociatorIso (S1743Lift A) (S1756ToSource A) (S1743Lift A)).symm
    have h3 : Iso
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
            (S1743Lift A)))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.id (S1743Source A)) (S1743Lift A))) :=
      S1756WhiskerLeftIso _ _ _ (S1756WhiskerRightIso _ _ _ hu)
    have h4 : Iso
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.id (S1743Source A)) (S1743Lift A)))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) :=
      S1756WhiskerLeftIso _ _ _ (S1756LeftUnitorIso (S1743Lift A))
    exact h1.trans (h2.trans (h3.trans h4))
  have heq : S1743YonedaEval (S1733Model A) (S1733Model A)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)))
      = S1743YonedaEval (S1733Model A) (S1733Model A)
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) :=
    S1743YonedaEval_congr_iso (S1733Model A) (S1733Model A) hiso
  rw [S1756End, ← hcomp, heq]

/-! ## 5. The missing unit 2-cell and its scheme-level form -/

/-- A quasi-equivalence between two category-valued etale stacks: a pair of
strong transformations with the two triangular 2-isomorphisms. -/
structure S1756StackEquiv (P Q : EtaleStackPseudofunctor S1726K) where
  /-- The forward strong transformation. -/
  hom : Pseudofunctor.StrongTrans P Q
  /-- The backward strong transformation. -/
  inv : Pseudofunctor.StrongTrans Q P
  /-- The unit 2-isomorphism `hom ≫ inv ≅ 𝟙`. -/
  unit : Iso (Pseudofunctor.StrongTrans.vcomp hom inv) (Pseudofunctor.StrongTrans.id P)
  /-- The counit 2-isomorphism `inv ≫ hom ≅ 𝟙`. -/
  counit : Iso (Pseudofunctor.StrongTrans.vcomp inv hom) (Pseudofunctor.StrongTrans.id Q)

/-- The missing unit 2-cell at the canonical lift: `toSource ≫ lift ≅ 𝟙`.
Written as a proposition because it is not available from the data. -/
def S1756Unit (A : S1728Cover) : Prop :=
  Nonempty (Iso
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
    (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))

/-- The missing unit 2-cell is exactly the scheme-level equation saying that the
self-endomorphism of the model is the identity. -/
theorem S1756Unit_iff_end (A : S1728Cover) :
    S1756Unit A ↔ S1756End A = 𝟙 (S1733Model A) := by
  have hk : S1743YonedaEval (S1733Model A) (S1733Model A)
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) =
      S1756End A := rfl
  constructor
  · rintro ⟨e⟩
    have h1 := S1743YonedaEval_congr_iso (S1733Model A) (S1733Model A) e
    rw [← hk, h1, S1756YonedaEval_id]
  · intro h
    refine S1756IsoOfEvalEq (S1733Model A) (S1733Model A) _ _ ?_
    rw [hk, h, S1756YonedaEval_id]

/-- The missing unit 2-cell, together with the unconditional counit, gives a
genuine quasi-equivalence of the affine model stack with the cover source. -/
noncomputable def S1756StackEquivOfUnit (A : S1728Cover) (h : S1756Unit A) :
    S1756StackEquiv (S1743ModelStack A) (S1743Source A) where
  hom := S1756ToSource A
  inv := S1743Lift A
  unit := h.some
  counit := (S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A)

/-- Representability of the cover source by its affine finite etale model, as a
genuine quasi-equivalence of category-valued etale stacks. -/
def S1756SourceRepresentable (A : S1728Cover) : Prop :=
  Nonempty (S1756StackEquiv (S1743ModelStack A) (S1743Source A))

/-- The scheme-level equation gives representability of the cover source. -/
theorem S1756SourceRepresentable_of_end (A : S1728Cover)
    (h : S1756End A = 𝟙 (S1733Model A)) : S1756SourceRepresentable A :=
  ⟨S1756StackEquivOfUnit A ((S1756Unit_iff_end A).mpr h)⟩

/-! ## 6. The exact first missing statement -/

/-- **The exact first missing statement**: for every cover, the identity-point
self-endomorphism of the affine model is the identity.  This is the 2-Yoneda /
descent statement identifying the pullback of `A.map` along the identity 1-cell
with the source itself. -/
def S1756FirstMissing : Prop := ∀ A : S1728Cover, S1756End A = 𝟙 (S1733Model A)

/-- Representability of every cover source by its affine finite etale model. -/
def S1756SourceRepresentableAll : Prop := ∀ A : S1728Cover, S1756SourceRepresentable A

/-- The first missing statement gives representability of every cover source. -/
theorem S1756SourceRepresentableAll_of_firstMissing (h : S1756FirstMissing) :
    S1756SourceRepresentableAll :=
  fun A => S1756SourceRepresentable_of_end A (h A)

/-- Any one-sided inverse of the comparison already forces the canonical
self-endomorphism to be the identity. -/
theorem S1756End_eq_one_of_retraction (A : S1728Cover)
    (h : ∃ inv : Pseudofunctor.StrongTrans (S1743Source A) (S1743ModelStack A),
      Nonempty (Iso
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))) :
    S1756End A = 𝟙 (S1733Model A) := by
  obtain ⟨inv, ⟨hinv⟩⟩ := h
  have hu : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)) :=
    (S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A)
  have hiso := S1756_unit_iso (S1756ToSource A) (S1743Lift A) inv hu hinv
  have hk : S1743YonedaEval (S1733Model A) (S1733Model A)
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) =
      S1756End A := rfl
  rw [← hk, (S1756IsoIffEval (S1733Model A) (S1733Model A)
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
    (Pseudofunctor.StrongTrans.id (S1743ModelStack A))).mp ⟨hiso⟩,
    S1756YonedaEval_id]

/-- The first missing statement is equivalent to S1743's retraction statement:
the choice of inverse does not matter. -/
theorem S1756Retraction_iff_firstMissing :
    S1743SourceRetraction ↔ S1756FirstMissing := by
  constructor
  · intro h A
    exact S1756End_eq_one_of_retraction A (h A)
  · intro h A
    exact ⟨S1743Lift A, (S1756Unit_iff_end A).mpr (h A)⟩

/-- If the structure morphism of the affine model is a monomorphism, the missing
equation holds: a counterexample would need a non-monomorphic finite etale
structure morphism. -/
theorem S1756End_eq_one_of_mono (A : S1728Cover)
    (hmono : Mono (S1756Projection A)) :
    S1756End A = 𝟙 (S1733Model A) := by
  haveI := hmono
  refine (cancel_mono (S1756Projection A)).mp ?_
  rw [Category.id_comp]
  exact S1756End_projection A

/-! ## 7. Checks -/

#check S1756AffineModelData
#check S1756AffineModelDataActual
#check S1756ToSource
#check S1756ProjectionMap
#check S1756End
#check S1756End_projection
#check S1756End_idempotent
#check S1756YonedaEval_id
#check S1756YonedaEval_projectionMap
#check S1756IsoOfEvalEq
#check S1756IsoIffEval
#check S1756StackEquiv
#check S1756Unit
#check S1756Unit_iff_end
#check S1756StackEquivOfUnit
#check S1756SourceRepresentable
#check S1756SourceRepresentable_of_end
#check S1756FirstMissing
#check S1756SourceRepresentableAll
#check S1756SourceRepresentableAll_of_firstMissing
#check S1756_unit_iso
#check S1756End_eq_one_of_retraction
#check S1756Retraction_iff_firstMissing
#check S1756End_eq_one_of_mono

#print axioms S1756AffineModelDataActual
#print axioms S1756ToSource
#print axioms S1756End
#print axioms S1756End_projection
#print axioms S1756End_idempotent
#print axioms S1756YonedaEval_id
#print axioms S1756YonedaEval_projectionMap
#print axioms S1756IsoOfEvalEq
#print axioms S1756IsoIffEval
#print axioms S1756Unit_iff_end
#print axioms S1756StackEquivOfUnit
#print axioms S1756SourceRepresentable_of_end
#print axioms S1756SourceRepresentableAll_of_firstMissing
#print axioms S1756_unit_iso
#print axioms S1756End_eq_one_of_retraction
#print axioms S1756Retraction_iff_firstMissing
#print axioms S1756End_eq_one_of_mono

end LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
