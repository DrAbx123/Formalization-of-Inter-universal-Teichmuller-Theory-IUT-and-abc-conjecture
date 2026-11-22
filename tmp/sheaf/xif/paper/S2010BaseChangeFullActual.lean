import tmp.sheaf.xif.paper.S2007CoverFiberDiscreteActual
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Limits

/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S2010
-/
/-!
# S2010: the full 2-universal property is FALSE for the recorded finite-etale base changes

## Result

The exact first missing statement of S2007/S1841/S1827,
S2007AllBaseChangesFull, is not an unproved theorem: it is refuted for the
recorded definition of EtaleStackBaseChangePresentation.

We construct an actual inhabitant S2010CounterCover : S1728Cover:

* its source is the orbicurve stack itself and its structure map is the identity;
* at every scheme-valued point (T, p) the recorded finite-etale base change is
  the split double cover T ⨿ T -> T, whose projection is finite etale
  (S2010CounterFiniteEtale); and
* the recorded weak TwoPullbackWitness is constructed explicitly
  (S2010Witness), with the canonical section T -> T ⨿ T as the lift.

The swap of the two sheets is an automorphism of the apex over T.  It agrees
with the tautological cone on both projections, but it is not 2-isomorphic to
the lift: evaluating at the identity point gives the scheme equation
projection ; section = swap, which is false because the left side sends the
first sheet to the first sheet while the swap sends it to the second.  Hence
the identity-point cone comparison is not essentially surjective
(S2010Counter_not_coneEssSurj), and consequently

  not S1827FirstMissing, not S1841FirstMissing,
  not S2007AllBaseChangesFull, not S2007FirstMissing.

Thus the weak seven-field witness is insufficient even when the base change is
a genuine finite-etale scheme over the test scheme.  The precise repair is to
strengthen TwoPullbackWitness to the full 2-dimensional universal property (or,
equivalently, to require the recorded presentation to be the actual iso-comma
fiber); no such property can be derived from the recorded fields.

## Honest boundary

No sorry, no new axiom, no fake 2-cell and no fake equivalence.  The
counterexample is an actual inhabitant of S1728Cover; its finite-etale field is
constructed, not assumed.  The only axioms used are propext,
Classical.choice and Quot.sound.
-/


noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2010BaseChangeFullActual

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
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S2007CoverFiberDiscreteActual

/-! ## 1. Scheme-level enlargement: the split double cover T ⨿ T -> T -/

/-- The fold map of the split double cover of a test scheme. -/
noncomputable def S2010Fold (T : SchemeOverField S1726K) :
    T.left ⨿ T.left ⟶ T.left :=
  Limits.coprod.desc (𝟙 T.left) (𝟙 T.left)

/-- The first inclusion into the split double cover. -/
noncomputable def S2010Inl (T : SchemeOverField S1726K) :
    T.left ⟶ T.left ⨿ T.left :=
  Limits.coprod.inl

/-- The swap of the two sheets of the split double cover. -/
noncomputable def S2010SwapScheme (T : SchemeOverField S1726K) :
    T.left ⨿ T.left ⟶ T.left ⨿ T.left :=
  Limits.coprod.desc (Limits.coprod.inr : T.left ⟶ T.left ⨿ T.left)
    (Limits.coprod.inl : T.left ⟶ T.left ⨿ T.left)

theorem S2010Inl_fold (T : SchemeOverField S1726K) :
    Limits.coprod.inl ≫ S2010Fold T = 𝟙 T.left :=
  Limits.coprod.inl_desc _ _

theorem S2010Inr_fold (T : SchemeOverField S1726K) :
    Limits.coprod.inr ≫ S2010Fold T = 𝟙 T.left :=
  Limits.coprod.inr_desc _ _

theorem S2010SwapScheme_inl (T : SchemeOverField S1726K) :
    Limits.coprod.inl ≫ S2010SwapScheme T = Limits.coprod.inr := by
  simp [S2010SwapScheme]

theorem S2010SwapScheme_inr (T : SchemeOverField S1726K) :
    Limits.coprod.inr ≫ S2010SwapScheme T = Limits.coprod.inl := by
  simp [S2010SwapScheme]

theorem S2010SwapScheme_fold (T : SchemeOverField S1726K) :
    S2010SwapScheme T ≫ S2010Fold T = S2010Fold T := by
  apply Limits.coprod.hom_ext
  · rw [← Category.assoc, S2010SwapScheme_inl, S2010Inr_fold, S2010Inl_fold]
  · rw [← Category.assoc, S2010SwapScheme_inr, S2010Inl_fold, S2010Inr_fold]

/-- The split double cover as a scheme over the base. -/
noncomputable abbrev S2010P (T : SchemeOverField S1726K) : SchemeOverField S1726K :=
  Over.mk (S2010Fold T ≫ T.hom)

/-- The projection of the split double cover. -/
noncomputable def S2010Projection (T : SchemeOverField S1726K) :
    S2010P T ⟶ T :=
  Over.homMk (S2010Fold T) rfl

/-- The canonical section of the projection. -/
noncomputable def S2010Section (T : SchemeOverField S1726K) :
    T ⟶ S2010P T :=
  Over.homMk (S2010Inl T) (by
    change Limits.coprod.inl ≫ S2010Fold T ≫ T.hom = T.hom
    rw [← Category.assoc, S2010Inl_fold, Category.id_comp])

/-- The swap sheet automorphism over the base. -/
noncomputable def S2010Swap (T : SchemeOverField S1726K) :
    S2010P T ⟶ S2010P T :=
  Over.homMk (S2010SwapScheme T) (by
    change S2010SwapScheme T ≫ S2010Fold T ≫ T.hom =
      S2010Fold T ≫ T.hom
    rw [← Category.assoc, S2010SwapScheme_fold])

theorem S2010Section_projection (T : SchemeOverField S1726K) :
    S2010Section T ≫ S2010Projection T = 𝟙 T := by
  apply Over.OverMorphism.ext
  exact S2010Inl_fold T

theorem S2010Swap_projection (T : SchemeOverField S1726K) :
    S2010Swap T ≫ S2010Projection T = S2010Projection T := by
  apply Over.OverMorphism.ext
  exact S2010SwapScheme_fold T

/-! ## 2. The uniform enlarged base-change presentation -/

/-- The strong transformation of the fold map. -/
noncomputable abbrev S2010FoldTrans (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y (S2010P T)) (S1743Y T) :=
  S1742StrongTransOfHom (F := S1726K) (S2010Projection T)

/-- The strong transformation of the section. -/
noncomputable abbrev S2010SectionTrans (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y T) (S1743Y (S2010P T)) :=
  S1742StrongTransOfHom (F := S1726K) (S2010Section T)

/-- The strong transformation of the swap. -/
noncomputable abbrev S2010SwapTrans (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y (S2010P T)) (S1743Y (S2010P T)) :=
  S1742StrongTransOfHom (F := S1726K) (S2010Swap T)

/-- The section followed by the projection is the identity transformation. -/
noncomputable def S2010SectionFoldIso (T : SchemeOverField S1726K) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2010SectionTrans T) (S2010FoldTrans T))
      (Pseudofunctor.StrongTrans.id (S1743Y T)) :=
  (S1844YComp (S2010Section T) (S2010Projection T)).trans
    ((eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K))
      (S2010Section_projection T))).trans (S1844YId T))

/-- The source stack of the counterexample cover: the orbicurve itself. -/
noncomputable abbrev S2010CounterSource : EtaleStackOverField S1726K where
  fiber := S1726Orbicurve.stack.fiber
  isStack := S1726Orbicurve.stack.isStack

/-- The identity map of the counterexample cover. -/
noncomputable abbrev S2010CounterMap : S2010CounterSource.Hom S1726Orbicurve.stack :=
  Pseudofunctor.StrongTrans.id _

/-- The enlarged square at a point p. -/
noncomputable def S2010Square (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) :
    EtalePseudofunctorSquare (S1743Y (S2010P T))
      S2010CounterSource.fiber (S1743Y T) S1726Orbicurve.stack.fiber where
  toX := Pseudofunctor.StrongTrans.vcomp (S2010FoldTrans T) p
  toY := S2010FoldTrans T
  xToBase := Pseudofunctor.StrongTrans.id S2010CounterSource.fiber
  yToBase := p
  commutes := S1756RightUnitorIso (Pseudofunctor.StrongTrans.vcomp (S2010FoldTrans T) p)

/-- The lift of a cone along the enlarged square. -/
noncomputable def S2010Lift (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber)
    {W : EtaleStackPseudofunctor S1726K} (c : (S2010Square T p).Cone W) :
    Pseudofunctor.StrongTrans W (S1743Y (S2010P T)) :=
  Pseudofunctor.StrongTrans.vcomp c.toY (S2010SectionTrans T)

/-- The recorded two-pullback witness for the enlarged square. -/
noncomputable def S2010Witness (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) :
    (S2010Square T p).TwoPullbackWitness where
  lift W c := S2010Lift T p c
  liftToX W c := by
    refine (S1756AssociatorIso c.toY (S2010SectionTrans T)
      (Pseudofunctor.StrongTrans.vcomp (S2010FoldTrans T) p)).trans ?_
    refine (S1756WhiskerLeftIso c.toY _ _
      (S1756AssociatorIso (S2010SectionTrans T) (S2010FoldTrans T) p).symm).trans ?_
    refine (S1756WhiskerLeftIso c.toY _ _
      (S1756WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp
        (S2010SectionTrans T) (S2010FoldTrans T))
        (Pseudofunctor.StrongTrans.id (S1743Y T)) p
        (S2010SectionFoldIso T))).trans ?_
    refine (S1756WhiskerLeftIso c.toY _ _
      (S1756LeftUnitorIso p)).trans ?_
    exact (c.commutes.symm).trans (S1756RightUnitorIso c.toX)
  liftToY W c :=
    (S1756AssociatorIso c.toY (S2010SectionTrans T) (S2010FoldTrans T)).trans
      ((S1756WhiskerLeftIso c.toY _ _ (S2010SectionFoldIso T)).trans
        (S1756RightUnitorIso c.toY))
  liftTwoCell W source target m :=
    Pseudofunctor.StrongTrans.whiskerRight m.toY (S2010SectionTrans T)
  liftTwoCell_toX W source target m :=
    (S1844SubsingletonMod _ _).allEq _ _
  liftTwoCell_toY W source target m :=
    (S1844SubsingletonMod _ _).allEq _ _
  twoCell_ext W first second alpha beta _ _ :=
    (S1844SubsingletonMod first second).allEq alpha beta

/-- The enlarged base-change presentation. -/
noncomputable def S2010BaseChange (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) :
    EtaleStackBaseChangePresentation S2010CounterMap T p where
  pullbackScheme := S2010P T
  projection := S2010Projection T
  projectionMap := S1743SchemeRepresentableMap (S2010Projection T)
  toSource := Pseudofunctor.StrongTrans.vcomp (S2010FoldTrans T) p
  commutes := S1756RightUnitorIso
    (Pseudofunctor.StrongTrans.vcomp (S2010FoldTrans T) p)
  isPullback := S2010Witness T p

/-- The counterexample finite-etale structure on the identity cover. -/
noncomputable def S2010CounterFiniteEtale :
    EtaleStackFiniteEtaleMorphism S2010CounterMap where
  baseChange T p := S2010BaseChange T p
  hasProperty T p := by
    constructor
    · show IsFinite (Limits.coprod.desc (𝟙 T.left) (𝟙 T.left))
      infer_instance
    · show Etale (Limits.coprod.desc (𝟙 T.left) (𝟙 T.left))
      rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale)
        (coprodOpenCover.{_, 0} T.left T.left)]
      intro i
      match i with
      | Sum.inl _ =>
          show Etale (Limits.coprod.inl ≫ Limits.coprod.desc (𝟙 T.left) (𝟙 T.left))
          rw [Limits.coprod.inl_desc]
          infer_instance
      | Sum.inr _ =>
          show Etale (Limits.coprod.inr ≫ Limits.coprod.desc (𝟙 T.left) (𝟙 T.left))
          rw [Limits.coprod.inr_desc]
          infer_instance

/-- The counterexample cover. -/
noncomputable def S2010CounterCover : S1728Cover where
  source := S2010CounterSource
  map := S2010CounterMap
  finiteEtale := S2010CounterFiniteEtale



/-! ## 3. The failure at the identity point -/

/-- The swap composed with the fold is the fold. -/
theorem S2010SwapTrans_fold (T : SchemeOverField S1726K) :
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (S2010SwapTrans T)
      (S2010FoldTrans T)) (S2010FoldTrans T)) := by
  refine ⟨(S1844YComp (S2010Swap T) (S2010Projection T)).trans ?_⟩
  exact (eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K))
    (S2010Swap_projection T))).trans (Iso.refl _)

/-- The swap composed with the first leg agrees with the first leg. -/
theorem S2010SwapTrans_toX (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S2010SwapTrans T)
        (Pseudofunctor.StrongTrans.vcomp (S2010FoldTrans T) p))
      (Pseudofunctor.StrongTrans.vcomp (S2010FoldTrans T) p)) := by
  obtain ⟨e⟩ := S2010SwapTrans_fold T
  exact ⟨(S1756AssociatorIso (S2010SwapTrans T) (S2010FoldTrans T) p).symm.trans
    (S1756WhiskerRightIso _ _ p e)⟩

/-- The tautological cone of the enlarged square. -/
noncomputable def S2010TautologicalCone (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) :
    (S2010Square T p).Cone (S1743Y (S2010P T)) where
  toX := (S2010Square T p).toX
  toY := (S2010Square T p).toY
  commutes := (S2010Square T p).commutes


/-- The base point of the affine model, as a point of the underlying scheme. -/
noncomputable def S2010BasePoint : S1726Base.left :=
  Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of S1726K)))

/-- A rational point of the affine model. -/
noncomputable def S2010AffinePoint : S1726AffineOver.left :=
  (S1726OverOfAlgHom (S1726PointAlgHom 0 0 S1726Equation_zero_zero)).left
    S2010BasePoint

/-- The projection followed by the section is not the swap, at the identity point. -/
theorem S2010ProjectionSection_ne_swap :
    S2010Projection S1726AffineOver ≫ S2010Section S1726AffineOver ≠
      S2010Swap S1726AffineOver := by
  intro h
  have hleft : (S2010Projection S1726AffineOver ≫
      S2010Section S1726AffineOver).left =
      (S2010Swap S1726AffineOver).left :=
    congrArg Over.Hom.left h
  have h2 : (Limits.coprod.inl : S1726AffineOver.left ⟶
      S1726AffineOver.left ⨿ S1726AffineOver.left) ≫
      (S2010Projection S1726AffineOver ≫ S2010Section S1726AffineOver).left =
      (Limits.coprod.inl : S1726AffineOver.left ⟶
      S1726AffineOver.left ⨿ S1726AffineOver.left) ≫
      (S2010Swap S1726AffineOver).left :=
    congrArg (fun f => Limits.coprod.inl ≫ f) hleft
  rw [show (S2010Projection S1726AffineOver ≫
      S2010Section S1726AffineOver).left =
      S2010Fold S1726AffineOver ≫ S2010Inl S1726AffineOver from rfl,
    ← Category.assoc, S2010Inl_fold, Category.id_comp,
    show (S2010Swap S1726AffineOver).left = S2010SwapScheme S1726AffineOver from rfl,
    S2010SwapScheme_inl] at h2
  have h3 : (Limits.coprod.inl : S1726AffineOver.left ⟶
      S1726AffineOver.left ⨿ S1726AffineOver.left) S2010AffinePoint =
      (Limits.coprod.inr : S1726AffineOver.left ⟶
      S1726AffineOver.left ⨿ S1726AffineOver.left) S2010AffinePoint := by
    exact congrArg (fun f => f S2010AffinePoint) h2
  exact inl_ne_inr S1726AffineOver.left S1726AffineOver.left
    S2010AffinePoint S2010AffinePoint h3


/-- The counterexample cover does not have the full 2-universal property at the
identity point. -/
theorem S2010Counter_not_coneEssSurj :
    ¬ S1827ConeEssSurj S2010CounterCover := by
  intro h
  let T : SchemeOverField S1726K := S1726AffineOver
  let p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber :=
    S1733BasePoint
  let C : S1728Cover := S2010CounterCover
  let c : (S2010Square T p).Cone (S1743Y (S2010P T)) :=
    S2010TautologicalCone T p
  let f : Pseudofunctor.StrongTrans (S1743Y (S2010P T)) (S1743Y (S2010P T)) :=
    S2010SwapTrans T
  have hX : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp f (S1743Square C).toX) c.toX) :=
    S2010SwapTrans_toX T p
  have hY : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp f (S1743Square C).toY) c.toY) :=
    S2010SwapTrans_fold T
  obtain ⟨e⟩ := h (S1743Y (S2010P T)) c f hX hY
  have hev := S1743YonedaEval_congr_iso (S2010P T) (S2010P T) e
  rw [show S1743YonedaEval (S2010P T) (S2010P T) f = S2010Swap T from
      S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) (S2010Swap T)] at hev
  have hlift : (S1743BaseChange C).isPullback.lift (S1743Y (S2010P T)) c =
      S2010Lift T p c := rfl
  rw [hlift] at hev
  have hcomp := S1743YonedaEval_vcomp (S2010P T) T (S2010P T)
    (S2010FoldTrans T) (S2010SectionTrans T)
  rw [show S1743YonedaEval (S2010P T) (S2010P T) (S2010Lift T p c) =
      S1743YonedaEval (S2010P T) (S2010P T)
        (Pseudofunctor.StrongTrans.vcomp (S2010FoldTrans T)
          (S2010SectionTrans T)) from rfl,
    hcomp,
    show S1743YonedaEval (S2010P T) T (S2010FoldTrans T) =
      S2010Projection T from
      S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) (S2010Projection T),
    show S1743YonedaEval T (S2010P T) (S2010SectionTrans T) =
      S2010Section T from
      S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) (S2010Section T)] at hev
  exact S2010ProjectionSection_ne_swap hev.symm


/-! ## 4. Consequences: the recorded full-property target is false -/

/-- The uniform identity-point full-property target fails. -/
theorem S2010_not_S1827FirstMissing : ¬ S1827FirstMissing :=
  fun h => S2010Counter_not_coneEssSurj (h S2010CounterCover)

/-- The finite-etale-algebra form of the first missing target fails. -/
theorem S2010_not_S1841FirstMissing : ¬ S1841FirstMissing :=
  fun h => S2010_not_S1827FirstMissing ((S1841FirstMissing_iff_S1827).mp h)

/-- The all-base-changes full 2-universal property is false for the recorded
definition of a finite-etale base-change presentation. -/
theorem S2010_not_S2007AllBaseChangesFull : ¬ S2007AllBaseChangesFull :=
  fun h => S2010_not_S1827FirstMissing
    (S2007AllBaseChangesFull_implies_identity h)

/-- Consequently the named first missing statement of S2007 is false. -/
theorem S2010_not_S2007FirstMissing : ¬ S2007FirstMissing :=
  fun h => S2010_not_S1827FirstMissing ((S2007FirstMissing_iff_full).mp h)

/-- The recorded finite-etale data at the identity point of the counterexample
cover is genuinely finite etale, although its square is not a full 2-pullback. -/
theorem S2010Counter_identity_finiteEtale :
    IsFinite (S2010BaseChange S1726AffineOver S1733BasePoint).projection.left ∧
      Etale (S2010BaseChange S1726AffineOver S1733BasePoint).projection.left :=
  S2010CounterFiniteEtale.hasProperty S1726AffineOver S1733BasePoint

/-- There is a cover whose identity-point base change is not a full 2-pullback. -/
theorem S2010_exists_counterexample :
    ∃ C : S1728Cover, ¬ S1827ConeEssSurj C :=
  ⟨S2010CounterCover, S2010Counter_not_coneEssSurj⟩

/-! ## 5. Checks and axiom audit -/

#check S2010Fold
#check S2010P
#check S2010Projection
#check S2010Section
#check S2010Swap
#check S2010Square
#check S2010Witness
#check S2010BaseChange
#check S2010CounterFiniteEtale
#check S2010CounterCover
#check S2010ProjectionSection_ne_swap
#check S2010Counter_not_coneEssSurj
#check S2010_not_S1827FirstMissing
#check S2010_not_S1841FirstMissing
#check S2010_not_S2007AllBaseChangesFull
#check S2010_not_S2007FirstMissing
#check S2010_exists_counterexample
#check S2010Counter_identity_finiteEtale

#print axioms S2010Inl_fold
#print axioms S2010SwapScheme_fold
#print axioms S2010Section_projection
#print axioms S2010Swap_projection
#print axioms S2010SectionFoldIso
#print axioms S2010Witness
#print axioms S2010BaseChange
#print axioms S2010CounterFiniteEtale
#print axioms S2010ProjectionSection_ne_swap
#print axioms S2010Counter_not_coneEssSurj
#print axioms S2010_not_S1827FirstMissing
#print axioms S2010_not_S1841FirstMissing
#print axioms S2010_not_S2007AllBaseChangesFull
#print axioms S2010_not_S2007FirstMissing
#print axioms S2010_exists_counterexample
#print axioms S2010Counter_identity_finiteEtale

end LeanFormal.IUT.XiFPaper.S2010BaseChangeFullActual