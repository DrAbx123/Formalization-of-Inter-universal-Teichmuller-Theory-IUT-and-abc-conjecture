/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2291
-/

import tmp.sheaf.xif.paper.S2269GraphCompatActual

/-!
# S2291: uniform graph compatibility is FALSE

## The question

S2269 isolated the exact missing input for the uniform S2185 strict-cone
comparison as S2269GraphCompatAll: for every source cover B and every target
cover C, the recorded PC-lift of the transported cone cPC is both the
Phi-composite and the graph composite.  S2269 proved this statement for
strong/coherent target covers and for the doubled target cover, and showed that
it is strictly weaker than the (refuted) PC-strongness.  The remaining question
was whether it holds for *arbitrary* weak target covers.

This file answers it negatively, by an explicit weak target cover.

## The cover

The doubled presentation of S1850 is *section based*: its recorded lift of any
cone is cone.toY ; inl.  The new cover S2291PathCover has the same source and
structure map as the doubled cover (the orbicurve itself and its identity), the
same underlying base-change scheme T coprod T -> T, but a different recorded
weak lift:

  S2291CondLift v = (if v collapses two distinct test points then v ; inl
                     else v ; inr)

where S2291Collapse v says that the test leg v identifies two distinct points
of the test stack.  S2291Collapse is invariant under cone morphisms
(S2291Collapse_of_twoCell), which is exactly what is needed for the liftTwoCell
field of the witness.  The remaining fields of TwoPullbackWitness are
subsingleton-valued at this square (both residual targets are representable:
the cover source is the orbicurve, whose fibre is the representable stack of the
affine model), so the whole structure is legitimate.  In particular

* S2291PathPresentation is an EtaleStackBaseChangePresentation of the identity
  map at every test scheme and point,
* S2291PathFiniteEtale makes it a finite-etale structure (the projection is the
  fold T coprod T -> T, finite and etale by S1850),
* S2291PathCover is therefore an actual S1728Cover.

The lift is *not* section based: it uses the second summand except on collapsing
test legs, where it uses the first.

## The refutations

At the test scheme T = Spec R' coprod Spec R' and the endomorphism
S2291Diag = (inl, inl) : T -> T (which is idempotent, not the identity, and
collapses the two summands), the cone with toY = y(S2291Diag) triggers the first
branch of the conditional lift, while the graph cone (whose toY is the identity)
triggers the second.  Taking A = B = C = S2291PathCover and the identity cover
maps, the graph candidate and the recorded PC-lift have underlying scheme maps

  graph candidate:  S2291Diag ; inr,   recorded lift:  S2291Diag ; inl,

so no 2-isomorphism can exist (evaluating at a point of T separates the two
coproduct inclusions).  The S2185 comparison at the same datum has underlying
maps S2291Diag ; inl and S2291Diag ; inr.  Consequently

* S2291NotGraphCompatAt and S2291NotGraphCompatAll:
  S2269GraphCompatAll is FALSE; the recorded missing statement
  S2269FirstMissing is refuted,
* S2291NotStrictConeIso:
  S2185StrictConeIso itself is FALSE at the same datum.  The S2185 comparison is
  not a formal consequence of the recorded weak presentation data: the weak
  TwoPullbackWitness constrains neither the dependence of the lift on the test
  leg nor its compatibility with the graph section.

## What this does and does not say

The D6 target S2130ConcreteTwoPullback is *not* changed or refuted here: it asks
for the existence of a two-pullback witness for the S2130 base square, which is
a different (and weaker) statement than the S2185 comparison.  What is settled
is that neither S2185StrictConeIso nor S2269GraphCompatAll can be proved from the
recorded cover data alone: any repair must either restrict the class of target
covers (strong/coherent covers and the doubled cover do satisfy graph
compatibility, by S2269) or add a coherence field to the presentation -- which
would change the recorded structures, hence is not done here.

No sorry, no axiom, no change of the D6 target or of any recorded definition.
Axiom footprint: propext, Classical.choice, Quot.sound.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

namespace LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
open LeanFormal.IUT.XiFPaper.S2185ConcreteTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual
open LeanFormal.IUT.XiFPaper.S2269GraphCompatActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

universe u

/-! ## 1. The second-summand companion of the S1850 splitting -/

theorem S2291Inr_fold (T : SchemeOverField S1726K) :
    S1850Inr T ≫ S1850Fold T = 𝟙 T := by
  apply Comma.hom_ext
  · show Limits.coprod.inr ≫ Limits.coprod.desc (𝟙 T.left) (𝟙 T.left) = 𝟙 T.left
    rw [Limits.coprod.inr_desc]
  · apply Subsingleton.elim

noncomputable abbrev S2291InrStrong (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y T) (S1743Y (S1850P T)) :=
  S1742StrongTransOfHom (S1850Inr T)

theorem S2291InrFold_eval (T : SchemeOverField S1726K) :
    S1743YonedaEval T T
      (Pseudofunctor.StrongTrans.vcomp (S2291InrStrong T) (S1850FoldStrong T)) = 𝟙 T := by
  rw [S1743YonedaEval_vcomp, S1743YonedaEval_eq_S1742, S1743YonedaEval_eq_S1742,
    S1742HomOfStrongTrans_strongTransOfHom,
    S1742HomOfStrongTrans_strongTransOfHom, S2291Inr_fold]

theorem S2291InrFold_iso (T : SchemeOverField S1726K) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S2291InrStrong T) (S1850FoldStrong T))
      (Pseudofunctor.StrongTrans.id (S1743Y T))) := by
  refine S1756IsoOfEvalEq T T _ _ ?_
  rw [S2291InrFold_eval, S1756YonedaEval_id]

noncomputable def S2291ConeIsoY_inr (T : SchemeOverField S1726K)
    {W : EtaleStackPseudofunctor S1726K}
    (v : Pseudofunctor.StrongTrans W (S1743Y T)) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp v (S2291InrStrong T)) (S1850FoldStrong T)) v :=
  (S1756AssociatorIso v (S2291InrStrong T) (S1850FoldStrong T)).trans
    ((S1756WhiskerLeftIso v _ _
        (Classical.choice (S2291InrFold_iso T))).trans
      (S1756RightUnitorIso v))

noncomputable def S2291ConeIsoX_inr (T : SchemeOverField S1726K)
    {W : EtaleStackPseudofunctor S1726K}
    (u : Pseudofunctor.StrongTrans W S1850X.fiber)
    (v : Pseudofunctor.StrongTrans W (S1743Y T))
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber)
    (comm : Iso (Pseudofunctor.StrongTrans.vcomp u
        (Pseudofunctor.StrongTrans.id S1850X.fiber))
      (Pseudofunctor.StrongTrans.vcomp v q)) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp v (S2291InrStrong T))
          (Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q)) u :=
  (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp v (S2291InrStrong T))
      (S1850FoldStrong T) q).symm.trans
    ((S1756WhiskerRightIso
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp v (S2291InrStrong T)) (S1850FoldStrong T))
        v q (S2291ConeIsoY_inr T v)).trans
      (comm.symm.trans (S1756RightUnitorIso u)))

/-! ## 2. A 2-cell into a representable stack is an isomorphism -/

theorem S2291Val_eq_of_twoCell {W : EtaleStackPseudofunctor S1726K}
    {T : SchemeOverField S1726K}
    {F G : Pseudofunctor.StrongTrans W (S1743Y T)} (alpha : F ⟶ G)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1911Val F U a = S1911Val G U a :=
  Discrete.eq_of_hom ((alpha.as.app U).toNatTrans.app a)

theorem S2291IsoOfTwoCell {W : EtaleStackPseudofunctor S1726K}
    {T : SchemeOverField S1726K}
    {F G : Pseudofunctor.StrongTrans W (S1743Y T)} (alpha : F ⟶ G) :
    Nonempty (Iso F G) :=
  S1911Val_isoOfValEq (fun U a => S2291Val_eq_of_twoCell alpha U a)

/-! ## 3. The collapse condition, the conditional lift and its weak presentation -/

/-- A test leg collapses two distinct points of the test stack. -/
def S2291Collapse {T : SchemeOverField S1726K} {W : EtaleStackPseudofunctor S1726K}
    (v : Pseudofunctor.StrongTrans W (S1743Y T)) : Prop :=
  ∃ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a b : W.obj U),
    a ≠ b ∧ S1911Val v U a = S1911Val v U b

theorem S2291Collapse_of_twoCell {T : SchemeOverField S1726K}
    {W : EtaleStackPseudofunctor S1726K}
    {f g : Pseudofunctor.StrongTrans W (S1743Y T)} (m : f ⟶ g) :
    S2291Collapse f ↔ S2291Collapse g := by
  constructor
  · rintro ⟨U, a, b, hne, hval⟩
    refine ⟨U, a, b, hne, ?_⟩
    rw [← S2291Val_eq_of_twoCell m U a, ← S2291Val_eq_of_twoCell m U b]
    exact hval
  · rintro ⟨U, a, b, hne, hval⟩
    refine ⟨U, a, b, hne, ?_⟩
    rw [S2291Val_eq_of_twoCell m U a, S2291Val_eq_of_twoCell m U b]
    exact hval

/-- The conditional lift: first summand on collapsing test legs, second summand
otherwise.  It is a legitimate weak lift but it is not section based. -/
noncomputable def S2291CondLift {T : SchemeOverField S1726K}
    {W : EtaleStackPseudofunctor S1726K}
    (v : Pseudofunctor.StrongTrans W (S1743Y T)) :
    Pseudofunctor.StrongTrans W (S1743Y (S1850P T)) := by
  classical
  exact
    if h : S2291Collapse v then
      Pseudofunctor.StrongTrans.vcomp v (S1850InlStrong T)
    else
      Pseudofunctor.StrongTrans.vcomp v (S2291InrStrong T)

theorem S2291CondLift_inl {T : SchemeOverField S1726K}
    {W : EtaleStackPseudofunctor S1726K}
    {v : Pseudofunctor.StrongTrans W (S1743Y T)} (h : S2291Collapse v) :
    S2291CondLift v = Pseudofunctor.StrongTrans.vcomp v (S1850InlStrong T) := by
  rw [S2291CondLift]
  exact dif_pos h

theorem S2291CondLift_inr {T : SchemeOverField S1726K}
    {W : EtaleStackPseudofunctor S1726K}
    {v : Pseudofunctor.StrongTrans W (S1743Y T)} (h : ¬ S2291Collapse v) :
    S2291CondLift v = Pseudofunctor.StrongTrans.vcomp v (S2291InrStrong T) := by
  rw [S2291CondLift]
  exact dif_neg h

/-- The weak base-change presentation of the identity map whose recorded lift is
the conditional lift. -/
noncomputable def S2291PathPresentation (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    EtaleStackBaseChangePresentation
      (map := Pseudofunctor.StrongTrans.id S1850X.fiber) T q where
  pullbackScheme := S1850P T
  projection := S1850Fold T
  projectionMap := S1850FoldMap T
  toSource := Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q
  commutes := S1850Commutes T q
  isPullback :=
    { lift := fun W c => S2291CondLift (T := T) c.toY
      liftToX := fun W c => by
        by_cases h : S2291Collapse c.toY
        · rw [S2291CondLift, dif_pos h]
          exact S1850ConeIsoX T c.toX c.toY q c.commutes
        · rw [S2291CondLift, dif_neg h]
          exact S2291ConeIsoX_inr T c.toX c.toY q c.commutes
      liftToY := fun W c => by
        by_cases h : S2291Collapse c.toY
        · rw [S2291CondLift, dif_pos h]
          exact S1850ConeIsoY T c.toY
        · rw [S2291CondLift, dif_neg h]
          exact S2291ConeIsoY_inr T c.toY
      liftTwoCell := fun W s t m => by
        have hiff := S2291Collapse_of_twoCell (T := T) m.toY
        by_cases hs : S2291Collapse s.toY
        · have ht := hiff.mp hs
          rw [S2291CondLift, dif_pos hs, S2291CondLift, dif_pos ht]
          exact Pseudofunctor.StrongTrans.whiskerRight m.toY (S1850InlStrong T)
        · have ht : ¬ S2291Collapse t.toY := fun h => hs (hiff.mpr h)
          rw [S2291CondLift, dif_neg hs, S2291CondLift, dif_neg ht]
          exact Pseudofunctor.StrongTrans.whiskerRight m.toY (S2291InrStrong T)
      liftTwoCell_toX := fun W s t m => by
        exact @Subsingleton.elim _
          (S2185SubsingletonRepresentable (W := W) (S := S1726AffineOver)
            (f := Pseudofunctor.StrongTrans.vcomp
              (S2291CondLift (T := T) s.toY)
              (Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q))
            (g := Pseudofunctor.StrongTrans.vcomp
              (S2291CondLift (T := T) t.toY)
              (Pseudofunctor.StrongTrans.vcomp (S1850FoldStrong T) q))) _ _
      liftTwoCell_toY := fun W s t m => by
        exact @Subsingleton.elim _
          (S2185SubsingletonRepresentable (W := W) (S := T)
            (f := Pseudofunctor.StrongTrans.vcomp
              (S2291CondLift (T := T) s.toY) (S1850FoldStrong T))
            (g := Pseudofunctor.StrongTrans.vcomp
              (S2291CondLift (T := T) t.toY) (S1850FoldStrong T))) _ _
      twoCell_ext := fun W first second alpha beta h1 h2 => by
        exact @Subsingleton.elim _
          (S2185SubsingletonRepresentable (W := W) (S := S1850P T)
            (f := first) (g := second)) _ _ }

noncomputable def S2291PathFiniteEtale :
    EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.id S1850X.fiber) where
  baseChange T q := S2291PathPresentation T q
  hasProperty T q := S1850Fold_finiteEtale T

/-- The weak target cover refuting uniform graph compatibility. -/
noncomputable def S2291PathCover : S1728Cover :=
  OrbicurveFiniteEtaleCover.mk S1850X (Pseudofunctor.StrongTrans.id S1850X.fiber)
    S2291PathFiniteEtale


/-! ## 4. The endomorphism used to separate the two sections -/

abbrev S2291T₀ : SchemeOverField S1726K := S1726AffineOver

abbrev S2291T : SchemeOverField S1726K := S1850P S2291T₀

noncomputable def S2291Diag : S2291T ⟶ S2291T :=
  Over.homMk (show Over.left S2291T ⟶ Over.left S2291T from
    Limits.coprod.desc
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)) (by
    show Limits.coprod.desc
        (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
        (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T) ≫
      Over.hom (S1850P S2291T₀) = Over.hom (S1850P S2291T₀)
    rw [show Over.hom (S1850P S2291T₀) =
      Limits.coprod.desc (Over.hom S2291T₀) (Over.hom S2291T₀) from rfl]
    rw [Limits.coprod.desc_comp]
    simp)

theorem S2291Diag_idem : S2291Diag ≫ S2291Diag = S2291Diag := by
  apply Over.OverMorphism.ext
  show Limits.coprod.desc
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T) ≫
    Limits.coprod.desc
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T) =
    Limits.coprod.desc
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
  rw [Limits.coprod.desc_comp]
  simp

theorem S2291Diag_ne_id : S2291Diag ≠ 𝟙 S2291T := by
  intro heq
  rw [S2291Diag] at heq
  have hleft : Over.Hom.left S2291Diag = Over.Hom.left (𝟙 S2291T) := congrArg Over.Hom.left heq
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  let x : ↥(Over.left S2291T₀) :=
    Classical.choice (show Nonempty ↥(Over.left S2291T₀) from hne)
  let z : ↥(Over.left S2291T) :=
    (Limits.coprod.inr : Over.left S2291T₀ ⟶ Over.left S2291T) x
  have hx := congrArg (fun f : Over.left S2291T ⟶ Over.left S2291T => f z) hleft
  change (Limits.coprod.desc
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
      (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)) z =
    (𝟙 (Over.left S2291T)) z at hx
  rw [show (Limits.coprod.desc
        (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
        (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)) z =
      (Limits.coprod.inr ≫ Limits.coprod.desc
        (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)
        (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T)) x from rfl,
    Limits.coprod.inr_desc] at hx
  exact (AlgebraicGeometry.inl_ne_inr (X := Over.left S2291T₀) (Y := Over.left S2291T₀)
    x x) hx

theorem S2291T_nonempty : Nonempty ↥(Over.left S2291T) := by
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  let x : ↥(Over.left S2291T₀) :=
    Classical.choice (show Nonempty ↥(Over.left S2291T₀) from hne)
  exact ⟨(Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T) x⟩

theorem S2291Diag_inl_ne_inr :
    S2291Diag ≫ S1850Inl S2291T ≠ S2291Diag ≫ S1850Inr S2291T := by
  intro hEq
  have hleft : Over.Hom.left (S2291Diag ≫ S1850Inl S2291T) =
      Over.Hom.left (S2291Diag ≫ S1850Inr S2291T) := congrArg Over.Hom.left hEq
  rw [Over.comp_left, Over.comp_left] at hleft
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  let x : ↥(Over.left S2291T₀) :=
    Classical.choice (show Nonempty ↥(Over.left S2291T₀) from hne)
  let z : ↥(Over.left S2291T) :=
    (Limits.coprod.inl : Over.left S2291T₀ ⟶ Over.left S2291T) x
  have hx := congrArg (fun f : Over.left S2291T ⟶ Over.left (S1850P S2291T) => f z) hleft
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, S1850Inl_left, S1850Inr_left] at hx
  exact (AlgebraicGeometry.inl_ne_inr (X := Over.left S2291T) (Y := Over.left S2291T)
    _ _) hx

/-! ## 5. The collapse witnesses -/

theorem S2291Val_id (T : SchemeOverField S1726K)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (a : (S1743Y T).obj U) :
    S1911Val (Pseudofunctor.StrongTrans.id (S1743Y T)) U a = a.as := by
  show (((Pseudofunctor.StrongTrans.id (S1743Y T)).app U).toFunctor.obj a).as = a.as
  rw [show (Pseudofunctor.StrongTrans.id (S1743Y T)).app U = 𝟙 ((S1743Y T).obj U) from rfl]
  rw [CategoryTheory.Cat.Hom.id_toFunctor]
  rfl

theorem S2291Collapse_id (T : SchemeOverField S1726K) :
    ¬ S2291Collapse (Pseudofunctor.StrongTrans.id (S1743Y T)) := by
  rintro ⟨U, a, b, hne, hval⟩
  rw [S2291Val_id, S2291Val_id] at hval
  exact hne (Discrete.ext hval)

theorem S2291Collapse_diag :
    S2291Collapse (S1742StrongTransOfHom (F := S1726K) S2291Diag) := by
  refine ⟨LocallyDiscrete.mk (Opposite.op S2291T), Discrete.mk (𝟙 S2291T),
    Discrete.mk S2291Diag, ?_, ?_⟩
  · intro h
    have h' : (𝟙 S2291T : S2291T ⟶ S2291T) = S2291Diag := congrArg Discrete.as h
    exact S2291Diag_ne_id h'.symm
  · rw [S2185Val_strongTransOfHom, S2185Val_strongTransOfHom, S2291Diag_idem,
      Category.id_comp]

theorem S2291Collapse_fold :
    S2291Collapse (T := S2291T) (S1850FoldStrong S2291T) := by
  refine ⟨LocallyDiscrete.mk (Opposite.op S2291T), Discrete.mk (S1850Inl S2291T),
    Discrete.mk (S1850Inr S2291T), ?_, ?_⟩
  · intro h
    exact (S1852Inl_ne_inr S2291T S2291T_nonempty) (congrArg Discrete.as h)
  · rw [S2185Val_strongTransOfHom, S2185Val_strongTransOfHom,
      S1850Inl_fold, S2291Inr_fold]

/-! ## 6. The failure datum -/

noncomputable abbrev S2291F : S1728CoverMap S2291PathCover S2291PathCover :=
  S1641CoverMapId S2291PathCover

noncomputable abbrev S2291PtA :
    Pseudofunctor.StrongTrans (S1743Y S2291T) S1850X.fiber :=
  Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom (S1850Fold S2291T₀))
    S1733BasePoint

noncomputable abbrev S2291PtC :
    Pseudofunctor.StrongTrans (S1743Y S2291T) S1850X.fiber :=
  S2130PtC S2291F S2291T S2291PtA

noncomputable def S2291Cone :
    (S2130BaseSquare S2291F S2291F S2291T S2291PtA).Cone (S1743Y S2291T) where
  toX := Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom S2291Diag) S2291PtC
  toY := S1742StrongTransOfHom S2291Diag
  commutes := Pseudofunctor.StrongTrans.rightUnitor
    (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom S2291Diag) S2291PtC)

theorem S2291ConeToY_eq :
    S1742HomOfStrongTrans (F := S1726K) S2291Cone.toY = S2291Diag :=
  S1742HomOfStrongTrans_strongTransOfHom S2291Diag

theorem S2291Graph_eq :
    S2130Graph S2291F S2291F S2291T S2291PtA = S1850Inr S2291T := by
  rw [S2130Graph, S2130GraphSite]
  change S1742HomOfStrongTrans
    (S2291CondLift (T := S2291T)
      (Pseudofunctor.StrongTrans.id (S1743Y S2291T))) = S1850Inr S2291T
  rw [S2291CondLift_inr (S2291Collapse_id S2291T)]
  exact S1742HomOfStrongTrans_strongTransOfHom (S1850Inr S2291T)

theorem S2291Phi_eq :
    S2130Phi S2291F S2291F S2291T S2291PtA =
      S1850Fold S2291T ≫ S1850Inl S2291T := by
  rw [S2130Phi, S2130PhiSite]
  change S1742HomOfStrongTrans
    (S2291CondLift (T := S2291T) (S1850FoldStrong S2291T)) =
      S1850Fold S2291T ≫ S1850Inl S2291T
  rw [S2291CondLift_inl S2291Collapse_fold, S2130HomOfStrongTrans_vcomp,
    S1742HomOfStrongTrans_strongTransOfHom, S1742HomOfStrongTrans_strongTransOfHom]

/-- Graph compatibility fails at the pathological target cover. -/
theorem S2291GraphLift_false :
    ¬ Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp S2291Cone.toY
          (S1742StrongTransOfHom (S2130Graph S2291F S2291F S2291T S2291PtA)))
        ((S2130PC S2291F S2291T S2291PtA).isPullback.lift
          (S1743Y S2291T)
          (S2240ConePC S2291F S2291F S2291T S2291PtA S2291Cone))) := by
  rintro ⟨e⟩
  have hEq := S1742HomOfStrongTrans_congr e
  have hL : S1742HomOfStrongTrans (F := S1726K)
      (Pseudofunctor.StrongTrans.vcomp S2291Cone.toY
        (S1742StrongTransOfHom (S2130Graph S2291F S2291F S2291T S2291PtA))) =
      S2291Diag ≫ S1850Inr S2291T := by
    rw [S2130HomOfStrongTrans_vcomp, S1742HomOfStrongTrans_strongTransOfHom,
      S2291ConeToY_eq, S2291Graph_eq]
  have hR : S1742HomOfStrongTrans (F := S1726K)
      ((S2130PC S2291F S2291T S2291PtA).isPullback.lift
        (S1743Y S2291T)
        (S2240ConePC S2291F S2291F S2291T S2291PtA S2291Cone)) =
      S2291Diag ≫ S1850Inl S2291T := by
    change S1742HomOfStrongTrans (F := S1726K)
      (S2291CondLift (T := S2291T) (S1742StrongTransOfHom S2291Diag)) =
        S2291Diag ≫ S1850Inl S2291T
    rw [S2291CondLift_inl S2291Collapse_diag, S2130HomOfStrongTrans_vcomp,
      S1742HomOfStrongTrans_strongTransOfHom, S1742HomOfStrongTrans_strongTransOfHom]
  rw [hL, hR] at hEq
  exact S2291Diag_inl_ne_inr hEq.symm

theorem S2291NotGraphCompatAt :
    ¬ S2269GraphCompatAt S2291PathCover S2291PathCover := by
  intro h
  exact S2291GraphLift_false
    ((h S2291PathCover S2291F S2291F S2291T S2291PtA).2 (S1743Y S2291T) S2291Cone)

theorem S2291NotGraphCompatAll : ¬ S2269GraphCompatAll :=
  fun h => S2291NotGraphCompatAt (h S2291PathCover S2291PathCover)

theorem S2291NotFirstMissing : ¬ S2269FirstMissing := S2291NotGraphCompatAll

/-- The S2185 strict-cone comparison fails at the same datum. -/
theorem S2291StrictCone_false :
    ¬ Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB S2291F S2291F S2291T S2291PtA).isPullback.lift (S1743Y S2291T)
            (S2185ConePB S2291F S2291F S2291T S2291PtA S2291Cone))
          (S1742StrongTransOfHom (S2130Phi S2291F S2291F S2291T S2291PtA)))
        (Pseudofunctor.StrongTrans.vcomp S2291Cone.toY
          (S1742StrongTransOfHom (S2130Graph S2291F S2291F S2291T S2291PtA)))) := by
  rintro ⟨e⟩
  have hEq := S1742HomOfStrongTrans_congr e
  have hL : S1742HomOfStrongTrans (F := S1726K)
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB S2291F S2291F S2291T S2291PtA).isPullback.lift (S1743Y S2291T)
          (S2185ConePB S2291F S2291F S2291T S2291PtA S2291Cone))
        (S1742StrongTransOfHom (S2130Phi S2291F S2291F S2291T S2291PtA))) =
      (S2291Diag ≫ S1850Inl S2291T) ≫ (S1850Fold S2291T ≫ S1850Inl S2291T) := by
    change S1742HomOfStrongTrans (F := S1726K)
      (Pseudofunctor.StrongTrans.vcomp
        (S2291CondLift (T := S2291T) (S1742StrongTransOfHom S2291Diag))
        (S1742StrongTransOfHom (S2130Phi S2291F S2291F S2291T S2291PtA))) =
      (S2291Diag ≫ S1850Inl S2291T) ≫ (S1850Fold S2291T ≫ S1850Inl S2291T)
    rw [S2130HomOfStrongTrans_vcomp, S2291CondLift_inl S2291Collapse_diag,
      S2130HomOfStrongTrans_vcomp, S1742HomOfStrongTrans_strongTransOfHom,
      S1742HomOfStrongTrans_strongTransOfHom, S2291Phi_eq,
      S1742HomOfStrongTrans_strongTransOfHom]
  have hR : S1742HomOfStrongTrans (F := S1726K)
      (Pseudofunctor.StrongTrans.vcomp S2291Cone.toY
        (S1742StrongTransOfHom (S2130Graph S2291F S2291F S2291T S2291PtA))) =
      S2291Diag ≫ S1850Inr S2291T := by
    rw [S2130HomOfStrongTrans_vcomp, S1742HomOfStrongTrans_strongTransOfHom,
      S2291ConeToY_eq, S2291Graph_eq]
  rw [hL, hR] at hEq
  have hsimp : (S2291Diag ≫ S1850Inl S2291T) ≫ (S1850Fold S2291T ≫ S1850Inl S2291T)
      = S2291Diag ≫ S1850Inl S2291T := by
    calc (S2291Diag ≫ S1850Inl S2291T) ≫ (S1850Fold S2291T ≫ S1850Inl S2291T)
        = (S2291Diag ≫ (S1850Inl S2291T ≫ S1850Fold S2291T)) ≫ S1850Inl S2291T := by
          simp only [Category.assoc]
      _ = (S2291Diag ≫ 𝟙 S2291T) ≫ S1850Inl S2291T := by rw [S1850Inl_fold]
      _ = S2291Diag ≫ S1850Inl S2291T := by simp
  rw [hsimp] at hEq
  exact S2291Diag_inl_ne_inr hEq

theorem S2291NotStrictConeIso : ¬ S2185StrictConeIso := by
  intro h
  exact S2291StrictCone_false
    (h S2291PathCover S2291PathCover S2291PathCover S2291F S2291F S2291T S2291PtA
      (S1743Y S2291T) S2291Cone)

theorem S2291NotS2185FirstMissing : ¬ S2185FirstMissing := S2291NotStrictConeIso

/-! ## 7. Checks and axiom audit -/

#check S2291PathCover
#check S2291PathPresentation
#check S2291CondLift
#check S2291Collapse
#check S2291Diag
#check S2291Cone
#check S2291Graph_eq
#check S2291Phi_eq
#check S2291GraphLift_false
#check S2291NotGraphCompatAt
#check S2291NotGraphCompatAll
#check S2291NotFirstMissing
#check S2291StrictCone_false
#check S2291NotStrictConeIso
#check S2291NotS2185FirstMissing

#print axioms S2291Inr_fold
#print axioms S2291IsoOfTwoCell
#print axioms S2291PathPresentation
#print axioms S2291PathCover
#print axioms S2291Collapse_of_twoCell
#print axioms S2291Diag_ne_id
#print axioms S2291Diag_inl_ne_inr
#print axioms S2291Collapse_diag
#print axioms S2291Collapse_fold
#print axioms S2291Graph_eq
#print axioms S2291Phi_eq
#print axioms S2291GraphLift_false
#print axioms S2291NotGraphCompatAll
#print axioms S2291NotFirstMissing
#print axioms S2291StrictCone_false
#print axioms S2291NotStrictConeIso
#print axioms S2291NotS2185FirstMissing

end LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual