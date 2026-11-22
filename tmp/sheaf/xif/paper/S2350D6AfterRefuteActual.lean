/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2350
-/

import tmp.sheaf.xif.paper.S2291UniformGraphCompatActual

/-!
# S2350: the S2130 concrete two-pullback is FALSE at the S2291 datum

## The question

S2291 refuted the uniform graph-compatibility statement S2269GraphCompatAll and, with it,
the S2185 strict-cone comparison S2185StrictConeIso, at an explicit weak target cover
S2291PathCover.  It deliberately left the D6 target S2130ConcreteTwoPullback untouched:
that target only asks, for every datum, for the *existence* of a
EtalePseudofunctorSquare.TwoPullbackWitness for the S2130 base square, which is implied by
(hence weaker than) asking the recorded presentation lift to agree with the graph
candidate, the input of S2185.

The question settled here: does S2130ConcreteTwoPullback nevertheless hold at the S2291
datum?  The answer is NO.

## The counterexample

Take the S2291 datum

  A = B = C = S2291PathCover,  f = g = S2291F = id,  T = S2291T,  ptA = S2291PtA.

At this datum S2291 computes the two base legs of the S2130 square:

  S2130Phi   = S1850Fold S2291T ; S1850Inl S2291T   (S2291Phi_eq)
  S2130Graph = S1850Inr S2291T                      (S2291Graph_eq)

and S2130P f g T ptA is by construction the strict fibre product of these two maps over
the pullback scheme T + T of the C-presentation.  The projections therefore satisfy

  S2130P_fst ; (fold ; inl) = S2130P_snd ; inr                  (S2350P_split_cond).

Consequently the underlying scheme of S2130P has *no points* (S2350P_isEmpty): a point
would produce a point x of T with inl (fold x) = inr x in T + T, contradicting
AlgebraicGeometry.inl_ne_inr.  Although S2130P is by construction the strict fibre product
of S2130Phi and S2130Graph, the S2130 square itself is therefore not a two-pullback:

* S2350NoSplitOfInlInr: the second projection of any square whose first leg is
  (fold ; inl) and whose second leg is inr cannot be split;
* a witness would split it: its lift of the explicit cone S2350Cone (toX = the C-point,
  toY = the identity) has underlying map h with h ; S2130P_snd = 1
  (S2350liftToY_apply);
* combining the two with the pullback condition gives h ; S2130P_fst ; (fold ; inl) =
  inr, i.e. an identification of the two summands of T + T.

Therefore

* S2350NotWitnessAt: the instance type at the S2291 datum is empty;
* S2350NotConcreteTwoPullback, S2350NotNonemptyConcreteTwoPullback, S2350IsEmpty: the
  uniform target S2130ConcreteTwoPullback has no inhabitant at all.

## What this does and does not say

* The D6 target is not changed: the statement refuted here is exactly the recorded
  S2130ConcreteTwoPullback, with its own apex S2130P.
* The *geometric* base-change statement is not refuted: at the very same datum a genuine
  EtaleStackBaseChangePresentation of the same map at the same point exists, namely
  S2291PathPresentation S2291T at the S2130 C-point (S2350PresentationAtDatum).  What
  fails is the recorded S2130 square: its apex S2130P is built from the recorded
  presentation lifts S2130Phi and S2130Graph, and at a weak cover these need not be the
  two projections of any fibre product.
* Hence D6 cannot be completed through S2130ConcreteTwoPullback as recorded, and the
  failure is not a missing coherence 2-cell of the same shape: the target itself is
  false.  The repair available from the recorded data is the per-cover one of S2240
  (strong or coherent target covers), where the witness is constructed once the target
  cover is fixed and coherent; the uniform statement has to be replaced by that
  restricted family, not proved.

## Honesty

No sorry, no admit, no new axiom, no change of any recorded definition and no change of
the D6 target.  The counterexample is produced by the recorded definitions themselves.
Axiom footprint: propext, Classical.choice, Quot.sound.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

namespace LeanFormal.IUT.XiFPaper.S2350D6AfterRefuteActual

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
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
open LeanFormal.IUT.XiFPaper.S2185ConcreteTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2269GraphCompatActual
open LeanFormal.IUT.XiFPaper.S2291UniformGraphCompatActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

universe u

/-! ## 1. The obstruction: a pullback of (fold ; inl) against inr cannot be split -/

/-- The obstruction.  Let pX and pY form a square with base legs (fold ; inl) and inr,
i.e. the two composites agree.  Then pY has no section: a section h would give
h ; pX ; (fold ; inl) = inr, and evaluating at a point of T would identify a point of the
first summand of T + T with a point of the second. -/
theorem S2350NoSplitOfInlInr {T : SchemeOverField S1726K}
    (hT : Nonempty ↥(Over.left T)) {P : SchemeOverField S1726K}
    (pX : P ⟶ S1850P T) (pY : P ⟶ T)
    (hcond : pX ≫ (S1850Fold T ≫ S1850Inl T) = pY ≫ S1850Inr T) :
    ¬ ∃ h : T ⟶ P, h ≫ pY = 𝟙 T := by
  rintro ⟨h, hh⟩
  obtain ⟨z⟩ := hT
  have h1 : (h ≫ pX) ≫ (S1850Fold T ≫ S1850Inl T) = S1850Inr T := by
    calc (h ≫ pX) ≫ (S1850Fold T ≫ S1850Inl T)
        = h ≫ (pX ≫ (S1850Fold T ≫ S1850Inl T)) := Category.assoc _ _ _
      _ = h ≫ (pY ≫ S1850Inr T) := by rw [hcond]
      _ = (h ≫ pY) ≫ S1850Inr T := (Category.assoc _ _ _).symm
      _ = 𝟙 T ≫ S1850Inr T := by rw [hh]
      _ = S1850Inr T := Category.id_comp _
  have h1' : (Over.Hom.left h ≫ Over.Hom.left pX) ≫
      (Over.Hom.left (S1850Fold T) ≫ Over.Hom.left (S1850Inl T)) =
      Over.Hom.left (S1850Inr T) := by
    have := congrArg (fun f : T ⟶ S1850P T => Over.Hom.left f) h1
    simpa only [Over.comp_left] using this
  have hpt := congrArg
    (fun f : Over.left T ⟶ Over.left (S1850P T) => f z) h1'
  simp only [Scheme.Hom.comp_apply, S1850Inl_left, S1850Inr_left, S1850Fold_left] at hpt
  exact (AlgebraicGeometry.inl_ne_inr (X := Over.left T) (Y := Over.left T)
    (Limits.coprod.desc (𝟙 (Over.left T)) (𝟙 (Over.left T))
      (Over.Hom.left pX (Over.Hom.left h z))) z) hpt

/-! ## 2. The cone whose lift the witness would have to provide -/

/-- The test cone over the S2130 base square at the S2291 datum: its first leg is the
C-point itself and its second leg is the identity.  Both composites in the square are
therefore the C-point up to unitors. -/
noncomputable def S2350Cone :
    (S2130BaseSquare S2291F S2291F S2291T S2291PtA).Cone (S1743Y S2291T) where
  toX := S2291PtC
  toY := Pseudofunctor.StrongTrans.id (S1743Y S2291T)
  commutes := (S1756RightUnitorIso S2291PtC).trans (S1756LeftUnitorIso S2291PtC).symm

/-- The pullback condition of the S2130 apex, as an equation of scheme morphisms. -/
theorem S2350P_fst_Phi :
    S2130P_fst S2291F S2291F S2291T S2291PtA ≫ S2130Phi S2291F S2291F S2291T S2291PtA =
      S2130P_snd S2291F S2291F S2291T S2291PtA ≫ S2130Graph S2291F S2291F S2291T S2291PtA := by
  apply Over.OverMorphism.ext
  exact Limits.pullback.condition

/-- A witness would split the second projection of the S2130 apex: the lift of
S2350Cone compared with the identity cone gives a scheme morphism h with
h ; S2130P_snd = 1. -/
theorem S2350liftToY_apply
    (w : (S2130BaseSquare S2291F S2291F S2291T S2291PtA).TwoPullbackWitness) :
    S1742HomOfStrongTrans (w.lift (S1743Y S2291T) S2350Cone) ≫
      S2130P_snd S2291F S2291F S2291T S2291PtA = 𝟙 S2291T := by
  have e := w.liftToY (S1743Y S2291T) S2350Cone
  have h := S1742HomOfStrongTrans_congr e
  rw [show (S2130BaseSquare S2291F S2291F S2291T S2291PtA).toY =
      S2130P_snd_site S2291F S2291F S2291T S2291PtA from rfl] at h
  rw [show S2130P_snd_site S2291F S2291F S2291T S2291PtA =
      S1742StrongTransOfHom (S2130P_snd S2291F S2291F S2291T S2291PtA) from rfl] at h
  rw [S2130HomOfStrongTrans_vcomp, S1742HomOfStrongTrans_strongTransOfHom] at h
  have hR : S1742HomOfStrongTrans S2350Cone.toY = 𝟙 S2291T := rfl
  rw [hR] at h
  exact h

/-- The S2291 computation of the two base legs, in the form used by the obstruction. -/
theorem S2350P_split_cond :
    S2130P_fst S2291F S2291F S2291T S2291PtA ≫
        (S1850Fold S2291T ≫ S1850Inl S2291T) =
      S2130P_snd S2291F S2291F S2291T S2291PtA ≫ S1850Inr S2291T := by
  rw [← S2291Phi_eq, ← S2291Graph_eq]
  exact S2350P_fst_Phi

/-! ## 3. The refutation at the S2291 datum, and its uniform form -/

/-- **The S2130 base square has no two-pullback witness at the S2291 datum.** -/
theorem S2350NotWitnessAt :
    ¬ Nonempty ((S2130BaseSquare S2291F S2291F S2291T S2291PtA).TwoPullbackWitness) := by
  rintro ⟨w⟩
  refine S2350NoSplitOfInlInr S2291T_nonempty
    (S2130P_fst S2291F S2291F S2291T S2291PtA)
    (S2130P_snd S2291F S2291F S2291T S2291PtA) S2350P_split_cond
    ⟨S1742HomOfStrongTrans (w.lift (S1743Y S2291T) S2350Cone), S2350liftToY_apply w⟩

/-- Consequently the underlying scheme of the S2130 apex has no points at this datum. -/
theorem S2350P_isEmpty :
    IsEmpty ↥(Over.left (S2130P S2291F S2291F S2291T S2291PtA)) := by
  constructor
  intro p
  have hpt := congrArg
    (fun f : Over.left (S2130P S2291F S2291F S2291T S2291PtA) ⟶
        Over.left (S1850P S2291T) => f p)
    (congrArg (fun f : S2130P S2291F S2291F S2291T S2291PtA ⟶ S1850P S2291T =>
      Over.Hom.left f) S2350P_split_cond)
  simp only [Scheme.Hom.comp_apply, S1850Inl_left, S1850Inr_left, S1850Fold_left,
    Over.comp_left] at hpt
  exact (AlgebraicGeometry.inl_ne_inr (X := Over.left S2291T) (Y := Over.left S2291T)
    (Limits.coprod.desc (𝟙 (Over.left S2291T)) (𝟙 (Over.left S2291T))
      (Over.Hom.left (S2130P_fst S2291F S2291F S2291T S2291PtA) p))
    (Over.Hom.left (S2130P_snd S2291F S2291F S2291T S2291PtA) p)) hpt

theorem S2350NotConcreteTwoPullback : S2130ConcreteTwoPullback → False :=
  fun h => S2350NotWitnessAt
    ⟨h S2291PathCover S2291PathCover S2291PathCover S2291F S2291F S2291T S2291PtA⟩

theorem S2350NotNonemptyConcreteTwoPullback : ¬ Nonempty S2130ConcreteTwoPullback := by
  rintro ⟨h⟩
  exact S2350NotConcreteTwoPullback h

/-- **The uniform D6 target of S2130 is an empty type.** -/
theorem S2350IsEmpty : IsEmpty S2130ConcreteTwoPullback :=
  ⟨S2350NotConcreteTwoPullback⟩

/-! ## 4. Contrast: the geometric base-change presentation exists at the same datum -/

/-- **The geometric statement is not refuted.**  At the very same datum, the S2291
presentation provides an actual base-change presentation of the same map at the same
point.  What fails above is the recorded S2130 apex, not the existence of a presentation.
-/
theorem S2350PresentationAtDatum :
    Nonempty (EtaleStackBaseChangePresentation (S2291F).map S2291T
      (S2130PtC S2291F S2291T S2291PtA)) :=
  ⟨S2291PathPresentation S2291T (S2130PtC S2291F S2291T S2291PtA)⟩

/-! ## 5. Checks and axiom audit -/

#check S2350NoSplitOfInlInr
#check S2350Cone
#check S2350P_fst_Phi
#check S2350liftToY_apply
#check S2350P_split_cond
#check S2350NotWitnessAt
#check S2350P_isEmpty
#check S2350NotConcreteTwoPullback
#check S2350NotNonemptyConcreteTwoPullback
#check S2350IsEmpty
#check S2350PresentationAtDatum

#print axioms S2350NoSplitOfInlInr
#print axioms S2350Cone
#print axioms S2350P_fst_Phi
#print axioms S2350liftToY_apply
#print axioms S2350P_split_cond
#print axioms S2350NotWitnessAt
#print axioms S2350P_isEmpty
#print axioms S2350NotConcreteTwoPullback
#print axioms S2350NotNonemptyConcreteTwoPullback
#print axioms S2350IsEmpty
#print axioms S2350PresentationAtDatum

end LeanFormal.IUT.XiFPaper.S2350D6AfterRefuteActual
