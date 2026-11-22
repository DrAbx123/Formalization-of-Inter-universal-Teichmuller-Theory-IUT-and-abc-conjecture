/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2269
-/

import tmp.sheaf.xif.paper.S2240StrictConeIsoActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual

/-!
# S2269: graph compatibility, a strictly weaker coherence for the S2185 comparison

## The question

S2240 settled the uniform strong-C input for the S2185 strict-cone comparison:
the hypothesis S2240CPresentationConeEssSurj (every C-presentation is
cone-essentially-surjective) is FALSE at S1850's doubled cover, so no uniform proof
of S2185StrictConeIso can pass through the full 2-universal property.  S2240 left
S2185StrictConeIso itself unproved and unrefuted, and named the missing content
"graph compatibility of the recorded presentation lift".

This file isolates that content and proves what can be proved about it.

## Definitions

For fixed data f, g, T, ptA the comparison of S2185 asks for
PB.lift c ; y(Phi) ~= c.toY ; y(Graph).  We split this into the two assertions
that each of the two candidates is *the* recorded PC-lift of the transported cone
cPC = S2240ConePC c:

* S2269PhiLiftData :  PB.lift c ; y(Phi) ~= PC.lift cPC,
* S2269GraphLiftData:  c.toY ; y(Graph)   ~= PC.lift cPC.

S2269GraphCompatData is their conjunction; S2269GraphCompatAt B C quantifies it
over all A, f, g, T, ptA at a fixed target cover C and test cover B; and
S2269GraphCompatAll is the uniform form over all B, C.

## What is proved

1. S2269ComparisonData_of_graphCompat: graph compatibility implies the S2185
   comparison (one trans of isomorphisms).
2. S2269GraphCompatData_of_coneEssSurj and
   S2269GraphCompatAt_of_coneEssSurjAt: full cone essential surjectivity of the
   PC-presentation implies graph compatibility.  Thus graph compatibility is a
   weakening of the PC-strong input.
3. S2269GraphCompatAt_of_strongCover / S2269GraphCompatAt_of_coherent: graph
   compatibility holds for every strong or coherent target cover, recovering the
   S2240 closed branch through the new interface.
4. S2269GraphCompatAt_of_doubledTarget: if the TARGET cover is S1850's doubled
   cover, graph compatibility holds for EVERY source cover B.  The proof computes
   the doubled presentation explicitly: its lift is c.toY ; inl, the graph section
   is inl, and the strict comparison map is PB.projection ; inl, so both
   candidates reduce to c.toY ; inl (the first via PB.liftToY, the second
   definitionally).
5. S2269NotConeEssSurjAt_doubled, S2269StrictlyWeakerThanPCStrongness:
   at B = C = S1850DoubledCover graph compatibility holds while the PC-strong
   input S2240ConeEssSurjAt fails.  Hence graph compatibility is strictly weaker
   than PC-strongness.
6. S2269DoubledNoCounterexample: for every source cover B the doubled target
   cover satisfies graph compatibility, hence the S2185 comparison exists for every
   datum at that target cover.  In particular the doubled cover is NOT a
   counterexample to S2185StrictConeIso.

## The exact missing statement

The new exact missing input for the uniform S2185 comparison is
S2269GraphCompatAll = forall B C, S2269GraphCompatAt B C; it implies
S2185StrictConeIso (S2269StrictConeIso_of_graphCompatAll) and is strictly weaker
than the refuted uniform PC-strongness.  It is proved here for strong/coherent target
covers and for the doubled target cover, uniformly in the source; the remaining case
is an arbitrary weak target cover whose recorded base-change witness is neither
coherent nor doubled.  No field of the recorded cover supplies that comparison, and
no fake witness is introduced.

## Axiom footprint

No sorry, no axiom, no change of any recorded definition or of the D6 target.  Every
declaration depends only on propext, Classical.choice and Quot.sound.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

namespace LeanFormal.IUT.XiFPaper.S2269GraphCompatActual

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
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
open LeanFormal.IUT.XiFPaper.S2185ConcreteTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2028SourceSchemeActual
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual

universe u

abbrev S2269Y (S : SchemeOverField S1726K) : EtaleStackPseudofunctor S1726K :=
  schemeRepresentableEtalePseudofunctor S1726K S

/-! ## 1. The graph-compatibility data and the reduction -/

/-- First half of graph compatibility: the PB-lift of the transported base cone,
composed with the strict comparison map Phi, is the recorded PC-lift of the
transported cone cPC. -/
def S2269PhiLiftData {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber) : Prop :=
  forall (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W),
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        ((S2130PC f T ptA).isPullback.lift W (S2240ConePC f g T ptA c)))

/-- Second half of graph compatibility: the graph composite c.toY ; y(Graph) is the
recorded PC-lift of the transported cone cPC.  This is the actual graph section
compatibility of the presentation. -/
def S2269GraphLiftData {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber) : Prop :=
  forall (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W),
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))
        ((S2130PC f T ptA).isPullback.lift W (S2240ConePC f g T ptA c)))

/-- Graph compatibility of the recorded presentation lift, at fixed data. -/
def S2269GraphCompatData {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber) : Prop :=
  S2269PhiLiftData f g T ptA ∧ S2269GraphLiftData f g T ptA

/-- Graph compatibility at a fixed target cover C. -/
def S2269GraphCompatAt (B C : S1728Cover) : Prop :=
  forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber),
    S2269GraphCompatData f g T ptA

/-- The uniform graph-compatibility statement: the exact new missing input for the
uniform S2185 comparison. -/
def S2269GraphCompatAll : Prop :=
  forall B C : S1728Cover, S2269GraphCompatAt B C

/-- The per-data S2185 comparison, isolated from S2185StrictConeIso. -/
def S2269ComparisonData {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber) : Prop :=
  forall (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W),
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA))))

/-- Graph compatibility implies the S2185 comparison, by transitivity through the
recorded PC-lift. -/
theorem S2269ComparisonData_of_graphCompat {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber)
    (h : S2269GraphCompatData f g T ptA) :
    S2269ComparisonData f g T ptA := by
  intro W c
  obtain ⟨ePhi⟩ := h.1 W c
  obtain ⟨eGraph⟩ := h.2 W c
  exact ⟨ePhi.trans eGraph.symm⟩

/-- The uniform S2185 strict-cone comparison from uniform graph compatibility. -/
theorem S2269StrictConeIso_of_graphCompatAll (h : S2269GraphCompatAll) :
    S2185StrictConeIso := by
  intro A B C f g T ptA W c
  exact S2269ComparisonData_of_graphCompat f g T ptA (h B C A f g T ptA) W c

/-- The recorded exact missing statement. -/
def S2269FirstMissing : Prop := S2269GraphCompatAll

/-- Conditional form of the uniform target from the recorded exact missing. -/
theorem S2269StrictConeIso_of_firstMissing (h : S2269FirstMissing) :
    S2185StrictConeIso :=
  S2269StrictConeIso_of_graphCompatAll h

/-- The actual S2130 concrete two-pullback (the D6 geometric target of S2185) from
uniform graph compatibility.  The D6 target itself is unchanged; this is the
consumer theorem of the new sufficient condition. -/
noncomputable def S2269ConcreteTwoPullback_of_graphCompatAll
    (h : S2269GraphCompatAll) : S2130ConcreteTwoPullback :=
  S2185ConcreteTwoPullback_of_strictConeIso
    (S2269StrictConeIso_of_graphCompatAll h)

/-! ## 2. Full cone essential surjectivity implies graph compatibility -/

/-- PC-strongness implies graph compatibility.  Both candidates are lifts of the
transported cone cPC; cone essential surjectivity of the PC-presentation identifies
each of them with the recorded PC-lift.  The comparison isomorphisms are the four
S2240 comparison chains. -/
theorem S2269GraphCompatData_of_coneEssSurj {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber)
    (hC : S1852ConeEssSurj (S2130PC f T ptA)) :
    S2269GraphCompatData f g T ptA := by
  constructor
  · intro W c
    let cPC : (S1852WeakSquare (S2130PC f T ptA)).Cone W :=
      S2240ConePC f g T ptA c
    have h1 : Nonempty
        (Iso
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp
              ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
              (S1742StrongTransOfHom (S2130Phi f g T ptA)))
            (S1852WeakSquare (S2130PC f T ptA)).toX)
          cPC.toX) :=
      ⟨S2240PhiToSource f g T ptA c⟩
    have h2 : Nonempty
        (Iso
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp
              ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
              (S1742StrongTransOfHom (S2130Phi f g T ptA)))
            (S1852WeakSquare (S2130PC f T ptA)).toY)
          cPC.toY) :=
      ⟨S2240PhiToProj f g T ptA c⟩
    exact hC W cPC
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA))) h1 h2
  · intro W c
    let cPC : (S1852WeakSquare (S2130PC f T ptA)).Cone W :=
      S2240ConePC f g T ptA c
    have h3 : Nonempty
        (Iso
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp c.toY
              (S1742StrongTransOfHom (S2130Graph f g T ptA)))
            (S1852WeakSquare (S2130PC f T ptA)).toX)
          cPC.toX) :=
      ⟨S2240GraphToSource f g T ptA c⟩
    have h4 : Nonempty
        (Iso
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp c.toY
              (S1742StrongTransOfHom (S2130Graph f g T ptA)))
            (S1852WeakSquare (S2130PC f T ptA)).toY)
          cPC.toY) :=
      ⟨S2240GraphToProj f g T ptA c⟩
    exact hC W cPC
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA))) h3 h4

/-- Graph compatibility at a fixed target cover from its PC-strongness. -/
theorem S2269GraphCompatAt_of_coneEssSurjAt {B C : S1728Cover}
    (h : S2240ConeEssSurjAt B C) : S2269GraphCompatAt B C := by
  intro A f g T ptA
  exact S2269GraphCompatData_of_coneEssSurj f g T ptA (h A f g T ptA)

/-- The uniform graph-compatibility statement from the (false) uniform PC-strongness:
the implication records that graph compatibility is a weakening, not a consequence of
a consistent strong field. -/
theorem S2269GraphCompatAll_of_coneEssSurj (h : S2240CPresentationConeEssSurj) :
    S2269GraphCompatAll := by
  intro B C
  exact S2269GraphCompatAt_of_coneEssSurjAt
    (fun A f g T ptA => h A B C f g T ptA)

/-- The per-cover S2185 comparison from graph compatibility. -/
theorem S2269ConeIsoAt_of_graphCompatAt {B C : S1728Cover}
    (h : S2269GraphCompatAt B C) : S2240ConeIsoAt B C := by
  intro A f g T ptA W c
  exact S2269ComparisonData_of_graphCompat f g T ptA (h A f g T ptA) W c

/-- Strong target covers satisfy graph compatibility. -/
theorem S2269GraphCompatAt_of_strongCover (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) :
    S2269GraphCompatAt B (StrongCover.cover Cs) :=
  S2269GraphCompatAt_of_coneEssSurjAt (B := B) (C := StrongCover.cover Cs)
    (S2240ConeEssSurjAt_of_strongCover Cs B)

/-- Coherent target covers satisfy graph compatibility. -/
theorem S2269GraphCompatAt_of_coherent (Cs : CoherentCover)
    (B : S1728Cover) :
    S2269GraphCompatAt B (CoherentCover.cover Cs) :=
  S2269GraphCompatAt_of_strongCover Cs.toStrongCover B

/-! ## 3. The doubled cover as target: graph compatibility for every source -/

/-- At the doubled target cover the graph section of the PC-presentation is literally
the first coproduct inclusion S1850Inl. -/
theorem S2269Graph_doubledTarget {A B : S1728Cover}
    (f : S1728CoverMap A S1850DoubledCover)
    (g : S1728CoverMap B S1850DoubledCover)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber) :
    S2130Graph f g T ptA = S1850Inl T := by
  rw [S2130Graph]
  change S1742HomOfStrongTrans
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.id (S2269Y T)) (S1850InlStrong T)) = S1850Inl T
  rw [S2130HomOfStrongTrans_vcomp, S2130HomOfStrongTrans_id,
    S1742HomOfStrongTrans_strongTransOfHom, Category.id_comp]

/-- At the doubled target cover the comparison map Phi is the composite of the
PB-projection with the first coproduct inclusion. -/
theorem S2269Phi_doubledTarget {A B : S1728Cover}
    (f : S1728CoverMap A S1850DoubledCover)
    (g : S1728CoverMap B S1850DoubledCover)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber) :
    S2130Phi f g T ptA = (S2130PB f g T ptA).projection ≫ S1850Inl T := by
  rw [S2130Phi]
  change S1742HomOfStrongTrans
    (Pseudofunctor.StrongTrans.vcomp
      ((S2130PB f g T ptA).projectionMap.transformation) (S1850InlStrong T)) =
    (S2130PB f g T ptA).projection ≫ S1850Inl T
  rw [S2130HomOfStrongTrans_vcomp,
    S2130HomOfStrongTrans_schemeRepresentableMap (S2130PB f g T ptA).projection
      (S2130PB f g T ptA).projectionMap,
    S1742HomOfStrongTrans_strongTransOfHom]

/-- First half of graph compatibility at the doubled target cover: the PB-lift
composed with Phi = PB.projection ; inl reduces, through PB.liftToY, to
c.toY ; inl, which is the recorded PC-lift. -/
theorem S2269PhiLift_doubledTarget {A B : S1728Cover}
    (f : S1728CoverMap A S1850DoubledCover)
    (g : S1728CoverMap B S1850DoubledCover)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        ((S2130PC f T ptA).isPullback.lift W (S2240ConePC f g T ptA c))) := by
  rw [S2269Phi_doubledTarget]
  let ePhi : Iso
      (S1742StrongTransOfHom ((S2130PB f g T ptA).projection ≫ S1850Inl T))
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).projectionMap.transformation) (S1850InlStrong T)) := by
    have h := S2240PhiTransIso f g T ptA
    rw [S2269Phi_doubledTarget] at h
    exact h
  let eLiftY : Iso
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        ((S2130PB f g T ptA).projectionMap.transformation))
      c.toY :=
    (S2130PB f g T ptA).isPullback.liftToY W (S2185ConePB f g T ptA c)
  let I := S1850InlStrong T
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom ((S2130PB f g T ptA).projection ≫ S1850Inl T)))
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).projectionMap.transformation) I)) :=
    S2058WhiskerLeftIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c)) _ _ ePhi
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).projectionMap.transformation) I))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          ((S2130PB f g T ptA).projectionMap.transformation)) I) :=
    (S2058AssociatorIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      ((S2130PB f g T ptA).projectionMap.transformation) I).symm
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          ((S2130PB f g T ptA).projectionMap.transformation)) I)
      (Pseudofunctor.StrongTrans.vcomp c.toY I) :=
    S2058WhiskerRightIso _ _ I eLiftY
  exact ⟨h1.trans (h2.trans h3)⟩

/-- Second half of graph compatibility at the doubled target cover: the recorded
PC-lift is c.toY ; inl by definition, and the graph section is inl. -/
theorem S2269GraphLift_doubledTarget {A B : S1728Cover}
    (f : S1728CoverMap A S1850DoubledCover)
    (g : S1728CoverMap B S1850DoubledCover)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))
        ((S2130PC f T ptA).isPullback.lift W (S2240ConePC f g T ptA c))) := by
  rw [S2269Graph_doubledTarget]
  exact ⟨Iso.refl _⟩

/-- Graph compatibility at every source cover when the target cover is doubled. -/
theorem S2269GraphCompatAt_of_doubledTarget (B : S1728Cover) :
    S2269GraphCompatAt B S1850DoubledCover := by
  intro A f g T ptA
  exact ⟨fun W c => S2269PhiLift_doubledTarget f g T ptA W c,
    fun W c => S2269GraphLift_doubledTarget f g T ptA W c⟩

/-- The doubled target cover satisfies graph compatibility at every source. -/
def S2269DoubledNoCounterexample : Prop :=
  forall B : S1728Cover, S2269GraphCompatAt B S1850DoubledCover

theorem S2269DoubledNoCounterexample_proof : S2269DoubledNoCounterexample :=
  S2269GraphCompatAt_of_doubledTarget

/-- The S2185 comparison at every datum whose target cover is doubled. -/
theorem S2269ConeIsoAt_of_doubledTarget (B : S1728Cover) :
    S2240ConeIsoAt B S1850DoubledCover :=
  S2269ConeIsoAt_of_graphCompatAt (S2269GraphCompatAt_of_doubledTarget B)

/-- In particular, the doubled target cover does not refute the S2185 comparison:
at every source and every datum the required 2-isomorphism exists. -/
theorem S2269Comparison_doubledTarget {A B : S1728Cover}
    (f : S1728CoverMap A S1850DoubledCover)
    (g : S1728CoverMap B S1850DoubledCover)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2269Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))) :=
  S2269ComparisonData_of_graphCompat f g T ptA
    (S2269GraphCompatAt_of_doubledTarget B A f g T ptA) W c

/-! ## 4. Strictness: the doubled cover separates graph compatibility from PC-strongness -/

/-- The PC-strong input fails at the doubled cover B = C = S1850DoubledCover. -/
theorem S2269NotConeEssSurjAt_doubled :
    ¬ S2240ConeEssSurjAt S1850DoubledCover S1850DoubledCover := by
  intro h
  exact S2240ConeEssSurj_doubled_false
    (h S1850DoubledCover (S1641CoverMapId S1850DoubledCover)
      (S1641CoverMapId S1850DoubledCover) S1726AffineOver S1733BasePoint)

/-- Graph compatibility holds at the doubled cover where PC-strongness fails, so it
is strictly weaker than PC-strongness. -/
def S2269StrictlyWeakerThanPCStrongness : Prop :=
  (forall B C : S1728Cover, S2240ConeEssSurjAt B C -> S2269GraphCompatAt B C) ∧
    (exists B C : S1728Cover, S2269GraphCompatAt B C ∧ ¬ S2240ConeEssSurjAt B C)

theorem S2269StrictlyWeakerThanPCStrongness_proof :
    S2269StrictlyWeakerThanPCStrongness := by
  refine ⟨fun B C h => S2269GraphCompatAt_of_coneEssSurjAt h, ?_⟩
  exact ⟨S1850DoubledCover, S1850DoubledCover,
    S2269GraphCompatAt_of_doubledTarget S1850DoubledCover,
    S2269NotConeEssSurjAt_doubled⟩

/-- The new exact missing is not the refuted uniform PC-strongness: the doubled cover
satisfies it at the same data where S2240ConeEssSurjAt fails. -/
theorem S2269FirstMissing_not_doubled_blocked :
    S2269GraphCompatAt S1850DoubledCover S1850DoubledCover ∧
      ¬ S2240ConeEssSurjAt S1850DoubledCover S1850DoubledCover :=
  ⟨S2269GraphCompatAt_of_doubledTarget S1850DoubledCover,
    S2269NotConeEssSurjAt_doubled⟩

/-! ## 5. Checks -/

#check S2269GraphCompatData
#check S2269GraphCompatAt
#check S2269GraphCompatAll
#check S2269ComparisonData
#check S2269ComparisonData_of_graphCompat
#check S2269StrictConeIso_of_graphCompatAll
#check S2269StrictConeIso_of_firstMissing
#check S2269ConcreteTwoPullback_of_graphCompatAll
#check S2269GraphCompatData_of_coneEssSurj
#check S2269GraphCompatAt_of_coneEssSurjAt
#check S2269ConeIsoAt_of_graphCompatAt
#check S2269GraphCompatAt_of_strongCover
#check S2269GraphCompatAt_of_coherent
#check S2269Graph_doubledTarget
#check S2269Phi_doubledTarget
#check S2269PhiLift_doubledTarget
#check S2269GraphLift_doubledTarget
#check S2269GraphCompatAt_of_doubledTarget
#check S2269ConeIsoAt_of_doubledTarget
#check S2269Comparison_doubledTarget
#check S2269NotConeEssSurjAt_doubled
#check S2269StrictlyWeakerThanPCStrongness_proof
#check S2269FirstMissing_not_doubled_blocked

#print axioms S2269ComparisonData_of_graphCompat
#print axioms S2269StrictConeIso_of_graphCompatAll
#print axioms S2269ConcreteTwoPullback_of_graphCompatAll
#print axioms S2269GraphCompatData_of_coneEssSurj
#print axioms S2269ConeIsoAt_of_graphCompatAt
#print axioms S2269GraphCompatAt_of_strongCover
#print axioms S2269GraphCompatAt_of_coherent
#print axioms S2269PhiLift_doubledTarget
#print axioms S2269GraphLift_doubledTarget
#print axioms S2269GraphCompatAt_of_doubledTarget
#print axioms S2269ConeIsoAt_of_doubledTarget
#print axioms S2269NotConeEssSurjAt_doubled
#print axioms S2269StrictlyWeakerThanPCStrongness_proof

end LeanFormal.IUT.XiFPaper.S2269GraphCompatActual
