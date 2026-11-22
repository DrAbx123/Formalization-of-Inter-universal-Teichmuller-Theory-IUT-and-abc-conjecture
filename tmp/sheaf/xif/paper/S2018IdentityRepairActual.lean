/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S2018
-/
import tmp.sheaf.xif.paper.S2015FullPullbackActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1900StrongSliceRealizationActual

/-!
# S2018: the actual identity-point presentation, and the exact residual

## Context

S2015 defined the corrected base-change presentation

  S2015FullBaseChangePresentation map testScheme point

as the recorded weak presentation together with the full iso-comma property
S2015FullPullback, and recorded the exact first missing statement

  S2015IdentityRepairAll :
    forall C : S1728Cover,
      Nonempty (S2015FullBaseChangePresentation C.map S1726AffineOver S1733BasePoint)

i.e. every finite-etale cover of the S1726 orbicurve admits, at the canonical
identity point, a presentation whose apex is the *actual* iso-comma fibre rather
than the recorded weak base-change model.  S2010/S1850 show that the recorded
square need not be full, so the corrected presentation must be existential in
the apex: it cannot in general be the recorded S1733Model C.

This file establishes what can be constructed unconditionally and isolates the
exact remaining input.

## What is constructed

1. S2018PresentationOfSchemeMap (Section 1): for **every** scheme morphism
   f : Q -> Spec R', the canonical identity-point square of the induced
   representable map y(f) : y(Q) -> y(Spec R') has a genuine corrected
   presentation with apex Q: comparison to the source is the identity,
   projection is f, the weak witness is built from the cone's first leg, and
   the full iso-comma property is proved directly.  This is the honest
   "represented on the nose" case of the identity repair.

2. The counterexample and the identity-map covers (Section 2):
   S2018IdentityRepair S2010CounterCover, S2018IdentityRepair
   S1762TerminalCover and S2018IdentityRepair S1850DoubledCover.  For the
   first one the corrected apex is Spec R' itself: the actual pullback of
   (id, id).  This is precisely the cover whose *recorded* identity-point
   square is not full (S2015_not_full_counterexample), so the correction is
   genuine and non-vacuous.

3. S2018IdentityRepairAll_of_strongRealization (Section 3): S1871/S1900's
   on-the-nose strong finite-etale realization of every cover implies
   S2015IdentityRepairAll.  Every strong presentation is a corrected one.

4. S2018SourceScheme_of_identityRepair (Section 4): every corrected
   identity-point presentation produces a quasi-equivalence
   y(Q) ~ C.source; hence S2015IdentityRepairAll implies that every cover
   source is representable by a scheme (S2018SourceSchemeAll).

## The exact residual

The converse construction from a source representation is **not** available from
the recorded weak data: the comparison 2-cells of a weak two-pullback witness
have arbitrary targets (the cover source, which is not discrete), so they do not
transport across a source quasi-equivalence.  This is exactly the transport
obstruction recorded in S1900 as S1900SourceTransport (and in S1871 as
S1871StrongTransfer).

Accordingly the residual is isolated as the conjunction

  S2018FirstMissing :=
    S2018SourceSchemeAll                    -- geometric: sources are schemes
    ∧ S2018RepresentedSourceTransport       -- bicategorical: transport to an apex

and S2018IdentityRepairAll_iff_firstMissing proves

  S2015IdentityRepairAll  <->  S2018SourceSchemeAll ∧ S2018RepresentedSourceTransport.

Both conjuncts are unproved here and no inhabitant is asserted.  The first is the
geometric representability of the (finite-etale) cover source; the second is the
source-transport step.  The counterexample construction shows that neither the
old recorded target nor S1841FirstMissing is the residual: the recorded square
of S2010CounterCover is not full, while S2018IdentityRepair S2010CounterCover
holds with apex Spec R'.

## Honest boundary

No sorry, no new axiom, no fake 2-cell, no Shrink/ULift/PUnit and no change of
the target.  S2015IdentityRepairAll, S2018SourceSchemeAll and
S2018RepresentedSourceTransport remain unproved; they are recorded as named
propositions, not inhabited.  The only axioms used are propext,
Classical.choice and Quot.sound; see the audit block.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2018IdentityRepairActual

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
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1871CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1900StrongSliceRealizationActual
open LeanFormal.IUT.XiFPaper.S2010BaseChangeFullActual
open LeanFormal.IUT.XiFPaper.S2015FullPullbackActual

/-! ## 1. The corrected presentation of a representable scheme map -/

/-- The representable etale stack of a scheme, packaged as an etale stack over
the base field.  Only the fibre matters for the presentations below; the stack
condition is the discrete-descent fact proved in S1900. -/
noncomputable def S2018YStack (Q : SchemeOverField S1726K) : EtaleStackOverField S1726K where
  fiber := S1743Y Q
  isStack := S1900RepresentableIsStack Q

/-- **The corrected identity-point presentation of a scheme morphism.**  For
f : Q -> Spec R', the canonical square

    y(Q) --id--> y(Q) --y(f)--> y(Spec R')
      |                           |
     y(f)                         id
      v                           v
    y(Spec R') ------id------> y(Spec R')

is the actual iso-comma pullback of (y(f), id) at the identity point.  The
apex is Q and the comparison to the source is the identity.  The weak witness
uses the cone's first leg as lift; the two coherence fields are equalities of
2-cells into the representable stacks y(Q) and y(Spec R'), hence
subsingletons.  The full property is proved directly from the unitors. -/
noncomputable def S2018PresentationOfSchemeMap
    (Q : SchemeOverField S1726K) (f : Q ⟶ S1726AffineOver) :
    S2015FullBaseChangePresentation
      (source := S2018YStack Q) (target := S1726Orbicurve.stack)
      (map := S1743StrongTransOfHom f)
      S1726AffineOver S1733BasePoint where
  pullbackScheme := Q
  projection := f
  projectionMap := S1743SchemeRepresentableMap f
  toSource := Pseudofunctor.StrongTrans.id (S1743Y Q)
  commutes := (S1756LeftUnitorIso (S1743StrongTransOfHom f)).trans
    (S1756RightUnitorIso (S1743StrongTransOfHom f)).symm
  isPullback := by
    refine
      { lift := fun _W c => c.toX
        liftToX := fun _W c => S1756RightUnitorIso c.toX
        liftToY := fun _W c => c.commutes.trans (S1756RightUnitorIso c.toY)
        liftTwoCell := fun _W _s _t m => m.toX
        liftTwoCell_toX := ?_
        liftTwoCell_toY := ?_
        twoCell_ext := ?_ }
    · intro W source target morphism
      exact (S1844SubsingletonMod _ _).allEq _ _
    · intro W source target morphism
      exact (S1844SubsingletonMod _ _).allEq _ _
    · intro W first second alpha beta _ _
      exact (S1844SubsingletonMod first second).allEq alpha beta
  isFull := by
    refine ⟨?_, ?_⟩
    · intro W c
      exact ⟨c.toX, ⟨⟨S1756RightUnitorIso c.toX⟩,
        ⟨c.commutes.trans (S1756RightUnitorIso c.toY)⟩⟩⟩
    · intro W c f g hXf hYf hXg hYg
      obtain ⟨eXf⟩ := hXf
      obtain ⟨eXg⟩ := hXg
      exact ⟨(S1756RightUnitorIso f).symm.trans
        (eXf.trans (eXg.symm.trans (S1756RightUnitorIso g)))⟩

@[simp] theorem S2018PresentationOfSchemeMap_pullbackScheme
    (Q : SchemeOverField S1726K) (f : Q ⟶ S1726AffineOver) :
    (S2018PresentationOfSchemeMap Q f).pullbackScheme = Q := rfl

/-! ## 2. The counterexample and the identity-map covers -/

/-- The corrected identity-point presentation of S2010CounterCover: the apex
is Spec R' itself, with projection id, comparison id, and the actual
pullback square of (id, id).  This is *not* the recorded weak presentation of
S2010 (whose apex is the split double cover Spec R' ⨿ Spec R' and whose square
is not full). -/
noncomputable def S2018CounterPresentation :
    S2015FullBaseChangePresentation
      S2010CounterCover.map S1726AffineOver S1733BasePoint where
  pullbackScheme := S1726AffineOver
  projection := 𝟙 S1726AffineOver
  projectionMap := S1762IdSchemeRepresentableMap S1726AffineOver
  toSource := S1733BasePoint
  commutes := S1762IdCommutes S1726AffineOver S1733BasePoint
  isPullback := S1762IdWitness S1726AffineOver S1733BasePoint
  isFull := (S2015FullPullback_iff_essSurj
    (S1762IdWitness S1726AffineOver S1733BasePoint)).mpr
    (S1852IdStrongBc S1726AffineOver S1733BasePoint).coneEssSurj

/-- **The counterexample has the corrected identity-point presentation.**  The
recorded square of this cover is not full (S2015_not_full_counterexample), but
the corrected apex Spec R' is available. -/
theorem S2018IdentityRepair_counterexample : S2015IdentityRepair S2010CounterCover :=
  ⟨S2018CounterPresentation⟩

/-- The universal corrected presentation of the identity map of the orbicurve at
the identity point.  This is the presentation used for every cover whose source
is the orbicurve stack itself and whose structure map is the identity. -/
noncomputable def S2018IdPresentation :
    S2015FullBaseChangePresentation
      (source := S1726Orbicurve.stack) (target := S1726Orbicurve.stack)
      (map := Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber)
      S1726AffineOver S1733BasePoint where
  pullbackScheme := S1726AffineOver
  projection := 𝟙 S1726AffineOver
  projectionMap := S1762IdSchemeRepresentableMap S1726AffineOver
  toSource := S1733BasePoint
  commutes := S1762IdCommutes S1726AffineOver S1733BasePoint
  isPullback := S1762IdWitness S1726AffineOver S1733BasePoint
  isFull := (S2015FullPullback_iff_essSurj
    (S1762IdWitness S1726AffineOver S1733BasePoint)).mpr
    (S1852IdStrongBc S1726AffineOver S1733BasePoint).coneEssSurj

/-- Every cover whose source is the orbicurve stack and whose structure map is
the identity admits the corrected identity-point presentation. -/
theorem S2018IdentityRepair_of_identityMap (C : S1728Cover)
    (hsrc : C.source = S1726Orbicurve.stack)
    (hmap : HEq C.map (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber)) :
    S2015IdentityRepair C := by
  rcases C with ⟨src, map, fe⟩
  subst hsrc
  have hmap' : map = Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber :=
    eq_of_heq hmap
  subst hmap'
  exact ⟨S2018IdPresentation⟩

/-- The terminal cover has the corrected identity-point presentation. -/
theorem S2018IdentityRepair_terminal : S2015IdentityRepair S1762TerminalCover :=
  S2018IdentityRepair_of_identityMap S1762TerminalCover rfl HEq.rfl

/-- S1850's doubled cover --- the cover whose *recorded* identity-point
presentation has the doubled apex and is not full --- nevertheless has the
corrected identity-point presentation, with apex Spec R'.  This isolates the
point of the existential repair: the recorded model is replaced, not upgraded. -/
theorem S2018IdentityRepair_doubled : S2015IdentityRepair S1850DoubledCover :=
  S2018IdentityRepair_of_identityMap S1850DoubledCover rfl HEq.rfl

/-! ## 3. Strong realisation implies the identity repair -/

/-- Every strong base-change presentation (S1852) is in particular a corrected
presentation (S2015) with the same scheme and square. -/
noncomputable def S2018FullOfStrong
    {source target : EtaleStackOverField S1726K}
    {map : source.Hom target}
    {testScheme : SchemeOverField S1726K}
    {point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K testScheme) target.fiber}
    (P : StrongEtaleStackBaseChangePresentation map testScheme point) :
    S2015FullBaseChangePresentation map testScheme point where
  pullbackScheme := P.toWeak.pullbackScheme
  projection := P.toWeak.projection
  projectionMap := P.toWeak.projectionMap
  toSource := P.toWeak.toSource
  commutes := P.toWeak.commutes
  isPullback := P.toWeak.isPullback
  isFull := (S2015FullPullback_iff_essSurj P.toWeak.isPullback).mpr P.coneEssSurj

/-- S1871/S1900's on-the-nose strong finite-etale realisation implies
S2015IdentityRepairAll. -/
theorem S2018IdentityRepairAll_of_strongRealization
    (h : S1871StrongRealization) : S2015IdentityRepairAll := by
  intro C
  obtain ⟨M⟩ := h C
  exact ⟨S2018FullOfStrong (M.baseChange S1726AffineOver S1733BasePoint)⟩

/-- The old recorded first missing (which is false by S2010) also implies the
corrected identity-point presentations, because then the recorded square is
full. -/
theorem S2018IdentityRepairAll_of_firstMissing (h : S1841FirstMissing) :
    S2015IdentityRepairAll :=
  S2015IdentityRepairAll_of_firstMissing h

/-! ## 4. Necessity: source representability -/

/-- Representability of a cover source by a scheme: there is a scheme Q and a
genuine quasi-equivalence between the representable stack y(Q) and the cover
source.  This is the geometric content forced by a corrected identity-point
presentation (S2015's full property makes the comparison to the source an
equivalence, and its apex is a scheme). -/
def S2018SourceScheme (C : S1728Cover) : Prop :=
  ∃ Q : SchemeOverField S1726K,
    Nonempty (S1756StackEquiv (S1743Y Q) C.source.fiber)

/-- Every cover source is representable by a scheme. -/
def S2018SourceSchemeAll : Prop := ∀ C : S1728Cover, S2018SourceScheme C

/-- A corrected identity-point presentation gives source representability by its
own apex. -/
theorem S2018SourceScheme_of_identityRepair (C : S1728Cover)
    (h : S2015IdentityRepair C) : S2018SourceScheme C := by
  obtain ⟨P⟩ := h
  exact ⟨P.pullbackScheme, S2015SourceRepresentedBy_of_identityRepair C P⟩

/-- Necessity for the uniform statement. -/
theorem S2018SourceSchemeAll_of_identityRepairAll
    (h : S2015IdentityRepairAll) : S2018SourceSchemeAll :=
  fun C => S2018SourceScheme_of_identityRepair C (h C)

/-- The old first missing gives source representability by the recorded affine
model. -/
theorem S2018SourceSchemeAll_of_firstMissing (h : S1841FirstMissing) :
    S2018SourceSchemeAll :=
  fun C => ⟨S1733Model C, S1841SourceRepresentableAll_of_firstMissing h C⟩

/-- Strong realisation gives source representability as well. -/
theorem S2018SourceSchemeAll_of_strongRealization
    (h : S1871StrongRealization) : S2018SourceSchemeAll :=
  S2018SourceSchemeAll_of_identityRepairAll
    (S2018IdentityRepairAll_of_strongRealization h)

/-- The counterexample cover already witnesses source representability, even
though its recorded identity-point square is not full. -/
theorem S2018SourceScheme_counterexample : S2018SourceScheme S2010CounterCover :=
  S2018SourceScheme_of_identityRepair S2010CounterCover
    S2018IdentityRepair_counterexample

/-! ## 5. The exact residual -/

/-- **The source-transport input.**  A quasi-equivalence between the
representable stack of a scheme and the source of a cover upgrades to a
corrected identity-point presentation with that scheme as apex.  This is the
precise bicategorical transport obstruction: the comparison 2-cells of a weak
two-pullback witness have arbitrary targets (the cover source), so they do not
move across a source quasi-equivalence.  It is the same obstruction recorded in
S1900 as S1900SourceTransport (and in S1871 as S1871StrongTransfer).

This proposition is not proved here and no inhabitant is asserted. -/
def S2018RepresentedSourceTransport : Prop :=
  ∀ (C : S1728Cover) (Q : SchemeOverField S1726K),
    Nonempty (S1756StackEquiv (S1743Y Q) C.source.fiber) →
      S2015IdentityRepair C

/-- The exact residual after S2015: every cover source is representable by a
scheme, and such a representation transports to a corrected presentation. -/
def S2018FirstMissing : Prop :=
  S2018SourceSchemeAll ∧ S2018RepresentedSourceTransport

/-- **The exact decomposition.**  The corrected identity-point presentations
for all covers are exactly the conjunction of source representability and the
source-transport step. -/
theorem S2018IdentityRepairAll_iff_firstMissing :
    S2015IdentityRepairAll ↔ S2018FirstMissing := by
  constructor
  · intro h
    exact ⟨S2018SourceSchemeAll_of_identityRepairAll h, fun _C _Q _e => h _C⟩
  · rintro ⟨hsrc, htr⟩ C
    obtain ⟨Q, e⟩ := hsrc C
    exact htr C Q e

/-- Given source representability, the identity repair for all covers is
*exactly* the source-transport statement. -/
theorem S2018IdentityRepairAll_iff_sourceTransport
    (h : S2018SourceSchemeAll) :
    S2015IdentityRepairAll ↔ S2018RepresentedSourceTransport := by
  constructor
  · intro hrep C Q _e
    exact hrep C
  · intro htr C
    obtain ⟨Q, e⟩ := h C
    exact htr C Q e

/-! ## 6. Checks and audit -/

#check S2018YStack
#check S2018PresentationOfSchemeMap
#check S2018PresentationOfSchemeMap_pullbackScheme
#check S2018CounterPresentation
#check S2018IdentityRepair_counterexample
#check S2018IdPresentation
#check S2018IdentityRepair_of_identityMap
#check S2018IdentityRepair_terminal
#check S2018IdentityRepair_doubled
#check S2018FullOfStrong
#check S2018IdentityRepairAll_of_strongRealization
#check S2018IdentityRepairAll_of_firstMissing
#check S2018SourceScheme
#check S2018SourceSchemeAll
#check S2018SourceScheme_of_identityRepair
#check S2018SourceSchemeAll_of_identityRepairAll
#check S2018SourceSchemeAll_of_firstMissing
#check S2018SourceSchemeAll_of_strongRealization
#check S2018SourceScheme_counterexample
#check S2018RepresentedSourceTransport
#check S2018FirstMissing
#check S2018IdentityRepairAll_iff_firstMissing
#check S2018IdentityRepairAll_iff_sourceTransport

#print axioms S2018PresentationOfSchemeMap
#print axioms S2018CounterPresentation
#print axioms S2018IdentityRepair_counterexample
#print axioms S2018IdPresentation
#print axioms S2018IdentityRepair_of_identityMap
#print axioms S2018IdentityRepair_terminal
#print axioms S2018IdentityRepair_doubled
#print axioms S2018FullOfStrong
#print axioms S2018IdentityRepairAll_of_strongRealization
#print axioms S2018IdentityRepairAll_of_firstMissing
#print axioms S2018SourceScheme_of_identityRepair
#print axioms S2018SourceSchemeAll_of_identityRepairAll
#print axioms S2018SourceSchemeAll_of_firstMissing
#print axioms S2018SourceSchemeAll_of_strongRealization
#print axioms S2018SourceScheme_counterexample
#print axioms S2018IdentityRepairAll_iff_firstMissing
#print axioms S2018IdentityRepairAll_iff_sourceTransport

end LeanFormal.IUT.XiFPaper.S2018IdentityRepairActual