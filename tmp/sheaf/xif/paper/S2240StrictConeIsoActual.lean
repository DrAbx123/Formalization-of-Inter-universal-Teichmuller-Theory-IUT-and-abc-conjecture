/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2240
-/

import tmp.sheaf.xif.paper.S2185ConcreteTwoPullbackActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S2100GPresentationConeEssSurjActual
import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual


/-!
# S2240: the exact coherence boundary of the S2185 strict-cone comparison

## The question

S2185 reduced the S2130 concrete two-pullback to the single 2-cell statement
S2185StrictConeIso: for every cone c over the base square, the two strong
transformations

  (S2130PB).isPullback.lift W c ; y(S2130Phi)   and   c.toY ; y(S2130Graph)

into y(C x_X T) are 2-isomorphic.  Since the target is a representable stack, such
an isomorphism is equivalent to an equality of the underlying scheme morphisms at
every test object; the issue is producing one.

This file determines exactly what that statement needs.  It does not assert
S2185StrictConeIso, and it does not fake a witness.

## What is proved

1. S2240StrictConeIsoAt (and its uniform form S2240StrictConeIso_of_coneEssSurj):
   if the C-presentation S2130PC carries the full 2-universal property
   (S1852ConeEssSurj, i.e. cone essential surjectivity), then the comparison
   2-cell exists for every cone c.

   The proof is the natural one: both 1-cells are candidates for the lift of
   the transported cone (c.toX ; g.map, c.toY) over the C-presentation square, and
   cone essential surjectivity identifies both with the recorded lift.  The four
   comparison 2-cells are explicit associator/whiskering chains
   (S2240PhiSiteToSource, S2240PhiSiteToProj, S2240GraphSiteToSource,
   S2240GraphSiteToProj), and the scheme maps S2130Phi, S2130Graph are replaced by
   their site forms S2130PhiSite, S2130GraphSite through the 2-Yoneda comparison
   S1742StrongTransIsoOfHom.

2. S2240ConcreteTwoPullback_of_coneEssSurj and S2240Hg_of_coneEssSurj: the S2130
   target and the S2130 base-change presentations follow from the same coherence.

3. S2240ConeEssSurj_doubled_false and S2240NotCPresentationConeEssSurj: the uniform
   coherence hypothesis is FALSE.  At S1850's doubled cover the C-presentation is
   literally S1850Doubled at the identity point, and S1852Doubled_not_coneEssSurj
   shows that it is not cone-essentially-surjective.  Hence the uniform
   S2130ConcreteTwoPullback cannot be closed from this hypothesis, exactly as S2100
   refutes the uniform strong-presentation input and S2094's literal form.

4. The per-cover construction, which is the usable repair: for a strong target cover
   Cs : StrongCover (S1852) and an arbitrary source cover B, the concrete
   two-pullback witness of S2130 exists for every A, f, g, T, ptA
   (S2240WitnessFor_strongCover), and hence so does the S2130 finite-etale
   presentation, with finite etale projection (S2240HgFor_strongCover,
   S2240HgFor_strongCover_finiteEtale).  The same holds for a coherent cover
   (S2240WitnessFor_coherent).  The full witness (lift, both comparisons, action on
   cone morphisms, 2-cell extensionality) is assembled from the S1911 strict-square
   witness and the comparison supplied by the coherence, exactly as in S2185 but
   with the hypothesis localised at the fixed target cover C.

## The exact first missing

S2185StrictConeIso remains unproved, and it is not refuted here.  What is settled:

* Its natural sufficient datum is the cone essential surjectivity of the
  C-presentation, S2240CPresentationConeEssSurj, and that datum is false
  (S2240NotCPresentationConeEssSurj).  So no uniform proof can pass through the
  strong presentation field.
* The missing content is exactly the 2-cell itself, best understood as follows: over
  the C-presentation square the transported cone has two candidate 1-cells, the
  recorded lift and the composite of the cone's test leg with the graph section, and
  the weak witness records no comparison between two candidates for the same cone.
  The gap is therefore the graph-compatibility of the recorded presentation lift.
  No field of EtaleStackBaseChangePresentation supplies it: the weak
  TwoPullbackWitness does not give cone essential surjectivity in general
  (S1801NoGenericEssSurj), the doubled presentation is a genuine weak presentation
  at which it fails (S1850Doubled, S1852Doubled_not_coneEssSurj), and S2123 shows
  that the strong field is vacuous at the recorded lift, the missing comparison
  being a coherent lift cone morphism (the presentation twist) of the same form.
* The repair used by the inverse construction is the coherent cover datum: for
  coherent/strong target covers the comparison and the witness are constructed
  here, with no extra assumption.

Consequently the uniform S2130ConcreteTwoPullback over all recorded (possibly
incoherent) covers is not obtained here; the coherent-cover form is, and it is the
form available from the coherent cover datum of S1852.

## Axiom footprint

No sorry, no new axiom, no change of any recorded definition.  Every declaration
below depends only on propext, Classical.choice and Quot.sound.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

namespace LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual

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

universe u

abbrev S2240Y (S : SchemeOverField S1726K) : EtaleStackPseudofunctor S1726K :=
  schemeRepresentableEtalePseudofunctor S1726K S

/-- The cone over the C-presentation square attached to a cone over the base square. -/
noncomputable def S2240ConePC
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    (S2185PCSquare f g T ptA).Cone W where
  toX := Pseudofunctor.StrongTrans.vcomp c.toX g.map
  toY := c.toY
  commutes :=
    (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map)
      (Pseudofunctor.StrongTrans.vcomp c.toY (S2130PtC f T ptA))
      C.map c.commutes).trans
      (S2058AssociatorIso c.toY (S2130PtC f T ptA) C.map)

/-- The comparison of the presentation scheme map S2130Phi with its site form. -/
noncomputable def S2240PhiTransIso
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    Iso (S1742StrongTransOfHom (S2130Phi f g T ptA)) (S2130PhiSite f g T ptA) :=
  S1742StrongTransIsoOfHom (S2130PhiSite f g T ptA)

/-- The comparison of the graph scheme map S2130Graph with its site form. -/
noncomputable def S2240GraphTransIso
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    Iso (S1742StrongTransOfHom (S2130Graph f g T ptA)) (S2130GraphSite f g T ptA) :=
  S1742StrongTransIsoOfHom (S2130GraphSite f g T ptA)

/-- First comparison for Phi, in site form. -/
noncomputable def S2240PhiSiteToSource
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S2130PhiSite f g T ptA))
        (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map) :=
  (S2058AssociatorIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S2130PhiSite f g T ptA)
      (S2130PC f T ptA).toSource).trans
    ((S2058WhiskerLeftIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (Pseudofunctor.StrongTrans.vcomp
        (S2130PhiSite f g T ptA) (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp
        (S2130PB f g T ptA).toSource g.map)
      ((S2130PC f T ptA).isPullback.liftToX (S2240Y (S2130PB f g T ptA).pullbackScheme)
        (S2130PhiCone f g T ptA))).trans
      ((S2058AssociatorIso
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S2130PB f g T ptA).toSource g.map).symm.trans
        (S2058WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp
            ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
            (S2130PB f g T ptA).toSource)
          c.toX g.map
          ((S2130PB f g T ptA).isPullback.liftToX W (S2185ConePB f g T ptA c)))))

/-- Second comparison for Phi, in site form. -/
noncomputable def S2240PhiSiteToProj
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S2130PhiSite f g T ptA))
        (S2130PC f T ptA).projectionMap.transformation)
      c.toY :=
  (S2058AssociatorIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S2130PhiSite f g T ptA)
      (S2130PC f T ptA).projectionMap.transformation).trans
    ((S2058WhiskerLeftIso
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (Pseudofunctor.StrongTrans.vcomp
        (S2130PhiSite f g T ptA) (S2130PC f T ptA).projectionMap.transformation)
      (S2130PhiCone f g T ptA).toY
      ((S2130PC f T ptA).isPullback.liftToY (S2240Y (S2130PB f g T ptA).pullbackScheme)
        (S2130PhiCone f g T ptA))).trans
      ((S2130PB f g T ptA).isPullback.liftToY W (S2185ConePB f g T ptA c)))

/-- First comparison for Graph. -/
noncomputable def S2240GraphSiteToSource
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp c.toY (S2130GraphSite f g T ptA))
        (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map) :=
  (S2058AssociatorIso c.toY (S2130GraphSite f g T ptA)
      (S2130PC f T ptA).toSource).trans
    ((S2058WhiskerLeftIso c.toY
      (Pseudofunctor.StrongTrans.vcomp
        (S2130GraphSite f g T ptA) (S2130PC f T ptA).toSource)
      (S2130PtC f T ptA)
      ((S2130PC f T ptA).isPullback.liftToX (S2240Y T)
        (S2130GraphCone f g T ptA))).trans c.commutes.symm)

/-- Second comparison for Graph. -/
noncomputable def S2240GraphSiteToProj
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp c.toY (S2130GraphSite f g T ptA))
        (S2130PC f T ptA).projectionMap.transformation)
      c.toY :=
  (S2058AssociatorIso c.toY (S2130GraphSite f g T ptA)
      (S2130PC f T ptA).projectionMap.transformation).trans
    ((S2058WhiskerLeftIso c.toY
      (Pseudofunctor.StrongTrans.vcomp
        (S2130GraphSite f g T ptA) (S2130PC f T ptA).projectionMap.transformation)
      (Pseudofunctor.StrongTrans.id (S2240Y T))
      ((S2130PC f T ptA).isPullback.liftToY (S2240Y T)
        (S2130GraphCone f g T ptA))).trans
      (Pseudofunctor.StrongTrans.rightUnitor c.toY))

/-- First comparison, with the scheme map Phi. -/
noncomputable def S2240PhiToSource
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map) :=
  (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S2130PhiSite f g T ptA))
      (S2130PC f T ptA).toSource
      (S2058WhiskerLeftIso
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA))
        (S2130PhiSite f g T ptA)
        (S2240PhiTransIso f g T ptA))).trans
    (S2240PhiSiteToSource f g T ptA c)

/-- Second comparison, with the scheme map Phi. -/
noncomputable def S2240PhiToProj
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (S2130PC f T ptA).projectionMap.transformation)
      c.toY :=
  (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S2130PhiSite f g T ptA))
      (S2130PC f T ptA).projectionMap.transformation
      (S2058WhiskerLeftIso
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA))
        (S2130PhiSite f g T ptA)
        (S2240PhiTransIso f g T ptA))).trans
    (S2240PhiSiteToProj f g T ptA c)

/-- First comparison, with the scheme map Graph. -/
noncomputable def S2240GraphToSource
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))
        (S2130PC f T ptA).toSource)
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map) :=
  (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp c.toY (S2130GraphSite f g T ptA))
      (S2130PC f T ptA).toSource
      (S2058WhiskerLeftIso c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA))
        (S2130GraphSite f g T ptA)
        (S2240GraphTransIso f g T ptA))).trans
    (S2240GraphSiteToSource f g T ptA c)

/-- Second comparison, with the scheme map Graph. -/
noncomputable def S2240GraphToProj
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))
        (S2130PC f T ptA).projectionMap.transformation)
      c.toY :=
  (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp c.toY (S2130GraphSite f g T ptA))
      (S2130PC f T ptA).projectionMap.transformation
      (S2058WhiskerLeftIso c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA))
        (S2130GraphSite f g T ptA)
        (S2240GraphTransIso f g T ptA))).trans
    (S2240GraphSiteToProj f g T ptA c)

/-- **Per-data form of the S2185 strict-cone comparison.**  If the C-presentation has the
full 2-universal property (cone essential surjectivity), the comparison 2-cell of S2185
exists. -/
theorem S2240StrictConeIsoAt
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    (hC : S1852ConeEssSurj (S2130PC f T ptA))
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA)))) := by
  let cPC : (S1852WeakSquare (S2130PC f T ptA)).Cone W := S2240ConePC f g T ptA c
  have h1 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (S1852WeakSquare (S2130PC f T ptA)).toX) cPC.toX) :=
    ⟨S2240PhiToSource f g T ptA c⟩
  have h2 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (S1852WeakSquare (S2130PC f T ptA)).toY) cPC.toY) :=
    ⟨S2240PhiToProj f g T ptA c⟩
  have h3 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA)))
      (S1852WeakSquare (S2130PC f T ptA)).toX) cPC.toX) :=
    ⟨S2240GraphToSource f g T ptA c⟩
  have h4 : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp c.toY
        (S1742StrongTransOfHom (S2130Graph f g T ptA)))
      (S1852WeakSquare (S2130PC f T ptA)).toY) cPC.toY) :=
    ⟨S2240GraphToProj f g T ptA c⟩
  obtain ⟨e1⟩ := hC W cPC
    (Pseudofunctor.StrongTrans.vcomp
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S1742StrongTransOfHom (S2130Phi f g T ptA))) h1 h2
  obtain ⟨e2⟩ := hC W cPC
    (Pseudofunctor.StrongTrans.vcomp c.toY
      (S1742StrongTransOfHom (S2130Graph f g T ptA))) h3 h4
  exact ⟨e1.trans e2.symm⟩

/-- The exact coherence hypothesis: every C-presentation carries the full 2-universal
property (cone essential surjectivity). -/
def S2240CPresentationConeEssSurj : Prop :=
  forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
    S1852ConeEssSurj (S2130PC f T ptA)

/-- **S2185StrictConeIso from the presentation coherence.** -/
theorem S2240StrictConeIso_of_coneEssSurj (h : S2240CPresentationConeEssSurj) :
    S2185StrictConeIso :=
  fun A B C f g T ptA W c => S2240StrictConeIsoAt f g T ptA (h A B C f g T ptA) c

/-- **The S2130 concrete two-pullback from the presentation coherence.** -/
noncomputable def S2240ConcreteTwoPullback_of_coneEssSurj (h : S2240CPresentationConeEssSurj) :
    S2130ConcreteTwoPullback :=
  S2185ConcreteTwoPullback_of_strictConeIso (S2240StrictConeIso_of_coneEssSurj h)

/-- The exact first missing statement: the C-presentation coherence. -/
def S2240FirstMissing : Prop := S2240CPresentationConeEssSurj

/-- Conditional form: the S2130 target from the recorded exact first missing. -/
noncomputable def S2240ConcreteTwoPullback_of_firstMissing (h : S2240FirstMissing) :
    S2130ConcreteTwoPullback :=
  S2240ConcreteTwoPullback_of_coneEssSurj h

/-- **The coherence hypothesis fails at the doubled cover of S1850.**  The presentation of
the identity structure map at the identity point is S1850Doubled, and S1852 proves that it
is not cone-essentially-surjective. -/
theorem S2240ConeEssSurj_doubled_false :
    ¬ S1852ConeEssSurj
      (S2130PC (A := S1850DoubledCover) (C := S1850DoubledCover)
        (f := S1641CoverMapId S1850DoubledCover) S1726AffineOver S1733BasePoint) := by
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  exact S1852Doubled_not_coneEssSurj S1726AffineOver
    (S2130PtX (S1641CoverMapId S1850DoubledCover) S1726AffineOver S1733BasePoint) hne

/-- **The uniform coherence hypothesis is false.**  Consequently it cannot be used to
close the uniform S2130 target: the strong-presentation property is refuted by the doubled
cover, exactly as S2100 refutes the uniform strong presentation input. -/
theorem S2240NotCPresentationConeEssSurj : ¬ S2240CPresentationConeEssSurj := by
  intro h
  exact S2240ConeEssSurj_doubled_false
    (h S1850DoubledCover S1850DoubledCover S1850DoubledCover
      (S1641CoverMapId S1850DoubledCover) (S1641CoverMapId S1850DoubledCover)
      S1726AffineOver S1733BasePoint)

/-- The same statement in the recorded first-missing form. -/
theorem S2240NotFirstMissing : ¬ S2240FirstMissing := S2240NotCPresentationConeEssSurj

/-- The S2130 finite-etale presentations of the C-cover, from the coherence. -/
noncomputable def S2240Hg_of_coneEssSurj (h : S2240CPresentationConeEssSurj) :
    ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
      EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA) :=
  S2130ConcreteHgOfTwoPullback (S2240ConcreteTwoPullback_of_coneEssSurj h)


/-! ## The per-cover form: fixed target cover, coherence from a strong structure -/

/-- The cone essential surjectivity of the C-presentations, at a fixed target cover. -/
def S2240ConeEssSurjAt (B C : S1728Cover) : Prop :=
  forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
    S1852ConeEssSurj (S2130PC f T ptA)

/-- The S2185 strict-cone comparison, at a fixed target cover. -/
def S2240ConeIsoAt (B C : S1728Cover) : Prop :=
  forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W),
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA))))

/-- The comparison at a fixed target cover from its presentation coherence. -/
theorem S2240ConeIsoAt_of_coneEssSurjAt (B C : S1728Cover)
    (h : S2240ConeEssSurjAt B C) : S2240ConeIsoAt B C :=
  fun A f g T ptA W c => S2240StrictConeIsoAt f g T ptA (h A f g T ptA) c

section Family

variable {B C : S1728Cover}

/-- The strict cone over the S2185 strict square, from the comparison at a fixed target
cover. -/
noncomputable def S2240StrictCone (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    (S2185StrictSquare f g T ptA).Cone W where
  toX := (S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c)
  toY := c.toY
  commutes := (h A f g T ptA W c).some

/-- The S1911 witness of the strict square (independent of the comparison). -/
noncomputable def S2240StrictWitness
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    (S2185StrictSquare f g T ptA).TwoPullbackWitness :=
  S1911Witness (sq := S2185StrictSquare f g T ptA)
    (pX := S2130P_fst f g T ptA) (pY := S2130P_snd f g T ptA)
    (by
      simpa only [S1911BaseF, S1911BaseG,
        S1742HomOfStrongTrans_strongTransOfHom] using
        S2185P_isPullback f g T ptA)
    rfl rfl

/-- The lift of a cone into the strict apex. -/
noncomputable def S2240Lift (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Pseudofunctor.StrongTrans W (S2240Y (S2130P f g T ptA)) :=
  (S2240StrictWitness f g T ptA).lift W (S2240StrictCone h f g T ptA c)

/-- The comparison of the lift with the source leg. -/
noncomputable def S2240LiftToX (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W c)
        (S2130ToSource f g T ptA)) c.toX :=
  (S2058AssociatorIso (S2240Lift h f g T ptA W c)
    (S1742StrongTransOfHom (S2130P_fst f g T ptA))
    (S2130PB f g T ptA).toSource).symm.trans
    ((S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W c)
        (S1742StrongTransOfHom (S2130P_fst f g T ptA)))
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S2130PB f g T ptA).toSource
      ((S2240StrictWitness f g T ptA).liftToX W
        (S2240StrictCone h f g T ptA c))).trans
      ((S2130PB f g T ptA).isPullback.liftToX W (S2185ConePB f g T ptA c)))

/-- The comparison of the lift with the test leg. -/
noncomputable def S2240LiftToY (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W c)
        (S2130Proj f g T ptA)) c.toY :=
  (S2240StrictWitness f g T ptA).liftToY W (S2240StrictCone h f g T ptA c)

end Family

section Family2

variable {B C : S1728Cover}

/-- Morphism of the PB-cones induced by a morphism of the base cones. -/
noncomputable def S2240ConePBMorphism
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    (S2185PBSquare f g T ptA).ConeMorphism (S2185ConePB f g T ptA s)
      (S2185ConePB f g T ptA t) where
  toX := m.toX
  toY := m.toY
  compatibility := by
    exact @Subsingleton.elim _ (S2185SubsingletonOrbicurve
      (f := Pseudofunctor.StrongTrans.vcomp (S2185ConePB f g T ptA s).toX
        (S2185PBSquare f g T ptA).xToBase)
      (g := Pseudofunctor.StrongTrans.vcomp (S2185ConePB f g T ptA t).toY
        (S2185PBSquare f g T ptA).yToBase)) _ _

/-- Morphism of the strict cones induced by a morphism of the base cones. -/
noncomputable def S2240ConeStrictMorphism (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    (S2185StrictSquare f g T ptA).ConeMorphism (S2240StrictCone h f g T ptA s)
      (S2240StrictCone h f g T ptA t) where
  toX := (S2130PB f g T ptA).isPullback.liftTwoCell W
    (S2185ConePB f g T ptA s) (S2185ConePB f g T ptA t)
    (S2240ConePBMorphism f g T ptA m)
  toY := m.toY
  compatibility := by
    exact @Subsingleton.elim _ (S2185SubsingletonRepresentable
      (S := (S2130PC f T ptA).pullbackScheme)
      (f := Pseudofunctor.StrongTrans.vcomp (S2240StrictCone h f g T ptA s).toX
        (S2185StrictSquare f g T ptA).xToBase)
      (g := Pseudofunctor.StrongTrans.vcomp (S2240StrictCone h f g T ptA t).toY
        (S2185StrictSquare f g T ptA).yToBase)) _ _

/-- The action of the lift on cone morphisms. -/
noncomputable def S2240LiftTwoCell (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    S2240Lift h f g T ptA W s ⟶ S2240Lift h f g T ptA W t :=
  (S2240StrictWitness f g T ptA).liftTwoCell W
    (S2240StrictCone h f g T ptA s) (S2240StrictCone h f g T ptA t)
    (S2240ConeStrictMorphism h f g T ptA m)

end Family2

section Family3

variable {B C : S1728Cover}

/-- The second projection equation of the lift's action on cone morphisms. -/
theorem S2240LiftTwoCell_toY (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (S2240LiftTwoCell h f g T ptA m)
        (S2130Proj f g T ptA) =
      (S2240LiftToY h f g T ptA s).hom ≫ m.toY ≫
        (S2240LiftToY h f g T ptA t).inv := by
  exact @Subsingleton.elim _
    (S2185SubsingletonRepresentable (S := T)
      (f := Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W s)
        (S2130Proj f g T ptA))
      (g := Pseudofunctor.StrongTrans.vcomp (S2240Lift h f g T ptA W t)
        (S2130Proj f g T ptA))) _ _

/-- The first projection equation of the lift's action on cone morphisms. -/
theorem S2240LiftTwoCell_toX (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (S2240LiftTwoCell h f g T ptA m)
        (S2130ToSource f g T ptA) =
      (S2240LiftToX h f g T ptA s).hom ≫ m.toX ≫
        (S2240LiftToX h f g T ptA t).inv := by
  exact @Subsingleton.elim _
    (S2185Modification_subsingleton (C := B) (S2028CoverFiberDiscrete B)
      (F := Pseudofunctor.StrongTrans.vcomp
        (S2240Lift h f g T ptA W s) (S2130ToSource f g T ptA))
      (G := Pseudofunctor.StrongTrans.vcomp
        (S2240Lift h f g T ptA W t) (S2130ToSource f g T ptA))) _ _

/-- Two 2-cells into the strict apex with equal projections are equal. -/
theorem S2240TwoCell_ext (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {first second : Pseudofunctor.StrongTrans W (S2240Y (S2130P f g T ptA))}
    (alpha beta : first ⟶ second)
    (h1 : Pseudofunctor.StrongTrans.whiskerRight alpha (S2130ToSource f g T ptA) =
      Pseudofunctor.StrongTrans.whiskerRight beta (S2130ToSource f g T ptA))
    (h2 : Pseudofunctor.StrongTrans.whiskerRight alpha (S2130Proj f g T ptA) =
      Pseudofunctor.StrongTrans.whiskerRight beta (S2130Proj f g T ptA)) :
    alpha = beta := by
  exact @Subsingleton.elim _
    (S2185SubsingletonRepresentable (S := S2130P f g T ptA)
      (f := first) (g := second)) alpha beta

/-- The concrete two-pullback witness of the base square, at a fixed target cover and
under its presentation coherence. -/
noncomputable def S2240TwoPullbackWitness (h : S2240ConeIsoAt B C)
    {A : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    (S2130BaseSquare f g T ptA).TwoPullbackWitness where
  lift W c := S2240Lift h f g T ptA W c
  liftToX W c := S2240LiftToX h f g T ptA c
  liftToY W c := S2240LiftToY h f g T ptA c
  liftTwoCell W s t m := S2240LiftTwoCell h f g T ptA m
  liftTwoCell_toX W s t m := S2240LiftTwoCell_toX h f g T ptA m
  liftTwoCell_toY W s t m := S2240LiftTwoCell_toY h f g T ptA m
  twoCell_ext W first second alpha beta h1 h2 :=
    S2240TwoCell_ext h f g T ptA alpha beta h1 h2

end Family3

section Family4

variable {B C : S1728Cover}

/-- The full family of concrete two-pullback witnesses for a fixed target cover, from its
presentation coherence. -/
noncomputable def S2240WitnessFamily (h : S2240ConeIsoAt B C) :
    forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
      (S2130BaseSquare f g T ptA).TwoPullbackWitness :=
  fun A f g T ptA => S2240TwoPullbackWitness h f g T ptA

/-- The same family, from the cone essential surjectivity of the C-presentation. -/
noncomputable def S2240WitnessFamily_of_coneEssSurjAt (h : S2240ConeEssSurjAt B C) :
    forall (A : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber),
      (S2130BaseSquare f g T ptA).TwoPullbackWitness :=
  S2240WitnessFamily (S2240ConeIsoAt_of_coneEssSurjAt B C h)

end Family4

/-- **A strong target cover satisfies the presentation coherence.**  The finite-etale
structure underlying a StrongCover carries the full 2-universal property at every point,
and its recorded weak presentation is definitionally the same presentation used by S2130. -/
theorem S2240ConeEssSurjAt_of_strongCover (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) :
    S2240ConeEssSurjAt B (StrongCover.cover Cs) := by
  intro A f g T ptA
  exact (Cs.finiteEtale.baseChange T (S2130PtX f T ptA)).coneEssSurj

/-- **The concrete two-pullback witness for a strong target cover.** -/
noncomputable def S2240WitnessFor_strongCover (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    (S2130BaseSquare f g T ptA).TwoPullbackWitness :=
  S2240WitnessFamily_of_coneEssSurjAt (S2240ConeEssSurjAt_of_strongCover Cs B)
    A f g T ptA

/-- **The concrete two-pullback witness for a coherent target cover.** -/
noncomputable def S2240WitnessFor_coherent (Cs : CoherentCover)
    (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (CoherentCover.cover Cs))
    (g : S1728CoverMap B (CoherentCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    (S2130BaseSquare f g T ptA).TwoPullbackWitness :=
  S2240WitnessFor_strongCover Cs.toStrongCover B A f g T ptA

/-- The S2130 base-change presentation at a strong target cover. -/
noncomputable def S2240HgFor_strongCover (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA) :=
  S2130PresentationOfWitness f g T ptA (S2240WitnessFor_strongCover Cs B A f g T ptA)

/-- Its projection is finite etale, unconditionally. -/
theorem S2240HgFor_strongCover_finiteEtale (Cs : StrongCover S1726Orbicurve)
    (B : S1728Cover) (A : S1728Cover)
    (f : S1728CoverMap A (StrongCover.cover Cs))
    (g : S1728CoverMap B (StrongCover.cover Cs))
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2240Y T) A.source.fiber) :
    IsFinite ((S2240HgFor_strongCover Cs B A f g T ptA).projection.left) ∧
      Etale ((S2240HgFor_strongCover Cs B A f g T ptA).projection.left) :=
  S2130PresentationOfWitness_finiteEtale f g T ptA
    (S2240WitnessFor_strongCover Cs B A f g T ptA)

#check S2240StrictConeIsoAt
#check S2240StrictConeIso_of_coneEssSurj
#check S2240ConcreteTwoPullback_of_coneEssSurj
#check S2240ConeEssSurj_doubled_false
#check S2240NotCPresentationConeEssSurj
#check S2240Hg_of_coneEssSurj
#check S2240ConeEssSurjAt
#check S2240ConeIsoAt
#check S2240ConeIsoAt_of_coneEssSurjAt
#check S2240WitnessFamily_of_coneEssSurjAt
#check S2240ConeEssSurjAt_of_strongCover
#check S2240WitnessFor_strongCover
#check S2240WitnessFor_coherent
#check S2240HgFor_strongCover
#check S2240HgFor_strongCover_finiteEtale

#print axioms S2240StrictConeIsoAt
#print axioms S2240StrictConeIso_of_coneEssSurj
#print axioms S2240ConcreteTwoPullback_of_coneEssSurj
#print axioms S2240ConeEssSurj_doubled_false
#print axioms S2240NotCPresentationConeEssSurj
#print axioms S2240Hg_of_coneEssSurj
#print axioms S2240ConeIsoAt_of_coneEssSurjAt
#print axioms S2240WitnessFamily_of_coneEssSurjAt
#print axioms S2240ConeEssSurjAt_of_strongCover
#print axioms S2240WitnessFor_strongCover
#print axioms S2240WitnessFor_coherent
#print axioms S2240HgFor_strongCover
#print axioms S2240HgFor_strongCover_finiteEtale

end LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual
