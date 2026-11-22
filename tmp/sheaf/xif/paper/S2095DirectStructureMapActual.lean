/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S2095
-/
import tmp.sheaf.xif.paper.S2091SchemeDirectActual
import tmp.sheaf.xif.paper.S2069D6CompositionClosureActual
import tmp.sheaf.xif.paper.S2076IsoCommaTwoPullbackActual
import tmp.sheaf.xif.paper.S2043D6StructureMapEqActual
import tmp.sheaf.xif.paper.S2090StackCancellationObstructionActual

/-!
# S2095: the direct structure-map route for D6(c) -- verdict and exact gap

D6(c) asks for EtaleStackFiniteEtaleMorphism (structureMap f g) with
structureMap f g = toA f g ; A.map.  S2043/S2044/S2069 reduce this to
S2044ToAFiniteEtaleField (representable finite etaleness of the iso-comma
projection toA), and S2086 builds the presentation of toA from a *finite
etale structure on g.map* plus the 2-categorical identification
S2086BaseChangePullback.  The alternative isolated input is
S2087GMapFiniteEtaleField (every cover map is representably finite etale);
S2088/S2090/S2092 record that it is not produced by scheme cancellation.

This file executes the two requested attempts.

## Path A (g.map from B.finiteEtale and C.finiteEtale)

S2095PathAPresentation builds, at every scheme point ptC of C.source, the
"base change through the base" candidate: present C.map at ptC ; C.map,
then present B.map over the apex of that presentation.  Its
pullbackScheme, projection (the composite of the two scheme projections),
projectionMap and toSource are constructed unconditionally, and its
hasProperty field is *free*: the projection is a composite of the two known
finite-etale projections (S2048 composition, no cancellation needed).

The two remaining fields are

* S2095PathAComparison -- the comparison 2-cell in C.source.fiber between
  toSource ; g.map and projection ; ptC;
* S2095PathAPullback -- the two-pullback witness of the candidate square.

Their exact status is proved here:

* S2095PathAComparisonOfPostcomp: the comparison 2-cell follows from
  postcomposition cancellation of 2-isomorphisms along C.map
  (S2090PostcompCancellation) applied to the recorded comparisons of
  B.finiteEtale and C.finiteEtale.  That principle is not available and is
  false for a general stack morphism (S2090); the data only gives the
  comparison after composing with C.map.
* S2095PathAPullback: the candidate apex is the base change of B.map over the
  apex of the C-presentation.  It is not constructed as the fibre product
  (T x_C B); the two-pullback field is exactly the butterfly identification
  that would force the two to agree.  It is recorded as a hypothesis, not
  asserted, and no claim is made that this candidate square is the true
  fibre-product square.

So path A does not close: the missing comparison is postcomposition
cancellation along C.map, and the missing pullback is the butterfly.

## Path B (direct structureMap)

structureMap f g is definitionally (toA f g ; A.map), so by the
(unconditional) composition closure S2069 it suffices that ONE iso-comma
projection is representably finite etale.  This file proves both conditional
assemblies:

* S2095D6FiniteEtale_of_toA,
* S2095D6FiniteEtale_of_toB (using S2043_structureMap_eq' and S2058
  iso-invariance).

For toB the construction goes through, modulo one field only: a finite-etale
certificate for the *other cospan leg* f.map gives, via S2076's two-pullback
witness of the iso-comma square, the full base-change presentation of toB at
every point ptB of B.source -- including its comparison 2-cell, because the
presentation of f.map produces a 2-cell in C.source.fiber, exactly the leg
the iso-comma cone needs.  The only remaining field is
S2095ToBButterfly, the two-pullback witness of the explicit square.  This is
precisely the butterfly (A x_C T) = (T x_B (A x_C B)).

## Honest boundary

No sorry, no new axiom, no Nonempty/Prop gate, no fabricated presentation,
2-cell, two-pullback witness or finite-etale certificate.  The missing inputs
are uninhabited Type-valued definitions.  The axiom audit at the end shows
only propext, Classical.choice and Quot.sound.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2095DirectStructureMapActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S2048FiniteEtaleCompSchemeActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2069D6CompositionClosureActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual
open LeanFormal.IUT.XiFPaper.S2088GMapCancellationActual
open LeanFormal.IUT.XiFPaper.S2090StackCancellationObstructionActual
open LeanFormal.IUT.XiFPaper.S2091SchemeDirectActual

universe u

/-! ## 1. Path B: assembly from one iso-comma projection -/

/-- A finite-etale certificate for the second iso-comma projection gives the
D6(c) structure-map certificate, by S2069 composition closure, S2043's
structureMap_eq' and S2058 2-isomorphism invariance. -/
noncomputable def S2095D6FiniteEtale_of_toB
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (htoB : EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := B.source) (toB f g)) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) := by
  have hcomp : EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := S1726Orbicurve.stack)
      (Pseudofunctor.StrongTrans.vcomp (toB f g) B.map) :=
    S2069CompositionClosure (X := S2042IsoCommaStackObj (f := f) (g := g))
      (Y := B.source) (Z := S1726Orbicurve.stack) (toB f g) B.map htoB B.finiteEtale
  exact S2058IsoInvarianceFiniteEtale
    (X := S2042IsoCommaStackObj (f := f) (g := g)) (Z := S1726Orbicurve.stack)
    (S2043_structureMap_eq' (f := f) (g := g)) hcomp

/-- A finite-etale certificate for the first iso-comma projection gives the
D6(c) structure-map certificate. -/
noncomputable def S2095D6FiniteEtale_of_toA
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (htoA : EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.source) (toA f g)) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) := by
  have hcomp : EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := S1726Orbicurve.stack)
      (Pseudofunctor.StrongTrans.vcomp (toA f g) A.map) :=
    S2069CompositionClosure (X := S2042IsoCommaStackObj (f := f) (g := g))
      (Y := A.source) (Z := S1726Orbicurve.stack) (toA f g) A.map htoA A.finiteEtale
  exact S2058IsoInvarianceFiniteEtale
    (X := S2042IsoCommaStackObj (f := f) (g := g)) (Z := S1726Orbicurve.stack)
    (structureMapEq (f := f) (g := g)) hcomp

/-! ## 2. Path B: construction of the toB presentation from the left leg -/

/-- The C-point (ptB ; g.map). -/
noncomputable def S2095PointC {B C : S1728Cover} (g : S1728CoverMap B C)
    {T : SchemeOverField S1726K}
    (ptB : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber :=
  Pseudofunctor.StrongTrans.vcomp ptB g.map

/-- The pseudo-cone over the iso-comma square attached to a base-change
presentation of the left leg f.map at the C-point (ptB ; g.map).  The
comparison 2-cell exists because f.map lands in C.source, the base of the
iso-comma square. -/
noncomputable def S2095ToBCone {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptB : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber)
    (Pf : EtaleStackBaseChangePresentation f.map T (S2095PointC g ptB)) :
    (EtalePseudofunctorSquare.mk (toA f g) (toB f g) f.map g.map
      (commutes f g)).Cone
      (schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme) where
  toX := Pf.toSource
  toY := Pseudofunctor.StrongTrans.vcomp Pf.projectionMap.transformation ptB
  commutes :=
    Pf.commutes.trans
      (S2043AssociatorIso Pf.projectionMap.transformation ptB g.map).symm

/-- The lift of that cone, from S2076's two-pullback witness. -/
noncomputable def S2095ToBLift {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptB : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber)
    (Pf : EtaleStackBaseChangePresentation f.map T (S2095PointC g ptB)) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme)
      (sitePseudofunctor f g) :=
  (S2076Witness (f := f) (g := g)).lift
    (schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme)
    (S2095ToBCone f g T ptB Pf)

/-- The comparison of the lift with toB: this is the commutes field of the
base-change presentation of toB at ptB. -/
noncomputable def S2095ToBLiftToB {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptB : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber)
    (Pf : EtaleStackBaseChangePresentation f.map T (S2095PointC g ptB)) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2095ToBLift f g T ptB Pf) (toB f g))
      (Pseudofunctor.StrongTrans.vcomp Pf.projectionMap.transformation ptB) :=
  (S2076Witness (f := f) (g := g)).liftToY
    (schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme)
    (S2095ToBCone f g T ptB Pf)

/-- The explicit base-change square of toB at ptB. -/
noncomputable def S2095ToBSquare {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptB : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber)
    (Pf : EtaleStackBaseChangePresentation f.map T (S2095PointC g ptB)) :
    EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor S1726K Pf.pullbackScheme)
      (sitePseudofunctor f g)
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber :=
  EtalePseudofunctorSquare.mk (S2095ToBLift f g T ptB Pf)
    Pf.projectionMap.transformation (toB f g) ptB (S2095ToBLiftToB f g T ptB Pf)

/-- The presentation of toB at ptB: every field except the two-pullback
witness is constructed. -/
noncomputable def S2095ToBPresentation {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptB : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber)
    (Pf : EtaleStackBaseChangePresentation f.map T (S2095PointC g ptB))
    (h : (S2095ToBSquare f g T ptB Pf).TwoPullbackWitness) :
    EtaleStackBaseChangePresentation
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := B.source) (toB f g) T ptB where
  pullbackScheme := Pf.pullbackScheme
  projection := Pf.projection
  projectionMap := Pf.projectionMap
  toSource := S2095ToBLift f g T ptB Pf
  commutes := S2095ToBLiftToB f g T ptB Pf
  isPullback := h

/-- The exact missing 2-categorical field of path B: for every point ptB and
every presentation of the left leg f.map at (ptB ; g.map), the explicit
square is a two-pullback.  This is the butterfly
(T x_C A) = (T x_B (A x_C B)). -/
def S2095ToBButterfly : Type 1 :=
  forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptB : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) B.source.fiber)
    (Pf : EtaleStackBaseChangePresentation f.map T (S2095PointC g ptB)),
    (S2095ToBSquare f g T ptB Pf).TwoPullbackWitness

/-- Path B, conditional form.  A finite-etale certificate for every left leg
f.map (the same field shape as S2087, for the first leg of the cospan)
together with the butterfly two-pullback field gives representable finite
etaleness of every toB.  The finite-etale property of the projection comes
from the left-leg certificate, not from cancellation. -/
noncomputable def S2095ToBFiniteEtale
    (hleft : forall (A B C : S1728Cover) (f : S1728CoverMap A C),
      EtaleStackFiniteEtaleMorphism f.map)
    (hb : S2095ToBButterfly) :
    forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
      EtaleStackFiniteEtaleMorphism
        (source := S2042IsoCommaStackObj (f := f) (g := g))
        (target := B.source) (toB f g) := by
  intro A B C f g
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptB
    exact S2095ToBPresentation f g T ptB
      ((hleft A B C f).baseChange T (S2095PointC g ptB))
      (hb A B C f g T ptB ((hleft A B C f).baseChange T (S2095PointC g ptB)))
  · intro T ptB
    exact (hleft A B C f).hasProperty T (S2095PointC g ptB)

/-- Path B end to end: the left-leg certificate plus the butterfly field give
D6(c). -/
noncomputable def S2095D6FiniteEtaleOfLeftLeg
    (hleft : forall (A B C : S1728Cover) (f : S1728CoverMap A C),
      EtaleStackFiniteEtaleMorphism f.map)
    (hb : S2095ToBButterfly)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2095D6FiniteEtale_of_toB f g (S2095ToBFiniteEtale hleft hb A B C f g)

/-- The global S2087 certificate (every cover map is representably finite
etale) together with the butterfly field gives D6(c).  This is the exact
conditional form of the path-B assembly. -/
noncomputable def S2095D6FiniteEtaleOfGMapCertificates
    (h : S2087GMapFiniteEtaleField) (hb : S2095ToBButterfly)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2095D6FiniteEtaleOfLeftLeg (fun A B C f => h A A C f) hb f g

/-! ## 3. Path A: candidate data and the exact obstruction -/

/-- The presentation of C.map at the point (ptC ; C.map). -/
noncomputable def S2095CPresentation {C : S1728Cover} (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber) :
    EtaleStackBaseChangePresentation C.map T
      (Pseudofunctor.StrongTrans.vcomp ptC C.map) :=
  C.finiteEtale.baseChange T (Pseudofunctor.StrongTrans.vcomp ptC C.map)

/-- The presentation of B.map over the apex of the C-presentation. -/
noncomputable def S2095BPresentation {B C : S1728Cover} (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber) :
    EtaleStackBaseChangePresentation B.map
      (S2095CPresentation T ptC).pullbackScheme
      (Pseudofunctor.StrongTrans.vcomp (S2095CPresentation T ptC).toSource C.map) :=
  B.finiteEtale.baseChange (S2095CPresentation T ptC).pullbackScheme
    (Pseudofunctor.StrongTrans.vcomp (S2095CPresentation T ptC).toSource C.map)

/-- The composite scheme projection of the path-A candidate. -/
noncomputable def S2095PathAProjectionMap {B C : S1728Cover}
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber) :
    SchemeRepresentableMap
      ((S2095BPresentation g T ptC).projection ≫ (S2095CPresentation T ptC).projection) :=
  S2058SchemeRepresentableMapComp (S2095BPresentation g T ptC).projectionMap
    (S2095CPresentation T ptC).projectionMap

/-- Path A, missing field 1: the comparison 2-cell in C.source.fiber. -/
def S2095PathAComparison : Type 1 :=
  forall (B C : S1728Cover) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber),
    Iso (Pseudofunctor.StrongTrans.vcomp (S2095BPresentation g T ptC).toSource g.map)
      (Pseudofunctor.StrongTrans.vcomp (S2095PathAProjectionMap g T ptC).transformation ptC)

/-- Path A, missing field 2: the two-pullback witness of the candidate square
(the butterfly for the candidate apex). -/
def S2095PathAPullback : Type 1 :=
  forall (B C : S1728Cover) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber)
    (h : Iso (Pseudofunctor.StrongTrans.vcomp (S2095BPresentation g T ptC).toSource g.map)
      (Pseudofunctor.StrongTrans.vcomp (S2095PathAProjectionMap g T ptC).transformation ptC)),
    (EtalePseudofunctorSquare.mk (S2095BPresentation g T ptC).toSource
      (S2095PathAProjectionMap g T ptC).transformation g.map ptC h).TwoPullbackWitness

/-- Postcomposition cancellation of 2-isomorphisms, at the level of
category-valued etale pseudofunctors.  No stack structure on the source is
required, so this is the applicable form of the principle S2090 records. -/
def S2095PostcompCancellation : Type 1 :=
  forall {X Y Z : EtaleStackPseudofunctor S1726K} (h : Y ⟶ Z) {a b : X ⟶ Y},
    Iso (Pseudofunctor.StrongTrans.vcomp a h)
      (Pseudofunctor.StrongTrans.vcomp b h) → Iso a b

/-- S2095PostcompCancellation specializes to S2090's statement. -/
def S2095PostcompCancellation_toS2090 (hpc : S2095PostcompCancellation) :
    S2090PostcompCancellation := by
  intro X Y Z g a b e
  exact hpc g e

/-- The obstruction of path A, formally.  Postcomposition cancellation of
2-isomorphisms along C.map would produce the missing comparison 2-cell from
the recorded comparisons of B.finiteEtale and C.finiteEtale.  That principle
is not available and is false for a general stack morphism; the recorded data
only gives the comparison after composing with C.map. -/
noncomputable def S2095PathAComparisonOfPostcomp
    (hpc : S2095PostcompCancellation)
    {B C : S1728Cover} (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2095BPresentation g T ptC).toSource g.map)
      (Pseudofunctor.StrongTrans.vcomp (S2095PathAProjectionMap g T ptC).transformation ptC) := by
  let bP := S2095BPresentation g T ptC
  let cP := S2095CPresentation T ptC
  have hchain :
      Iso (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp bP.toSource g.map) C.map)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp bP.projectionMap.transformation
              cP.projectionMap.transformation) ptC) C.map) :=
    (S2043AssociatorIso bP.toSource g.map C.map).trans
      ((S2043WhiskerLeftIso bP.toSource
          (Pseudofunctor.StrongTrans.vcomp g.map C.map) B.map g.commutes).trans
        (bP.commutes.trans
          ((S2043WhiskerLeftIso bP.projectionMap.transformation
              (Pseudofunctor.StrongTrans.vcomp cP.toSource C.map)
              (Pseudofunctor.StrongTrans.vcomp cP.projectionMap.transformation
                (Pseudofunctor.StrongTrans.vcomp ptC C.map))
              cP.commutes).trans
            ((S2043AssociatorIso bP.projectionMap.transformation
                cP.projectionMap.transformation
                (Pseudofunctor.StrongTrans.vcomp ptC C.map)).symm.trans
              ((S2043AssociatorIso
                (Pseudofunctor.StrongTrans.vcomp bP.projectionMap.transformation
                  cP.projectionMap.transformation) ptC C.map).symm)))))
  exact hpc C.map hchain

/-- The path-A candidate presentation, given its two missing fields. -/
noncomputable def S2095PathAPresentation {B C : S1728Cover} (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber)
    (hcom : Iso (Pseudofunctor.StrongTrans.vcomp (S2095BPresentation g T ptC).toSource g.map)
      (Pseudofunctor.StrongTrans.vcomp (S2095PathAProjectionMap g T ptC).transformation ptC))
    (hpb : (EtalePseudofunctorSquare.mk (S2095BPresentation g T ptC).toSource
      (S2095PathAProjectionMap g T ptC).transformation g.map ptC hcom).TwoPullbackWitness) :
    EtaleStackBaseChangePresentation g.map T ptC where
  pullbackScheme := (S2095BPresentation g T ptC).pullbackScheme
  projection := (S2095BPresentation g T ptC).projection ≫ (S2095CPresentation T ptC).projection
  projectionMap := S2095PathAProjectionMap g T ptC
  toSource := (S2095BPresentation g T ptC).toSource
  commutes := hcom
  isPullback := hpb

/-- Path A, conditional form: the two 2-categorical fields (comparison and
butterfly) give S2087GMapFiniteEtaleField.  The finite-etale property of the
candidate projection is free (S2048 on the two known projections). -/
noncomputable def S2095GMapFiniteEtaleOfPathA
    (hc : S2095PathAComparison) (hp : S2095PathAPullback) :
    S2087GMapFiniteEtaleField := by
  intro A B C g
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptC
    exact S2095PathAPresentation g T ptC (hc B C g T ptC) (hp B C g T ptC (hc B C g T ptC))
  · intro T ptC
    have hb : AlgebraicGeometry.IsFinite (S2095BPresentation g T ptC).projection.left ∧
        AlgebraicGeometry.Etale (S2095BPresentation g T ptC).projection.left :=
      B.finiteEtale.hasProperty (S2095CPresentation T ptC).pullbackScheme
        (Pseudofunctor.StrongTrans.vcomp (S2095CPresentation T ptC).toSource C.map)
    have hc' : AlgebraicGeometry.IsFinite (S2095CPresentation T ptC).projection.left ∧
        AlgebraicGeometry.Etale (S2095CPresentation T ptC).projection.left :=
      C.finiteEtale.hasProperty T (Pseudofunctor.StrongTrans.vcomp ptC C.map)
    haveI := hb.1
    haveI := hb.2
    haveI := hc'.1
    haveI := hc'.2
    exact S2048_isFinite_and_etale_comp
      (f := (S2095BPresentation g T ptC).projection.left)
      (g := (S2095CPresentation T ptC).projection.left)

/-! ## 4. The exact first missing for g.map (representability + property) -/

/-- Exact missing geometric input 1: the base change of every cover map is
representable by a scheme, at every scheme point of its target. -/
def S2095BaseChangePresentations : Type 1 :=
  forall (A B C : S1728Cover) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber),
    EtaleStackBaseChangePresentation g.map T ptC

/-- Exact missing geometric input 2: the projection of *any* base-change
presentation of a cover map is finite etale.  This is the half that would use
scheme cancellation S2091; it needs the presentation to be compared with a
known finite-etale one, which the recorded API does not provide. -/
def S2095ProjectionFiniteEtale : Prop :=
  forall (A B C : S1728Cover) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptC : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber)
    (P : EtaleStackBaseChangePresentation g.map T ptC),
    AlgebraicGeometry.IsFinite P.projection.left ∧
      AlgebraicGeometry.Etale P.projection.left

/-- The two missing geometric inputs give S2087GMapFiniteEtaleField. -/
noncomputable def S2095GMapFiniteEtaleOfData
    (hp : S2095BaseChangePresentations) (hq : S2095ProjectionFiniteEtale) :
    S2087GMapFiniteEtaleField := by
  intro A B C g
  exact { baseChange := fun T ptC => hp A B C g T ptC
          hasProperty := fun T ptC => hq A B C g T ptC (hp A B C g T ptC) }

#print axioms S2095D6FiniteEtale_of_toB
#print axioms S2095D6FiniteEtale_of_toA
#print axioms S2095ToBCone
#print axioms S2095ToBLift
#print axioms S2095ToBLiftToB
#print axioms S2095ToBPresentation
#print axioms S2095ToBFiniteEtale
#print axioms S2095D6FiniteEtaleOfLeftLeg
#print axioms S2095D6FiniteEtaleOfGMapCertificates
#print axioms S2095PathAComparisonOfPostcomp
#print axioms S2095PathAPresentation
#print axioms S2095GMapFiniteEtaleOfPathA
#print axioms S2095GMapFiniteEtaleOfData

end LeanFormal.IUT.XiFPaper.S2095DirectStructureMapActual

end
