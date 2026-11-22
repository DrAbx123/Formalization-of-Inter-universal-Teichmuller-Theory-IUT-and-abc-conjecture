/-
# S2562: S2559HasLiftUnique as an explicit hypothesis for corrected EssSurj

This file connects the refinement predicate S2559HasLiftUnique (lift uniqueness
for the abstract two-pullback witness of an orbicurve cover) to the corrected
essential-surjectivity chain of S2553/S2554/S2555, as an *explicit hypothesis*.

## What is proved here

* S2562HasLiftUnique X / S2562HasLiftUniqueAll: the hypothesis
  hLU : forall X, S2559HasLiftUnique X.finiteEtale.
* S2562CanonicalLift_unique: the exact content of hLU at a scheme-valued
  point: any 1-cell that is a lift of a cone is 2-isomorphic to the canonical
  lift P.isPullback.lift W c.  This is the only place hLU is consumed.
* S2562HasLiftUnique_identityStack / S2562HasLiftUnique_terminalCover:
  the hypothesis is *non-vacuous*: it holds for the identity finite-etale
  structure S2514IdentityFiniteEtale (witness S2514IdWitness, whose lift is
  cone.toY and whose toY leg is the identity).
* The residual obligation S2562ExtractionIsoFromLiftUnique, split into the two
  precise sub-obligations
  S2562TriangleFromLiftUnique and S2562ExtractionIsoFromTriangle, with
  S2562ExtractionIsoFromLiftUnique_of_factor composing them.
* The conditional chain, all compiling:
  extraction iso -> S2554CanonicalData -> S2554CanonicalCover
  -> S2554CanonicalEssSurj -> S2553CorrectedEssSurj
  -> S2541EssSurjOnRepresentable (the last one with the corresponding
  object-identification hypothesis).

## The exact remaining goal (step 1 of the task)

Write bc := X.finiteEtale.baseChange S2482AffineOver S2519BasePoint,
e := bc.toSource : rep bc.pullbackScheme --> X.source.fiber, and let
c : (S2562PointSquare X S2482AffineOver S2519BasePoint).Cone X.source.fiber
be the identity cone S2562IdentityCone X (toX = id, toY = X.map; this is
well typed precisely because S2519BasePoint = StrongTrans.id, i.e. because the
test point is the identity).  Put q := bc.isPullback.lift X.source.fiber c
(= S2562ExtractionLift X).

(a) S2562TriangleFromLiftUnique: hLU gives vcomp e q ~= id on
    rep bc.pullbackScheme.  Indeed id_P and vcomp e q are both lifts of the
    identity cone on P: the toX comparison is
    associator e q bc.toSource ~= whiskerLeftIso e (bc.isPullback.liftToX _ c)
    ~= rightUnitor e, and the toY comparison is
    associator e q bc.projectionMap.transformation ~= whiskerLeftIso e
    (bc.isPullback.liftToY _ c) ~= bc.commutes ~= rightUnitor
    bc.projectionMap.transformation, where the last step uses
    S2519BasePoint = StrongTrans.id.  So hLU at P and the identity cone on P
    applies.
(b) S2562ExtractionIsoFromTriangle: transport e and q along hS and apply
    the 2-Yoneda comparison S1742HomOfStrongTrans.  The *unit* triangle
    vcomp q e ~= c.toX = id is bc.isPullback.liftToX (no hypothesis), and
    (a) is the *counit* triangle, so S1742HomOfStrongTrans e is an iso of
    schemes with inverse S1742HomOfStrongTrans q.  The compatibility
    e_scheme ~= S2554CanonicalMap X S hS = bc.projection is the 2-Yoneda image
    of bc.commutes (whose right leg is the identity S2519BasePoint).

Step (a) is PROVED in section 3b (S2562TriangleFromLiftUnique_proof).  Only
step (b) remains: S2562ExtractionIsoFromTriangle, the 2-Yoneda translation of
the triangle plus bc.commutes into a scheme isomorphism with the required
compatibility.  Everything downstream is proved below from the resulting
S2555ExtractionIso.
-/
import tmp.sheaf.xif.paper.S2559ConcreteWitnessRefinementPlanActual
import tmp.sheaf.xif.paper.S2555ExtractionTransportActual
import tmp.sheaf.xif.paper.S2554CanonicalEssSurjActual
import tmp.sheaf.xif.paper.S2553CorrectedEssSurjConditionalActual
import tmp.sheaf.xif.paper.S2541EssSurjAuditActual
import tmp.sheaf.xif.paper.S2521RepresentableStackActual
import tmp.sheaf.xif.paper.S2514IdentityFiniteEtaleActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
open LeanFormal.IUT.XiFPaper.S2541EssSurjAuditActual
open LeanFormal.IUT.XiFPaper.S2554CanonicalEssSurjActual
open LeanFormal.IUT.XiFPaper.S2555ExtractionTransportActual
open LeanFormal.IUT.XiFPaper.S2553CorrectedEssSurjConditionalActual
open LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
open LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual
open LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual


/-! ## 1. The explicit lift-uniqueness hypothesis -/

/-- Explicit hypothesis: the lift uniqueness of S2559 for the finite-etale
structure of one orbicurve cover. -/
def S2562HasLiftUnique (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) : Prop :=
  S2559HasLiftUnique X.finiteEtale

/-- The all-covers form of the hypothesis, as required by the conditional
essential-surjectivity chain. -/
def S2562HasLiftUniqueAll : Prop :=
  ∀ X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve, S2562HasLiftUnique X

/-- The exact content of hLU at a scheme-valued point of the base. -/
theorem S2562HasLiftUnique.at
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (hLU : S2562HasLiftUnique X)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      S2482Orbicurve.stack.fiber) :
    (let bc := X.finiteEtale.baseChange T q
     let sq := Iut.EtalePseudofunctorSquare.mk
       bc.toSource bc.projectionMap.transformation X.map q bc.commutes
     S2558LiftUnique sq bc.isPullback) :=
  hLU T q

/-- The base-change square of the finite-etale structure at a scheme-valued
point, written out as a named square. -/
noncomputable def S2562PointSquare
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      S2482Orbicurve.stack.fiber) :
    Iut.EtalePseudofunctorSquare
      (Iut.schemeRepresentableEtalePseudofunctor F
        (X.finiteEtale.baseChange T q).pullbackScheme)
      X.source.fiber
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      S2482Orbicurve.stack.fiber :=
  Iut.EtalePseudofunctorSquare.mk
    (X.finiteEtale.baseChange T q).toSource
    (X.finiteEtale.baseChange T q).projectionMap.transformation
    X.map q (X.finiteEtale.baseChange T q).commutes

/-- Lift uniqueness for the named square. -/
theorem S2562PointSquare_hasLiftUnique
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (hLU : S2562HasLiftUnique X)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      S2482Orbicurve.stack.fiber) :
    S2558LiftUnique (S2562PointSquare X T q)
      (X.finiteEtale.baseChange T q).isPullback :=
  hLU T q

/-- The canonical lift is characterized by lift uniqueness: every lift of a cone
is 2-isomorphic to P.isPullback.lift W c.  This is the exact form in which
hLU enters the extraction argument. -/
theorem S2562CanonicalLift_unique
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (hLU : S2562HasLiftUnique X)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      S2482Orbicurve.stack.fiber)
    (W : Iut.EtaleStackPseudofunctor F)
    {c : (S2562PointSquare X T q).Cone W}
    {L : Pseudofunctor.StrongTrans W
      (Iut.schemeRepresentableEtalePseudofunctor F
        (X.finiteEtale.baseChange T q).pullbackScheme)}
    (hL : S2558LiftOfCone (S2562PointSquare X T q) c L) :
    Nonempty (L ≅ (X.finiteEtale.baseChange T q).isPullback.lift W c) :=
  S2562PointSquare_hasLiftUnique hLU T q W c L _
    hL
    ⟨(X.finiteEtale.baseChange T q).isPullback.liftToX W c,
      (X.finiteEtale.baseChange T q).isPullback.liftToY W c⟩

/-! ## 2. Non-vacuity of the hypothesis -/

/-- The identity finite-etale structure satisfies lift uniqueness.  The witness
is S2514IdWitness: its toY leg is the identity, so every lift of a cone is
2-isomorphic to cone.toY through the cone's own comparison. -/
theorem S2562HasLiftUnique_identityStack :
    S2559HasLiftUnique
      (map := Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber)
      S2514IdentityFiniteEtale := by
  intro T q W c L1 L2 h1 h2 lift1 lift2
  exact ⟨(Pseudofunctor.StrongTrans.rightUnitor h1).symm.trans
    (lift1.toY.trans
      (lift2.toY.symm.trans (Pseudofunctor.StrongTrans.rightUnitor h2)))⟩

/-- The identity cover of the S2482 orbicurve satisfies the explicit
hypothesis. -/
theorem S2562HasLiftUnique_terminalCover :
    S2562HasLiftUnique S2514TerminalCover :=
  S2562HasLiftUnique_identityStack

/-- The all-covers hypothesis is inhabited at the identity cover: it is not a
vacuous assumption, only an unproved one for arbitrary covers. -/
theorem S2562HasLiftUnique_terminalCover_apply :
    S2559HasLiftUnique S2514TerminalCover.finiteEtale :=
  S2562HasLiftUnique_terminalCover

/-! ## 3. The extraction point and the exact residual obligations -/

/-- The base change at the identity point, the one used by S2555ExtractionIso. -/
noncomputable def S2562ExtractionBaseChange
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    Iut.EtaleStackBaseChangePresentation X.map S2482AffineOver S2519BasePoint :=
  X.finiteEtale.baseChange S2482AffineOver S2519BasePoint

/-- The identity cone on the source of a representable cover.  It is a cone on
the base-change square exactly because the test point S2519BasePoint is the
identity strong transformation. -/
noncomputable def S2562IdentityCone
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    (S2562PointSquare X S2482AffineOver S2519BasePoint).Cone X.source.fiber where
  toX := Pseudofunctor.StrongTrans.id X.source.fiber
  toY := X.map
  commutes := (Pseudofunctor.StrongTrans.leftUnitor X.map).trans
    (Pseudofunctor.StrongTrans.rightUnitor X.map).symm

/-- The lift q of the identity cone: the extraction comparison from the source
cover to the base-changed scheme. -/
noncomputable def S2562ExtractionLift
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    Pseudofunctor.StrongTrans X.source.fiber
      (Iut.schemeRepresentableEtalePseudofunctor F
        (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme) :=
  (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).isPullback.lift
    X.source.fiber (S2562IdentityCone X)

/-- The P-side triangle that lift uniqueness has to produce:
toSource ~= lift(identity cone) ~= id on the base-changed scheme.  This is the
counit triangle of the two-pullback square at the identity point. -/
def S2562ExtractionTriangle
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) : Prop :=
  Nonempty
    (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
        (S2562ExtractionLift X))
      (Pseudofunctor.StrongTrans.id
        (Iut.schemeRepresentableEtalePseudofunctor F
          (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme)))

/-- Residual obligation (a): lift uniqueness implies the P-side triangle. -/
def S2562TriangleFromLiftUnique : Prop :=
  ∀ X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve,
    S2562HasLiftUnique X → S2562ExtractionTriangle X

/-- Residual obligation (b): the P-side triangle (together with the
unit triangle already supplied by liftToX) implies the extraction iso,
by 2-Yoneda and the compatibility recorded in bc.commutes. -/
def S2562ExtractionIsoFromTriangle : Prop :=
  ∀ (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S),
    S2562ExtractionTriangle X → S2555ExtractionIso X S hS

/-- The single residual obligation of step 1: lift uniqueness implies the
missing extraction isomorphism. -/
def S2562ExtractionIsoFromLiftUnique : Prop :=
  ∀ (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S),
    S2562HasLiftUnique X → S2555ExtractionIso X S hS

/-- The residual obligation factors through the two precise sub-obligations. -/
theorem S2562ExtractionIsoFromLiftUnique_of_factor
    (hTri : S2562TriangleFromLiftUnique )
    (hIso : S2562ExtractionIsoFromTriangle ) :
    S2562ExtractionIsoFromLiftUnique  :=
  fun X S hS hLU => hIso X S hS (hTri X hLU)

/-! ## 3b. Step 1(a): lift uniqueness proves the P-side triangle

The triangle is the *counit* of the two-pullback square at the identity point.
Both the identity 1-cell and toSource (composed with) lift(identity cone) are
lifts of the identity cone on the base-changed scheme, so lift uniqueness
identifies them.
-/

/-- The identity cone on the base-changed scheme P. -/
noncomputable def S2562IdentityConeP
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    (S2562PointSquare X S2482AffineOver S2519BasePoint).Cone
      (Iut.schemeRepresentableEtalePseudofunctor F
        (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme) where
  toX := (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
  toY := (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).projectionMap.transformation
  commutes := (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).commutes

/-- The identity 1-cell is a lift of the identity cone. -/
def S2562LiftOfCone_idP
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    S2558LiftOfCone (S2562PointSquare X S2482AffineOver S2519BasePoint)
      (S2562IdentityConeP X)
      (Pseudofunctor.StrongTrans.id
        (Iut.schemeRepresentableEtalePseudofunctor F
          (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme)) :=
  ⟨Pseudofunctor.StrongTrans.leftUnitor _, Pseudofunctor.StrongTrans.leftUnitor _⟩

/-- The canonical lift of the identity cone is a lift of the identity cone. -/
def S2562LiftOfCone_canonical
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    S2558LiftOfCone (S2562PointSquare X S2482AffineOver S2519BasePoint)
      (S2562IdentityConeP X)
      ((X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).isPullback.lift
        (Iut.schemeRepresentableEtalePseudofunctor F
          (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme)
        (S2562IdentityConeP X)) :=
  ⟨(X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).isPullback.liftToX _ _,
    (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).isPullback.liftToY _ _⟩

/-- The toX comparison of the lift-of-cone datum for toSource (composed with)
lift(identity cone). -/
noncomputable def S2562ExtractionTriangle_cmpX
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp
            (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
            (S2562ExtractionLift X))
          (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource)
      (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource := by
  let Bicat := Iut.EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let a : Bicat := Iut.schemeRepresentableEtalePseudofunctor F
    (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme
  let b : Bicat := X.source.fiber
  let f : a ⟶ b := (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
  let g : b ⟶ a := S2562ExtractionLift X
  let k : a ⟶ b := (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
  let eta : (g ≫ k) ≅ 𝟙 b :=
    (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).isPullback.liftToX
      X.source.fiber (S2562IdentityCone X)
  exact (Bicategory.associator f g k).trans
    ((Bicategory.whiskerLeftIso f eta).trans (Bicategory.rightUnitor f))

/-- The toY comparison of the same lift-of-cone datum; it uses bc.commutes,
whose right leg is the identity S2519BasePoint. -/
noncomputable def S2562ExtractionTriangle_cmpY
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp
            (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
            (S2562ExtractionLift X))
          (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).projectionMap.transformation)
      (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).projectionMap.transformation := by
  let Bicat := Iut.EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let a : Bicat := Iut.schemeRepresentableEtalePseudofunctor F
    (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme
  let b : Bicat := X.source.fiber
  let c : Bicat := Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver
  let f : a ⟶ b := (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
  let g : b ⟶ a := S2562ExtractionLift X
  let k : a ⟶ c :=
    (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).projectionMap.transformation
  let m : b ⟶ c := X.map
  let etaY : (g ≫ k) ≅ m :=
    (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).isPullback.liftToY
      X.source.fiber (S2562IdentityCone X)
  let comm : (f ≫ m) ≅ (k ≫ 𝟙 c) :=
    (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).commutes
  exact (Bicategory.associator f g k).trans
    ((Bicategory.whiskerLeftIso f etaY).trans
      (comm.trans (Bicategory.rightUnitor k)))

/-- toSource (composed with) lift(identity cone) is a lift of the identity
cone on P. -/
def S2562LiftOfCone_extraction
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) :
    S2558LiftOfCone (S2562PointSquare X S2482AffineOver S2519BasePoint)
      (S2562IdentityConeP X)
      (Pseudofunctor.StrongTrans.vcomp
        (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
        (S2562ExtractionLift X)) :=
  ⟨S2562ExtractionTriangle_cmpX X, S2562ExtractionTriangle_cmpY X⟩

/-- Step 1(a), proved: lift uniqueness yields the P-side triangle. -/
theorem S2562TriangleFromLiftUnique_proof :
    S2562TriangleFromLiftUnique := by
  intro X hLU
  have hq := hLU S2482AffineOver S2519BasePoint
    (Iut.schemeRepresentableEtalePseudofunctor F
      (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme)
    (S2562IdentityConeP X)
    (Pseudofunctor.StrongTrans.vcomp
      (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).toSource
      (S2562ExtractionLift X))
    ((X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).isPullback.lift _
      (S2562IdentityConeP X))
    (S2562LiftOfCone_extraction X) (S2562LiftOfCone_canonical X)
  have hi := hLU S2482AffineOver S2519BasePoint
    (Iut.schemeRepresentableEtalePseudofunctor F
      (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme)
    (S2562IdentityConeP X)
    (Pseudofunctor.StrongTrans.id
      (Iut.schemeRepresentableEtalePseudofunctor F
        (X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).pullbackScheme))
    ((X.finiteEtale.baseChange S2482AffineOver S2519BasePoint).isPullback.lift _
      (S2562IdentityConeP X))
    (S2562LiftOfCone_idP X) (S2562LiftOfCone_canonical X)
  exact ⟨hq.some.trans hi.some.symm⟩

/-- Step 1 reduces to obligation (b) alone: the P-side triangle is proved. -/
theorem S2562ExtractionIsoFromLiftUnique_of_triangle
    (hIso : S2562ExtractionIsoFromTriangle) :
    S2562ExtractionIsoFromLiftUnique :=
  S2562ExtractionIsoFromLiftUnique_of_factor S2562TriangleFromLiftUnique_proof hIso

/-! ## 4. Conditional chain from the extraction iso -/

/-- Step 1 consumed: the extraction iso, as a hypothesis. -/
theorem S2562ExtractionIso
    (hRes : S2562ExtractionIsoFromLiftUnique )
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (hLU : S2562HasLiftUnique X) :
    S2555ExtractionIso X S hS :=
  hRes X S hS hLU

/-- Step 2: the canonical finite-etale data. -/
theorem S2562CanonicalData
    (hRes : S2562ExtractionIsoFromLiftUnique )
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (hLU : S2562HasLiftUnique X) :
    S2554CanonicalData X S hS :=
  S2555CanonicalData_of_extractionIso X S hS (hRes X S hS hLU)

/-- The canonical data are inhabited. -/
theorem S2562CanonicalData_nonempty
    (hRes : S2562ExtractionIsoFromLiftUnique )
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (hLU : S2562HasLiftUnique X) :
    Nonempty (S2554CanonicalData X S hS) :=
  ⟨S2562CanonicalData hRes S hS hLU⟩

/-- Step 3: the canonical cover C0. -/
noncomputable def S2562CanonicalCover
    (hRes : S2562ExtractionIsoFromLiftUnique )
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (hLU : S2562HasLiftUnique X) :
    FiniteEtaleCover S2482AffineScheme :=
  S2554CanonicalCover X S hS (S2562CanonicalData hRes S hS hLU)

/-- The canonical cover is the S2554 canonical cover at the extraction data. -/
theorem S2562CanonicalCover_eq
    (hRes : S2562ExtractionIsoFromLiftUnique )
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (hLU : S2562HasLiftUnique X) :
    S2562CanonicalCover hRes S hS hLU
      = S2554CanonicalCover X S hS (S2562CanonicalData hRes S hS hLU) :=
  rfl

/-! ## 5. Cover identification: the residual object-level input -/

/-- Residual object-level input: the canonical cover of S2554 is isomorphic
to the original cover.  Its scheme is S by construction, so this is a
statement about the cover maps and their 2-isomorphism classes. -/
def S2562CanonicalCoverIsoFromData : Prop :=
  ∀ (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS),
    Nonempty (S2517InvObj (S2554CanonicalCover X S hS D) ≅ X)

/-- The stronger object-level input needed for the equality form
S2541EssSurjOnRepresentable. -/
def S2562CanonicalCoverIdFromData : Prop :=
  ∀ (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve)
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS),
    ∃ C : FiniteEtaleCover S2482AffineScheme, S2517InvObj C = X

/-- The canonical cover has scheme S by construction.  Thus the cover
identification is exactly a map-level statement. -/
theorem S2562CanonicalCover_scheme
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (S : Iut.SchemeOverField F) (hS : X.source = S2517TStack S)
    (D : S2554CanonicalData X S hS) :
    S2517CScheme (S2554CanonicalCover X S hS D) = S := by
  show Over.mk (Over.Hom.left (S2554CanonicalMap X S hS) ≫ S2482AffineOver.hom) = S
  rw [Over.w (S2554CanonicalMap X S hS)]
  rfl

/-! ## 6. Conditional essential surjectivity -/

/-- Step 3-4: the S2554 canonical essential-surjectivity target, conditionally
on the extraction iso and on the cover identification. -/
theorem S2562CanonicalEssSurj
    (hRes : S2562ExtractionIsoFromLiftUnique )
    (hLU : S2562HasLiftUniqueAll )
    (hCov : S2562CanonicalCoverIsoFromData ) :
    S2554CanonicalEssSurj  := by
  intro X S hS _
  exact ⟨S2562CanonicalCover hRes S hS (hLU X),
    hCov X S hS (S2562CanonicalData hRes S hS (hLU X))⟩

/-- Step 4: the corrected representable essential-surjectivity target
S2553CorrectedEssSurj, conditionally on the same data. -/
theorem S2562CorrectedEssSurj
    (hRes : S2562ExtractionIsoFromLiftUnique )
    (hLU : S2562HasLiftUniqueAll )
    (hCov : S2562CanonicalCoverIsoFromData ) :
    S2553CorrectedEssSurj  := by
  intro X hX
  obtain ⟨S, hS⟩ := hX
  exact ⟨S2562CanonicalCover hRes S hS (hLU X),
    hCov X S hS (S2562CanonicalData hRes S hS (hLU X))⟩

/-- The equality form S2541EssSurjOnRepresentable, conditionally on the
object-identification input. -/
theorem S2562EssSurjOnRepresentable
    (hRes : S2562ExtractionIsoFromLiftUnique )
    (hLU : S2562HasLiftUniqueAll )
    (hId : S2562CanonicalCoverIdFromData ) :
    S2541EssSurjOnRepresentable  := by
  intro X hX
  obtain ⟨S, hS⟩ := hX
  exact hId X S hS (S2562CanonicalData hRes S hS (hLU X))

/-- The same statement directly in the form of the S2519 essential-surjectivity
goal, restricted to representable covers. -/
theorem S2562CorrectedEssSurj_apply
    (hRes : S2562ExtractionIsoFromLiftUnique )
    (hLU : S2562HasLiftUniqueAll )
    (hCov : S2562CanonicalCoverIsoFromData )
    {X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve}
    (hX : S2541Representable X) :
    ∃ C : FiniteEtaleCover S2482AffineScheme,
      Nonempty (S2517InvObj C ≅ X) :=
  S2562CorrectedEssSurj hRes hLU hCov X hX

/-! ## 7. Final conditional targets with (a) discharged -/

/-- The S2554 target from the single residual (b) and the cover identification. -/
theorem S2562CanonicalEssSurj_of_triangle
    (hIso : S2562ExtractionIsoFromTriangle)
    (hLU : S2562HasLiftUniqueAll)
    (hCov : S2562CanonicalCoverIsoFromData) :
    S2554CanonicalEssSurj :=
  S2562CanonicalEssSurj (S2562ExtractionIsoFromLiftUnique_of_triangle hIso) hLU hCov

/-- The corrected representable essential-surjectivity target S2553, from the
single residual (b), the explicit lift-uniqueness hypothesis on all covers, and
the cover identification. -/
theorem S2562CorrectedEssSurj_of_triangle
    (hIso : S2562ExtractionIsoFromTriangle)
    (hLU : S2562HasLiftUniqueAll)
    (hCov : S2562CanonicalCoverIsoFromData) :
    S2553CorrectedEssSurj :=
  S2562CorrectedEssSurj (S2562ExtractionIsoFromLiftUnique_of_triangle hIso) hLU hCov

/-- The equality form, from the same data and the object-identification input. -/
theorem S2562EssSurjOnRepresentable_of_triangle
    (hIso : S2562ExtractionIsoFromTriangle)
    (hLU : S2562HasLiftUniqueAll)
    (hId : S2562CanonicalCoverIdFromData) :
    S2541EssSurjOnRepresentable :=
  S2562EssSurjOnRepresentable (S2562ExtractionIsoFromLiftUnique_of_triangle hIso) hLU hId

#check S2562HasLiftUnique
#check S2562HasLiftUniqueAll
#check S2562HasLiftUnique.at
#check S2562PointSquare
#check S2562PointSquare_hasLiftUnique
#check S2562CanonicalLift_unique
#check S2562HasLiftUnique_identityStack
#check S2562HasLiftUnique_terminalCover
#check S2562ExtractionBaseChange
#check S2562IdentityCone
#check S2562ExtractionLift
#check S2562ExtractionTriangle
#check S2562TriangleFromLiftUnique
#check S2562ExtractionIsoFromTriangle
#check S2562ExtractionIsoFromLiftUnique
#check S2562ExtractionIsoFromLiftUnique_of_factor
#check S2562ExtractionIso
#check S2562CanonicalData
#check S2562CanonicalData_nonempty
#check S2562CanonicalCover
#check S2562CanonicalCover_scheme
#check S2562CanonicalCoverIsoFromData
#check S2562CanonicalCoverIdFromData
#check S2562CanonicalEssSurj
#check S2562CorrectedEssSurj
#check S2562EssSurjOnRepresentable
#check S2562IdentityConeP
#check S2562LiftOfCone_idP
#check S2562LiftOfCone_canonical
#check S2562ExtractionTriangle_cmpX
#check S2562ExtractionTriangle_cmpY
#check S2562LiftOfCone_extraction
#check S2562TriangleFromLiftUnique_proof
#check S2562ExtractionIsoFromLiftUnique_of_triangle
#check S2562CanonicalEssSurj_of_triangle
#check S2562CorrectedEssSurj_of_triangle
#check S2562EssSurjOnRepresentable_of_triangle
#check S2562CorrectedEssSurj_apply

#print axioms S2562CanonicalLift_unique
#print axioms S2562HasLiftUnique_identityStack
#print axioms S2562HasLiftUnique_terminalCover
#print axioms S2562CanonicalCover_scheme
#print axioms S2562CanonicalEssSurj
#print axioms S2562CorrectedEssSurj
#print axioms S2562EssSurjOnRepresentable
#print axioms S2562TriangleFromLiftUnique_proof
#print axioms S2562CorrectedEssSurj_of_triangle

end LeanFormal.IUT.XiFPaper.S2562CorrectedEssSurjLiftUniqueActual
end
