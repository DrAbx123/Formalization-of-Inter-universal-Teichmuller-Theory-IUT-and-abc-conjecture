import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# S2070: the actual CurveEtaleFundamentalGroupCard for the once-punctured curve

Task: construct an inhabitant of
LeanFormal.IUT.IUTII.Frobenioid.Example36.CurveEtaleFundamentalGroupCard K
for the once-punctured curve y^2 = x^3 - x (i.e. E \ {O}), or give the exact
first missing, with no fake and no Nonempty wrapper.

## What this file does

1.  (task (1)) Fills coverCategory with
    FiniteEtaleCover (puncturedEllipticCurveScheme K) from
    LeanFormal/IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean, and
    fiber with geometricFiberFunctor Omega x (the geometric point
    x : Spec Omega -> X).  Both are the actual objects, no substitution.

2.  (task (2)) Reduces PreGaloisCategory (FiniteEtaleCover X) to EXACTLY ONE
    missing axiom.  Of the five PreGaloisCategory fields, four are already
    proved in the tree for an arbitrary scheme (Example36CurveGaloisCategory):
    terminal (G1), pullbacks (G1), finite coproducts (G2), direct summands (G3).
    The only unproved field is hasQuotientsByFiniteGroups (G2).  This is
    proved here as a reduction, with no axiom introduced:
    preGaloisCategory_of_hasQuotients.

3.  (task (3)) Settles the profinite structure.  Aut F is ALREADY a profinite
    group in Mathlib (it carries the compact, totally disconnected, Hausdorff
    topological-group structure of Mathlib/CategoryTheory/Galois/Topology.lean),
    so NO profinite completion is needed: ProfiniteGrp.of (Aut F) is the
    fundamental group, and Mathlib's
    PreGaloisCategory.IsFundamentalGroup F (Aut F) is an instance.  This is
    proved here for ProfiniteGrp.of (Aut F).

4.  (task (4)) Two precise findings, both checked in this file.

    UNIVERSE OBSTRUCTION (fatal for the frozen card).  The frozen
    CurveEtaleFundamentalGroupCard (Example36CurveScheme.lean:294) declares
    coverCategory : Type u with Category.{u, u} and
    fundamentalGroup : ProfiniteGrp.{u}.  For K : Type u the actual cover
    category is FiniteEtaleCover (puncturedEllipticCurveScheme K), which lives
    in Type (u+1) with Category.{u, u+1}, and its fiber-functor automorphism
    group lives in Type (u+1).  All three are off by exactly one universe, so
    the frozen card CANNOT be instantiated with the actual finite etale covers
    at the universe of K; this is independent of any missing Galois-category
    theorem.  The corrected card is CurveEtaleFundamentalGroupCardV below
    (every universe raised by one).

    MATHEMATICAL RESIDUE.  After the universe correction the frozen card has
    exactly two mathematical obligations, namely
    GaloisCategory (FiniteEtaleCover X) and a FintypeCat-valued fiber functor.
    Everything else in the card is unconstrained data (geometricPiOne :
    ProfiniteGrp and geometricConnectedness : Prop have no property attached),
    and fundamentalGroup / action / isFundamentalGroup are produced by Mathlib
    from any fiber functor.  This is proved: mkCardV below is fully generic in
    the category and the fiber functor.

    The two remaining obligations are frozen as precise Props:
    CurveQuotientsByFiniteGroups and GeometricFiberFinite, and the six
    FiberFunctor obligations as the Prop structure FiberFunctorCertificate.
    No inhabitant is asserted.

## References

* LeanFormal/IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean
  (FiniteEtaleCover, geometricFiberObject, geometricFiberFunctor,
  curveEtaleFundamentalGroup)
* LeanFormal/IUT/IUTII/Frobenioid/Example36CurveGaloisCategory.lean
  (the four proved PreGaloisCategory fields)
* LeanFormal/IUT/IUTII/Frobenioid/Example36CurveScheme.lean (the frozen card)
* LeanFormal/IUT/Foundations/AlgebraicGeometry/SourceCurveG2Quotients.lean
  (scheme-level G2 reduction, consumed below)
* Mathlib CategoryTheory.Galois.Basic, ...IsFundamentalgroup, ...Topology
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open LeanFormal.IUT.Foundations.Geometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

/-! ## 1. The category of finite etale covers and the geometric fiber functor -/

/-- The base scheme: the affine once-punctured elliptic curve E \ {O} with
E : y^2 = x^3 - x, exactly as defined in
IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean.  It is
definitionally Example36.curveScheme K (see curveBase_eq_curveScheme), so
every scheme-level result of Example36 applies verbatim. -/
abbrev CurveBase (K : Type u) [Field K] : Scheme.{u} := puncturedEllipticCurveScheme K

/-- Task (1): the coverCategory of the card, instantiated with the actual
category FiniteEtaleCover X = ObjectProperty.FullSubcategory (Etale AND
IsFinite over X) of finite etale covers of the once-punctured curve. -/
abbrev CurveEtaleCoverCategory (K : Type u) [Field K] : Type (u + 1) :=
  FiniteEtaleCover (CurveBase K)

instance (K : Type u) [Field K] : Category.{u, u + 1} (CurveEtaleCoverCategory K) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory
    (finiteEtaleCoverProperty (CurveBase K))))

/-- The base curve is definitionally the Example36 affine Weierstrass curve. -/
theorem curveBase_eq_curveScheme (K : Type u) [Field K] :
    CurveBase K = curveScheme K := rfl

/-- The cover category used below is definitionally the Example36 cover
category, so the four proved PreGaloisCategory fields transfer verbatim. -/
theorem curveEtaleCoverCategory_eq (K : Type u) [Field K] :
    CurveEtaleCoverCategory K =
      EtaleCoverFoundations.FiniteEtaleCover (curveScheme K) := rfl

/-- Task (1): the fiber of the card, instantiated with the actual geometric
fiber functor Y |-> { s : Spec Omega -> Y // s >> structure Y = x } of
CurveEtaleFundamentalGroup.lean.  It is Type u-valued here; the
FintypeCat-valued lift is curveGeometricFiberFunctorFintype below, and is
conditional on the missing finiteness of the geometric fiber. -/
abbrev curveGeometricFiberFunctor (K : Type u) [Field K] (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) :
    CurveEtaleCoverCategory K ⥤ Type u :=
  geometricFiberFunctor (X := CurveBase K) Omega x

/-- The automorphism group of the geometric fiber functor, i.e. the actual
etale fundamental group of CurveEtaleFundamentalGroup.lean. -/
abbrev curveFiberAutGroup (K : Type u) [Field K] (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) : Type (u + 1) :=
  curveEtaleFundamentalGroup (X := CurveBase K) Omega x

/-- The geometric-connectedness proposition of the card, supplied with genuine
content for the curve: connectedness of the base scheme.  (The card's field has
no property attached; this is the honest reading, and it is a theorem for the
once-punctured curve.) -/
def curveGeometricConnectedness (K : Type u) [Field K] : Prop :=
  ConnectedSpace (CurveBase K)

/-- The once-punctured curve is connected (proved in the tree as
Example36.curveOncePunctured_connected). -/
theorem curveGeometricConnectedness_holds (K : Type u) [Field K] :
    curveGeometricConnectedness K :=
  curveOncePunctured_connected K

/-! ## 2. The four already-proved PreGaloisCategory fields

These are the Example36CurveGaloisCategory theorems, restated for the
CurveEtaleFundamentalGroup.FiniteEtaleCover of task (1).  The restatement is
rfl-convertible (curveEtaleCoverCategory_eq), so nothing is reproved.
-/

/-- (G1) The identity cover is a terminal object. -/
theorem curveEtaleCover_hasTerminal (K : Type u) [Field K] :
    HasTerminal (CurveEtaleCoverCategory K) :=
  (finiteEtaleCover_terminalCover_isTerminal (curveScheme K)).hasTerminal

/-- (G1) Finite etale covers have pullbacks. -/
theorem curveEtaleCover_hasPullbacks (K : Type u) [Field K] :
    HasPullbacks (CurveEtaleCoverCategory K) :=
  finiteEtaleCoverHasPullbacks (curveScheme K)

/-- (G2) Finite etale covers have finite coproducts. -/
theorem curveEtaleCover_hasFiniteCoproducts (K : Type u) [Field K] :
    HasFiniteCoproducts (CurveEtaleCoverCategory K) :=
  finiteEtaleCover_hasFiniteCoproducts (S := curveScheme K)

/-- (G3) Every monomorphism of finite etale covers is an isomorphism on a
direct summand. -/
theorem curveEtaleCover_monoInducesIsoOnDirectSummand (K : Type u) [Field K]
    {X Y : CurveEtaleCoverCategory K} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : CurveEtaleCoverCategory K) (v : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i v)) :=
  @finiteEtaleCover_monoInducesIsoOnDirectSummand (curveScheme K) X Y i ‹Mono i›

/-! ## 3. PreGaloisCategory reduced to exactly one missing field -/

/-- The exact missing PreGaloisCategory field (G2), stated as a Prop for the
actual cover category: quotients of finite etale covers by finite group
actions.  This is the only unproved field. -/
def CurveQuotientsByFiniteGroups (K : Type u) [Field K] : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (CurveEtaleCoverCategory K)

/-- Internal syntactic presentation of the cover category, definitionally equal
to CurveEtaleCoverCategory K (curveEtaleCoverCategory_eq, rfl).  It exists so
that the four proved PreGaloisCategory fields apply without any definitional
unfolding of the ring/scheme terms; the transport back to
CurveEtaleCoverCategory K is the cheap type-level conversion of
preGaloisCategory_of_hasQuotients. -/
abbrev CurveCoverCategoryE36 (K : Type u) [Field K] : Type (u + 1) :=
  EtaleCoverFoundations.FiniteEtaleCover (curveScheme K)

/-- The same missing G2 field, stated at the syntactic presentation. -/
def CurveQuotientsE36 (K : Type u) [Field K] : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (CurveCoverCategoryE36 K)

/-- The PreGaloisCategory instance assembled purely from the four proved
Example36 theorems plus the single missing field. -/
theorem preGaloisCategory_e36 (K : Type u) [Field K] (hq : CurveQuotientsE36 K) :
    PreGaloisCategory (CurveCoverCategoryE36 K) where
  hasTerminal := (finiteEtaleCover_terminalCover_isTerminal (curveScheme K)).hasTerminal
  hasPullbacks := finiteEtaleCoverHasPullbacks (curveScheme K)
  hasFiniteCoproducts := finiteEtaleCover_hasFiniteCoproducts
  hasQuotientsByFiniteGroups := fun G _ _ => hq G
  monoInducesIsoOnDirectSummand := fun i => finiteEtaleCover_monoInducesIsoOnDirectSummand i

/-- Task (2): PreGaloisCategory for the actual finite etale cover category of
the once-punctured curve, from the single missing quotient field.  The other
four fields are the proved theorems of section 2; no axiom is used. -/
theorem preGaloisCategory_of_hasQuotients (K : Type u) [Field K]
    (hq : CurveQuotientsByFiniteGroups K) :
    PreGaloisCategory (CurveEtaleCoverCategory K) :=
  preGaloisCategory_e36 K hq

/-- The same reduction, consuming the existing frozen tree card
CurvePreGaloisCategoryRemainingFields (Example36CurveGaloisCategory.lean:330)
instead of the restated Prop.  This is the actual consumer of that card. -/
theorem preGaloisCategory_of_remainingFields (K : Type u) [Field K]
    (h : CurvePreGaloisCategoryRemainingFields (curveScheme K)) :
    PreGaloisCategory (CurveEtaleCoverCategory K) :=
  preGaloisCategory_of_hasQuotients K h.hasQuotientsByFiniteGroups

/-- The reduction composed with the scheme-level G2 donor
SourceCurveG2Quotients (restated here, since
curveScheme K = Spec (CommRingCat.of (curveCoordinateRing K)) is rfl): it is
enough to prove the quotient axiom for the affine base Spec K[x,y]/(y^2-x^3+x)
itself. -/
theorem preGaloisCategory_of_affineBaseG2 (K : Type u) [Field K]
    (h : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G)
        (EtaleCoverFoundations.FiniteEtaleCover
          (Spec (CommRingCat.of (curveCoordinateRing K))))) :
    PreGaloisCategory (CurveEtaleCoverCategory K) :=
  preGaloisCategory_of_hasQuotients K (fun G _ _ => h G)

/-! ## 4. The geometric fiber functor is FintypeCat-valued, given fiber finiteness -/

/-- The exact missing finiteness input: the geometric fiber of a finite etale
cover (the type of lifts of the geometric point x) is finite.  This is true
(the fiber of a finite morphism is finite) but is not in Mathlib 4.32.2. -/
def GeometricFiberFinite (K : Type u) [Field K] (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) : Prop :=
  ∀ Y : CurveEtaleCoverCategory K, Finite (geometricFiberObject Omega x Y)

/-- The FintypeCat-valued geometric fiber functor: the ObjectProperty.lift of
the Type u-valued geometric fiber functor through Finite. -/
abbrev curveGeometricFiberFunctorFintype (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hfin : GeometricFiberFinite K Omega x) :
    CurveEtaleCoverCategory K ⥤ FintypeCat.{u} :=
  ObjectProperty.lift (fun T : Type u => Finite T)
    (curveGeometricFiberFunctor K Omega x) hfin

/-- The FintypeCat-valued functor is the actual geometric fiber functor: its
composite with FintypeCat.incl is the Type u-valued geometric fiber functor.
(Records that the lift is not a substitution.) -/
theorem curveGeometricFiberFunctorFintype_comp_incl (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hfin : GeometricFiberFinite K Omega x) :
    curveGeometricFiberFunctorFintype K hfin ⋙ FintypeCat.incl =
      curveGeometricFiberFunctor K Omega x := rfl

/-! ## 5. The six exact FiberFunctor obligations -/

/-- The six PreGaloisCategory.FiberFunctor fields, frozen as a Prop structure.
This is exactly the missing content of a fiber functor certificate (G4)-(G6)
for the geometric fiber functor, with no field added and none dropped. -/
structure FiberFunctorCertificate {C : Type (u + 1)} [Category.{u, u + 1} C]
    (F : C ⥤ FintypeCat.{u}) : Prop where
  /-- (G4) preserves terminal objects. -/
  preservesTerminalObjects : PreservesLimitsOfShape (Discrete PEmpty.{1}) F
  /-- (G4) preserves pullbacks. -/
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F
  /-- (G5) preserves finite coproducts. -/
  preservesFiniteCoproducts : PreservesFiniteCoproducts F
  /-- (G5) preserves epimorphisms. -/
  preservesEpis : Functor.PreservesEpimorphisms F
  /-- (G5) preserves quotients by finite groups. -/
  preservesQuotientsByFiniteGroups :
    ∀ (G : Type u) [Group G] [Finite G], PreservesColimitsOfShape (SingleObj G) F
  /-- (G6) reflects isomorphisms. -/
  reflectsIsos : F.ReflectsIsomorphisms

/-- A fiber functor certificate is exactly a PreGaloisCategory.FiberFunctor. -/
theorem fiberFunctor_of_certificate {C : Type (u + 1)} [Category.{u, u + 1} C]
    [PreGaloisCategory C] {F : C ⥤ FintypeCat.{u}}
    (h : FiberFunctorCertificate F) :
    PreGaloisCategory.FiberFunctor F where
  preservesTerminalObjects := h.preservesTerminalObjects
  preservesPullbacks := h.preservesPullbacks
  preservesFiniteCoproducts := h.preservesFiniteCoproducts
  preservesEpis := h.preservesEpis
  preservesQuotientsByFiniteGroups := fun G _ _ => h.preservesQuotientsByFiniteGroups G
  reflectsIsos := h.reflectsIsos

/-- GaloisCategory follows from PreGaloisCategory plus one fiber functor. -/
theorem galoisCategory_of_fiberFunctor {C : Type (u + 1)} [Category.{u, u + 1} C]
    [PreGaloisCategory C] (F : C ⥤ FintypeCat.{u})
    [PreGaloisCategory.FiberFunctor F] :
    GaloisCategory C :=
  ⟨F, ⟨inferInstance⟩⟩

/-! ## 6. The profinite structure: no completion is needed -/

/-- Task (3): Aut F is already a profinite group in Mathlib - its topology
(Mathlib/CategoryTheory/Galois/Topology.lean) is compact, Hausdorff and totally
disconnected, and it is a topological group.  Hence the fundamental group of the
Galois category is ProfiniteGrp.of (Aut F); no profinite completion of Aut F,
and no abstract fundamental-group input, is required. -/
abbrev fiberAutProfiniteGrp {C : Type (u + 1)} [Category.{u, u + 1} C]
    (F : C ⥤ FintypeCat.{u}) : ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.of (CategoryTheory.Aut F)

/-- Task (2)/(3): Aut F is a fundamental group of F (Mathlib instance). -/
theorem aut_isFundamentalGroup {C : Type (u + 1)} [Category.{u, u + 1} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{u})
    [PreGaloisCategory.FiberFunctor F] :
    PreGaloisCategory.IsFundamentalGroup F (CategoryTheory.Aut F) :=
  inferInstance

/-- The same statement in ProfiniteGrp form: the profinite group
ProfiniteGrp.of (Aut F) is a fundamental group of F for the canonical
MulAction. -/
theorem profiniteAut_isFundamentalGroup {C : Type (u + 1)} [Category.{u, u + 1} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{u})
    [PreGaloisCategory.FiberFunctor F] :
    PreGaloisCategory.IsFundamentalGroup F (fiberAutProfiniteGrp F : Type (u + 1)) :=
  inferInstance

/-! ## 7. The universe-corrected card and its realization -/

/-- The universe check, recorded as a definition so that it is typechecked: the
frozen card's coverCategory field lives in Type u.  The actual cover category
CurveEtaleCoverCategory K lives in Type (u+1) (see
CurveEtaleCoverCategory), and curveFiberAutGroup K Omega x : Type (u+1). -/
def frozenCardCoverCategory {K : Type u} [Field K]
    (c : CurveEtaleFundamentalGroupCard K) : Type u :=
  c.coverCategory

/-- The corrected card: identical to
LeanFormal.IUT.IUTII.Frobenioid.Example36.CurveEtaleFundamentalGroupCard except
that every universe is raised by one, so that the actual finite etale cover
category of a Scheme.{u} can instantiate it. -/
structure CurveEtaleFundamentalGroupCardV (K : Type u) [Field K] where
  /-- The category of finite etale covers of the punctured curve. -/
  coverCategory : Type (u + 1)
  [coverCategory_category : Category.{u, u + 1} coverCategory]
  [coverCategory_galoisCategory : GaloisCategory coverCategory]
  /-- The fiber functor. -/
  fiber : coverCategory ⥤ FintypeCat.{u}
  [fiber_fiberFunctor : PreGaloisCategory.FiberFunctor fiber]
  /-- The etale fundamental group. -/
  fundamentalGroup : ProfiniteGrp.{u + 1}
  /-- The action of the fundamental group on each fiber. -/
  action : ∀ X : coverCategory,
    MulAction (fundamentalGroup : Type (u + 1)) (fiber.obj X).obj
  /-- The fundamental-group property, with the fiber actions as instances. -/
  isFundamentalGroup :
    letI (X : coverCategory) := action X
    PreGaloisCategory.IsFundamentalGroup fiber (fundamentalGroup : Type (u + 1))
  /-- The geometric fundamental group. -/
  geometricPiOne : ProfiniteGrp.{u + 1}
  /-- Geometric connectedness of the curve. -/
  geometricConnectedness : Prop

/-- The card's realized mathematical content.  Given ANY category C with
GaloisCategory C and ANY fiber functor F, the universe-corrected card is
inhabited, with fundamentalGroup := ProfiniteGrp.of (Aut F).  Nothing about the
once-punctured curve enters: this is exactly why the frozen card, after the
universe correction, is equivalent to the Galois-category certificate, and why
its geometricPiOne / geometricConnectedness fields carry no content (they are
unconstrained data supplied by the caller). -/
def mkCardV (K : Type u) [Field K] (C : Type (u + 1)) [Category.{u, u + 1} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{u})
    [hF : PreGaloisCategory.FiberFunctor F]
    (geomPi : ProfiniteGrp.{u + 1}) (geomConn : Prop) :
    CurveEtaleFundamentalGroupCardV K where
  coverCategory := C
  fiber := F
  fundamentalGroup := fiberAutProfiniteGrp F
  action := fun X => (inferInstance : MulAction (CategoryTheory.Aut F) (F.obj X))
  isFundamentalGroup := by
    letI (X : C) := (inferInstance : MulAction (CategoryTheory.Aut F) (F.obj X))
    exact profiniteAut_isFundamentalGroup F
  geometricPiOne := geomPi
  geometricConnectedness := geomConn

/-- The corrected card for the actual once-punctured curve: coverCategory is
FiniteEtaleCover (puncturedEllipticCurveScheme K) and fiber is the lift of the
actual geometric fiber functor at a geometric point x : Spec Omega -> X. -/
def curveEtaleFundamentalGroupCardV (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hq : CurveQuotientsByFiniteGroups K)
    (hfin : GeometricFiberFinite K Omega x)
    (hcert : FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin))
    (geomPi : ProfiniteGrp.{u + 1}) (geomConn : Prop) :
    CurveEtaleFundamentalGroupCardV K :=
  haveI : PreGaloisCategory (CurveEtaleCoverCategory K) :=
    preGaloisCategory_of_hasQuotients K hq
  haveI : PreGaloisCategory.FiberFunctor (curveGeometricFiberFunctorFintype K hfin) :=
    fiberFunctor_of_certificate hcert
  haveI : GaloisCategory (CurveEtaleCoverCategory K) :=
    galoisCategory_of_fiberFunctor (curveGeometricFiberFunctorFintype K hfin)
  mkCardV K (CurveEtaleCoverCategory K) (curveGeometricFiberFunctorFintype K hfin)
    geomPi geomConn

/-- The headline reduction.  The universe-corrected
CurveEtaleFundamentalGroupCard for the actual finite etale covers of the
once-punctured curve is realized as soon as three precise, named mathematical
inputs are supplied.  No Nonempty gate, no axiom and no substituted category is
used: the three inputs are the first missing items of the task.

* CurveQuotientsByFiniteGroups K - quotients by finite group actions (the
  single missing PreGaloisCategory field);
* GeometricFiberFinite K Omega x - finiteness of the geometric fiber;
* FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin) - the six
  (G4)-(G6) preservation/reflection obligations for that functor. -/
theorem curveEtaleFundamentalGroupCardV_realized_of_certificates (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hq : CurveQuotientsByFiniteGroups K)
    (hfin : GeometricFiberFinite K Omega x)
    (hcert : FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin))
    (geomPi : ProfiniteGrp.{u + 1}) (geomConn : Prop) :
    Nonempty (CurveEtaleFundamentalGroupCardV K) :=
  ⟨curveEtaleFundamentalGroupCardV K hq hfin hcert geomPi geomConn⟩

/-- Specialized statement: after the universe correction the ONLY obstruction to
GaloisCategory (FiniteEtaleCover X) is the pair
(CurveQuotientsByFiniteGroups, fiber-functor certificate). -/
theorem galoisCategory_curve_of_certificates (K : Type u) [Field K]
    {Omega : Type u} [Field Omega]
    {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}
    (hq : CurveQuotientsByFiniteGroups K)
    (hfin : GeometricFiberFinite K Omega x)
    (hcert : FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin)) :
    GaloisCategory (CurveEtaleCoverCategory K) :=
  haveI : PreGaloisCategory (CurveEtaleCoverCategory K) :=
    preGaloisCategory_of_hasQuotients K hq
  haveI : PreGaloisCategory.FiberFunctor (curveGeometricFiberFunctorFintype K hfin) :=
    fiberFunctor_of_certificate hcert
  galoisCategory_of_fiberFunctor (curveGeometricFiberFunctorFintype K hfin)


/-! ## 8. Appendix: the exact missing lemma list

### (A) CurveQuotientsByFiniteGroups K  (the single missing PreGaloisCategory field)

Statement: for every finite group G, the G-indexed diagram
"G -> FiniteEtaleCover X" has a colimit, i.e. for a finite etale cover
Y -> X with a G-action, the quotient Y/G exists as a finite etale cover of X
and is the colimit.  Nothing of this is in Mathlib 4.32.2: the only
HasColimitsOfShape (SingleObj G) instances in Mathlib are for FintypeCat and
Action FintypeCat G (Mathlib/CategoryTheory/Galois/Examples.lean:76, 86); there
is no scheme quotient by a finite group anywhere in Mathlib, and
PreGaloisCategory.hasQuotientsByFiniteGroups is a field of a class, never
discharged for a scheme-side category.

Required ingredients (none present in the tree either):
  (a) a categorical quotient "Y // G" of a scheme by a finite group action,
      with "Y -> Y//G" finite etale and G-invariant;
  (b) that this quotient is the colimit of the SingleObj G diagram in
      FiniteEtaleCover X (i.e. the forgetful functor to Over X / Scheme
      preserves the quotient);
  (c) the base-change compatibility with the structure morphism to X.

Tree status: Example36CurveGaloisCategory.lean freezes exactly this as
CurvePreGaloisCategoryRemainingFields.hasQuotientsByFiniteGroups, with no
inhabitant; SourceCurveG2Quotients.lean reduces it to the affine base
Spec K[x,y]/(y^2-x^3+x) but proves nothing about that base.

### (B) GeometricFiberFinite K Omega x

Statement: for a field Omega, a scheme X, a geometric point
x : Spec Omega -> X and a finite etale cover Y -> X, the type
{ s : Spec Omega -> Y // s >> (Y -> X) = x } is finite.

Required ingredients (not packaged in Mathlib 4.32.2):
  (a) Mathlib HAS: IsFinite is stable under base change, so
      "IsFinite (pullback.snd f x)" where f = Y -> X (used in
      Example36EtaleCoverFoundations.finiteEtale_pullback);
  (b) MISSING: "a scheme finite over Spec Omega is affine and its ring is a
      finite Omega-module", and the resulting bijection between lifts of x and
      Omega-algebra maps out of that ring;
  (c) MISSING: "a finite-dimensional algebra over a field has only finitely many
      maximal ideals, and each residue field is a finite extension, so there are
      finitely many Omega-algebra maps to Omega"; this is the Artinian structure
      theorem plus finite separability of the residue extensions.

### (C) FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin)

The six (G4)-(G6) obligations, frozen verbatim as a Prop structure in section 5.
Given (B), they are the statements that the geometric fiber functor preserves
terminal objects, pullbacks, finite coproducts, epimorphisms, quotients by
finite groups, and reflects isomorphisms.  Mathlib supplies none of them for a
scheme-side geometric fiber functor: the corresponding fibre-functor API exists
only for the field-side Galois categories (CommAlgCat.FiniteEtale K)^op, see
Mathlib/CategoryTheory/Galois/Examples.lean.

### (D) What is NOT missing

* The four other PreGaloisCategory fields are theorems in the tree, restated in
  section 2 (terminal, pullbacks, finite coproducts, direct summands).
* The profinite structure of the fundamental group is free: Aut F is compact,
  Hausdorff, totally disconnected and a topological group by
  Mathlib/CategoryTheory/Galois/Topology.lean, so ProfiniteGrp.of (Aut F) needs
  no profinite completion and no separation of "abstract" from "profinite"
  fundamental groups (section 6).
* The fundamental-group property IsFundamentalGroup F (Aut F) is a Mathlib
  instance (section 6).
* The card fields fundamentalGroup / action / isFundamentalGroup are produced
  from any fiber functor (section 7, mkCardV).
-/

/-! ## 9. Axiom audit -/


#print axioms preGaloisCategory_of_hasQuotients
#print axioms preGaloisCategory_of_remainingFields
#print axioms curveEtaleCover_monoInducesIsoOnDirectSummand
#print axioms fiberFunctor_of_certificate
#print axioms profiniteAut_isFundamentalGroup
#print axioms curveEtaleFundamentalGroupCardV_realized_of_certificates
#print axioms galoisCategory_curve_of_certificates

end LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual

end
