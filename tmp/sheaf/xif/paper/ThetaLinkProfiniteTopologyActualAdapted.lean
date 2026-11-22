import LeanFormal.IUT.Foundations.Geometry.ProfiniteFundamentalGroup
import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitFactorizationProvider
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-!
# Actual profinite topology for Theta-link product groups

IUT III, Proposition 1.2, uses the profinite local groups Pi_v with their
profinite topology.  The reduced FPrimeStrip record carries only Group, not
TopologicalSpace.  Mathlib's ProfiniteCompletion constructs the actual
profinite group as an inverse limit of finite quotients:

  completion G = limit (finite-index normal quotients of G).

This file constructs that actual profinite group for the pair group and for the
common four-corner product, with its compact Hausdorff totally disconnected
topology, and the actual eta maps from the abstract product groups.  These are
actual topological groups, not an arbitrary/discrete topology.

The Kummer layer construction additionally needs a common topological group
acting on all four strips through actual factor maps.  That common group can be
taken as the completion of the fourfold product below; what is missing is the
actual Kummer data on that common group (the source supplies only strip
equivalences), recorded at the end.

No toy topology, PUnit/True, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ThetaLinkProfiniteTopologyActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Geometry
open LeanFormal.IUT.Theorem311Source
open CategoryTheory

universe uv ua upi umon ui

variable {V : Type uv}

/-- The common product group of an F-prime-strip pair. -/
abbrev PairGroup (upper lower : FPrimeStrip V) : Type _ :=
  (v : V) -> upper.toDPrimeStrip.Pi v × lower.toDPrimeStrip.Pi v

/-- The actual profinite completion of the pair group: inverse limit of its
finite-index normal quotients, with its actual profinite topology. -/
noncomputable abbrev PairProfiniteGroup (upper lower : FPrimeStrip V) : Type _ :=
  ↥(profiniteCompletionOfGroup (GrpCat.of (PairGroup upper lower)))

instance pairProfiniteGroupGroup (upper lower : FPrimeStrip V) :
    Group (PairProfiniteGroup upper lower) :=
  inferInstance

instance pairProfiniteGroupTopologicalSpace (upper lower : FPrimeStrip V) :
    TopologicalSpace (PairProfiniteGroup upper lower) :=
  inferInstance

instance pairProfiniteGroupCompactSpace (upper lower : FPrimeStrip V) :
    CompactSpace (PairProfiniteGroup upper lower) :=
  inferInstance

instance pairProfiniteGroupTotallyDisconnected (upper lower : FPrimeStrip V) :
    TotallyDisconnectedSpace (PairProfiniteGroup upper lower) :=
  inferInstance

/-- The actual map from the abstract pair group to its profinite completion. -/
noncomputable def pairProfiniteEta (upper lower : FPrimeStrip V) :
    PairGroup upper lower →* PairProfiniteGroup upper lower :=
  (profiniteCompletionEta (GrpCat.of (PairGroup upper lower))).hom

/-- The actual upper factorization from the profinite completion. -/
noncomputable def pairProfiniteFactorUpper
    (upper lower : FPrimeStrip V) (v : V) :
    PairProfiniteGroup upper lower →* upper.toDPrimeStrip.Pi v :=
  (FPrimeStrip.pairFactorizationUpper upper lower v).comp
    (pairProfiniteEta upper lower)

/-- The actual lower factorization from the profinite completion. -/
noncomputable def pairProfiniteFactorLower
    (upper lower : FPrimeStrip V) (v : V) :
    PairProfiniteGroup upper lower →* lower.toDPrimeStrip.Pi v :=
  (FPrimeStrip.pairFactorizationLower upper lower v).comp
    (pairProfiniteEta upper lower)

/-- The common four-corner product whose profinite completion can serve as one
topological group for all four strips. -/
abbrev FourCornerGroup
    (S00 S01 S10 S11 : FPrimeStrip V) : Type _ :=
  (v : V) ->
    S00.toDPrimeStrip.Pi v × S01.toDPrimeStrip.Pi v ×
      S10.toDPrimeStrip.Pi v × S11.toDPrimeStrip.Pi v

/-- The actual profinite completion of the four-corner product. -/
noncomputable abbrev CommonThetaLinkGroup
    (S00 S01 S10 S11 : FPrimeStrip V) : Type _ :=
  ↥(profiniteCompletionOfGroup (GrpCat.of (FourCornerGroup S00 S01 S10 S11)))

instance commonThetaLinkGroupGroup (S00 S01 S10 S11 : FPrimeStrip V) :
    Group (CommonThetaLinkGroup S00 S01 S10 S11) :=
  inferInstance

instance commonThetaLinkGroupTopologicalSpace
    (S00 S01 S10 S11 : FPrimeStrip V) :
    TopologicalSpace (CommonThetaLinkGroup S00 S01 S10 S11) :=
  inferInstance

instance commonThetaLinkGroupCompactSpace
    (S00 S01 S10 S11 : FPrimeStrip V) :
    CompactSpace (CommonThetaLinkGroup S00 S01 S10 S11) :=
  inferInstance

instance commonThetaLinkGroupTotallyDisconnected
    (S00 S01 S10 S11 : FPrimeStrip V) :
    TotallyDisconnectedSpace (CommonThetaLinkGroup S00 S01 S10 S11) :=
  inferInstance

/-- The actual eta map into the common four-corner completion. -/
noncomputable def commonThetaLinkEta
    (S00 S01 S10 S11 : FPrimeStrip V) :
    FourCornerGroup S00 S01 S10 S11 →*
      CommonThetaLinkGroup S00 S01 S10 S11 :=
  (profiniteCompletionEta
    (GrpCat.of (FourCornerGroup S00 S01 S10 S11))).hom

/-- Projection of the fourfold product onto the S00/S01 pair. -/
def fourCornerToS00S01
    (S00 S01 S10 S11 : FPrimeStrip V) :
    FourCornerGroup S00 S01 S10 S11 →*
      PairGroup S00 S01 where
  toFun f v := (f v).1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of the fourfold product onto the S01/S11 pair. -/
def fourCornerToS01S11
    (S00 S01 S10 S11 : FPrimeStrip V) :
    FourCornerGroup S00 S01 S10 S11 →*
      PairGroup S01 S11 where
  toFun f v := ((f v).2.1, (f v).2.2.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of the fourfold product onto the S10/S11 pair. -/
def fourCornerToS10S11
    (S00 S01 S10 S11 : FPrimeStrip V) :
    FourCornerGroup S00 S01 S10 S11 →*
      PairGroup S10 S11 where
  toFun f v := ((f v).2.2.1, (f v).2.2.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-! ## Exact missing Kummer data on the common topological group

The common topological group CommonThetaLinkGroup exists.  What is not supplied
by the frozen source is the actual SourceTimesMuKummerLayer /
SourceEvaluationUnitPortion on this common group: the strip links give
FPrimeStripEquiv, but not the G-equivariant Kummer isomorphism with the
invariant-image law over all open subgroups of the common profinite group.
That is the exact remaining field; no trivial action or arbitrary
isomorphism is inserted.
-/

def MissingCommonKummerLayer
    (S00 S01 S10 S11 : FPrimeStrip V) : Prop :=
  Nonempty (SourceTimesMuKummerLayer
    (CommonThetaLinkGroup S00 S01 S10 S11) S00 S01)

def MissingCommonEvaluationUnitPortion
    (S00 S01 S10 S11 : FPrimeStrip V) : Prop :=
  Nonempty (SourceEvaluationUnitPortion
    (CommonThetaLinkGroup S00 S01 S10 S11) S01 S11)

end LeanFormal.IUT.XiFPaper.ThetaLinkProfiniteTopologyActualAdapted

end