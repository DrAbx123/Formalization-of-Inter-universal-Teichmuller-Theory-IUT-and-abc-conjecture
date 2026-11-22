/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.A503HeightRegionObjectActual
import tmp.sheaf.xif.paper.Mzk1LiteralIQCarrierActual
import tmp.sheaf.xif.paper.Mzk1HullDetObjectActual
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.xif.paper.Mzk1FourTriangleSharedActual
import tmp.sheaf.xif.paper.LiteralHullObjectActual
import Mathlib.Tactic

/-! # A568 ABC Stage 5, Gap 1: height-region object and its bridge input

Gap 1 of the Cor 3.12 -> ABC bridge is the comparison field

  height_le_normalizedRegionVolume : for every ABC triple (a,b,c),
    Height.logHeight₁ (abcRationalPoint a c) <= (1+eps) *
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal

(IUT IV section 2 arithmetic line-bundle comparison).  This file builds the
height-region object that feeds that input, reusing the actual assets:

* A503 HeightRegionObject / heightRegionOf: the height and arithmetic-weight
  data of a concrete ABC triple;
* Mzk1LiteralIQCarrierActual: the literal IQ carrier with its actual hull
  interface IQHullLogVolumeInterface (literalIQInterface, from unit/hull regions
  and explicit LiteralCarrierAxioms Haar facts);
* LiteralHullObjectActual.literalHullObject: the actual literal hull region with
  its compactness;
* Mzk1HullDetObjectActual.HullDetObject: the Cor 3.12 side hull/det readout with
  its proved det-normalized comparison, supplying the theta-side consistency datum.

The comparison field itself remains the single NAMED gap (Gap 1); it is a field of
HeightRegionGap1Data, not derived from the object data.  Gap 2 is kept as the
second named input when the full per-eps Cor312EpsilonArithmeticComparison is
assembled.  Status: object layer + wiring PROVED/CONDITIONAL; gaps named; ABC gate
NOT passed.  No sorry/axiom/True. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.Objects.HeightRegion
open LeanFormal.IUT.XiFPaper.Mzk1LiteralIQCarrierActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1HullDetObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual

universe u v w

/-! ## 1. The Gap-1 height-region object -/

/-- Gap-1 input package: the height-region data of every ABC triple (A503 object),
an explicit theta-side bound from the finite hull log-volume (Cor 3.12 finiteness),
and the single NAMED Gap-1 comparison field. -/
structure HeightRegionGap1Data {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat -> Nat -> Nat -> X) (epsilon : Real) where
  heightData : forall a b c : Nat, IsABCTriple a b c -> HeightRegionObject
  thetaBound : Real
  thetaBound_eq : thetaBound = (W.logVolume W.hull).toReal
  height_le_normalizedRegionVolume : forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcRationalPoint a c) <=
      (1 + epsilon) *
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal

/-- The height-region object of a concrete ABC triple, from the A503 object layer. -/
def heightRegionGap1Data_object (a b c : Nat) (h : IsABCTriple a b c) :
    HeightRegionObject :=
  heightRegionOf a b c h

theorem heightRegionGap1Data_object_height (a b c : Nat) (h : IsABCTriple a b c) :
    (heightRegionGap1Data_object a b c h).height =
      Height.logHeight₁ (abcRationalPoint a c) := rfl

theorem heightRegionGap1Data_object_weight (a b c : Nat) (h : IsABCTriple a b c) :
    (heightRegionGap1Data_object a b c h).weightData.weight =
      arithmeticWeight (abcRationalPoint a c) := rfl

/-- Theta-bound from Cor 3.12 finiteness: the hull log-volume is finite, so its
toReal is a faithful real theta bound. -/
def thetaBoundOfHull {X : Type u} (W : IQHullLogVolumeInterface X) : Real :=
  (W.logVolume W.hull).toReal

theorem thetaBoundOfHull_eq {X : Type u} (W : IQHullLogVolumeInterface X) :
    thetaBoundOfHull W = (W.logVolume W.hull).toReal := rfl

theorem thetaBoundOfHull_finite {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull < ⊤ :=
  W.hull_logVolume_lt_top

/-- The hull/det object of the Cor 3.12 side, with its proved det-normalized
comparison (re-exported for wiring). -/
def hullDetReadout {label : Type u} [Fintype label] [DecidableEq label]
    (O : HullDetObject label) : Real :=
  hullReadout O.state

theorem hullDetReadout_lt_zero {label : Type u} [Fintype label] [DecidableEq label]
    (O : HullDetObject label) : hullReadout O.state < 0 :=
  O.hneg

def hullDet_comparison {label : Type u} [Fintype label] [DecidableEq label]
    (O : HullDetObject label) :
    (fourTriangleReadout hullDetHDD (hullDetDsc O.state) hullDetSheOut).1 <=
      (fourTriangleReadout hullDetHDD (hullDetDsc O.state) hullDetSheOut).2 :=
  hullDetObject_comparison O

/-! ## 2. From the object to the Gap-1 bridge input -/

theorem heightRegionGap1_comparison {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat -> Nat -> Nat -> X} {epsilon : Real}
    (D : HeightRegionGap1Data W logShellPoint epsilon) :
    forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) <=
        (1 + epsilon) *
          (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
  D.height_le_normalizedRegionVolume

def comparisonOfHeightRegionGap1 {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat -> Nat -> Nat -> X} {epsilon : Real}
    (D : HeightRegionGap1Data W logShellPoint epsilon)
    (gap2 : exists D0 : Real, forall a b c : Nat, IsABCTriple a b c ->
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal <=
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D0) :
    Cor312EpsilonArithmeticComparison W epsilon where
  logShellPoint := logShellPoint
  height_le_normalizedRegionVolume := D.height_le_normalizedRegionVolume
  regionVolume_le_normalizedWeight := gap2

def bridgeInterfaceOfHeightRegionGap1 (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat -> Nat -> Nat -> X)
    (D : forall epsilon : Real, 0 < epsilon ->
      HeightRegionGap1Data W logShellPoint epsilon)
    (gap2 : forall epsilon : Real, 0 < epsilon ->
      exists D0 : Real, forall a b c : Nat, IsABCTriple a b c ->
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal <=
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D0) :
    Cor312ToABCBridgeInterface.{u} where
  carrier := X
  hullData := W
  epsilonComparison := fun epsilon hepsilon =>
    comparisonOfHeightRegionGap1 (D epsilon hepsilon) (gap2 epsilon hepsilon)

theorem heightBound_of_heightRegionGap1 (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat -> Nat -> Nat -> X)
    (D : forall epsilon : Real, 0 < epsilon ->
      HeightRegionGap1Data W logShellPoint epsilon)
    (gap2 : forall epsilon : Real, 0 < epsilon ->
      exists D0 : Real, forall a b c : Nat, IsABCTriple a b c ->
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal <=
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D0) :
    forall epsilon : Real, 0 < epsilon -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound
    (bridgeInterfaceOfHeightRegionGap1 X W logShellPoint D gap2)



/-! ## 4. Status table (named fields explicitly listed) -/

def heightRegionGap1Rows : List (String × String × String) :=
  [ ("A503 height-region object", "heightRegionOf / heightRegionGap1Data_object", "PROVED/DEF (object)"),
    ("literal hull region + Haar interface", "literalHullObject / literalIQInterface (available, wired in Stage-5 consumer)", "PROVED/DEF (object)"),
    ("Cor 3.12 hull/det readout", "HullDetObject / hullDetReadout / hullDetObject_comparison", "PROVED (3.12 side)"),
    ("theta bound (hull finiteness)", "thetaBoundOfHull / hull_logVolume_lt_top", "PROVED (from interface)"),
    ("Gap 1 height comparison", "height_le_normalizedRegionVolume", "NAMED (IUT IV section 2)"),
    ("Gap 2 region-volume estimate", "regionVolume_le_normalizedWeight (passed in)", "NAMED (IUT IV main estimate)"),
    ("scope", "conditional bridge only; ABC gate NOT passed", "INTEGRITY") ]

theorem heightRegionGap1Rows_length : heightRegionGap1Rows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual

end