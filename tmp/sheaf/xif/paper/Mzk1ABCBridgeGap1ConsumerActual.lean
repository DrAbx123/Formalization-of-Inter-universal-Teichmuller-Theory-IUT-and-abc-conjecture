/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCBridgeHeightRegionActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # A573: Gap-1 height-region consumer for the Cor 3.12 -> ABC bridge

Consumer module (no new mathematics): it takes the PROVED Gap-1 object wiring of
`Mzk1ABCBridgeHeightRegionActual` (`heightRegionGap1_comparison`, the A503 height
objects and the hull-finiteness theta bound) together with the still-NAMED Gap-2
region-volume estimate, assembles the per-eps `Cor312EpsilonArithmeticComparison`
and the `Cor312ToABCBridgeInterface`, and derives the conditional ABC height bound
via the green `cor312ToABCBridge_heightBound`.  The two named inputs are explicit
parameters; the gate below prints their axiom footprint. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual

universe u

variable {X : Type u} (W : IQHullLogVolumeInterface X)
variable (logShellPoint : Nat -> Nat -> Nat -> X)

/-- The per-eps Gap-1 object family (each carries the named Gap-1 comparison). -/
abbrev Gap1DataFamily (epsilon : Real) :=
  HeightRegionGap1Data W logShellPoint epsilon

/-- The per-eps Gap-2 NAMED input: the IUT IV main estimate of the comparison
region log-volume (arithmetic weight + theta bound + residual constant). -/
abbrev Gap2NamedInput (epsilon : Real) : Prop :=
  exists D0 : Real, forall a b c : Nat, IsABCTriple a b c ->
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal <=
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D0

/-- The Gap-1 comparison of the object (exactly the input field shape required by
`Cor312EpsilonArithmeticComparison.height_le_normalizedRegionVolume`). -/
theorem gap1_consumer_comparison {epsilon : Real}
    (D : Gap1DataFamily W logShellPoint epsilon) :
    forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) <=
        (1 + epsilon) *
          (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal :=
  heightRegionGap1_comparison D

/-- Per-eps comparison assembled from the Gap-1 object and the named Gap-2 input. -/
def epsilonComparisonOfGap1Consumer {epsilon : Real}
    (D : Gap1DataFamily W logShellPoint epsilon)
    (G2 : Gap2NamedInput W logShellPoint epsilon) :
    Cor312EpsilonArithmeticComparison W epsilon :=
  comparisonOfHeightRegionGap1 D G2

/-- The bridge interface with Gap-1 PROVED-object-wiring and Gap-2 still named. -/
def bridgeInterfaceOfGap1Consumer
    (D : forall epsilon : Real, 0 < epsilon -> Gap1DataFamily W logShellPoint epsilon)
    (G2 : forall epsilon : Real, 0 < epsilon -> Gap2NamedInput W logShellPoint epsilon) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterfaceOfHeightRegionGap1 X W logShellPoint D G2

/-- The conditional ABC height bound from the Gap-1 consumer. -/
theorem heightBound_of_gap1Consumer
    (D : forall epsilon : Real, 0 < epsilon -> Gap1DataFamily W logShellPoint epsilon)
    (G2 : forall epsilon : Real, 0 < epsilon -> Gap2NamedInput W logShellPoint epsilon) :
    forall epsilon : Real, 0 < epsilon -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  heightBound_of_heightRegionGap1 X W logShellPoint D G2

/-- Same bound obtained through the assembled bridge interface (green consumer
theorem `cor312ToABCBridge_heightBound`). -/
theorem heightBound_of_gap1Consumer_via_bridge
    (D : forall epsilon : Real, 0 < epsilon -> Gap1DataFamily W logShellPoint epsilon)
    (G2 : forall epsilon : Real, 0 < epsilon -> Gap2NamedInput W logShellPoint epsilon) :
    forall epsilon : Real, 0 < epsilon -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound
    (bridgeInterfaceOfGap1Consumer W logShellPoint D G2)

/-- The theta-side bound carried by the Gap-1 object is the finite hull log-volume
(Cor 3.12 finiteness). -/
theorem gap1Consumer_thetaBound_finite {epsilon : Real}
    (D : Gap1DataFamily W logShellPoint epsilon) :
    W.logVolume W.hull < ⊤ :=
  thetaBoundOfHull_finite W

/-- Status: PROVED object wiring vs NAMED paper inputs. -/
def gap1ConsumerRows : List (String × String × String) :=
  [ ("Gap-1 height object", "HeightRegionGap1Data / heightRegionGap1_comparison", "PROVED (object wiring; gap field carried)"),
    ("theta bound", "thetaBoundOfHull_finite", "PROVED (hull_logVolume_lt_top)"),
    ("Gap-1 comparison", "height_le_normalizedRegionVolume", "NAMED (IUT IV section 2)"),
    ("Gap-2 region volume", "Gap2NamedInput", "NAMED (IUT IV main estimate)"),
    ("bridge interface", "bridgeInterfaceOfGap1Consumer", "PROVED from the two named inputs"),
    ("ABC height bound", "heightBound_of_gap1Consumer(_via_bridge)", "PROVED (conditional)"),
    ("scope", "conditional; ABC gate NOT passed", "INTEGRITY") ]

theorem gap1ConsumerRows_length : gap1ConsumerRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual

/-! ## Axiom gate -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.gap1_consumer_comparison
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.epsilonComparisonOfGap1Consumer
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.bridgeInterfaceOfGap1Consumer
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.heightBound_of_gap1Consumer
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.heightBound_of_gap1Consumer_via_bridge
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.gap1Consumer_thetaBound_finite

end