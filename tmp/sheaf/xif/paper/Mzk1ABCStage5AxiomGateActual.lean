/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap1ConsumerActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import tmp.sheaf.xif.paper.Mzk1ABCStage5AcceptanceActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCStage5Gap2ConsumerActual
import Mathlib.Tactic

#check LeanFormal.IUT.Objects.ABCBridgeGap2.gap2_real_bound

/-! # A574: ABC Stage-5 axiom gate — payload + evidence pack

Evidence package for the Stage-5 conditional ABC chain:

* Cor 3.12 side: `Mzk1Cor312FinalAssemblyActual.cor312Conclusion_final` (green);
* Gap-1 consumer: `Mzk1ABCBridgeGap1ConsumerActual` — height-region object wiring
  (PROVED) plus the two NAMED paper inputs (Gap-1 comparison, Gap-2 estimate);
* Gap-2 consumer: `Mzk1ABCBridgeGap2ConsumerActual` — A502 ENNReal/Real adapter and
  the minimal named analytic estimate;
* IUT IV Stage-5 reductions: `Mzk1ABCStage5AcceptanceActual` and
  `Mzk1StepXIABCStage5Gap2ConsumerActual` (conditional on explicit estimates).

`Stage5AxiomGatePayload` bundles the two named inputs; from it we PROVE the
bridge interface, the height bound, and the conditional ABC reduction.  The
`#print axioms` gate at the end records the axiom footprint of every consumed
green theorem (expected: propext, Classical.choice, Quot.sound only).

Scope: conditional; no gap proved; ABC gate NOT passed.  No sorry/axiom/True. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AxiomGateActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual
open LeanFormal.IUT.Objects.ABCBridgeGap2

universe u

/-- The Stage-5 gate payload: Gap-1 height-region objects and the two NAMED paper
inputs (Gap-1 comparison carried by the objects, Gap-2 as the explicit named
analytic estimate). -/
structure Stage5AxiomGatePayload (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat -> Nat -> Nat -> X) where
  /-- Per-eps Gap-1 height-region object family (named Gap-1 field inside). -/
  gap1 : forall epsilon : Real, 0 < epsilon ->
    HeightRegionGap1Data W logShellPoint epsilon
  /-- Per-eps Gap-2 NAMED analytic estimate. -/
  gap2 : forall epsilon : Real, 0 < epsilon ->
    exists D0 : Real, forall a b c : Nat, IsABCTriple a b c ->
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal <=
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D0

/-- The bridge interface assembled from the payload. -/
def payloadBridge {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat -> Nat -> Nat -> X} (P : Stage5AxiomGatePayload X W logShellPoint) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterfaceOfGap1Consumer W logShellPoint P.gap1 P.gap2

/-- The conditional ABC height bound from the payload (through the Gap-1 consumer). -/
theorem payload_heightBound {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat -> Nat -> Nat -> X} (P : Stage5AxiomGatePayload X W logShellPoint) :
    forall epsilon : Real, 0 < epsilon -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  heightBound_of_gap1Consumer W logShellPoint P.gap1 P.gap2

/-- Same bound via the bridge interface and the green bridge consumer theorem. -/
theorem payload_heightBound_via_bridge {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat -> Nat -> Nat -> X} (P : Stage5AxiomGatePayload X W logShellPoint) :
    forall epsilon : Real, 0 < epsilon -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound (payloadBridge P)

/-- Gap-2 consumer re-export: named ENNReal estimate gives the real-form bound. -/
theorem payload_gap2_real_bound {regionVolume : ENNReal} {eps weight theta D : Real}
    (hR : 0 <= (1 + eps) * weight + theta + D)
    (hS : SNamed regionVolume eps weight theta D) :
    regionVolume.toReal <= (1 + eps) * weight + theta + D :=
  gap2_real_bound hR hS

/-- Evidence table: green theorems consumed by the Stage-5 gate and their status. -/
def stage5GateRows : List (String × String × String) :=
  [ ("Cor 3.12 final assembly", "Mzk1Cor312FinalAssemblyActual.cor312Conclusion_final", "GREEN"),
    ("Gap-1 height-region object", "Mzk1ABCBridgeHeightRegionActual.HeightRegionGap1Data", "GREEN (object); Gap-1 named field"),
    ("Gap-1 consumer", "Mzk1ABCBridgeGap1ConsumerActual.heightBound_of_gap1Consumer", "GREEN (conditional on named gaps)"),
    ("Gap-2 adapter/consumer", "Mzk1ABCBridgeGap2ConsumerActual.gap2_real_bound / SNamed", "GREEN (adapter); Gap-2 named estimate"),
    ("Stage-5 acceptance", "Mzk1ABCStage5AcceptanceActual.acceptance_abcStage5", "GREEN (conditional)"),
    ("Stage-5 stepxi consumer", "Mzk1StepXIABCStage5Gap2ConsumerActual.stepxi_abcStage5_gap2", "GREEN (conditional)"),
    ("payload bridge/height bound", "payloadBridge / payload_heightBound(_via_bridge)", "PROVED from the two named inputs"),
    ("scope", "conditional; named gaps explicit; ABC gate NOT passed", "INTEGRITY") ]

theorem stage5GateRows_length : stage5GateRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AxiomGateActual

/-! ## A574 axiom gate (#print axioms evidence in the watchdog log) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.cor312Conclusion_final
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.heightBound_of_gap1Consumer
#print axioms LeanFormal.IUT.Objects.ABCBridgeGap2.gap2_real_bound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceActual.acceptance_abcStage5
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIABCStage5Gap2ConsumerActual.stepxi_abcStage5_gap2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AxiomGateActual.payloadBridge
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AxiomGateActual.payload_heightBound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AxiomGateActual.payload_heightBound_via_bridge

end
-- A575: force recompile after merged-version log; single owner mainline.
