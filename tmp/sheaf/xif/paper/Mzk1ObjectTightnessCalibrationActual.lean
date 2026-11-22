/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalConditionalABCActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A696/R19 object-level tightness calibration (mainline; two directions)

Two-direction calibration around the single explicit arithmetic input
`NatRadicalWeightBound`:

* `namedInput_implies_bridge`: `NatRadicalWeightBound` => the bridge interface is
  inhabited (via the green `final_conditional_ABC` and the green calibration
  `Nonempty bridge <=> ABC`);
* `bridge_implies_ABC`: the bridge interface implies `ABCConjecture` (green calibration);
* scope: the REVERSE chain `Nonempty bridge -> NatRadicalWeightBound` is NOT proved and
  NOT claimed (the `d_b` coefficient obstruction); the abstract two-sided calibration
  `Nonempty bridge <=> ABC` is green.

No canonical change; ABC gate NOT passed; no new mathematical object. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 600000

namespace LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessCalibrationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalABCActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Direction 1: the explicit named input implies the bridge interface is inhabited. -/
theorem namedInput_implies_bridge
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal)
    (hnat : NatRadicalWeightBound T eN) :
    Nonempty Cor312ToABCBridgeInterface.{0} :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.mpr
    (final_conditional_ABC T point eN hc0 hcT hd hfull hunit hhull hnat)

/-- Direction 2: the bridge interface implies ABC (green calibration). -/
theorem bridge_implies_ABC (h : Nonempty Cor312ToABCBridgeInterface.{0}) :
    ABCConjecture :=
  cor312ToABCBridgeInterface_abcConjecture_of_nonempty h

/-- The green abstract two-sided calibration. -/
theorem bridge_iff_ABC :
    Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture

/-- Scope rows of the object-level tightness calibration. -/
def objectTightnessRows : List (String × String) :=
  [ ("NamedInput => bridge inhabited", "PROVED (namedInput_implies_bridge)"),
    ("bridge => ABC", "PROVED (bridge_implies_ABC)"),
    ("bridge <=> ABC (abstract)", "GREEN (bridge_iff_ABC)"),
    ("bridge/ABC => NamedInput (reverse)", "NOT_PROVED (d_b coefficient obstruction)"),
    ("scope", "ABC gate NOT passed; no canonical change") ]

theorem objectTightnessRows_length : objectTightnessRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessCalibrationActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessCalibrationActual.namedInput_implies_bridge
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessCalibrationActual.bridge_implies_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessCalibrationActual.bridge_iff_ABC