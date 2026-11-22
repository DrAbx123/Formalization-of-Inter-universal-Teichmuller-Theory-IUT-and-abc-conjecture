/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CorrectedGap1UnconditionalActual
import tmp.sheaf.xif.paper.Mzk1CorrectedGap2ToABCActual
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import tmp.sheaf.xif.paper.Mzk1GapTightnessActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A689 Gap 2 arithmetic tightness (mainline; corrected direction only)

Proved here:
* `badSumWeightBound_implies_ABC`: the pure-arithmetic bad-sum bound implies ABC
  (using the green `log_height_le_badSum_of_fullSupport`);
* `correctedGap2Shape_implies_ABC`: the corrected-region Gap 2 shape implies ABC
  (re-export of the green theorem);
* `bridge_boundary_calibrated`: the abstract tightness calibration
  `Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture` (green).

**The REVERSE (ABC => BadSumWeightBound) is NOT true in general**:
`Σ_b e_b d_b log p_b ≤ (Σ_b d_b) log N` and `D0 = Σ_b d_b` may exceed 1, so ABC's
coefficient `1+ε` cannot be absorbed; it would need extra assumptions (e.g.
`Σ_b d_b ≤ 1+ε`, or `d_b = 1` with distinct bad primes).  Hence object-level
tightness is only the abstract bridge calibration; ABC gate NOT passed.

No canonical change. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticTightnessActual

open scoped Pointwise ENNReal BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Bad-sum bound implies ABC** (proved direction of the arithmetic tightness). -/
theorem badSumWeightBound_implies_ABC
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hbad : Mzk1Gap2ArithmeticReductionActual.BadSumWeightBound T eN) :
    ABCConjecture := by
  refine abcConjecture_iff_abcArithmeticWeightHeightBound.mpr ?_
  intro ε hε
  obtain ⟨D, hD⟩ := hbad ε hε
  refine ⟨D, ?_⟩
  intro aN bN cN habc
  have harith := log_height_le_badSum_of_fullSupport T eN hd aN bN cN habc
    (hfull aN bN cN habc)
  have hD' := hD aN bN cN habc
  have hheight : Height.logHeight₁ (abcRationalPoint aN cN) = Real.log (cN : ℝ) :=
    abcRationalPoint_logHeight₁ habc
  rw [hheight]
  linarith

/-- **Corrected-region Gap 2 shape implies ABC** (re-export of the green theorem). -/
theorem correctedGap2Shape_implies_ABC
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hGap2 : CorrectedGap2Shape T point eN) : ABCConjecture :=
  correctedGap2_to_ABC T point eN hc0 hcT hd hfull hunit hGap2

/-- The abstract tightness calibration (green). -/
theorem bridge_boundary_calibrated :
    Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture :=
  paperGap_boundary_calibrated

/-- Scope rows: proved direction vs NOT-proved reverse. -/
def tightnessRows : List (String × String) :=
  [ ("BadSumWeightBound => ABC", "PROVED (badSumWeightBound_implies_ABC)"),
    ("corrected Gap2 shape => ABC", "PROVED (re-export)"),
    ("ABC => BadSumWeightBound (reverse)",
     "NOT_PROVED: D0 = sum_b d_b may exceed 1; needs extra assumptions"),
    ("abstract tightness", "GREEN: Nonempty bridge <=> ABCConjecture"),
    ("scope", "ABC gate NOT passed; no canonical change") ]

theorem tightnessRows_length : tightnessRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticTightnessActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticTightnessActual.badSumWeightBound_implies_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticTightnessActual.correctedGap2Shape_implies_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticTightnessActual.bridge_boundary_calibrated