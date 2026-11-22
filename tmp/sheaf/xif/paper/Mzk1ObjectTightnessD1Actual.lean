/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Stage4BadSumTightnessActual
import tmp.sheaf.xif.paper.Mzk1FinalConditionalABCActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A698 object-level exact calibration in the `d_b = 1` model (mainline)

In the `d_b = 1` model, the remaining named input is EXACTLY ABC:
* `badSum_eq_logN` (green stage4): full support + `d_b = 1` gives
  `Σ_b e_b d_b log p_b = log N`;
* `natRadicalWeightBound_implies_ABC`: the named input implies ABC (green chain);
* `abc_implies_natRadicalWeightBound`: ABC implies the named input when `d_b = 1`
  (`log N <= log c + log 3` absorbs the constant);
* `natRadicalWeightBound_iff_ABC`: the object-level EQUIVALENCE.

This is a tightness/calibration result, NOT an ABC proof: the reverse for `d_b > 1`
is not true in general (A692 obstruction).  ABC gate NOT passed; no canonical change. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessD1Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalABCActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1BadSumWeightBoundExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4BadSumTightnessActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Re-export of the green tightness identity (`d_b = 1` => bad sum = log N). -/
theorem badSum_eq_logN
    (e : Bad (nativePlaceSelection T) → Nat) (N : Nat) (hN : 0 < N)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) = 1)
    (hfull : N = ∏ bBad : Bad (nativePlaceSelection T),
      (qVFamTensorP T bBad) ^ (e bBad)) :
    (∑ bBad : Bad (nativePlaceSelection T),
        (e bBad : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
            Real.log ((qVFamTensorP T bBad : ℝ)))) =
      Real.log (N : ℝ) :=
  Mzk1Stage4BadSumTightnessActual.badSum_eq_logN T e N hN hd hfull

/-- Direction 1: `NatRadicalWeightBound` implies ABC. -/
theorem natRadicalWeightBound_implies_ABC
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd1 : ∀ bBad : Bad (nativePlaceSelection T),
      (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) = 1)
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal)
    (hnat : NatRadicalWeightBound T eN) : ABCConjecture :=
  final_conditional_ABC T point eN hc0 hcT
    (fun bBad => by rw [hd1 bBad]) hfull hunit hhull hnat

/-- Direction 2: ABC implies `NatRadicalWeightBound` when `d_b = 1`. -/
theorem abc_implies_natRadicalWeightBound
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hd1 : ∀ bBad : Bad (nativePlaceSelection T),
      (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) = 1)
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hABC : ABCConjecture) : NatRadicalWeightBound T eN := by
  unfold NatRadicalWeightBound Mzk1BadSumWeightBoundExplicitActual.FinalNamedInput
    Mzk1BadSumWeightBoundExplicitActual.BadSumWeightBoundNat
  intro ε hε
  obtain ⟨A, hA⟩ := (abcConjecture_iff_abcArithmeticWeightHeightBound.mp hABC) ε hε
  refine ⟨A + Real.log 3, ?_⟩
  intro aN bN cN habc
  have hsum := badSum_eq_logN T (eN aN bN cN) (aN + bN + cN + 1)
    (by positivity) hd1 (hfull aN bN cN habc)
  have hlogN := logN_le_log_c_add_log3 habc
  have hA' := hA aN bN cN habc
  rw [arithmeticWeight_abc_eq_log_natRadical habc] at hA'
  have hheight : Height.logHeight₁ (abcRationalPoint aN cN) = Real.log (cN : ℝ) :=
    abcRationalPoint_logHeight₁ habc
  rw [hheight] at hA'
  rw [hsum]
  linarith

/-- **Object-level exact calibration**: in the `d_b = 1` model, the single named
  input is equivalent to ABC. -/
theorem natRadicalWeightBound_iff_ABC
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd1 : ∀ bBad : Bad (nativePlaceSelection T),
      (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) = 1)
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal) :
    NatRadicalWeightBound T eN ↔ ABCConjecture :=
  ⟨natRadicalWeightBound_implies_ABC T point eN hc0 hcT hd1 hfull hunit hhull,
   abc_implies_natRadicalWeightBound T eN hd1 hfull⟩

/-- Scope rows of the `d_b = 1` object-level calibration. -/
def d1CalibrationRows : List (String × String) :=
  [ ("d_b = 1 tightness: bad sum = log N", "PROVED (stage4 green)"),
    ("named input => ABC", "PROVED (natRadicalWeightBound_implies_ABC)"),
    ("ABC => named input when d_b = 1", "PROVED (abc_implies_natRadicalWeightBound)"),
    ("equivalence (d_b = 1)", "PROVED (natRadicalWeightBound_iff_ABC)"),
    ("reverse for d_b > 1", "NOT true in general (A692 obstruction)"),
    ("scope", "calibration, not ABC proof; ABC gate NOT passed; no canonical change") ]

theorem d1CalibrationRows_length : d1CalibrationRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessD1Actual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessD1Actual.natRadicalWeightBound_iff_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessD1Actual.abc_implies_natRadicalWeightBound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ObjectTightnessD1Actual.d1CalibrationRows_length