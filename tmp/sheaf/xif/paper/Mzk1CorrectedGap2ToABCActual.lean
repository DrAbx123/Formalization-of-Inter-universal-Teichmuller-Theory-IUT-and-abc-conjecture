/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CorrectedGap1UnconditionalActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A678 corrected-model Gap 2 => ABC (mainline)

Honest final boundary: with Gap 1 now a THEOREM, the only remaining named input in the
corrected model is the Gap 2 shape.  This file proves the implication

`correctedGap2_to_ABC`: full bad support + `d_b >= 1` + `unit >= 0` + the corrected
region Gap 2 shape imply `ABCConjecture`.

The CONVERSE (ABC => corrected Gap 2) is NOT claimed: bad primes need not lie in the
support of `rad(abc)`, so ABC does not control `Σ e_b d_b log p_b`; that would need
extra arithmetic hypotheses.  No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual

open scoped Pointwise ENNReal BigOperators
open MeasureTheory
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
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Gap 2 (corrected model) implies ABC.**  The named inputs are exactly: full bad
  support, `d_b >= 1`, positive unit region, and the corrected-region Gap 2 shape. -/
theorem correctedGap2_to_ABC
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hGap2 : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      (s1902LogVolume T
        (badInvScale T (eN aN bN cN) '' (s1902UnitRegion T ∪ {point aN bN cN}))).toReal ≤
          (1 + ε) * arithmeticWeight (abcRationalPoint aN cN) +
            (s1902LogVolume T (s1902Hull T)).toReal + D) :
    ABCConjecture := by
  refine abcConjecture_iff_abcArithmeticWeightHeightBound.mpr ?_
  intro ε hε
  obtain ⟨D, hD⟩ := hGap2 ε hε
  refine ⟨(s1902LogVolume T (s1902Hull T)).toReal + D, ?_⟩
  intro aN bN cN habc
  have hlogv := correctedRegion_logLaw T point eN hc0 hcT aN bN cN
  have harith := log_height_le_badSum_of_fullSupport T eN hd aN bN cN habc
    (hfull aN bN cN habc)
  have hlogp_nonneg : ∀ bBad : Bad (nativePlaceSelection T),
      0 ≤ Real.log ((qVFamTensorP T bBad : ℕ) : ℝ) := by
    intro bBad
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((qVFamTensorP T bBad : Nat) : ℝ) := by
      exact_mod_cast (le_of_lt (Fact.out : Nat.Prime (qVFamTensorP T bBad)).one_lt)
    simpa using this
  have hsum_nonneg : 0 ≤ ∑ bBad : Bad (nativePlaceSelection T),
        (eN aN bN cN bBad : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
            Real.log ((qVFamTensorP T bBad : ℕ) : ℝ)) := by
    refine Finset.sum_nonneg ?_
    intro bBad _
    have hdb := hd bBad
    have hlogb := hlogp_nonneg bBad
    have he : (0 : ℝ) ≤ (eN aN bN cN bBad : ℝ) := by positivity
    exact mul_nonneg he (mul_nonneg (by linarith) hlogb)
  have hle_vol : Real.log (cN : ℝ) ≤
      (s1902LogVolume T
        (badInvScale T (eN aN bN cN) '' (s1902UnitRegion T ∪ {point aN bN cN}))).toReal := by
    rw [hlogv]
    linarith
  have hD' := hD aN bN cN habc
  have hheight : Height.logHeight₁ (abcRationalPoint aN cN) = Real.log (cN : ℝ) :=
    abcRationalPoint_logHeight₁ habc
  rw [hheight]
  linarith

/-- Audit rows for the corrected-model Gap 2 boundary. -/
def calibrationRows : List (String × String) :=
  [ ("Gap 1 in corrected model", "THEOREM (Mzk1CorrectedGap1UnconditionalActual)"),
    ("Gap 2 in corrected model", "named hypothesis (this file)"),
    ("Gap 2 => ABC", "PROVED (correctedGap2_to_ABC)"),
    ("ABC => Gap 2", "NOT claimed: bad primes not controlled by rad(abc)"),
    ("scope", "ABC gate NOT passed; no canonical change") ]

theorem calibrationRows_length : calibrationRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual.correctedGap2_to_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ToABCActual.calibrationRows_length