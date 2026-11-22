/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CorrectedRegionLogLawProvedActual
import tmp.sheaf.xif.paper.Mzk1ProductHaarSingletonActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A675 corrected-region log law + unconditional Gap 1 (mainline)

B1 is now GREEN (`Mzk1ProductHaarSingletonActual.productHaar_singleton_zero`), so no
geometric parameter is needed:
* `correctedRegion_logLaw`: full log law for `badInvScale eN '' (unitRegion ∪ {point})`
  (unit-region law + null singleton union);
* `corrected_gap1_unconditional`: full bad support + `d_b >= 1` + `unit >= 0` imply the
  corrected-region Gap 1 height comparison.

No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual

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
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawProvedActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawBlockersActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual
open LeanFormal.IUT.XiFPaper.Mzk1ProductHaarSingletonActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Measure of `A ∪ nullB` equals measure of `A`. -/
theorem measure_union_eq_left_of_null {μ : Measure (S1902Carrier T)}
    (A B : Set (S1902Carrier T)) (hB : μ B = 0) : μ (A ∪ B) = μ A := by
  refine le_antisymm ?_ (measure_mono (Set.subset_union_left))
  calc μ (A ∪ B) ≤ μ A + μ B := measure_union_le A B
    _ = μ A := by rw [hB, add_zero]

/-- **Full corrected-region log law** (B1 applied via null singleton). -/
theorem correctedRegion_logLaw
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (aN bN cN : Nat) :
    (s1902LogVolume T
        (badInvScale T (eN aN bN cN) '' (s1902UnitRegion T ∪ {point aN bN cN}))).toReal =
      (s1902LogVolume T (s1902UnitRegion T)).toReal +
        ∑ bBad : Bad (nativePlaceSelection T),
          (eN aN bN cN bBad : ℝ) *
            ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
              Real.log ((qVFamTensorP T bBad : ℕ) : ℝ)) := by
  rw [Set.image_union, Set.image_singleton]
  have hB : rootExtensionProductHaar T
      ({badInvScale T (eN aN bN cN) (point aN bN cN)} : Set (S1902Carrier T)) = 0 :=
    productHaar_singleton_zero T _
  have hμeq : rootExtensionProductHaar T
      (badInvScale T (eN aN bN cN) '' s1902UnitRegion T ∪
        {badInvScale T (eN aN bN cN) (point aN bN cN)}) =
      rootExtensionProductHaar T (badInvScale T (eN aN bN cN) '' s1902UnitRegion T) :=
    measure_union_eq_left_of_null T _ _ hB
  have hνeq : (s1902HaarScale T • rootExtensionProductHaar T)
      (badInvScale T (eN aN bN cN) '' s1902UnitRegion T ∪
        {badInvScale T (eN aN bN cN) (point aN bN cN)}) =
      (s1902HaarScale T • rootExtensionProductHaar T)
        (badInvScale T (eN aN bN cN) '' s1902UnitRegion T) := by
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, hμeq]
  have hvol : s1902LogVolume T
      (badInvScale T (eN aN bN cN) '' s1902UnitRegion T ∪
        {badInvScale T (eN aN bN cN) (point aN bN cN)}) =
      s1902LogVolume T (badInvScale T (eN aN bN cN) '' s1902UnitRegion T) := by
    unfold s1902LogVolume s1902NormalizedHaar
    unfold haarLogVolume
    rw [hνeq]
  rw [hvol]
  exact corrected_unitRegion_logLaw T (eN aN bN cN) hc0 hcT

/-- Arithmetic core: full support and `d_b >= 1` absorb `log c`. -/
theorem log_height_le_badSum_of_fullSupport
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (aN bN cN : Nat) (habc : IsABCTriple aN bN cN)
    (hfull : aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
      (qVFamTensorP T bBad) ^ (eN aN bN cN bBad)) :
    Real.log (cN : ℝ) ≤ ∑ bBad : Bad (nativePlaceSelection T),
      (eN aN bN cN bBad : ℝ) *
        ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
          Real.log ((qVFamTensorP T bBad : ℕ) : ℝ)) := by
  have hcpos : (0 : ℝ) < (cN : ℝ) := by exact_mod_cast habc.c_pos
  have hcle : (cN : ℝ) ≤ ((aN + bN + cN + 1 : Nat) : ℝ) := by
    have : cN ≤ aN + bN + cN + 1 := by omega
    exact_mod_cast this
  have hlogc : Real.log (cN : ℝ) ≤ Real.log (((aN + bN + cN + 1 : Nat)) : ℝ) :=
    Real.log_le_log hcpos hcle
  rw [hfull] at hlogc
  have hlogprod : Real.log (((∏ bBad : Bad (nativePlaceSelection T),
      (qVFamTensorP T bBad) ^ (eN aN bN cN bBad) : Nat) : ℝ)) =
      ∑ bBad : Bad (nativePlaceSelection T),
        (eN aN bN cN bBad : ℝ) * Real.log ((qVFamTensorP T bBad : ℝ)) := by
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro bBad _
      rw [Nat.cast_pow, Real.log_pow]
    · intro bBad _
      have hp : (qVFamTensorP T bBad : Nat) ≠ 0 :=
        (Fact.out : Nat.Prime (qVFamTensorP T bBad)).ne_zero
      exact_mod_cast (pow_ne_zero (eN aN bN cN bBad) hp)
  rw [hlogprod] at hlogc
  have hlogp_nonneg : ∀ bBad : Bad (nativePlaceSelection T),
      0 ≤ Real.log ((qVFamTensorP T bBad : ℝ)) := by
    intro bBad
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((qVFamTensorP T bBad : Nat) : ℝ) := by
      exact_mod_cast (le_of_lt (Fact.out : Nat.Prime (qVFamTensorP T bBad)).one_lt)
    simpa using this
  have hsum_mono : (∑ bBad : Bad (nativePlaceSelection T),
        (eN aN bN cN bBad : ℝ) * Real.log ((qVFamTensorP T bBad : ℝ))) ≤
      ∑ bBad : Bad (nativePlaceSelection T),
        (eN aN bN cN bBad : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
            Real.log ((qVFamTensorP T bBad : ℝ))) := by
    refine Finset.sum_le_sum ?_
    intro bBad _
    have hdb := hd bBad
    have hlogb := hlogp_nonneg bBad
    have he : (0 : ℝ) ≤ (eN aN bN cN bBad : ℝ) := by positivity
    calc (eN aN bN cN bBad : ℝ) * Real.log ((qVFamTensorP T bBad : ℝ))
        = (eN aN bN cN bBad : ℝ) * (1 * Real.log ((qVFamTensorP T bBad : ℝ))) := by ring
      _ ≤ (eN aN bN cN bBad : ℝ) *
            ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
              Real.log ((qVFamTensorP T bBad : ℝ))) := by
          exact mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_right hdb hlogb) he
  linarith

/-- **Unconditional corrected Gap 1** (B1 discharged by the green singleton lemma). -/
theorem corrected_gap1_unconditional
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hd : ∀ bBad : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ))
    (hfull : ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      aN + bN + cN + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN aN bN cN bBad))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
      Height.logHeight₁ (abcRationalPoint aN cN) ≤
        (1 + ε) * (s1902LogVolume T
          (badInvScale T (eN aN bN cN) ''
            (s1902UnitRegion T ∪ {point aN bN cN}))).toReal := by
  intro aN bN cN habc
  have hlogv := correctedRegion_logLaw T point eN hc0 hcT aN bN cN
  have harith := log_height_le_badSum_of_fullSupport T eN hd aN bN cN habc (hfull aN bN cN habc)
  have hheight : Height.logHeight₁ (abcRationalPoint aN cN) = Real.log (cN : ℝ) :=
    abcRationalPoint_logHeight₁ habc
  have hsum : Real.log (cN : ℝ) ≤
      (s1902LogVolume T (s1902UnitRegion T)).toReal +
        ∑ bBad : Bad (nativePlaceSelection T),
          (eN aN bN cN bBad : ℝ) *
            ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
              Real.log ((qVFamTensorP T bBad : ℕ) : ℝ)) := by linarith
  have hsum_nonneg : 0 ≤ ∑ bBad : Bad (nativePlaceSelection T),
        (eN aN bN cN bBad : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
            Real.log ((qVFamTensorP T bBad : ℕ) : ℝ)) := by
    refine Finset.sum_nonneg ?_
    intro bBad _
    have hdb := hd bBad
    have hlogb : 0 ≤ Real.log ((qVFamTensorP T bBad : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((qVFamTensorP T bBad : Nat) : ℝ) := by
        exact_mod_cast (le_of_lt (Fact.out : Nat.Prime (qVFamTensorP T bBad)).one_lt)
      simpa using this
    have he : (0 : ℝ) ≤ (eN aN bN cN bBad : ℝ) := by positivity
    exact mul_nonneg he (mul_nonneg (by linarith) hlogb)
  have hX : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal +
      ∑ bBad : Bad (nativePlaceSelection T),
        (eN aN bN cN bBad : ℝ) *
          ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
            Real.log ((qVFamTensorP T bBad : ℕ) : ℝ)) := by linarith
  rw [hheight, hlogv]
  have hle1 : (1 : ℝ) ≤ 1 + ε := by linarith
  calc Real.log (cN : ℝ)
      ≤ 1 * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          ∑ bBad : Bad (nativePlaceSelection T),
            (eN aN bN cN bBad : ℝ) *
              ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
                Real.log ((qVFamTensorP T bBad : ℕ) : ℝ))) := by simpa using hsum
    _ ≤ (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          ∑ bBad : Bad (nativePlaceSelection T),
            (eN aN bN cN bBad : ℝ) *
              ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
                Real.log ((qVFamTensorP T bBad : ℕ) : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hle1 hX

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual.correctedRegion_logLaw
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual.log_height_le_badSum_of_fullSupport
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual.corrected_gap1_unconditional