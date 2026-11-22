import tmp.sheaf.xif.paper.S2758MixedSpaceIQHullActual
import tmp.sheaf.xif.paper.S2758FundamentalDomainScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullLogShellRegion
import Mathlib.RingTheory.FractionalIdeal.Norm

noncomputable section
open scoped ENNReal nonZeroDivisors Classical Pointwise
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2758MixedSpaceIQHullActual
open LeanFormal.IUT.XiFPaper.S2758FundamentalDomainScalingActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The actual paper scaling factor `r = min 1 (absNorm J)⁻¹` at a fractional
ideal unit. -/
noncomputable def S2760R (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) : Real :=
  min 1 (((FractionalIdeal.absNorm J.1 : ℚ) : Real)⁻¹)

theorem S2760R_nonneg (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    0 ≤ S2760R K J := by
  unfold S2760R
  refine le_min (by norm_num) ?_
  refine inv_nonneg.mpr ?_
  exact_mod_cast FractionalIdeal.absNorm_nonneg J.1

theorem S2760R_le_one (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    S2760R K J ≤ 1 := by
  unfold S2760R
  exact min_le_left _ _

theorem S2760R_pow_le_one (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    S2760R K J ^ Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K) ≤ 1 :=
  pow_le_one₀ (S2760R_nonneg K J) (S2760R_le_one K J)

noncomputable def S2760ScaledUnitRegion
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    Set (NumberField.mixedEmbedding.mixedSpace K) :=
  S2760R K J • S2758UnitRegion K

theorem S2760ScaledUnitRegion_volume_le
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    volume (S2760ScaledUnitRegion K J) ≤ volume (S2758UnitRegion K) := by
  unfold S2760ScaledUnitRegion
  rw [S2758_haar_smul_of_nonneg (μ := volume) (S2760R_nonneg K J)]
  have hpow : ENNReal.ofReal
      (S2760R K J ^ Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K)) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal (S2760R_pow_le_one K J)
  exact mul_le_of_le_one_left bot_le hpow

theorem S2760ScaledUnitRegion_logVolume_le
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    haarLogVolume volume (S2760ScaledUnitRegion K J) ≤
      haarLogVolume volume (S2758UnitRegion K) := by
  by_cases hzero : volume (S2760ScaledUnitRegion K J) = 0
  · rw [haarLogVolume_eq_zero_of_null hzero]
    exact bot_le
  · exact haarLogVolume_le_of_measure_le
      (lt_of_le_of_ne bot_le (Ne.symm hzero))
      (S2758UnitRegion_volume_lt_top K)
      (S2760ScaledUnitRegion_volume_le K J)

/-- Nontrivial actual paper-factor IQ-hull interface on the mixed space. -/
noncomputable def S2760IQHullInterface
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    IQHullLogVolumeInterface (NumberField.mixedEmbedding.mixedSpace K) where
  imageSet := S2760ScaledUnitRegion K J
  hull := S2760ScaledUnitRegion K J
  imageSet_subset_hull := subset_rfl
  logVolume := fun S => haarLogVolume volume S
  logVolume_mono := by
    intro S T hST
    exact haarLogVolume_mono hST
  unitRegion := S2758UnitRegion K
  scaleShift := fun x => S2760R K J • x
  hull_subset_scaleShift := by
    intro x hx
    simpa [S2760ScaledUnitRegion] using hx
  unitRegion_logVolume_lt_top := S2758UnitRegion_logVolume_lt_top K
  scaleShift_unitRegion_logVolume_le := S2760ScaledUnitRegion_logVolume_le K J

#check S2760R
/-- For an integral fractional ideal (`1 ≤ absNorm J`), the paper factor is
exactly `(absNorm J)^(-1)`; the `min 1` truncation is inactive. -/
theorem S2760R_eq_inv_of_one_le
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)
    (h : 1 ≤ ((FractionalIdeal.absNorm J.1 : ℚ) : Real)) :
    S2760R K J = 1 / (((FractionalIdeal.absNorm J.1 : ℚ) : Real)) := by
  unfold S2760R
  rw [min_eq_right (inv_le_one_of_one_le₀ h)]
  ring

#check S2760R_nonneg
#check S2760R_le_one
#check S2760ScaledUnitRegion
#check S2760ScaledUnitRegion_volume_le
#check S2760ScaledUnitRegion_logVolume_le
#check S2760IQHullInterface
#print axioms S2760IQHullInterface

end LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual
end
