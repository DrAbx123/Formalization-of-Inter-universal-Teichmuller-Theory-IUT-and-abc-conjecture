import tmp.sheaf.xif.paper.S2758MixedSpaceIQHullActual
import tmp.sheaf.xif.paper.S2758FundamentalDomainScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullLogShellRegion

noncomputable section
open scoped ENNReal nonZeroDivisors Classical Pointwise
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2759MixedSpaceNontrivialScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2758MixedSpaceIQHullActual
open LeanFormal.IUT.XiFPaper.S2758FundamentalDomainScalingActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- Nontrivial actual factor `r = 1/2`, in `[0,1]`. -/
noncomputable def S2759R : Real := (2 : Real)⁻¹

theorem S2759R_nonneg : 0 ≤ S2759R := by
  unfold S2759R
  norm_num

theorem S2759R_le_one : S2759R ≤ 1 := by
  unfold S2759R
  norm_num

theorem S2759R_pow_le_one :
    S2759R ^ Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K) ≤ 1 :=
  pow_le_one₀ S2759R_nonneg S2759R_le_one

/-- Actual nontrivial scaling region `r • fundamentalDomain`, `r = 1/2`. -/
noncomputable def S2759ScaledUnitRegion :
    Set (NumberField.mixedEmbedding.mixedSpace K) :=
  S2759R • S2758UnitRegion K

theorem S2759ScaledUnitRegion_volume_le :
    volume (S2759ScaledUnitRegion K) ≤ volume (S2758UnitRegion K) := by
  unfold S2759ScaledUnitRegion
  rw [S2758_haar_smul_of_nonneg (μ := volume) S2759R_nonneg]
  have hpow : ENNReal.ofReal
      (S2759R ^ Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K)) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal (S2759R_pow_le_one K)
  exact mul_le_of_le_one_left bot_le hpow

theorem S2759ScaledUnitRegion_volume_lt_top :
    volume (S2759ScaledUnitRegion K) < ⊤ :=
  lt_of_le_of_lt (S2759ScaledUnitRegion_volume_le K)
    (S2758UnitRegion_volume_lt_top K)

theorem S2759ScaledUnitRegion_logVolume_le :
    haarLogVolume volume (S2759ScaledUnitRegion K) ≤
      haarLogVolume volume (S2758UnitRegion K) := by
  by_cases hzero : volume (S2759ScaledUnitRegion K) = 0
  · rw [haarLogVolume_eq_zero_of_null hzero]
    exact bot_le
  · exact haarLogVolume_le_of_measure_le
      (lt_of_le_of_ne bot_le (Ne.symm hzero))
      (S2758UnitRegion_volume_lt_top K)
      (S2759ScaledUnitRegion_volume_le K)

/-- Actual nontrivial-r IQ-hull interface on the mixed space: same fundamental
domain, scaling by `r = 1/2`, image/hull the scaled region. -/
noncomputable def S2759IQHullInterface :
    IQHullLogVolumeInterface (NumberField.mixedEmbedding.mixedSpace K) where
  imageSet := S2759ScaledUnitRegion K
  hull := S2759ScaledUnitRegion K
  imageSet_subset_hull := subset_rfl
  logVolume := fun S => haarLogVolume volume S
  logVolume_mono := by
    intro S T hST
    exact haarLogVolume_mono hST
  unitRegion := S2758UnitRegion K
  scaleShift := fun x => S2759R • x
  hull_subset_scaleShift := by
    intro x hx
    simpa [S2759ScaledUnitRegion] using hx
  unitRegion_logVolume_lt_top := S2758UnitRegion_logVolume_lt_top K
  scaleShift_unitRegion_logVolume_le := by
    exact S2759ScaledUnitRegion_logVolume_le K

#check S2759R
#check S2759ScaledUnitRegion
#check S2759ScaledUnitRegion_volume_le
#check S2759ScaledUnitRegion_logVolume_le
#check S2759IQHullInterface
#print axioms S2759IQHullInterface

end LeanFormal.IUT.XiFPaper.S2759MixedSpaceNontrivialScalingActual
end
