import tmp.sheaf.xif.paper.S2756FractionalIdealHaarActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

noncomputable section
open scoped ENNReal nonZeroDivisors Classical
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2758MixedSpaceIQHullActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2756FractionalIdealHaarActual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u

variable (K : Type u) [Field K] [NumberField K]



/-- The actual unit region: the Haar fundamental domain of the unit fractional
ideal lattice in the mixed space. -/
noncomputable def S2758UnitRegion : Set (NumberField.mixedEmbedding.mixedSpace K) :=
  S2756IdealFundamentalDomain K (1 : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)

/-- Actual set-level Haar log-volume on the mixed space. -/
noncomputable def S2758LogVolume :
    Set (NumberField.mixedEmbedding.mixedSpace K) → ENNReal :=
  fun S => haarLogVolume volume S

theorem S2758LogVolume_mono {S T : Set (NumberField.mixedEmbedding.mixedSpace K)}
    (hST : S ⊆ T) : S2758LogVolume K S ≤ S2758LogVolume K T :=
  haarLogVolume_mono hST

theorem S2758UnitRegion_volume_lt_top :
    volume (S2758UnitRegion K) < ⊤ := by
  unfold S2758UnitRegion S2756IdealFundamentalDomain
  have h := NumberField.mixedEmbedding.minkowskiBound_lt_top K
    (1 : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)
  unfold NumberField.mixedEmbedding.minkowskiBound at h
  rcases ENNReal.mul_lt_top_iff.mp h with ⟨ha, _⟩ | hzero | hzero
  · exact ha
  · rw [hzero]
    exact ENNReal.zero_lt_top
  · exact absurd hzero (ENNReal.pow_ne_zero (by norm_num) _)

theorem S2758UnitRegion_logVolume_lt_top :
    S2758LogVolume K (S2758UnitRegion K) < ⊤ := by
  unfold S2758LogVolume
  rw [haarLogVolume_of_lt_top (S2758UnitRegion_volume_lt_top K)]
  exact ENNReal.ofReal_lt_top

/-- Actual IQ-hull interface on the mixed space, with the genuine Haar
log-volume and the actual unit-ideal fundamental domain.  The scaling is the
identity (the actual `≤ 1` factor `r = 1`); the nontrivial factor `r =
(absNorm J)⁻¹` requires the separate positivity/finite-determinant scaling
estimate and is not asserted here. -/
noncomputable def S2758IQHullInterface :
    IQHullLogVolumeInterface (NumberField.mixedEmbedding.mixedSpace K) where
  imageSet := S2758UnitRegion K
  hull := S2758UnitRegion K
  imageSet_subset_hull := subset_rfl
  logVolume := S2758LogVolume K
  logVolume_mono := by
    intro S T hST
    exact S2758LogVolume_mono K hST
  unitRegion := S2758UnitRegion K
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  unitRegion_logVolume_lt_top := S2758UnitRegion_logVolume_lt_top K
  scaleShift_unitRegion_logVolume_le := by
    rw [Set.image_id]

#check S2758UnitRegion
#check S2758LogVolume
#check S2758IQHullInterface
#print axioms S2758IQHullInterface

end LeanFormal.IUT.XiFPaper.S2758MixedSpaceIQHullActual
end
