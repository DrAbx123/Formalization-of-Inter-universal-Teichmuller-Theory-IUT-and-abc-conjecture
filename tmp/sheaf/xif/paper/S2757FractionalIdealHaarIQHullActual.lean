import tmp.sheaf.xif.paper.S2756FractionalIdealHaarActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

noncomputable section
open MeasureTheory
open scoped ENNReal nonZeroDivisors
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2757FractionalIdealHaarIQHullActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2756FractionalIdealHaarActual

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The unit group of fractional ideals, used as the lattice carrier. -/
abbrev IdealCarrier : Type u := (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ

/-- Actual set-level lattice log-volume: supremum over the Haar fundamental
domain volumes of the fractional ideals in the set. -/
noncomputable def IdealSetHaarVolume (S : Set (IdealCarrier K)) : ENNReal :=
  ⨆ I : S, S2756IdealHaarVolume K I.1

theorem IdealSetHaarVolume_mono {S T : Set (IdealCarrier K)} (hST : S ⊆ T) :
    IdealSetHaarVolume K S ≤ IdealSetHaarVolume K T := by
  refine iSup_le fun I : S => ?_
  exact le_iSup (fun J : T => S2756IdealHaarVolume K J.1) ⟨I.1, hST I.2⟩

theorem S2757_unitIdeal_haarVolume_lt_top :
    S2756IdealHaarVolume K (1 : IdealCarrier K) < ⊤ := by
  rw [S2756IdealHaarVolume_eq]
  rw [show ((1 : IdealCarrier K).1) = (1 : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) from rfl]
  rw [FractionalIdeal.absNorm_one]
  rw [show ((1 : ℚ) : ℝ) = 1 by norm_num]
  rw [ENNReal.ofReal_one, one_mul]
  rw [NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis]
  exact ENNReal.mul_lt_top (by simp) (by simp)

/-- Actual IQ-hull interface on the fractional-ideal lattice carrier.  It uses
the genuine Haar fundamental-domain volume (not an indicator).  The single
unit lattice point is used for image/hull/unitRegion; it is an actual fixed-point
interface, not the full paper theta hull. -/
noncomputable def IdealIQHullInterface :
    IQHullLogVolumeInterface (IdealCarrier K) where
  imageSet := {1}
  hull := {1}
  imageSet_subset_hull := subset_rfl
  logVolume := IdealSetHaarVolume K
  logVolume_mono := by
    intro S T hST
    exact IdealSetHaarVolume_mono K hST
  unitRegion := {1}
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  unitRegion_logVolume_lt_top := by
    refine lt_of_le_of_lt (iSup_le fun I => ?_) (S2757_unitIdeal_haarVolume_lt_top K)
    have hI : I.1 = 1 := Set.mem_singleton_iff.mp I.2
    rw [hI]
  scaleShift_unitRegion_logVolume_le := by
    rw [Set.image_id]

#check IdealCarrier
#check IdealSetHaarVolume
#check IdealSetHaarVolume_mono
#check S2757_unitIdeal_haarVolume_lt_top
#check IdealIQHullInterface
#print axioms IdealIQHullInterface

end LeanFormal.IUT.XiFPaper.S2757FractionalIdealHaarIQHullActual
end
