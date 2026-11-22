import tmp.sheaf.xif.paper.S2733ScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2739HaarLogVolumeNormActualAdapted

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2733ScalingActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3SetSMul2739 :
    SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

theorem c3HaarLogVolume_smul_norm
    (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3))
    (hpos : actualC3LogShellTensorHaar C3 S ≠ 0)
    (hfinite : actualC3LogShellTensorHaar C3 S ≠ ⊤) :
    (haarLogVolume (actualC3LogShellTensorHaar C3) (u • S)).toReal =
      Real.log ((↑((‖(u : ℚ_[C3.p])‖₊) ^
        Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3)) : ℝ)) +
      (haarLogVolume (actualC3LogShellTensorHaar C3) S).toReal := by
  set c : ℝ≥0 := (‖(u : ℚ_[C3.p])‖₊) ^
    Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) with hcdef
  have hbase : (0 : ℝ≥0) < ‖(u : ℚ_[C3.p])‖₊ := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact norm_pos_iff.mpr (Units.ne_zero u)
  have hcpos : 0 < c := by
    rw [hcdef]
    exact pow_pos hbase _
  have hcne : (c : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hcpos)
  have hcfin : (c : ENNReal) < ⊤ := ENNReal.coe_lt_top
  have hfin' : actualC3LogShellTensorHaar C3 (u • S) < ⊤ := by
    rw [S2733_scalingHaar_norm]
    rw [← hcdef]
    exact ENNReal.mul_lt_top hcfin (lt_top_iff_ne_top.mpr hfinite)
  have hpos' : actualC3LogShellTensorHaar C3 (u • S) ≠ 0 := by
    rw [S2733_scalingHaar_norm]
    rw [← hcdef]
    exact mul_ne_zero hcne hpos
  rw [haarLogVolume_of_lt_top hfin',
    haarLogVolume_of_lt_top (lt_top_iff_ne_top.mpr hfinite)]
  rw [S2733_scalingHaar_norm]
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  subst c
  rw [Real.log_mul]
  · ring
  · exact ne_of_gt hcpos
  · exact ENNReal.toReal_ne_zero.mpr ⟨hpos, hfinite⟩

#check c3HaarLogVolume_smul_norm
end LeanFormal.IUT.XiFPaper.S2739HaarLogVolumeNormActualAdapted
end
