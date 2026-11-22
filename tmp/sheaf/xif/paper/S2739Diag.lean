import tmp.sheaf.xif.paper.S2733ScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2739Diag

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2733ScalingActual
open LeanFormal.IUT.XiFPaper.S2737C3BlockCharActual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance diagMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance diagBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance diagSMul : SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) := ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

set_option pp.all true in
example (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3)) (c : ℝ≥0)
    (hscale : actualC3LogShellTensorHaar C3 (u • S) = (c : ENNReal) * actualC3LogShellTensorHaar C3 S)
    (hpos : actualC3LogShellTensorHaar C3 S ≠ 0)
    (hfinite : actualC3LogShellTensorHaar C3 S ≠ ⊤) :
    (haarLogVolume (actualC3LogShellTensorHaar C3) (u • S)).toReal =
      Real.log ((c : ℝ)) + (haarLogVolume (actualC3LogShellTensorHaar C3) S).toReal := by
  have hcpos : 0 < c := by
    by_contra h
    push_neg at h
    have : (c : ENNReal) = 0 := by exact_mod_cast (le_antisymm h (zero_le c))
    have : actualC3LogShellTensorHaar C3 (u • S) = 0 := by rw [hscale, this, zero_mul]
    exact hpos (by rw [hscale, this, zero_mul])
  have hcfin : (c : ENNReal) < ⊤ := ENNReal.coe_lt_top
  have hfin' : actualC3LogShellTensorHaar C3 (u • S) < ⊤ := by
    rw [hscale]; exact ENNReal.mul_lt_top hcfin (lt_top_iff_ne_top.mpr hfinite)
  have hpos' : actualC3LogShellTensorHaar C3 (u • S) ≠ 0 := by
    rw [hscale]; exact mul_ne_zero (by exact_mod_cast (ne_of_gt hcpos)) hpos
  rw [haarLogVolume_of_lt_top hfin', haarLogVolume_of_lt_top (lt_top_iff_ne_top.mpr hfinite)]
  rw [hscale, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [Real.log_mul]
  trace_state
  sorry

end LeanFormal.IUT.XiFPaper.S2739Diag
end
