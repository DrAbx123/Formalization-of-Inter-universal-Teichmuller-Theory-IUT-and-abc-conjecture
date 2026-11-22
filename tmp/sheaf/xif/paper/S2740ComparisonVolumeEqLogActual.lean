import tmp.sheaf.xif.paper.S2740HaarLogVolumeToRealActual
import tmp.sheaf.xif.paper.S2727V2RegionTarget

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2740ComparisonVolumeEqLogActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
open LeanFormal.IUT.XiFPaper.S2740HaarLogVolumeToRealActual

variable {l : PrimeGeFive} {V : Type*} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2741Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2741Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem comparisonRegionVolume_eq_log
    (hfinite : actualC3LogShellTensorHaar C3
      (comparisonRegion C3 T e) ≠ ⊤)
    (hge1 : 1 ≤ (actualC3LogShellTensorHaar C3
      (comparisonRegion C3 T e)).toReal) :
    comparisonRegionVolume C3 T e =
      Real.log ((actualC3LogShellTensorHaar C3
        (comparisonRegion C3 T e)).toReal) := by
  rw [comparisonRegionVolume]
  exact haarLogVolume_toReal_eq_log (μ := actualC3LogShellTensorHaar C3)
    (S := comparisonRegion C3 T e) hfinite hge1

#check comparisonRegionVolume_eq_log
end LeanFormal.IUT.XiFPaper.S2740ComparisonVolumeEqLogActual
end
