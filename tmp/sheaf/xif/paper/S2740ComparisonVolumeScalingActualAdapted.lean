import tmp.sheaf.xif.paper.S2727V2RegionTarget
import tmp.sheaf.xif.paper.S2733ScalingActual

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2740ComparisonVolumeScalingActualAdapted

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
open LeanFormal.IUT.XiFPaper.S2733ScalingActual

variable {l : PrimeGeFive} {V : Type*} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2740Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2740Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance s2740SMul : SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) := ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

theorem haarLogVolume_toReal_eq_log
    (S : Set (C3LogShellTensorBlock C3))
    (hfinite : actualC3LogShellTensorHaar C3 S ≠ ⊤)
    (hge1 : 1 ≤ (actualC3LogShellTensorHaar C3 S).toReal) :
    (haarLogVolume (actualC3LogShellTensorHaar C3) S).toReal =
      Real.log ((actualC3LogShellTensorHaar C3 S).toReal) := by
  rw [haarLogVolume_of_lt_top (lt_top_iff_ne_top.mpr hfinite)]
  rw [ENNReal.toReal_ofReal (Real.log_nonneg hge1)]

theorem comparisonRegionVolume_eq_log
    (hfinite : actualC3LogShellTensorHaar C3
      (comparisonRegion C3 T e) ≠ ⊤)
    (hge1 : 1 ≤ (actualC3LogShellTensorHaar C3
      (comparisonRegion C3 T e)).toReal) :
    comparisonRegionVolume C3 T e =
      Real.log ((actualC3LogShellTensorHaar C3
        (comparisonRegion C3 T e)).toReal) := by
  rw [comparisonRegionVolume]
  exact haarLogVolume_toReal_eq_log C3 _ hfinite hge1

#check haarLogVolume_toReal_eq_log
#check comparisonRegionVolume_eq_log
end LeanFormal.IUT.XiFPaper.S2740ComparisonVolumeScalingActualAdapted
end
