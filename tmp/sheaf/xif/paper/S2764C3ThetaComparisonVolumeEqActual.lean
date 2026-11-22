import tmp.sheaf.xif.paper.S2747C3NormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S2740HaarLogVolumeToRealActual
import tmp.sheaf.xif.paper.S2761C3NormalizedThetaPilotLogVolumeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2764C3ThetaComparisonVolumeEqActual

open MeasureTheory
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2740HaarLogVolumeToRealActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2747C3NormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2761C3NormalizedThetaPilotLogVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measY : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelY : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem c3NormalizedThetaPilotLogVolume_eq_comparisonLogVolume :
    c3NormalizedThetaPilotLogVolume (l := l) (V := V) (I := I) C3 T e =
      c3NormalizedComparisonRegionLogVolume (l := l) (V := V) (I := I) C3 T e := by
  unfold c3NormalizedThetaPilotLogVolume c3NormalizedComparisonRegionLogVolume
  rw [haarLogVolume_toReal_eq_log (μ := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
    (ne_of_lt (c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e))
    (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)]

#check c3NormalizedThetaPilotLogVolume_eq_comparisonLogVolume
end LeanFormal.IUT.XiFPaper.S2764C3ThetaComparisonVolumeEqActual
end
