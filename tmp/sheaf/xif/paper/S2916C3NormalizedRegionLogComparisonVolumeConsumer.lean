import tmp.sheaf.xif.paper.S2778C3NormalizedRegionHaarLogEqActual
import tmp.sheaf.xif.paper.S2827C3NormalizedRegionHaarLogEqLogActual
import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2916C3NormalizedRegionLogComparisonVolumeConsumer

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2778C3NormalizedRegionHaarLogEqActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2827C3NormalizedRegionHaarLogEqLogActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCJ : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCJ : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3NormalizedRegion_logVolume_eq_comparisonVolume :
    (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
        c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e :=
  by
    rw [C3NormalizedRegion_haarLogVolume_toReal_eq_log (l := l) (V := V) (I := I) C3 T e]
    exact (c3ComparisonRegionVolume_eq (l := l) (V := V) (I := I) C3 T e).symm

#check C3NormalizedRegion_logVolume_eq_comparisonVolume

end LeanFormal.IUT.XiFPaper.S2916C3NormalizedRegionLogComparisonVolumeConsumer
end
