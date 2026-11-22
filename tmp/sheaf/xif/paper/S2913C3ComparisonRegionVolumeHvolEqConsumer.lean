import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.S2910C3NormalizedHvolConsumerActual
import tmp.sheaf.xif.paper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2913C3ComparisonRegionVolumeHvolEqConsumer

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
open LeanFormal.IUT.XiFPaper.S2774C3NormalizedThetaVolumeNonnegActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2910C3NormalizedHvolConsumerActual
open LeanFormal.IUT.XiFPaper.S2911C3NormalizedThetaVolumeConsumerActual
open LeanFormal.IUT.XiFPaper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCH : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCH : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3ComparisonRegionVolume_eq_normalizedHvolVolume :
    c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
      c3NormalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e := by
  rw [c3ComparisonRegionVolume_eq (l := l) (V := V) (I := I) C3 T e]
  exact (c3NormalizedComparisonRegionVolume_eq_log (l := l) (V := V) (I := I) C3 T e).symm

theorem C3NormalizedThetaVolume_eq_normalizedHvolVolume :
    c3NormalizedThetaVolume (l := l) (V := V) (I := I) C3 T e =
      c3NormalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e := by
  rw [C3NormalizedThetaVolume_eq_normalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e,
    C3ComparisonRegionVolume_eq_normalizedHvolVolume (l := l) (V := V) (I := I) C3 T e]

#check C3ComparisonRegionVolume_eq_normalizedHvolVolume

end LeanFormal.IUT.XiFPaper.S2913C3ComparisonRegionVolumeHvolEqConsumer
end
