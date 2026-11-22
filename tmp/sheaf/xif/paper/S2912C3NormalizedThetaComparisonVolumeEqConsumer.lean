import tmp.sheaf.xif.paper.S2911C3NormalizedThetaVolumeConsumerActual
import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2912C3NormalizedThetaComparisonVolumeEqConsumer

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
open LeanFormal.IUT.XiFPaper.S2761C3NormalizedThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2774C3NormalizedThetaVolumeNonnegActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2911C3NormalizedThetaVolumeConsumerActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCG : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCG : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- S2790 的 c3ComparisonRegionVolume 定义为 normalized Haar log-volume：
`Real.log ((c3NormalizedTensorHaar C3 region).toReal)`，不是 actualC3LogShellTensorHaar。 -/
theorem C3NormalizedThetaVolume_eq_normalizedComparisonRegionVolume :
    c3NormalizedThetaVolume (l := l) (V := V) (I := I) C3 T e =
      c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e := by
  rw [c3NormalizedThetaVolume_eq (l := l) (V := V) (I := I) C3 T e,
    c3ComparisonRegionVolume_eq (l := l) (V := V) (I := I) C3 T e]

theorem C3NormalizedThetaVolume_nonneg_and_eq_normalizedComparison :
    0 ≤ c3NormalizedThetaVolume (l := l) (V := V) (I := I) C3 T e ∧
      c3NormalizedThetaVolume (l := l) (V := V) (I := I) C3 T e =
        c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e :=
  ⟨c3NormalizedThetaVolume_nonneg (l := l) (V := V) (I := I) C3 T e,
    C3NormalizedThetaVolume_eq_normalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e⟩

#check C3NormalizedThetaVolume_eq_normalizedComparisonRegionVolume
end LeanFormal.IUT.XiFPaper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
end
