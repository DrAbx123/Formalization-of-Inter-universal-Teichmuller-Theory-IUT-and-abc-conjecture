import tmp.sheaf.xif.paper.S2882C3ThetaQPilotScalingConsumerActual
import tmp.sheaf.xif.paper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
import tmp.sheaf.xif.paper.S2774C3NormalizedThetaVolumeNonnegActual
import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2928C3ThetaVolumeScalingConsumerActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
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
open LeanFormal.IUT.XiFPaper.S2882C3ThetaQPilotScalingConsumerActual
open LeanFormal.IUT.XiFPaper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCS : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCS : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3ThetaVolume_scaling_consumer
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (u : ℚ_[C3.p]ˣ) :
    c3NormalizedThetaVolume (l := l) (V := V) (I := I) C3 T e =
        c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e ∧
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 => ((u : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
        c3NormalizedThetaVolume (l := l) (V := V) (I := I) C3 T e +
          Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ)) :=
  ⟨C3NormalizedThetaVolume_eq_normalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e, by
    rw [c3NormalizedThetaVolume_eq (l := l) (V := V) (I := I) C3 T e]
    exact (C3ThetaQPilot_scaling_consumer (l := l) (V := V) (I := I) C3 T e u).1⟩

#check C3ThetaVolume_scaling_consumer
end LeanFormal.IUT.XiFPaper.S2928C3ThetaVolumeScalingConsumerActual
end
