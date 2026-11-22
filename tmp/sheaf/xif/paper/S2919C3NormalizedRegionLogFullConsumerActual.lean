import tmp.sheaf.xif.paper.S2917C3NormalizedRegionLogScalingConsumerActual
import tmp.sheaf.xif.paper.S2918C3NormalizedRegionLogHvolEqConsumerActual
import tmp.sheaf.xif.paper.S2915C3NormalizedRegionLogConsumerActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2919C3NormalizedRegionLogFullConsumerActual

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
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2778C3NormalizedRegionHaarLogEqActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2820C3NormalizedRegionRealLogScalingSelfActual
open LeanFormal.IUT.XiFPaper.S2827C3NormalizedRegionHaarLogEqLogActual
open LeanFormal.IUT.XiFPaper.S2910C3NormalizedHvolConsumerActual
open LeanFormal.IUT.XiFPaper.S2913C3ComparisonRegionVolumeHvolEqConsumer
open LeanFormal.IUT.XiFPaper.S2915C3NormalizedRegionLogConsumerActual
open LeanFormal.IUT.XiFPaper.S2916C3NormalizedRegionLogComparisonVolumeConsumer
open LeanFormal.IUT.XiFPaper.S2917C3NormalizedRegionLogScalingConsumerActual
open LeanFormal.IUT.XiFPaper.S2918C3NormalizedRegionLogHvolEqConsumerActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCL : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCL : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance smulCL : SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩


theorem C3NormalizedRegionLog_scaling_and_hvol_consumer :
    (∀ u : ℚ_[C3.p]ˣ,
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) +
          Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ))) ∧
      (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
        c3NormalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e :=
  ⟨fun u => (C3NormalizedRegion_log_scaling_consumer (l := l) (V := V) (I := I) C3 T e u).1,
    C3NormalizedRegion_logVolume_eq_normalizedHvolVolume (l := l) (V := V) (I := I) C3 T e⟩

#check C3NormalizedRegionLog_scaling_and_hvol_consumer

end LeanFormal.IUT.XiFPaper.S2919C3NormalizedRegionLogFullConsumerActual
end
