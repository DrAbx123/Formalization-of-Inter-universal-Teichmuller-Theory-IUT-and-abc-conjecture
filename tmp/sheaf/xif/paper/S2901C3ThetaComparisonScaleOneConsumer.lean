import tmp.sheaf.xif.paper.S2898C3ThetaComparisonScalingAllConsumer
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual
import tmp.sheaf.xif.paper.S2899C3ThetaComparisonUnitScalingAllConsumer
import tmp.sheaf.xif.paper.S2897C3ThetaComparisonScalingConsumer

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2901C3ThetaComparisonScaleOneConsumer

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
open LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2835C3QPilotThetaDataConsumer
open LeanFormal.IUT.XiFPaper.S2882C3ThetaQPilotScalingConsumerActual
open LeanFormal.IUT.XiFPaper.S2883C3ThetaQPilotUnitScalingConsumer
open LeanFormal.IUT.XiFPaper.S2897C3ThetaComparisonScalingConsumer
open LeanFormal.IUT.XiFPaper.S2898C3ThetaComparisonScalingAllConsumer
open LeanFormal.IUT.XiFPaper.S2899C3ThetaComparisonUnitScalingAllConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBZ : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBZ : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3ThetaComparison_scale_one_consumer :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((fun x : C3LogShellTensorBlock C3 =>
        ((1 : ℚ_[C3.p]ˣ) : ℚ_[C3.p]) • x) ''
        C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume := by
  have h := C3ThetaComparison_scaling_consumer (l := l) (V := V) (I := I) C3 T e (1 : ℚ_[C3.p]ˣ)
  simpa using h

#check C3ThetaComparison_scale_one_consumer

end LeanFormal.IUT.XiFPaper.S2901C3ThetaComparisonScaleOneConsumer
end
