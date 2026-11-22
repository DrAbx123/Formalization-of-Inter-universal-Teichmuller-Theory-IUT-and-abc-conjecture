import tmp.sheaf.xif.paper.S2894C3ScalingLogVolumeAllConsumer
import tmp.sheaf.xif.paper.S2897C3ThetaComparisonScalingConsumer
import tmp.sheaf.xif.paper.S2895C3ScalingLogVolumeOneConsumer
import tmp.sheaf.xif.paper.S2882C3ThetaQPilotScalingConsumerActual
import tmp.sheaf.xif.paper.S2883C3ThetaQPilotUnitScalingConsumer
import tmp.sheaf.xif.paper.S2834C3QPilotThetaComparisonDataConsumer
import tmp.sheaf.xif.paper.S2835C3QPilotThetaDataConsumer
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2899C3ThetaComparisonUnitScalingAllConsumer

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
open LeanFormal.IUT.XiFPaper.S2897C3ThetaComparisonScalingConsumer
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
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

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBX : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBX : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3ThetaComparison_unit_scaling_all_consumer :
    (∀ w : (PadicInt C3.p)ˣ,
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          ((fun x : C3LogShellTensorBlock C3 =>
            ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
            C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
        (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume) ∧
      0 ≤ (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume :=
  ⟨C3ThetaComparison_unit_scaling_consumer (l := l) (V := V) (I := I) C3 T e,
    C3QPilotThetaData_theta_nonneg (l := l) (V := V) (I := I) C3 T e⟩

#check C3ThetaComparison_unit_scaling_all_consumer

end LeanFormal.IUT.XiFPaper.S2899C3ThetaComparisonUnitScalingAllConsumer
end
