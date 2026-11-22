import tmp.sheaf.xif.paper.S2902C3ThetaComparisonUnitQPilotConsumer
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual
import tmp.sheaf.xif.paper.S2901C3ThetaComparisonScaleOneConsumer
import tmp.sheaf.xif.paper.S2903C3ThetaComparisonScalingLatticeConsumer
import tmp.sheaf.xif.paper.S2835C3QPilotThetaDataConsumer
import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2905C3ThetaComparisonScalingOneLatticeConsumer

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
open LeanFormal.IUT.XiFPaper.S2902C3ThetaComparisonUnitQPilotConsumer
open LeanFormal.IUT.XiFPaper.S2901C3ThetaComparisonScaleOneConsumer
open LeanFormal.IUT.XiFPaper.S2903C3ThetaComparisonScalingLatticeConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCB : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCB : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3ThetaComparison_scaling_one_and_lattice_consumer :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((1 : ℚ_[C3.p]ˣ) • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume ∧
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (tensorLattice (p := C3.p)
          (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) = 1 :=
  ⟨C3ThetaComparison_scale_one_consumer (l := l) (V := V) (I := I) C3 T e,
    c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3⟩

#check C3ThetaComparison_scaling_one_and_lattice_consumer

end LeanFormal.IUT.XiFPaper.S2905C3ThetaComparisonScalingOneLatticeConsumer
end
