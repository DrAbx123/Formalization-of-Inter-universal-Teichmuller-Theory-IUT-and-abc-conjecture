import tmp.sheaf.xif.paper.S2892C3LatticeRegionLogScalingCompareConsumer
import tmp.sheaf.xif.paper.S2893C3LatticeRegionUnitLogVolumeCompareConsumer
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual
import tmp.sheaf.xif.paper.S2882C3ThetaQPilotScalingConsumerActual
import tmp.sheaf.xif.paper.S2883C3ThetaQPilotUnitScalingConsumer
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2894C3ScalingLogVolumeAllConsumer

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
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2882C3ThetaQPilotScalingConsumerActual
open LeanFormal.IUT.XiFPaper.S2883C3ThetaQPilotUnitScalingConsumer
open LeanFormal.IUT.XiFPaper.S2892C3LatticeRegionLogScalingCompareConsumer
open LeanFormal.IUT.XiFPaper.S2893C3LatticeRegionUnitLogVolumeCompareConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBW : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBW : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3Scaling_logVolume_all_consumer :
    (∀ u : ℚ_[C3.p]ˣ,
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          ((fun x : C3LogShellTensorBlock C3 => ((u : ℚ_[C3.p]) • x)) ''
            (tensorLattice (p := C3.p)
              (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :
              Set (C3LogShellTensorBlock C3)))).toReal) =
        Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ))
      ∧ Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          ((fun x : C3LogShellTensorBlock C3 => ((u : ℚ_[C3.p]) • x)) ''
            C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) +
          Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ))) ∧
    (∀ w : (PadicInt C3.p)ˣ,
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          ((fun x : C3LogShellTensorBlock C3 =>
            ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
            (tensorLattice (p := C3.p)
              (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :
              Set (C3LogShellTensorBlock C3)))).toReal) = 0
      ∧ Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          ((fun x : C3LogShellTensorBlock C3 =>
            ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
            C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)) :=
  ⟨fun u => C3LatticeRegion_logVolume_scaling_compare (l := l) (V := V) (I := I) C3 T e u,
    fun w => C3LatticeRegion_unit_logVolume_compare (l := l) (V := V) (I := I) C3 T e w⟩

#check C3Scaling_logVolume_all_consumer

end LeanFormal.IUT.XiFPaper.S2894C3ScalingLogVolumeAllConsumer
end
