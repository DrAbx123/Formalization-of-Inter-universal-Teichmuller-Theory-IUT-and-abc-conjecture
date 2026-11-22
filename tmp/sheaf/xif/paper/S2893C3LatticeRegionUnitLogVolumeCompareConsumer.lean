import tmp.sheaf.xif.paper.S2890C3LatticeLogVolumeScalingConsumer
import tmp.sheaf.xif.paper.S2891C3LatticeLogVolumeUnitConsumer
import tmp.sheaf.xif.paper.S2882C3ThetaQPilotScalingConsumerActual
import tmp.sheaf.xif.paper.S2883C3ThetaQPilotUnitScalingConsumer

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2893C3LatticeRegionUnitLogVolumeCompareConsumer

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
open LeanFormal.IUT.XiFPaper.S2882C3ThetaQPilotScalingConsumerActual
open LeanFormal.IUT.XiFPaper.S2883C3ThetaQPilotUnitScalingConsumer
open LeanFormal.IUT.XiFPaper.S2887C3LatticeRegionScalingConsumer
open LeanFormal.IUT.XiFPaper.S2888C3LatticeRegionUnitScalingConsumer
open LeanFormal.IUT.XiFPaper.S2890C3LatticeLogVolumeScalingConsumer
open LeanFormal.IUT.XiFPaper.S2891C3LatticeLogVolumeUnitConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBV : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBV : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3LatticeRegion_unit_logVolume_compare (w : (PadicInt C3.p)ˣ) :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 =>
          ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
          (tensorLattice (p := C3.p)
            (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :
            Set (C3LogShellTensorBlock C3)))).toReal) = 0 ∧
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 =>
          ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :=
  ⟨C3Lattice_logVolume_unit_consumer (l := l) (V := V) (I := I) C3 T e w,
    C3ThetaQPilot_unit_scaling_consumer (l := l) (V := V) (I := I) C3 T e w⟩

#check C3LatticeRegion_unit_logVolume_compare

end LeanFormal.IUT.XiFPaper.S2893C3LatticeRegionUnitLogVolumeCompareConsumer
end
