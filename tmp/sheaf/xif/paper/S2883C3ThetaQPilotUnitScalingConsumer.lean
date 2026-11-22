import tmp.sheaf.xif.paper.S2882C3ThetaQPilotScalingConsumerActual
import tmp.sheaf.xif.paper.S2831C3RegionUnitInvarianceSummaryActual
import tmp.sheaf.xif.paper.S2833C3RegionRealLogScalingUnitSummaryActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import tmp.sheaf.xif.paper.S2734LatticeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2883C3ThetaQPilotUnitScalingConsumer

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
open LeanFormal.IUT.XiFPaper.S2831C3RegionUnitInvarianceSummaryActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2882C3ThetaQPilotScalingConsumerActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBQ : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBQ : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance smulBQ : SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

theorem C3ThetaQPilot_unit_scaling_consumer (w : (PadicInt C3.p)ˣ) :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 =>
          ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) := by
  rw [(C3Region_unit_invariance_summary (l := l) (V := V) (I := I) C3 T e w).2.1]

#check C3ThetaQPilot_unit_scaling_consumer
end LeanFormal.IUT.XiFPaper.S2883C3ThetaQPilotUnitScalingConsumer
end
