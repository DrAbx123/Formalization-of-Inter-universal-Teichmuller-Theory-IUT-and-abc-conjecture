import tmp.sheaf.xif.paper.S2884C3ThetaQPilotScalingAllConsumer
import tmp.sheaf.xif.paper.S2885C3ThetaQPilotScaleOneConsumer
import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2886C3ThetaQPilotScalingQPilotConsumer

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
open LeanFormal.IUT.XiFPaper.S2884C3ThetaQPilotScalingAllConsumer
open LeanFormal.IUT.XiFPaper.S2885C3ThetaQPilotScaleOneConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBS : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBS : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3ThetaQPilot_scaling_and_qPilot_nonneg :
    (∀ u : ℚ_[C3.p]ˣ,
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 => ((u : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) +
          Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ))) ∧
      0 ≤ Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) ∧
      0 ≤ (∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i) :=
  ⟨(C3ThetaQPilot_scaling_all_consumer (l := l) (V := V) (I := I) C3 T e).1,
    (C3ThetaQPilot_scaling_all_consumer (l := l) (V := V) (I := I) C3 T e).2.2,
    Finset.sum_nonneg (fun i _ =>
      C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e i)⟩

#check C3ThetaQPilot_scaling_and_qPilot_nonneg

end LeanFormal.IUT.XiFPaper.S2886C3ThetaQPilotScalingQPilotConsumer
end
