import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2771C3QPilotThetaComparisonConsumerActual

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
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measQ : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelQ : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


noncomputable def c3QPilotThetaSum : ℝ :=
  ∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i

theorem c3QPilotThetaSum_eq :
    c3QPilotThetaSum (l := l) (V := V) (I := I) C3 T e =
      ∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i := rfl

theorem c3QPilotThetaSum_nonneg :
    0 ≤ c3QPilotThetaSum (l := l) (V := V) (I := I) C3 T e :=
  Finset.sum_nonneg (fun i _ =>
    C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e i)

noncomputable def c3NormalizedThetaVolumeConsumer : ℝ :=
  Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)

theorem c3NormalizedThetaVolumeConsumer_nonneg :
    0 ≤ c3NormalizedThetaVolumeConsumer (l := l) (V := V) (I := I) C3 T e :=
  Real.log_nonneg (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)

#check c3QPilotThetaSum_nonneg
#check c3NormalizedThetaVolumeConsumer_nonneg

end LeanFormal.IUT.XiFPaper.S2771C3QPilotThetaComparisonConsumerActual
end
