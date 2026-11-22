import tmp.sheaf.xif.paper.S2845C3ComparisonBundleConsumerActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2846C3ComparisonBundleRealLogConsumer

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
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2840C3NormalizedComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2843C3ComparisonDataLinkConsumer
open LeanFormal.IUT.XiFPaper.S2844C3ComparisonConsumerBundleActual
open LeanFormal.IUT.XiFPaper.S2845C3ComparisonBundleConsumerActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAW : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAW : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3ComparisonBundle_theta_eq_realLog :
    (c3ComparisonConsumerBundle (l := l) (V := V) (I := I) C3 T e).thetaVolume =
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) := by
  rw [(c3ComparisonConsumerBundle (l := l) (V := V) (I := I) C3 T e).thetaVolume_eq_normalized]
  exact (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume_eq

theorem C3ComparisonBundle_qPilot_eq_sum_and_theta_eq_realLog :
    (c3ComparisonConsumerBundle (l := l) (V := V) (I := I) C3 T e).qPilotVolume =
        (∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i) ∧
      (c3ComparisonConsumerBundle (l := l) (V := V) (I := I) C3 T e).thetaVolume =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :=
  ⟨C3ComparisonBundle_qPilot_eq_sum (l := l) (V := V) (I := I) C3 T e,
    C3ComparisonBundle_theta_eq_realLog (l := l) (V := V) (I := I) C3 T e⟩

#check C3ComparisonBundle_qPilot_eq_sum_and_theta_eq_realLog
end LeanFormal.IUT.XiFPaper.S2846C3ComparisonBundleRealLogConsumer
end
