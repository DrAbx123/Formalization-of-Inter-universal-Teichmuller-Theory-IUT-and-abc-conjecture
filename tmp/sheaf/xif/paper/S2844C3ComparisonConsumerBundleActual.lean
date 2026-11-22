import tmp.sheaf.xif.paper.S2843C3ComparisonDataLinkConsumer
import tmp.sheaf.xif.paper.S2834C3QPilotThetaComparisonDataConsumer
import tmp.sheaf.xif.paper.S2835C3QPilotThetaDataConsumer
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2844C3ComparisonConsumerBundleActual

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
open LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2835C3QPilotThetaDataConsumer
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2840C3NormalizedComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2843C3ComparisonDataLinkConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAV : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAV : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


structure C3ComparisonConsumerBundle where
  qPilotVolume : ℝ
  thetaVolume : ℝ
  normalizedLogVolume : ℝ
  qPilotVolume_eq_sum : qPilotVolume =
    (∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i)
  thetaVolume_eq_normalized : thetaVolume = normalizedLogVolume
  qPilotVolume_nonneg : 0 ≤ qPilotVolume
  thetaVolume_nonneg : 0 ≤ thetaVolume
  normalizedLogVolume_nonneg : 0 ≤ normalizedLogVolume

noncomputable def c3ComparisonConsumerBundle :
    C3ComparisonConsumerBundle (l := l) (V := V) (I := I) C3 T e where
  qPilotVolume := (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume
  thetaVolume := (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume
  normalizedLogVolume := (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume
  qPilotVolume_eq_sum := (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume_eq
  thetaVolume_eq_normalized := C3ComparisonData_theta_eq_normalizedLogVolume (l := l) (V := V) (I := I) C3 T e
  qPilotVolume_nonneg := C3QPilotThetaData_qPilot_nonneg (l := l) (V := V) (I := I) C3 T e
  thetaVolume_nonneg := C3QPilotThetaData_theta_nonneg (l := l) (V := V) (I := I) C3 T e
  normalizedLogVolume_nonneg := (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume_nonneg

#check c3ComparisonConsumerBundle

end LeanFormal.IUT.XiFPaper.S2844C3ComparisonConsumerBundleActual
end
