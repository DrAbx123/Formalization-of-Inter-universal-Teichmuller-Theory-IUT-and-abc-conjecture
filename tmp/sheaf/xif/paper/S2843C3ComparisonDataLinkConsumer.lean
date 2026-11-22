import tmp.sheaf.xif.paper.S2834C3QPilotThetaComparisonDataConsumer
import tmp.sheaf.xif.paper.S2840C3NormalizedComparisonDataConsumer
import tmp.sheaf.xif.paper.S2835C3QPilotThetaDataConsumer

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2843C3ComparisonDataLinkConsumer

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
open LeanFormal.IUT.XiFPaper.S2835C3QPilotThetaDataConsumer
open LeanFormal.IUT.XiFPaper.S2840C3NormalizedComparisonDataConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAU : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAU : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3ComparisonData_theta_eq_normalizedLogVolume :
    (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume =
      (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume := by
  simp [c3QPilotThetaComparisonData, c3NormalizedComparisonData]

theorem C3ComparisonData_qPilot_eq_sum :
    (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume =
      ∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i :=
  (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume_eq

theorem C3ComparisonData_theta_nonneg_and_logVolume_eq :
    0 ≤ (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume ∧
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume =
        (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume :=
  ⟨C3QPilotThetaData_theta_nonneg (l := l) (V := V) (I := I) C3 T e,
    C3ComparisonData_theta_eq_normalizedLogVolume (l := l) (V := V) (I := I) C3 T e⟩

#check C3ComparisonData_theta_eq_normalizedLogVolume
#check C3ComparisonData_qPilot_eq_sum
#check C3ComparisonData_theta_nonneg_and_logVolume_eq
end LeanFormal.IUT.XiFPaper.S2843C3ComparisonDataLinkConsumer
end
