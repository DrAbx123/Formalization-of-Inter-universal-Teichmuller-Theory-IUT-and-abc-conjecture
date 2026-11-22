import tmp.sheaf.xif.paper.S2834C3QPilotThetaComparisonDataConsumer
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual
import tmp.sheaf.xif.paper.S2835C3QPilotThetaDataConsumer

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2837C3QPilotThetaDataSummaryConsumer

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

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAO : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAO : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3QPilotThetaData_summary :
    (0 ≤ (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume) ∧
      (0 ≤ (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume) ∧
      ((c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume =
        ∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i) :=
  ⟨C3QPilotThetaData_qPilot_nonneg (l := l) (V := V) (I := I) C3 T e,
    C3QPilotThetaData_theta_nonneg (l := l) (V := V) (I := I) C3 T e,
    C3QPilotThetaData_qPilot_eq_sum (l := l) (V := V) (I := I) C3 T e⟩

#check C3QPilotThetaData_summary

end LeanFormal.IUT.XiFPaper.S2837C3QPilotThetaDataSummaryConsumer
end
