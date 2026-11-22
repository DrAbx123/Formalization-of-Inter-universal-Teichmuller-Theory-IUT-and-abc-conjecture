import tmp.sheaf.xif.paper.S2834C3QPilotThetaComparisonDataConsumer
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import tmp.sheaf.xif.paper.S2833C3RegionRealLogScalingUnitSummaryActual
import tmp.sheaf.xif.paper.S2831C3RegionUnitInvarianceSummaryActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2835C3QPilotThetaDataConsumer

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
open LeanFormal.IUT.XiFPaper.S2833C3RegionRealLogScalingUnitSummaryActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

theorem C3QPilotThetaData_qPilot_nonneg :
    0 ≤ (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume :=
  (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume_nonneg

theorem C3QPilotThetaData_theta_nonneg :
    0 ≤ (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume :=
  (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume_nonneg

theorem C3QPilotThetaData_qPilot_eq_sum :
    (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume =
      ∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i :=
  (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).qPilotVolume_eq

theorem C3QPilotThetaData_theta_scale (u : ℚ_[C3.p]ˣ) :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((fun x : C3LogShellTensorBlock C3 => ((u : ℚ_[C3.p]) • x)) ''
        C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume +
        Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ)) := by
  have h := (C3Region_realLog_scaling_and_unit_summary (l := l) (V := V) (I := I) C3 T e u (1 : (PadicInt C3.p)ˣ)).1
  simpa [c3QPilotThetaComparisonData] using h

#check C3QPilotThetaData_theta_scale
end LeanFormal.IUT.XiFPaper.S2835C3QPilotThetaDataConsumer
end
