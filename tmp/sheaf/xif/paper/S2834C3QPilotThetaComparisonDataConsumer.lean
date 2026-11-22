import tmp.sheaf.xif.paper.S2832C3RegionScalingUnitSummaryActual
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual
import tmp.sheaf.xif.paper.S2833C3RegionRealLogScalingUnitSummaryActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer

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
open LeanFormal.IUT.XiFPaper.S2832C3RegionScalingUnitSummaryActual
open LeanFormal.IUT.XiFPaper.S2833C3RegionRealLogScalingUnitSummaryActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAN : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAN : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

structure C3QPilotThetaComparisonData where
  qPilotVolume : ℝ
  thetaVolume : ℝ
  qPilotVolume_eq : qPilotVolume =
    (∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i)
  thetaVolume_eq : thetaVolume =
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)
  qPilotVolume_nonneg : 0 ≤ qPilotVolume
  thetaVolume_nonneg : 0 ≤ thetaVolume
  thetaVolume_scale_eq : ∀ u : ℚ_[C3.p]ˣ,
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      thetaVolume + Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ))
  thetaVolume_unit_eq : ∀ w : (PadicInt C3.p)ˣ,
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (unitQHom (p := C3.p) w • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) = thetaVolume

noncomputable def c3QPilotThetaComparisonData :
    C3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e where
  qPilotVolume := ∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i
  thetaVolume := Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)
  qPilotVolume_eq := rfl
  thetaVolume_eq := rfl
  qPilotVolume_nonneg := Finset.sum_nonneg (fun i _ =>
    C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e i)
  thetaVolume_nonneg := Real.log_nonneg
    (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)
  thetaVolume_scale_eq := by
    intro u
    exact (C3Region_realLog_scaling_and_unit_summary (l := l) (V := V) (I := I) C3 T e u (1 : (PadicInt C3.p)ˣ)).1
  thetaVolume_unit_eq := by
    intro w
    have hmeas : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (unitQHom (p := C3.p) w • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) =
        c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :=
      C3Region_scaling_and_unit_summary (l := l) (V := V) (I := I) C3 T e (1 : ℚ_[C3.p]ˣ) w |>.2
    rw [hmeas]

#check c3QPilotThetaComparisonData
end LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer
end
