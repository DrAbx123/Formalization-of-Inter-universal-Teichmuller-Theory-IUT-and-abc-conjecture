import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2840C3NormalizedComparisonDataConsumer

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

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAR : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAR : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance smulAR : SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩


structure C3NormalizedComparisonData
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex] where
  region : Set (C3LogShellTensorBlock C3)
  logVolume : ℝ
  logVolume_eq : logVolume = Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region).toReal)
  logVolume_nonneg : 0 ≤ logVolume
  measure_lt_top : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region < ⊤
  measure_ne_zero : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region ≠ 0
  one_le_toReal : 1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region).toReal

noncomputable def c3NormalizedComparisonData :
    C3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e where
  region := C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e
  logVolume := Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)
  logVolume_eq := rfl
  logVolume_nonneg := Real.log_nonneg (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)
  measure_lt_top := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  measure_ne_zero := by
    have hne : (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one
        (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e))
    exact (ENNReal.toReal_ne_zero.mp hne).1
  one_le_toReal := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e

#check c3NormalizedComparisonData

end LeanFormal.IUT.XiFPaper.S2840C3NormalizedComparisonDataConsumer
end
