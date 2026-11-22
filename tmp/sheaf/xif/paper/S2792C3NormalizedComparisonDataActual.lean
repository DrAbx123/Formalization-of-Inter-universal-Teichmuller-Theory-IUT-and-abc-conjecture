import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2792C3NormalizedComparisonDataActual

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

local instance measN : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelN : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


noncomputable def c3NormalizedComparisonLogVolume : ℝ :=
  Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)

structure C3NormalizedComparisonData where
  logVolume : ℝ
  logVolume_eq : logVolume = c3NormalizedComparisonLogVolume (l := l) (V := V) (I := I) C3 T e
  logVolume_nonneg : 0 ≤ logVolume
  region_lt_top : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤
  region_ne_zero : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ≠ 0

theorem c3NormalizedComparisonLogVolume_nonneg :
    0 ≤ c3NormalizedComparisonLogVolume (l := l) (V := V) (I := I) C3 T e :=
  Real.log_nonneg (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)

noncomputable def c3NormalizedComparisonData :
    C3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e where
  logVolume := c3NormalizedComparisonLogVolume (l := l) (V := V) (I := I) C3 T e
  logVolume_eq := rfl
  logVolume_nonneg := c3NormalizedComparisonLogVolume_nonneg (l := l) (V := V) (I := I) C3 T e
  region_lt_top := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  region_ne_zero := by
    have hne : (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one
        (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e))
    exact (ENNReal.toReal_ne_zero.mp hne).1

#check c3NormalizedComparisonData

end LeanFormal.IUT.XiFPaper.S2792C3NormalizedComparisonDataActual
end
