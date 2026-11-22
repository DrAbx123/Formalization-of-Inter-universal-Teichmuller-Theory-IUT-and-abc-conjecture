import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2785C3NormalizedRegionMeasurePosActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2768C3NormalizedRegionConsumerActual

open MeasureTheory
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2785C3NormalizedRegionMeasurePosActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measV : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelV : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

structure C3NormalizedRegionData
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex] where
  region : Set (C3LogShellTensorBlock C3)
  measure_lt_top : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region < ⊤
  measure_ne_zero : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region ≠ 0
  one_le_toReal : 1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region).toReal

noncomputable def c3NormalizedRegionData : C3NormalizedRegionData (l := l) (V := V) (I := I) C3 T e where
  region := C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e
  measure_lt_top := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  measure_ne_zero := c3NormalizedRegion_measure_ne_zero (l := l) (V := V) (I := I) C3 T e
  one_le_toReal := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e

theorem c3NormalizedRegionData_one_le :
    1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (c3NormalizedRegionData (l := l) (V := V) (I := I) C3 T e).region).toReal := by
  rw [show (c3NormalizedRegionData (l := l) (V := V) (I := I) C3 T e).region =
      C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e from rfl]
  exact c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e

#check c3NormalizedRegionData_one_le
end LeanFormal.IUT.XiFPaper.S2768C3NormalizedRegionConsumerActual
end
