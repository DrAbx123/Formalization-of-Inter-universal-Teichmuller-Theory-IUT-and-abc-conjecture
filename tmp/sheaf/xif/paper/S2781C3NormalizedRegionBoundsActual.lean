import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2785C3NormalizedRegionMeasurePosActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2781C3NormalizedRegionBoundsActual

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

local instance measB : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelB : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

structure C3NormalizedRegionBounds where
  lt_top : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤
  ne_zero : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ≠ 0
  one_le_toReal : 1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal
  zero_lt_toReal : 0 < (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal

noncomputable def c3NormalizedRegionBounds :
    C3NormalizedRegionBounds (l := l) (V := V) (I := I) C3 T e where
  lt_top := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  ne_zero := c3NormalizedRegion_measure_ne_zero (l := l) (V := V) (I := I) C3 T e
  one_le_toReal := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
  zero_lt_toReal := lt_of_lt_of_le zero_lt_one
    (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)

#check c3NormalizedRegionBounds
end LeanFormal.IUT.XiFPaper.S2781C3NormalizedRegionBoundsActual
end
