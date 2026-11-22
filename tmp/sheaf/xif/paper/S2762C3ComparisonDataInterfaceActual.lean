import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2758C3NormalizedRegionPosActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2762C3ComparisonDataInterfaceActual

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
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2758C3NormalizedRegionPosActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measX : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelX : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


structure C3ComparisonRegionData where
  region : Set (C3LogShellTensorBlock C3)
  logVolume : ℝ
  region_eq : region = C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e
  logVolume_eq : logVolume = Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region).toReal)
  measure_lt_top : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region < ⊤
  measure_ne_zero : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region ≠ 0
  one_le_toReal : 1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 region).toReal

noncomputable def c3ComparisonRegionData : C3ComparisonRegionData (l := l) (V := V) (I := I) C3 T e where
  region := C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e
  logVolume := Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)
  region_eq := rfl
  logVolume_eq := rfl
  measure_lt_top := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  measure_ne_zero := c3NormalizedRegion_measure_ne_zero (l := l) (V := V) (I := I) C3 T e
  one_le_toReal := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e

#check c3ComparisonRegionData
end LeanFormal.IUT.XiFPaper.S2762C3ComparisonDataInterfaceActual
end
