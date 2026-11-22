import tmp.sheaf.xif.paper.S2754C3RegionAllHaarFiniteActual
import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2805C3RegionHaarSummaryActual

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
open LeanFormal.IUT.XiFPaper.S2754C3RegionAllHaarFiniteActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measX2 : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelX2 : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


structure C3RegionHaarSummary where
  actual_lt_top : actualC3LogShellTensorHaar C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤
  normalized_lt_top : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤
  normalized_one_le_toReal : 1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal
  normalized_logVolume_nonneg : 0 ≤ (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal

theorem c3NormalizedRegion_haarLogVolume_nonneg :
    0 ≤ (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal := by
  have hfin := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  have hge1 := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
  rw [haarLogVolume_of_lt_top hfin]
  rw [ENNReal.toReal_ofReal (Real.log_nonneg hge1)]
  exact Real.log_nonneg hge1

noncomputable def c3RegionHaarSummary : C3RegionHaarSummary (l := l) (V := V) (I := I) C3 T e where
  actual_lt_top := C3PerPlaceUpdateRegionAll_haar_finite (l := l) (V := V) (I := I) C3 T e
  normalized_lt_top := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  normalized_one_le_toReal := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
  normalized_logVolume_nonneg := c3NormalizedRegion_haarLogVolume_nonneg (l := l) (V := V) (I := I) C3 T e

#check c3RegionHaarSummary

end LeanFormal.IUT.XiFPaper.S2805C3RegionHaarSummaryActual
end
