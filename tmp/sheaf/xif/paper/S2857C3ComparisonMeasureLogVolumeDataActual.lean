import tmp.sheaf.xif.paper.S2855C3LatticeRegionLogVolumeSummaryActual
import tmp.sheaf.xif.paper.S2856C3RegionMeasureComparisonOfRealActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2857C3ComparisonMeasureLogVolumeDataActual

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
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2853C3RegionMeasureComparisonDataActual
open LeanFormal.IUT.XiFPaper.S2855C3LatticeRegionLogVolumeSummaryActual
open LeanFormal.IUT.XiFPaper.S2856C3RegionMeasureComparisonOfRealActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBC : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBC : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


structure C3ComparisonMeasureLogVolumeData
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex] where
  regionMeasure : ENNReal
  regionLogVolume : ℝ
  regionMeasure_lt_top : regionMeasure < ⊤
  regionMeasure_ge_one : 1 ≤ regionMeasure
  regionLogVolume_eq : regionLogVolume = Real.log (regionMeasure.toReal)
  regionLogVolume_nonneg : 0 ≤ regionLogVolume

noncomputable def c3ComparisonMeasureLogVolumeData :
    C3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e where
  regionMeasure := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
  regionLogVolume := (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal
  regionMeasure_lt_top := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  regionMeasure_ge_one := by
    rw [← c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3]
    exact measure_mono (tensorLattice_subset_C3RegionAll (l := l) (V := V) (I := I) C3 T e
      (C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e))
  regionLogVolume_eq := (C3LatticeRegion_logVolume_summary (l := l) (V := V) (I := I) C3 T e).2.1
  regionLogVolume_nonneg := (C3LatticeRegion_logVolume_summary (l := l) (V := V) (I := I) C3 T e).2.2

#check c3ComparisonMeasureLogVolumeData

end LeanFormal.IUT.XiFPaper.S2857C3ComparisonMeasureLogVolumeDataActual
end
