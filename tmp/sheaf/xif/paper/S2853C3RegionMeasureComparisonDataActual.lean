import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2853C3RegionMeasureComparisonDataActual

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

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBA : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBA : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


structure C3RegionMeasureComparisonData
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex] where
  latticeMeasure : ENNReal
  regionMeasure : ENNReal
  latticeMeasure_eq_one : latticeMeasure = 1
  lattice_le_region : latticeMeasure ≤ regionMeasure
  region_ge_one : 1 ≤ regionMeasure
  region_lt_top : regionMeasure < ⊤

noncomputable def c3RegionMeasureComparisonData :
    C3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e where
  latticeMeasure := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (tensorLattice (p := C3.p)
      (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i))
  regionMeasure := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
  latticeMeasure_eq_one := c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3
  lattice_le_region := measure_mono (tensorLattice_subset_C3RegionAll (l := l) (V := V) (I := I) C3 T e
    (C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e))
  region_ge_one := by
    rw [← c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3]
    exact measure_mono (tensorLattice_subset_C3RegionAll (l := l) (V := V) (I := I) C3 T e
      (C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e))
  region_lt_top := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e

#check c3RegionMeasureComparisonData

end LeanFormal.IUT.XiFPaper.S2853C3RegionMeasureComparisonDataActual
end
