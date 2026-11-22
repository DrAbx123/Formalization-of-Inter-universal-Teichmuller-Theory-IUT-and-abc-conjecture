import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.S2853C3RegionMeasureComparisonDataActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2855C3LatticeRegionLogVolumeSummaryActual

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

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBB : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBB : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3LatticeRegion_logVolume_summary :
    (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (tensorLattice (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i))).toReal = 0 ∧
      (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) ∧
      0 ≤ (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal :=
  ⟨by
    rw [haarLogVolume_of_lt_top]
    · rw [c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3]
      simp
    · rw [c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3]
      exact ENNReal.one_lt_top
  , by
    have hfin := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
    have hge1 := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
    rw [haarLogVolume_of_lt_top hfin]
    rw [ENNReal.toReal_ofReal (Real.log_nonneg hge1)]
  , by
    have hfin := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
    have hge1 := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
    rw [haarLogVolume_of_lt_top hfin]
    rw [ENNReal.toReal_ofReal (Real.log_nonneg hge1)]
    exact Real.log_nonneg hge1⟩

#check C3LatticeRegion_logVolume_summary

end LeanFormal.IUT.XiFPaper.S2855C3LatticeRegionLogVolumeSummaryActual
end
