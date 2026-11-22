import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2788C3ComparisonDataConsumerNoDepsActual

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

local instance measI : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelI : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3ComparisonData_qPilot_nonneg :
    0 ≤ (∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i) :=
  Finset.sum_nonneg (fun i _ =>
    C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e i)

theorem C3ComparisonData_thetaLog_nonneg :
    0 ≤ Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :=
  Real.log_nonneg (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)

theorem C3ComparisonData_region_finite :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤ :=
  c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e

theorem C3ComparisonData_region_one_le :
    (1 : ENNReal) ≤ c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) := by
  rw [← c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3]
  exact measure_mono (tensorLattice_subset_C3RegionAll (l := l) (V := V) (I := I) C3 T e
    (C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e))

#check C3ComparisonData_region_one_le
end LeanFormal.IUT.XiFPaper.S2788C3ComparisonDataConsumerNoDepsActual
end
