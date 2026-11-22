import tmp.sheaf.xif.paper.S2861C3LogVolumeLatticeRegionConsumerActual
import tmp.sheaf.xif.paper.S2862C3MeasureLogVolumeRegionConsumerActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2863C3MeasureLogVolumeFullSummaryActual

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
open LeanFormal.IUT.XiFPaper.S2857C3ComparisonMeasureLogVolumeDataActual
open LeanFormal.IUT.XiFPaper.S2859C3LatticeRegionComparisonConsumerActual
open LeanFormal.IUT.XiFPaper.S2860C3ComparisonMeasureLogVolumeOfRealConsumerActual
open LeanFormal.IUT.XiFPaper.S2861C3LogVolumeLatticeRegionConsumerActual
open LeanFormal.IUT.XiFPaper.S2862C3MeasureLogVolumeRegionConsumerActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBF : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBF : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3MeasureLogVolume_full_summary :
    (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (tensorLattice (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i))).toReal = 0 ∧
      0 ≤ (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal ∧
      (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionLogVolume =
        Real.log ((c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionMeasure).toReal ∧
      (1 : ENNReal) ≤ (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionMeasure :=
  ⟨(C3LogVolume_lattice_region_summary (l := l) (V := V) (I := I) C3 T e).1,
    (C3LogVolume_lattice_region_summary (l := l) (V := V) (I := I) C3 T e).2.1,
    (C3MeasureLogVolume_region_summary (l := l) (V := V) (I := I) C3 T e).1,
    (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionMeasure_ge_one⟩

#check C3MeasureLogVolume_full_summary

end LeanFormal.IUT.XiFPaper.S2863C3MeasureLogVolumeFullSummaryActual
end
