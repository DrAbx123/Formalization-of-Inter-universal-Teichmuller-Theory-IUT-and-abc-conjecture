import tmp.sheaf.xif.paper.S2863C3MeasureLogVolumeFullSummaryActual
import tmp.sheaf.xif.paper.S2864C3MeasureLogVolumeBoundsConsumerActual
import tmp.sheaf.xif.paper.S2853C3RegionMeasureComparisonDataActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2866C3RegionMeasureComparisonLatticeOfRealActual

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
open LeanFormal.IUT.XiFPaper.S2863C3MeasureLogVolumeFullSummaryActual
open LeanFormal.IUT.XiFPaper.S2864C3MeasureLogVolumeBoundsConsumerActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBG : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBG : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3RegionMeasureComparison_lattice_ofReal_summary :
    (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).latticeMeasure = 1 ∧
      (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).latticeMeasure ≤
        (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).regionMeasure ∧
      (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).regionMeasure =
        ENNReal.ofReal ((c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).regionMeasure).toReal :=
  ⟨(c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).latticeMeasure_eq_one,
    (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).lattice_le_region,
    (ENNReal.ofReal_toReal (ne_of_lt (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).region_lt_top)).symm⟩

#check C3RegionMeasureComparison_lattice_ofReal_summary

end LeanFormal.IUT.XiFPaper.S2866C3RegionMeasureComparisonLatticeOfRealActual
end
