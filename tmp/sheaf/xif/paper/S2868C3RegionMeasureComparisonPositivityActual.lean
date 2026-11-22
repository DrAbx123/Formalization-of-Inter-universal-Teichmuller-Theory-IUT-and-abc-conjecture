import tmp.sheaf.xif.paper.S2865C3MeasureLogVolumeSummary2Actual
import tmp.sheaf.xif.paper.S2866C3RegionMeasureComparisonLatticeOfRealActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2868C3RegionMeasureComparisonPositivityActual

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
open LeanFormal.IUT.XiFPaper.S2865C3MeasureLogVolumeSummary2Actual
open LeanFormal.IUT.XiFPaper.S2866C3RegionMeasureComparisonLatticeOfRealActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBH : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBH : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3RegionMeasureComparison_region_ne_zero :
    (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).regionMeasure ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one
    (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).region_ge_one)

theorem C3RegionMeasureComparison_region_pos :
    0 < (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).regionMeasure :=
  lt_of_lt_of_le zero_lt_one
    (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).region_ge_one

#check C3RegionMeasureComparison_region_pos

end LeanFormal.IUT.XiFPaper.S2868C3RegionMeasureComparisonPositivityActual
end
