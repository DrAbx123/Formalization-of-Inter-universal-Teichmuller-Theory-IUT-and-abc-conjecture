import tmp.sheaf.xif.paper.S2877C3MeasureDataRegionLinkActual
import tmp.sheaf.xif.paper.S2876C3MeasureDataLinkActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2878C3MeasureDataEqConsumerActual

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
open LeanFormal.IUT.XiFPaper.S2867C3ComparisonMeasureLogVolumeAllActual
open LeanFormal.IUT.XiFPaper.S2871C3RegionMeasurePosLogConsumerActual
open LeanFormal.IUT.XiFPaper.S2873C3RegionMeasureComparisonLogLinkActual
open LeanFormal.IUT.XiFPaper.S2874C3MeasureLogVolumeDataRegionActual
open LeanFormal.IUT.XiFPaper.S2875C3MeasureLogVolumeRegionEqActual
open LeanFormal.IUT.XiFPaper.S2876C3MeasureDataLinkActual
open LeanFormal.IUT.XiFPaper.S2877C3MeasureDataRegionLinkActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBN : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBN : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3MeasureData_region_measures_eq :
    (c3RegionMeasureComparisonData (l := l) (V := V) (I := I) C3 T e).regionMeasure =
        (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionMeasure ∧
      (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionLogVolume =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :=
  ⟨C3RegionMeasureComparison_data_eq_measureLogData (l := l) (V := V) (I := I) C3 T e,
    (C3MeasureData_region_link (l := l) (V := V) (I := I) C3 T e).2.2⟩

#check C3MeasureData_region_measures_eq

end LeanFormal.IUT.XiFPaper.S2878C3MeasureDataEqConsumerActual
end
