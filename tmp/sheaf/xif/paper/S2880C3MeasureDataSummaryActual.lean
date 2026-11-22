import tmp.sheaf.xif.paper.S2878C3MeasureDataEqConsumerActual
import tmp.sheaf.xif.paper.S2879C3MeasureDataLogVolumeSummaryActual
import tmp.sheaf.xif.paper.S2874C3MeasureLogVolumeDataRegionActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2880C3MeasureDataSummaryActual

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
open LeanFormal.IUT.XiFPaper.S2878C3MeasureDataEqConsumerActual
open LeanFormal.IUT.XiFPaper.S2879C3MeasureDataLogVolumeSummaryActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBO : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBO : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3MeasureData_summary :
    (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionMeasure =
        c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ∧
      (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionLogVolume =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) ∧
      0 ≤ (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionLogVolume ∧
      (1 : ENNReal) ≤ (c3ComparisonMeasureLogVolumeData (l := l) (V := V) (I := I) C3 T e).regionMeasure :=
  ⟨C3ComparisonMeasureLogVolume_data_regionMeasure (l := l) (V := V) (I := I) C3 T e,
    (C3MeasureData_logVolume_summary (l := l) (V := V) (I := I) C3 T e).1,
    (C3MeasureData_logVolume_summary (l := l) (V := V) (I := I) C3 T e).2.1,
    (C3MeasureData_logVolume_summary (l := l) (V := V) (I := I) C3 T e).2.2⟩

#check C3MeasureData_summary

end LeanFormal.IUT.XiFPaper.S2880C3MeasureDataSummaryActual
end
