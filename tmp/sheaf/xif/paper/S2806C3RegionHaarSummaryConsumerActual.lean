import tmp.sheaf.xif.paper.S2754C3RegionAllHaarFiniteActual
import tmp.sheaf.xif.paper.S2805C3RegionHaarSummaryActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2806C3RegionHaarSummaryConsumerActual

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
open LeanFormal.IUT.XiFPaper.S2805C3RegionHaarSummaryActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measX2 : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelX2 : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3RegionHaarSummary_one_le :
    1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal :=
  (c3RegionHaarSummary (l := l) (V := V) (I := I) C3 T e).normalized_one_le_toReal

theorem C3RegionHaarSummary_logVolume_nonneg :
    0 ≤ (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal :=
  (c3RegionHaarSummary (l := l) (V := V) (I := I) C3 T e).normalized_logVolume_nonneg

#check C3RegionHaarSummary_one_le

end LeanFormal.IUT.XiFPaper.S2806C3RegionHaarSummaryConsumerActual
end
