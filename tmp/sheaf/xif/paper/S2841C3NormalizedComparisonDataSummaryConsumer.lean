import tmp.sheaf.xif.paper.S2840C3NormalizedComparisonDataConsumer

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2841C3NormalizedComparisonDataSummaryConsumer

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
open LeanFormal.IUT.XiFPaper.S2840C3NormalizedComparisonDataConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAS : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAS : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3NormalizedComparisonData_summary :
    (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).region =
        C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e ∧
      (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) ∧
      0 ≤ (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume ∧
      1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal :=
  ⟨rfl, rfl,
    (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume_nonneg,
    (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).one_le_toReal⟩

#check C3NormalizedComparisonData_summary
end LeanFormal.IUT.XiFPaper.S2841C3NormalizedComparisonDataSummaryConsumer
end
