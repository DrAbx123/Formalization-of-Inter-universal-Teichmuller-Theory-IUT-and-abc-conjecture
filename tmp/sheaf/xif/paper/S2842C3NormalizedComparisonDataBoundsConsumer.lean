import tmp.sheaf.xif.paper.S2841C3NormalizedComparisonDataSummaryConsumer

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2842C3NormalizedComparisonDataBoundsConsumer

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
open LeanFormal.IUT.XiFPaper.S2841C3NormalizedComparisonDataSummaryConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAT : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAT : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3NormalizedComparisonData_bounds :
    0 ≤ (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume ∧
      1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).region).toReal :=
  ⟨(C3NormalizedComparisonData_summary (l := l) (V := V) (I := I) C3 T e).2.2.1, by
    rw [show (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).region
        = C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e from rfl]
    exact (C3NormalizedComparisonData_summary (l := l) (V := V) (I := I) C3 T e).2.2.2⟩

#check C3NormalizedComparisonData_bounds
end LeanFormal.IUT.XiFPaper.S2842C3NormalizedComparisonDataBoundsConsumer
end
