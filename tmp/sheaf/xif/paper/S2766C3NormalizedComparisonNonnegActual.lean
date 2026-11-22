import tmp.sheaf.xif.paper.S2747C3NormalizedLogVolumeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2766C3NormalizedComparisonNonnegActual

open MeasureTheory
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2747C3NormalizedLogVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measZ : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelZ : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem c3NormalizedComparisonRegionLogVolume_nonneg :
    0 ≤ c3NormalizedComparisonRegionLogVolume (l := l) (V := V) (I := I) C3 T e := by
  rw [c3NormalizedRegionLogVolume_eq_log]
  exact Real.log_nonneg (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)

theorem c3NormalizedComparisonRegionLogVolume_eq_realLog :
    c3NormalizedComparisonRegionLogVolume (l := l) (V := V) (I := I) C3 T e =
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :=
  c3NormalizedRegionLogVolume_eq_log (l := l) (V := V) (I := I) C3 T e

#check c3NormalizedComparisonRegionLogVolume_nonneg
end LeanFormal.IUT.XiFPaper.S2766C3NormalizedComparisonNonnegActual
end
