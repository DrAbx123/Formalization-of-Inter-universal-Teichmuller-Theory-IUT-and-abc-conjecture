import tmp.sheaf.xif.paper.S2760C3NormalizedQPilotLogVolumeActual
import tmp.sheaf.xif.paper.S2726C3PerPlaceUpdateRegionActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2763C3QPilotLocalLogSumActual

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
open LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2760C3NormalizedQPilotLogVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

theorem c3NormalizedQPilotLogVolume_eq_localLogMagnitude_sum :
    c3NormalizedQPilotLogVolume (l := l) (V := V) (I := I) C3 T e =
      ∑ i, localLogMagnitude (badPlaceQCandidate (nativePlaceSelection T) (e i)) := by
  unfold c3NormalizedQPilotLogVolume C3PerPlaceUpdateRho
  simp [S2726C3PerPlaceUpdateRho]

#check c3NormalizedQPilotLogVolume_eq_localLogMagnitude_sum
end LeanFormal.IUT.XiFPaper.S2763C3QPilotLocalLogSumActual
end
