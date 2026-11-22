import tmp.sheaf.xif.paper.S2760C3NormalizedQPilotLogVolumeActual
import tmp.sheaf.xif.paper.S2761C3NormalizedThetaPilotLogVolumeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2765C3QPilotThetaComparisonActual

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
open LeanFormal.IUT.XiFPaper.S2760C3NormalizedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2761C3NormalizedThetaPilotLogVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

structure C3QPilotThetaPilotComparison where
  qPilotLogVolume : ℝ
  thetaPilotLogVolume : ℝ
  qPilotLogVolume_eq : qPilotLogVolume =
    c3NormalizedQPilotLogVolume (l := l) (V := V) (I := I) C3 T e
  thetaPilotLogVolume_eq : thetaPilotLogVolume =
    c3NormalizedThetaPilotLogVolume (l := l) (V := V) (I := I) C3 T e
  qPilotLogVolume_nonneg : 0 ≤ qPilotLogVolume
  thetaPilotLogVolume_nonneg : 0 ≤ thetaPilotLogVolume

noncomputable def c3QPilotThetaPilotComparison :
    C3QPilotThetaPilotComparison (l := l) (V := V) (I := I) C3 T e where
  qPilotLogVolume := c3NormalizedQPilotLogVolume (l := l) (V := V) (I := I) C3 T e
  thetaPilotLogVolume := c3NormalizedThetaPilotLogVolume (l := l) (V := V) (I := I) C3 T e
  qPilotLogVolume_eq := rfl
  thetaPilotLogVolume_eq := rfl
  qPilotLogVolume_nonneg := c3NormalizedQPilotLogVolume_nonneg (l := l) (V := V) (I := I) C3 T e
  thetaPilotLogVolume_nonneg := c3NormalizedThetaPilotLogVolume_nonneg (l := l) (V := V) (I := I) C3 T e

#check c3QPilotThetaPilotComparison
end LeanFormal.IUT.XiFPaper.S2765C3QPilotThetaComparisonActual
end
