import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
import tmp.sheaf.xif.paper.S2913C3ComparisonRegionVolumeHvolEqConsumer
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2934C3NormalizedHheightInterfaceActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2774C3NormalizedThetaVolumeNonnegActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
open LeanFormal.IUT.XiFPaper.S2913C3ComparisonRegionVolumeHvolEqConsumer
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

/-- Normalized analogue of S2727V2 hheightTarget: arithmetic height bounded by (1+eps)*comparison volume + C. -/
def c3NormalizedHheightTarget (height eps C : ℝ) : Prop :=
  height ≤ (1 + eps) * c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + C

theorem c3NormalizedHheightTarget_iff (height eps C : ℝ) :
    c3NormalizedHheightTarget (l := l) (V := V) (I := I) C3 T e height eps C ↔
      height ≤ (1 + eps) * c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + C :=
  Iff.rfl

theorem c3NormalizedHheightTarget_holds_bound (eps C : ℝ) :
    c3NormalizedHheightTarget (l := l) (V := V) (I := I) C3 T e
      ((1 + eps) * c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + C) eps C :=
  le_rfl

theorem c3NormalizedHheightTarget_of_le {height eps C : ℝ}
    (h : height ≤ (1 + eps) * c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + C) :
    c3NormalizedHheightTarget (l := l) (V := V) (I := I) C3 T e height eps C :=
  h

#check c3NormalizedHheightTarget_iff
end LeanFormal.IUT.XiFPaper.S2934C3NormalizedHheightInterfaceActual
end
