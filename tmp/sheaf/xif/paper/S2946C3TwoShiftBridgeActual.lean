import tmp.sheaf.xif.paper.S2944C3ActualAllRegionVolumeActual
import tmp.sheaf.xif.paper.S2945C3RegionChangeShiftActual
import tmp.sheaf.xif.paper.S2934C3NormalizedHheightInterfaceActual
import tmp.sheaf.xif.paper.S2937C3HheightNormalizationBridgeConsumer
import tmp.sheaf.xif.paper.S2941C3HheightShiftBridgeActual
import tmp.sheaf.xif.paper.S2943C3NormalizationDeltaActual
import tmp.sheaf.xif.paper.S2727V2RegionTarget
import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2946C3TwoShiftBridgeActual

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
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2934C3NormalizedHheightInterfaceActual
open LeanFormal.IUT.XiFPaper.S2937C3HheightNormalizationBridgeConsumer
open LeanFormal.IUT.XiFPaper.S2941C3HheightShiftBridgeActual
open LeanFormal.IUT.XiFPaper.S2943C3NormalizationDeltaActual
open LeanFormal.IUT.XiFPaper.S2944C3ActualAllRegionVolumeActual
open LeanFormal.IUT.XiFPaper.S2945C3RegionChangeShiftActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measDI : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelDI : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem c3ActualComparisonRegionVolume_eq_add_shift :
    c3ActualComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
      c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e +
        c3NormalizationShift (l := l) (V := V) (I := I) C3 T e := by
  unfold c3NormalizationShift
  ring

theorem c3NormalizedHheightTarget_of_hheightTarget_twoShift
    {height eps C : ℝ}
    (h : hheightTarget (l := l) (V := V) (I := I) C3 T e height eps C) :
    c3NormalizedHheightTarget (l := l) (V := V) (I := I) C3 T e height eps
      (C + (1 + eps) *
        (c3NormalizationShift (l := l) (V := V) (I := I) C3 T e +
          c3RegionChangeShift (l := l) (V := V) (I := I) C3 T e)) := by
  unfold hheightTarget at h
  unfold c3NormalizedHheightTarget
  rw [comparisonRegionVolume_eq_actualVolume_add_regionShift (l := l) (V := V) (I := I) C3 T e] at h
  rw [c3ActualComparisonRegionVolume_eq_add_shift (l := l) (V := V) (I := I) C3 T e] at h
  linarith

theorem hheightTarget_of_c3NormalizedHheightTarget_twoShift
    {height eps C : ℝ}
    (h : c3NormalizedHheightTarget (l := l) (V := V) (I := I) C3 T e height eps C) :
    hheightTarget (l := l) (V := V) (I := I) C3 T e height eps
      (C - (1 + eps) *
        (c3NormalizationShift (l := l) (V := V) (I := I) C3 T e +
          c3RegionChangeShift (l := l) (V := V) (I := I) C3 T e)) := by
  unfold hheightTarget
  unfold c3NormalizedHheightTarget at h
  rw [comparisonRegionVolume_eq_actualVolume_add_regionShift (l := l) (V := V) (I := I) C3 T e]
  rw [c3ActualComparisonRegionVolume_eq_add_shift (l := l) (V := V) (I := I) C3 T e]
  linarith

#check c3NormalizedHheightTarget_of_hheightTarget_twoShift
#check hheightTarget_of_c3NormalizedHheightTarget_twoShift
end LeanFormal.IUT.XiFPaper.S2946C3TwoShiftBridgeActual
end
