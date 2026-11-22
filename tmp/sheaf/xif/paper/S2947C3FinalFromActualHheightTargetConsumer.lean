import tmp.sheaf.xif.paper.S2946C3TwoShiftBridgeActual
import tmp.sheaf.xif.paper.S2936C3IUTIILogVolumeFinalSummaryActual
import tmp.sheaf.xif.paper.S2934C3NormalizedHheightInterfaceActual
import tmp.sheaf.xif.paper.S2931C3ComparisonFinalSummaryActual
import tmp.sheaf.xif.paper.S2910C3NormalizedHvolConsumerActual
import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.S2727V2RegionTarget
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2947C3FinalFromActualHheightTargetConsumer

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
open LeanFormal.IUT.XiFPaper.S2774C3NormalizedThetaVolumeNonnegActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2910C3NormalizedHvolConsumerActual
open LeanFormal.IUT.XiFPaper.S2931C3ComparisonFinalSummaryActual
open LeanFormal.IUT.XiFPaper.S2934C3NormalizedHheightInterfaceActual
open LeanFormal.IUT.XiFPaper.S2936C3IUTIILogVolumeFinalSummaryActual
open LeanFormal.IUT.XiFPaper.S2944C3ActualAllRegionVolumeActual
open LeanFormal.IUT.XiFPaper.S2945C3RegionChangeShiftActual
open LeanFormal.IUT.XiFPaper.S2946C3TwoShiftBridgeActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measDJ : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelDJ : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3Final_from_actualHheightTarget
    {height eps C : ℝ}
    (h : hheightTarget (l := l) (V := V) (I := I) C3 T e height eps C) :
    c3NormalizedHheightTarget (l := l) (V := V) (I := I) C3 T e height eps
        (C + (1 + eps) *
          (c3NormalizationShift (l := l) (V := V) (I := I) C3 T e +
            c3RegionChangeShift (l := l) (V := V) (I := I) C3 T e))
      ∧ c3NormalizedHvolTarget (l := l) (V := V) (I := I) C3 T e
      ∧ c3NormalizedThetaVolume C3 T e =
          c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e :=
  ⟨c3NormalizedHheightTarget_of_hheightTarget_twoShift (l := l) (V := V) (I := I) C3 T e h,
    c3NormalizedHvolTarget_holds (l := l) (V := V) (I := I) C3 T e,
    (C3ComparisonFinal_summary (l := l) (V := V) (I := I) C3 T e (1 : ℚ_[C3.p]ˣ) (1 : (PadicInt C3.p)ˣ)).1⟩

#check C3Final_from_actualHheightTarget
end LeanFormal.IUT.XiFPaper.S2947C3FinalFromActualHheightTargetConsumer
end
