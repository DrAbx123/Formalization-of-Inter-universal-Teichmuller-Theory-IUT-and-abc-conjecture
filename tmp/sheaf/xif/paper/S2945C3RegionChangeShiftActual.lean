import tmp.sheaf.xif.paper.S2944C3ActualAllRegionVolumeActual
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
namespace LeanFormal.IUT.XiFPaper.S2945C3RegionChangeShiftActual

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
open LeanFormal.IUT.XiFPaper.S2943C3NormalizationDeltaActual
open LeanFormal.IUT.XiFPaper.S2944C3ActualAllRegionVolumeActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measDH : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelDH : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Region-change part of the total comparison-volume bridge: S2727V2's old
support≤1 region versus the all-coordinates region, both actual-Haar. -/
noncomputable def c3RegionChangeShift : ℝ :=
  comparisonRegionVolume (l := l) (V := V) (I := I) C3 T e -
    c3ActualComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e

theorem comparisonRegionVolume_eq_actualVolume_add_regionShift :
    comparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
      c3ActualComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e +
        c3RegionChangeShift (l := l) (V := V) (I := I) C3 T e := by
  unfold c3RegionChangeShift
  ring

theorem c3NormalizationDelta_eq_shift_add_regionShift :
    c3NormalizationDelta (l := l) (V := V) (I := I) C3 T e =
      c3NormalizationShift (l := l) (V := V) (I := I) C3 T e +
        c3RegionChangeShift (l := l) (V := V) (I := I) C3 T e := by
  unfold c3NormalizationDelta c3RegionChangeShift c3NormalizationShift
  ring

#check c3NormalizationDelta_eq_shift_add_regionShift
end LeanFormal.IUT.XiFPaper.S2945C3RegionChangeShiftActual
end
