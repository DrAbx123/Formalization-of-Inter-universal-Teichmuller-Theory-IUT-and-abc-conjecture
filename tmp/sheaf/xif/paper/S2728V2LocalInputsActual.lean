import tmp.sheaf.xif.paper.S2727V2RegionTarget
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2728V2LocalInputsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

/-- Actual local degree at a tensor place. -/
noncomputable def S2728LocalDegree (i : C3.tensorIndex) : ℕ :=
  Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i)

theorem S2728LocalDegree_pos (i : C3.tensorIndex) :
    0 < S2728LocalDegree C3 i :=
  Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i)))

/-- Minimal hvol input: the tensor log-volume is the sum of local log-volumes. -/
def S2728HvolInput (localVolume : C3.tensorIndex → ℝ) : Prop :=
  comparisonRegionVolume C3 T e = ∑ i, localVolume i

/-- Minimal hheight input with (1+eps) times the sum of local volumes plus A. -/
def S2728HheightInput
    (localVolume : C3.tensorIndex → ℝ) (height eps A : ℝ) : Prop :=
  height ≤ (1 + eps) * (∑ i, localVolume i) + A

/-- Additive constant calibrated by the real-line log-volume functional. -/
noncomputable def S2728RealLineAdditiveConstant (y : ℝ) : ℝ :=
  (realLineLogVolume ({y} : Set ℝ)).toReal

theorem S2728RealLineAdditiveConstant_eq (y : ℝ) :
    S2728RealLineAdditiveConstant y = (ENNReal.ofReal y).toReal := by
  rw [S2728RealLineAdditiveConstant, realLineLogVolume_singleton]

#check S2728LocalDegree_pos
#check S2728HvolInput
#check S2728HheightInput
#check S2728RealLineAdditiveConstant_eq
end LeanFormal.IUT.XiFPaper.S2728V2LocalInputsActual
end
