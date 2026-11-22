import tmp.sheaf.xif.paper.S2726C3PerPlaceUpdateRegionActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

noncomputable section
set_option synthInstance.maxHeartbeats 400000
namespace LeanFormal.IUT.XiFPaper.S2727V2RegionTarget

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
open LeanFormal.IUT.XiFPaper.S2726C3TensorComparisonRegionRhoActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

local instance s2727MeasurableSpace
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    MeasurableSpace (C3LogShellTensorBlock C3) :=
  borel _

local instance s2727BorelSpace
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- V2 comparison region attached to the explicit index equivalence e. -/
noncomputable def comparisonRegion
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex] :
    Set (C3LogShellTensorBlock C3) :=
  S2726C3PerPlaceUpdateRegion C3 T e

/-- Its Haar log-volume. -/
noncomputable def comparisonRegionVolume
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex] : ℝ :=
  (haarLogVolume (actualC3LogShellTensorHaar C3) (comparisonRegion C3 T e)).toReal

/-- hvol target: comparisonRegionVolume is exactly the Haar log-volume of comparisonRegion. -/
def hvolTarget
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex] : Prop :=
  comparisonRegionVolume C3 T e =
    (haarLogVolume (actualC3LogShellTensorHaar C3) (comparisonRegion C3 T e)).toReal

/-- hheight target: arithmetic height bounded by (1+eps)*comparisonRegionVolume + C. -/
def hheightTarget
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex]
    (height eps C : ℝ) : Prop :=
  height ≤ (1 + eps) * comparisonRegionVolume C3 T e + C

#check comparisonRegion
#check comparisonRegionVolume
#check hheightTarget
end LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
end
