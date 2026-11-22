import tmp.sheaf.xif.paper.S2728V2LocalInputsActual
import tmp.sheaf.xif.paper.PrimeStripLogShellActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.MeasureTheory.Measure.Haar.Basic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2729LocalVolumeActual

open scoped BigOperators
open MeasureTheory
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
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
open LeanFormal.IUT.XiFPaper.S2728V2LocalInputsActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2729MeasurableSpace (i : C3.tensorIndex) :
    MeasurableSpace (C3LogShellFiber C3 i) := borel _

local instance s2729BorelSpace (i : C3.tensorIndex) :
    BorelSpace (C3LogShellFiber C3 i) := ⟨rfl⟩

/-- Local additive Haar measure on the completed local field. -/
noncomputable def S2729LocalHaar (i : C3.tensorIndex) :
    Measure (C3LogShellFiber C3 i) := Measure.addHaar

/-- Actual local log-shell volume. -/
noncomputable def S2729LocalVolume (i : C3.tensorIndex) : ℝ :=
  (haarLogVolume (S2729LocalHaar C3 i) (actualC3LogShell C3 i)).toReal

/-- Exact hvol target: tensor Haar log-volume of comparisonRegion is the
sum of the actual local log-shell volumes.  Not proved below. -/
def S2729HvolTarget : Prop :=
  S2728HvolInput C3 T e (S2729LocalVolume C3)

#check S2729HvolTarget
