/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.Tactic
/-! # L Haar log-volume clipping (historical separation)

`actualC3LogShellTensorLogVolumeL` is defined via `haarLogVolume` and is clipped by
`(ENNReal.ofReal r).toReal = max r 0`.  The current `thetaNormReadL` does NOT use it:
it uses the direct `thetaReadActual`.  This file records the distinction, not a defect
of the current normalized readout. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LHaarLogClipActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
/-- `actualC3LogShellTensorLogVolumeL` (old Haar-log-volume def) is clipped. -/
theorem actualC3LogShellTensorLogVolumeL_eq_max :
    actualC3LogShellTensorLogVolumeL (I := I) (C3L := C3LAt I place) =
      max 0 (Real.log ((actualC3LogShellTensorHaarL (I := I) (C3L := C3LAt I place))
        (actualC3LogShellTensorRegionL (I := I) (C3L := C3LAt I place))).toReal) := by
  unfold actualC3LogShellTensorLogVolumeL
  rw [haarLogVolume_of_lt_top
    (actualC3LogShellTensorHaarL_lt_top (I := I) (C3L := C3LAt I place))]
  exact ENNReal.toReal_ofReal'
/-- The current normalized readout uses direct `thetaReadActual`, not the clipped old
`actualC3LogShellTensorLogVolumeL`. -/
theorem thetaNormReadL_eq_thetaReadActual_sub_log_unitMass :
    thetaNormReadL (I := I) (place := place) =
      thetaReadActual I place - Real.log (actualUnitMassL (I := I) (place := place)) := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0LHaarLogClipActual
end