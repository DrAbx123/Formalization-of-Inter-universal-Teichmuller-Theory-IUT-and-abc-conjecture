/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TensorRegionNormalizationActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic
/-! # Unit-lattice one-way bound inside the actual C3 theta region -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaUnitLatticeBoundActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1TensorRegionNormalizationActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory
open scoped Pointwise ENNReal
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
local instance : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
/-- Integer tensor region is inside the actual C3 log-shell tensor region. -/
theorem tensorIntegerRegion_subset_actualRegion :
    tensorIntegerRegion (p := C3.p) (A := fun i => C3LogShellFiber C3 i) ⊆
      actualC3LogShellTensorRegion C3 := by
  letI : Fact C3.p.Prime := C3.hp
  apply tensorIntegralRegion_mono
  intro i
  rw [actualC3LogShell_eq_integralLogShell]
  exact integers_subset_integralLogShell (K := C3LogShellFiber C3 i) (p := C3.p)
/-- One-way log-volume bound for the integer tensor lattice, with raw
positivity/finiteness as explicit GAP. -/
theorem unitLatticeLogVolume_le_thetaHull
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (tensorIntegerRegion (p := C3.p) (A := fun i => C3LogShellFiber C3 i)))
    (hfin : (actualC3LogShellTensorHaar C3) (tensorIntegerRegion (p := C3.p) (A := fun i => C3LogShellFiber C3 i)) < ⊤) :
    Real.log ((actualC3LogShellTensorHaar C3) (tensorIntegerRegion (p := C3.p) (A := fun i => C3LogShellFiber C3 i))).toReal ≤
      thetaPilotHullLogVolumeReal C3 := by
  let μ := actualC3LogShellTensorHaar C3
  let L : Set (C3LogShellTensorBlock C3) := tensorIntegerRegion (p := C3.p) (A := fun i => C3LogShellFiber C3 i)
  letI : Measure.IsAddHaarMeasure μ := actualC3LogShellTensorHaar_isAddHaar (C3 := C3)
  have hmono : μ L ≤ μ (actualC3LogShellTensorRegion C3) := measure_mono (tensorIntegerRegion_subset_actualRegion (C3 := C3))
  have hRfin : μ (actualC3LogShellTensorRegion C3) < ⊤ := (actualC3LogShellTensorRegion_compact C3).measure_lt_top
  have hlog := Real.log_le_log (ENNReal.toReal_pos hpos.ne' hfin.ne) (ENNReal.toReal_mono hRfin.ne hmono)
  have htheta := thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)
  rw [htheta]
  exact hlog
end LeanFormal.IUT.XiFPaper.Mzk1ThetaUnitLatticeBoundActual
end