/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralTensorCovolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.Tactic
/-! # One-way full-lattice bound for the C3 theta hull -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaFullLatticeBoundActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open MeasureTheory
open scoped Pointwise ENNReal
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
local instance : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
/-- Full-lattice one-way bound, conditional on the two hull/unit bridges. -/
theorem fullLattice_le_thetaHull_of_bridges
    (hsub : arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple ⊆
      actualC3LogShellTensorRegion C3)
    (hunit : 1 ≤ ((actualC3LogShellTensorHaar C3)
      (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal) :
    arithmeticTupleLogTensorUnitLogVolume C3.tensorPlaces C3.tensorTuple ≤
      thetaPilotHullLogVolumeReal C3 := by
  letI : Measure.IsAddHaarMeasure (actualC3LogShellTensorHaar C3) :=
    actualC3LogShellTensorHaar_isAddHaar (C3 := C3)
  have hfull := arithmeticTupleLogTensorUnitLogVolume_le_hull
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple)
    (μ := actualC3LogShellTensorHaar C3)
  have hrel := arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple)
    (μ := actualC3LogShellTensorHaar C3)
  have hmono : (actualC3LogShellTensorHaar C3)
      (arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple) ≤
      (actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3) :=
    measure_mono hsub
  have hunitlog : 0 ≤ Real.log ((actualC3LogShellTensorHaar C3)
      (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal :=
    Real.log_nonneg hunit
  have hcanon := measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple)
    (μ := actualC3LogShellTensorHaar C3)
  have hfinReg : (actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3) < ⊤ :=
    (actualC3LogShellTensorRegion_compact C3).measure_lt_top
  have htoReal := ENNReal.toReal_mono hfinReg.ne hmono
  have hlogmono : Real.log ((actualC3LogShellTensorHaar C3)
      (arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple)).toReal ≤
      Real.log ((actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3)).toReal :=
    Real.log_le_log (ENNReal.toReal_pos hcanon.1.1.ne' hcanon.1.2.ne) htoReal
  have htheta := thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)
  rw [htheta]
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1ThetaFullLatticeBoundActual
end