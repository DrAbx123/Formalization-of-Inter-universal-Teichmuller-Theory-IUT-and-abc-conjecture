import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance r1BlockMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance r1BlockBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-!
# R1 Theta-half bridge: lattice's Theta hull readout and the actual paper hull

**Component, not a paper object.**  Consumer: lattice's R1 residual
(`S3137NativeToC3SameCReadoutActual` / `qThetaPilotLogVolumeComparison`).

Lattice's actual Theta-side container
`S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHull` is *definitionally*
the actual least lambda-O hull of the actual C3 tensor log-shell region, the very
same object as the paper hull of `S3132PaperHullSetPropertiesActual`
(`paperHullHaarReadout` / `paperHullRealLogVolume`; that file's definitions are
the same expression).  This module records the exact readout relations using only
the actual C3-packet objects, avoiding cross-file universe friction:

* `thetaPilotHull_eq_actualHolomorphicHull` — the containers are the same set;
* `thetaPilotHullLogVolumeReal_eq_log_actualHaar` — lattice's real Theta reading
  is the logarithm of the actual Haar measure of the actual paper hull;
* `thetaPilotHullLogVolume_eq_haarLogVolume_actualHull` — its packaged ENNReal
  reading;
* `thetaPilotHull_haar_lt_top` — finiteness from actual compactness of the
  tensor log-shell region (the paper hull of the region is the region).

Lattice's convention note: `thetaPilotHullLogVolumeReal` = Real.log of the Haar
measure; the hull-stream real readout `paperHullRealLogVolume` is the Haar
measure itself, so the two are related by `Real.log`.

Sign caution (paper): IUT III Corollary 3.12 (corpus 10352-10353) asserts the
signed comparison `-|log(Theta)| >= -|log(q)|` (i.e. `H <= |log q|` in positive
magnitudes).  This bridge identifies only the Theta-half readout; it asserts no
comparison and no cross-carrier containment.

Source: IUT III, Proposition 3.9, (i) (p. 115); Remark 3.9.5, (i), (ii)
(pp. 158-160); Corollary 3.12 proof Step (xi-e) (pp. 174-175).
-/

/-- The two actual Theta containers are the same set: lattice's hull is the
actual least lambda-O hull of the actual C3 tensor log-shell region. -/
theorem thetaPilotHull_eq_actualHolomorphicHull :
    thetaPilotHull C3 = actualHolomorphicHull C3 (actualUnitRegion C3) :=
  rfl

/-- Finiteness of the actual Haar measure of the paper hull (the paper hull of
the actual tensor region is that compact region). -/
theorem thetaPilotHull_haar_lt_top :
    actualC3LogShellTensorHaar C3
      (actualHolomorphicHull C3 (actualUnitRegion C3)) < ⊤ := by
  rw [actualHolomorphicHull_unitRegion_eq C3]
  haveI hAdd : Measure.IsAddHaarMeasure (actualC3LogShellTensorHaar C3) :=
    inferInstance
  haveI hFin : IsFiniteMeasureOnCompacts (actualC3LogShellTensorHaar C3) :=
    hAdd.toIsFiniteMeasureOnCompacts
  exact (actualC3LogShellTensorRegion_compact C3).measure_lt_top

/-- **Theta-half readout relation (lattice convention).**  Lattice's real Theta
reading is the logarithm of the actual Haar measure of the actual paper hull. -/
theorem thetaPilotHullLogVolumeReal_eq_log_actualHaar :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3
        (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal) := by
  unfold thetaPilotHullLogVolumeReal
  rw [thetaPilotHull_eq_actualHolomorphicHull C3]

/-- The same relation with the actual upper bound on the Haar mass made explicit:
the logarithm's argument is finite. -/
theorem thetaPilotHullLogVolumeReal_eq_log_actualHaar_of_lt_top :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3
        (actualHolomorphicHull C3 (actualUnitRegion C3))).toReal) :=
  thetaPilotHullLogVolumeReal_eq_log_actualHaar C3

/-- **Packaged ENNReal Theta reading.** -/
theorem thetaPilotHullLogVolume_eq_haarLogVolume_actualHull :
    thetaPilotHullLogVolume C3 =
      haarLogVolume (actualC3LogShellTensorHaar C3)
        (actualHolomorphicHull C3 (actualUnitRegion C3)) := by
  unfold thetaPilotHullLogVolume
  rw [thetaPilotHull_eq_actualHolomorphicHull C3]

/-- **Finiteness of the packaged Theta log-volume readout** from the actual
compactness of the paper hull. -/
theorem thetaPilotHullLogVolume_ne_top_from_actualHull :
    thetaPilotHullLogVolume C3 ≠ ⊤ := by
  rw [thetaPilotHullLogVolume_eq_haarLogVolume_actualHull]
  rw [haarLogVolume_of_lt_top (thetaPilotHull_haar_lt_top C3)]
  exact ENNReal.ofReal_ne_top

#check thetaPilotHull_eq_actualHolomorphicHull
#check thetaPilotHullLogVolumeReal_eq_log_actualHaar
#check thetaPilotHullLogVolume_eq_haarLogVolume_actualHull
#check thetaPilotHullLogVolume_ne_top_from_actualHull

end LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual

end
