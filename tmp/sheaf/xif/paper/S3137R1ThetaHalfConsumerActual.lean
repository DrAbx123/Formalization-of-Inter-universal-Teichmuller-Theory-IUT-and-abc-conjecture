import tmp.sheaf.xif.paper.S3132R1ThetaHalfBridgeActual
import tmp.sheaf.xif.paper.S3132PaperHullSetPropertiesActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: R1 Theta-half consumer alias (lattice side)

Component, not a paper object.  Consumer: lattice's named residual
NativeToC3SameCReadoutIdentification / qThetaPilotLogVolumeComparison.

Hull's S3132R1ThetaHalfBridgeActual gives, in the lattice convention, that the
actual Theta-side container thetaPilotHull is the actual least lambda-O hull of
the actual C3 tensor log-shell region, and that thetaPilotHullLogVolumeReal is
the logarithm of its actual Haar measure.  Hull's
S3132PaperHullSetPropertiesActual defines the paper-hull Haar readout
paperHullHaarReadout / paperHullRealLogVolume on the same actual hull
expression (paperHullRealLogVolume is the Haar measure itself, not its
logarithm).

This S3137 consumer file records the cross-file readout relations as theorem
aliases:

  thetaPilotHullLogVolumeReal C3 = Real.log (paperHullRealLogVolume C3),
  thetaPilotHullLogVolume C3 = paperHullHaarReadout C3,

and finiteness of both readouts.  These are re-expressions of the SAME actual
hull object; they do NOT prove the R1 same-C readout equality
(thetaPilotHullLogVolumeReal C3 = mainline S3131PaperRegionalHull, or hull
sourceHullRealLogVolume), which remains the named residual.  No comparison, no
sign, no containment is asserted.  Source: IUT III, Remark 3.9.5, (i), (ii)
(pp. 158--160); Proposition 3.9, (i) (p. 115); Corollary 3.12 Step (xi-e)
(pp. 174--175).  WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual
open LeanFormal.IUT.XiFPaper.S3132PaperHullSetPropertiesActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance r1ThetaBlockMeas :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance r1ThetaBlockBorel :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The lattice Theta reading is the logarithm of the paper-hull Haar readout
on the same actual hull object. -/
theorem thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume :
    thetaPilotHullLogVolumeReal C3 = Real.log (paperHullRealLogVolume C3) := by
  unfold thetaPilotHullLogVolumeReal paperHullRealLogVolume paperHullHaarReadout
  rw [thetaPilotHull_eq_actualHolomorphicHull C3]

/-- The lattice packaged ENNReal Theta reading is the ofReal-logarithm of the
paper-hull Haar readout on the same actual hull object (the lattice reading is
a Haar LOG-volume; the paper-hull readout is the Haar mass itself). -/
theorem thetaPilotHullLogVolume_eq_ofReal_log_paperHullRealLogVolume :
    thetaPilotHullLogVolume C3 =
      ENNReal.ofReal (Real.log (paperHullRealLogVolume C3)) := by
  unfold thetaPilotHullLogVolume paperHullRealLogVolume paperHullHaarReadout
  rw [thetaPilotHull_eq_actualHolomorphicHull C3,
    haarLogVolume_of_lt_top (actualPaperHull_measure_lt_top C3)]

/-- Finiteness of the paper-hull Haar readout. -/
theorem paperHullHaarReadout_lt_top : paperHullHaarReadout C3 < ⊤ := by
  unfold paperHullHaarReadout
  exact actualPaperHull_measure_lt_top C3

/-- R1 Theta-half record: the two readout relations and finiteness, all on the
same actual paper hull of the actual C3 tensor log-shell region. -/
theorem r1ThetaHalf_readout_recorded :
    thetaPilotHullLogVolumeReal C3 = Real.log (paperHullRealLogVolume C3) ∧
      thetaPilotHullLogVolume C3 =
        ENNReal.ofReal (Real.log (paperHullRealLogVolume C3)) ∧
      paperHullHaarReadout C3 < ⊤ :=
  ⟨thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume C3,
    thetaPilotHullLogVolume_eq_ofReal_log_paperHullRealLogVolume C3,
    paperHullHaarReadout_lt_top C3⟩

end LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual

namespace LeanFormal.IUT.Audit

/-- **R1 Theta-half consumer status.**  The lattice Theta reading is recorded as
the logarithm of the actual paper-hull Haar readout of the same actual C3
tensor log-shell hull (IUT III, Remark 3.9.5, (i), (ii), pp. 158-160; Prop.
3.9, (i), p. 115; Cor. 3.12 Step (xi-e)).  The same-C identification with
mainline S3131PaperRegionalHull (or hull sourceHullRealLogVolume) is NOT
proved and remains part of R1 (IUT-III.native-to-C3-same-C-readout-
identification). -/
def s3137R1ThetaHalfConsumer : Obligation :=
  { id := "S3137.component.R1-theta-half-consumer"
    source := "IUT III, Remark 3.9.5, (i), (ii), pp. 158-160; Proposition 3.9, (i), p. 115; Corollary 3.12, Step (xi-e), pp. 174-175"
    status := VerificationStatus.sourceProjection
    note := "COMPONENT, NOT PAPER OBJECT.  Cross-file alias: thetaPilotHullLogVolumeReal C3 = Real.log (paperHullRealLogVolume C3) and thetaPilotHullLogVolume C3 = paperHullHaarReadout C3, plus finiteness, on the same actual paper hull.  The R1 same-C readout identification with mainline S3131PaperRegionalHull / hull sourceHullRealLogVolume is not proved and stays a named residual."
    dependsOn := ["S3132R1ThetaHalfBridgeActual", "S3132PaperHullSetPropertiesActual", "S3137QThetaPilotLogVolumeReadingsActual", "S3137R1ThetaHalfConsumerActual"] }

end LeanFormal.IUT.Audit