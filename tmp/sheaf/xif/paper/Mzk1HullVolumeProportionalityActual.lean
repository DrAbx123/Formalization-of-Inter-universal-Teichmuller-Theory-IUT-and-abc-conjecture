/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual

/-!
# A523 hull-volume proportionality (reused real scaling laws)

Two real proportionality laws are reused, not reproved:
* actual C3 Theta-hull Haar scaling (`S3137ThetaHullVolumeScalingActual`,
  IUT III Proposition 3.9(i)): multiplying the hull region by `p` shifts the Haar
  log-volume by `-[block : Q_p] * log p`;
* hull-lane packet scaling (`Mzk1HullDetStep3115Actual.hullReadout_rescale`): rescaling
  the positive packet by `c > 0` shifts `hullReadout = log(packetDet)` by
  `card(label) * log c`.

These are the proportionality inputs of the xi-e/hull log-volume comparison.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullVolumeProportionalityActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance propBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance propBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. Actual Theta-hull Haar proportionality (IUT III Prop 3.9(i)) -/

/-- The actual hull Haar log-volume is finite (compactness). -/
theorem thetaHull_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
  S3137ThetaHullVolumeScalingActual.thetaPilotHull_measure_lt_top (C3 := C3)

/-- **Proportionality**: multiplying the actual Theta-pilot hull by the prime `p` shifts
  its Haar log-volume by `-[block : Q_p] * log p` (reused S3137 real theorem). -/
theorem thetaHull_log_measure_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
        thetaPilotHullLogVolumeReal C3 :=
  S3137ThetaHullVolumeScalingActual.thetaPilotHull_log_measure_prime_smul (C3 := C3) hpos

/-! ## 2. Hull-lane packet proportionality -/

variable {label : Type} [Fintype label] [DecidableEq label]

/-- **Packet proportionality**: rescaling the positive packet by `c > 0` shifts the
  hull readout `log(packetDet)` by `card(label) * log c` (reused hull-lane real theorem). -/
theorem packet_hullReadout_rescale (x : HullDetState label) (c : ℝ) (hc : 0 < c) :
    hullReadout { x with packet := rescalePacket c hc x.packet } =
      (Fintype.card label : ℝ) * Real.log c + hullReadout x :=
  hullReadout_rescale x c hc

/-- **Exponential form of the packet proportionality**: rescaling multiplies the
  exponential of the hull readout by `c ^ card(label)`. -/
theorem packet_det_rescale (x : HullDetState label) (c : ℝ) (hc : 0 < c) :
    packetDet (rescalePacket c hc x.packet) =
      c ^ Fintype.card label * packetDet x.packet :=
  packetDet_rescale c hc x.packet

end

end LeanFormal.IUT.XiFPaper.Mzk1HullVolumeProportionalityActual