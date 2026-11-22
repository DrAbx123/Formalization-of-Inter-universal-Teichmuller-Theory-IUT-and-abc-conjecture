import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportConjugation
import tmp.sheaf.xif.paper.SHEOutputActual

-- S1204: fourth joint audit.  Actual 1-column log-shift/readout algebra
-- from the actual oneColumnPacket/scale/thetaValueAt; no weak interface.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual 1-column log readout at stage `m` and label `j`. -/
noncomputable def oneColumnLogReadout (m : Int) (j : SignedLabel l.value) : Real :=
  Real.log (I.oneColumnScale m j)

/-- Actual vertical log-shift invariance of the 1-column readout. -/
theorem oneColumnLogReadout_shift (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout I m j = oneColumnLogReadout I m' j := by
  unfold oneColumnLogReadout
  rw [I.oneColumnScale_transport m m' j]

theorem oneColumnLogReadout_succ (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout I m j = oneColumnLogReadout I (m + 1) j :=
  oneColumnLogReadout_shift I m (m + 1) j

/-- Actual readout identification with the source theta value at the
one-column shared boundary. -/
theorem oneColumnLogReadout_theta (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout I m j = Real.log (I.thetaValueAt m 0 j) := by
  unfold oneColumnLogReadout
  rw [← I.thetaValueAt_eq_oneColumnScale m j]

/-- Actual readout through the positive-packet scale. -/
theorem oneColumnLogReadout_positivePacket (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout I m j =
      Real.log ((I.oneColumnPacket m).toPositivePacket.scale j) := by
  unfold oneColumnLogReadout oneColumnScale
  rw [FiniteThetaPacket.toPositivePacket_scale]

/-- Actual q-shift invariance of the 1-column. -/
theorem oneColumnQ_shift (m : Int) :
    I.oneColumnQ m = I.oneColumnQ (m + 1) :=
  I.oneColumnQ_vertical m

#check oneColumnLogReadout
#check oneColumnLogReadout_shift
#check oneColumnLogReadout_theta
#check oneColumnLogReadout_positivePacket
#check oneColumnQ_shift

end LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual

end