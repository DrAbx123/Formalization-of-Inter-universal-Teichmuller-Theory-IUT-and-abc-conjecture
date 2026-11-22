/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual

/-! # A726: S3137 q-pilot readout, product form -/

/- Two different formalizations of the q-pilot object exist and must not be conflated:
* A716 `paperQPilotObjectOfInputs` : `Theorem311Source.PaperQPilotObject` (boundary/
  oneColumn/lineBundle/logKummer inputs; green constructor exists);
* S3137 readout is over `N8Closure.PaperQPilotObjectActual` (fields C1/C2/C3/strip/
  oneColumn/logKummer, declared in QPilotObjectActual.lean:154), which has NO green
  constructor — its docstring states that existence is the paper source obligation.
Bridging the two q-pilot objects needs an inhabitant of `PaperQPilotObjectActual`; that
inhabitant is an external source construction, not fabricated here. -/

set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1S3137ReadoutBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

variable {l : PrimeGeFive} {V : Type} {I : LeanFormal.IUT.Theorem311Source.OriginalInput l V}

/-- ① The S3137 readout is definitionally the signed q-pilot log-volume. -/
theorem qPilotLogVolumeReading_eq_signed (P : PaperQPilotObjectActual I) :
    LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.qPilotLogVolumeReading P
      = P.signedQPilotLogVolume :=
  rfl

/-- ② The readout equals `log ||q||` (S3137 green refinement, re-exported). -/
theorem qPilotLogVolumeReading_eq_log_norm (P : PaperQPilotObjectActual I) :
    LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.qPilotLogVolumeReading P
      = Real.log ‖P.line.C3.q.q‖ := by
  simpa only [qPilotLogVolumeReading_eq_signed] using P.signedQPilotLogVolume_eq_log_norm

/-- ③ A readout consumes an inhabitant: every readout fact below is parameterized by
`P : PaperQPilotObjectActual I`.  The inhabitation itself (`Nonempty (PaperQPilotObjectActual I)`)
is the external paper source obligation recorded in the file header; it is not a named
assumption of the theorems (they are implications from `P`). -/
theorem qPilotLogVolumeReading_nonpos (P : PaperQPilotObjectActual I) :
    LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.qPilotLogVolumeReading P ≤ 0 :=
  P.signedQPilotLogVolume_neg.le

/-- Honest record of the remaining inhabitation bridge (not fabricated). -/
def qPilotReadoutInhabitationGap : String :=
  "remaining: inhabitant of N8Closure.PaperQPilotObjectActual (C1/C2/C3/strip/oneColumn/logKummer = paper source obligation)"

end LeanFormal.IUT.XiFPaper.Mzk1S3137ReadoutBridgeActual
