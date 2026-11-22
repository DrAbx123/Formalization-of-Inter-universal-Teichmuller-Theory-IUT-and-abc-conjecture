import tmp.sheaf.xif.paper.S2564Batch5CorrectActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597c0CStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepC0 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C0 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qcstep0 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C1 := by
  simpa only [Acstep0, Bcstep0, Ncstep0, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C0, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C1] using cstep0

end LeanFormal.IUT.XiFPaper.S2597c0CStepActual
end
