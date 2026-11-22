import tmp.sheaf.xif.paper.S2564Batch5CorrectActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597c3CStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepC3 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C3 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qcstep3 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4 := by
  simpa only [Acstep3, Bcstep3, Ncstep3, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C3, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C4] using cstep3

end LeanFormal.IUT.XiFPaper.S2597c3CStepActual
end
