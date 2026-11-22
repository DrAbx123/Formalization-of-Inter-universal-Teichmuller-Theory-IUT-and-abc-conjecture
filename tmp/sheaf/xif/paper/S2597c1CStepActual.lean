import tmp.sheaf.xif.paper.S2564Batch5CorrectActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597c1CStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepC1 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C1 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qcstep1 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C2 := by
  simpa only [Acstep1, Bcstep1, Ncstep1, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C1, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C2] using cstep1

end LeanFormal.IUT.XiFPaper.S2597c1CStepActual
end
