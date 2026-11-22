import tmp.sheaf.xif.paper.S2564Batch5CorrectActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597c2CStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepC2 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C2 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qcstep2 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C3 := by
  simpa only [Acstep2, Bcstep2, Ncstep2, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C2, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.C3] using cstep2

end LeanFormal.IUT.XiFPaper.S2597c2CStepActual
end
