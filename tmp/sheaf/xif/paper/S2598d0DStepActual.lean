import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d0DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD0 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep0 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1 := by
  simpa only [Adstep0, Bdstep0, Ndstep0, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1] using dstep0

end LeanFormal.IUT.XiFPaper.S2598d0DStepActual
end
