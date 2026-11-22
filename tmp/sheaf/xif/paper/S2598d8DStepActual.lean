import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d8DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD8 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep8 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9 := by
  simpa only [Adstep8, Bdstep8, Ndstep8, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9] using dstep8

end LeanFormal.IUT.XiFPaper.S2598d8DStepActual
end
