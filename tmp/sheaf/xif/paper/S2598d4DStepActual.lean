import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d4DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD4 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep4 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 := by
  simpa only [Adstep4, Bdstep4, Ndstep4, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5] using dstep4

end LeanFormal.IUT.XiFPaper.S2598d4DStepActual
end
