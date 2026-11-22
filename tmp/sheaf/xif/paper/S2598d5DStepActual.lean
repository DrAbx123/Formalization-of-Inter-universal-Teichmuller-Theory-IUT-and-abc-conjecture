import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d5DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD5 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep5 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 := by
  simpa only [Adstep5, Bdstep5, Ndstep5, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6] using dstep5

end LeanFormal.IUT.XiFPaper.S2598d5DStepActual
end
