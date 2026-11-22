import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d9DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD9 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep9 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D10 := by
  simpa only [Adstep9, Bdstep9, Ndstep9, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D9, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D10] using dstep9

end LeanFormal.IUT.XiFPaper.S2598d9DStepActual
end
