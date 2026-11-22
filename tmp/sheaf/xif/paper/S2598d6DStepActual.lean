import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d6DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD6 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep6 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 := by
  simpa only [Adstep6, Bdstep6, Ndstep6, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7] using dstep6

end LeanFormal.IUT.XiFPaper.S2598d6DStepActual
end
