import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d7DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD7 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep7 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8 := by
  simpa only [Adstep7, Bdstep7, Ndstep7, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D8] using dstep7

end LeanFormal.IUT.XiFPaper.S2598d7DStepActual
end
