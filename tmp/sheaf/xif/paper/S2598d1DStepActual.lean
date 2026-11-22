import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d1DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD1 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep1 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2 := by
  simpa only [Adstep1, Bdstep1, Ndstep1, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D1, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2] using dstep1

end LeanFormal.IUT.XiFPaper.S2598d1DStepActual
end
