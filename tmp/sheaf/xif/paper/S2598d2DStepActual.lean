import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d2DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD2 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep2 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3 := by
  simpa only [Adstep2, Bdstep2, Ndstep2, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D2, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3] using dstep2

end LeanFormal.IUT.XiFPaper.S2598d2DStepActual
end
