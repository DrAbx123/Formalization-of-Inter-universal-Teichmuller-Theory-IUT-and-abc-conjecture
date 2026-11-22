import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598d3DStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepD3 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qdstep3 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4 := by
  simpa only [Adstep3, Bdstep3, Ndstep3, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D3, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D4] using dstep3

end LeanFormal.IUT.XiFPaper.S2598d3DStepActual
end
