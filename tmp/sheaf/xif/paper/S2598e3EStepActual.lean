import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598e3EStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepE3 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qestep3 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4 := by
  simpa only [Aestep3, Bestep3, Nestep3, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D0, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E4] using estep3

end LeanFormal.IUT.XiFPaper.S2598e3EStepActual
end
