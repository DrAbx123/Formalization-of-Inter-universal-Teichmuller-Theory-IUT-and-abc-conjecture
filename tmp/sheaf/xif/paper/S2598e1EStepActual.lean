import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598e1EStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepE1 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qestep1 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2 := by
  simpa only [Aestep1, Bestep1, Nestep1, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D6, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2] using estep1

end LeanFormal.IUT.XiFPaper.S2598e1EStepActual
end
