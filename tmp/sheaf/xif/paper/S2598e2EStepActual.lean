import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598e2EStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepE2 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qestep2 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3 := by
  simpa only [Aestep2, Bestep2, Nestep2, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E2, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D5, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E3] using estep2

end LeanFormal.IUT.XiFPaper.S2598e2EStepActual
end
