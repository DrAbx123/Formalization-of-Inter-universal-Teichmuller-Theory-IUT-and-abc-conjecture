import tmp.sheaf.xif.paper.S2564Batch5CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2598e0EStepActual
open LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepE0 : LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E0 *
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7 =
    F10 * LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.Qestep0 +
    LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1 := by
  simpa only [Aestep0, Bestep0, Nestep0, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E0, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.D7, LeanFormal.IUT.XiFPaper.S2564Batch5CorrectActual.E1] using estep0

end LeanFormal.IUT.XiFPaper.S2598e0EStepActual
end
