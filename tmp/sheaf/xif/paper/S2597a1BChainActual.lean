import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a1BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepB1 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep1 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2 := by
  simpa only [Abstep1, Bbstep1, Nbstep1, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2] using bstep1

end LeanFormal.IUT.XiFPaper.S2597a1BChainActual
end
