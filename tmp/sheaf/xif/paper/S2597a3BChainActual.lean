import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a3BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepB3 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep3 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B4 := by
  simpa only [Abstep3, Bbstep3, Nbstep3, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B4] using bstep3

end LeanFormal.IUT.XiFPaper.S2597a3BChainActual
end
