import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a2BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepB2 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep2 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3 := by
  simpa only [Abstep2, Bbstep2, Nbstep2, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B2, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B3] using bstep2

end LeanFormal.IUT.XiFPaper.S2597a2BChainActual
end
