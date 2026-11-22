import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a7BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepB7 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep7 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8 := by
  simpa only [Abstep7, Bbstep7, Nbstep7, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8] using bstep7

end LeanFormal.IUT.XiFPaper.S2597a7BChainActual
end
