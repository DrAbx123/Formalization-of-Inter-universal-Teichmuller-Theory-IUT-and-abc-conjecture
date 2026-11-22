import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a5BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepB5 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep5 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6 := by
  simpa only [Abstep5, Bbstep5, Nbstep5, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B5, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6] using bstep5

end LeanFormal.IUT.XiFPaper.S2597a5BChainActual
end
