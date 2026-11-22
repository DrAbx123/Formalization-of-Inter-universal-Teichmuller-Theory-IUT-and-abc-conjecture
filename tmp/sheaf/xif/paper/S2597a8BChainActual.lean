import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a8BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepB8 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep8 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9 := by
  simpa only [Abstep8, Bbstep8, Nbstep8, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B8, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9] using bstep8

end LeanFormal.IUT.XiFPaper.S2597a8BChainActual
end
