import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a9BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepB9 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep9 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B10 := by
  simpa only [Abstep9, Bbstep9, Nbstep9, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B9, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B10] using bstep9

end LeanFormal.IUT.XiFPaper.S2597a9BChainActual
end
