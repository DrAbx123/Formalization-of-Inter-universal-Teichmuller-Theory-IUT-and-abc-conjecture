import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a6BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma hstepB6 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep6 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7 := by
  simpa only [Abstep6, Bbstep6, Nbstep6, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B6, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B7] using bstep6

end LeanFormal.IUT.XiFPaper.S2597a6BChainActual
end
