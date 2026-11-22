import tmp.sheaf.xif.paper.S2594bAChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2597a0BChainActual
open LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual

abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10

lemma B0_eq_A4 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 =
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4 := rfl

lemma hB0 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249) -
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 := by
  rw [B0_eq_A4]
  exact hA4

lemma hstepB0 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 *
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0 =
    F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qbstep0 +
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1 := by
  simpa only [Abstep0, Bbstep0, Nbstep0, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B0, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.B1] using bstep0

end LeanFormal.IUT.XiFPaper.S2597a0BChainActual

end