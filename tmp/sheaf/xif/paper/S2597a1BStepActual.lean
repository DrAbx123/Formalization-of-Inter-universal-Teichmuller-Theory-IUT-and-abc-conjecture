import tmp.sheaf.xif.paper.S2597a0BStepActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
namespace LeanFormal.IUT.XiFPaper.S2597a1BStepActual

lemma hstepB1 : B1 * B1 = F10 * Qbstep1 + B2 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep1,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep1,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep1,
    B1, B2, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep1
