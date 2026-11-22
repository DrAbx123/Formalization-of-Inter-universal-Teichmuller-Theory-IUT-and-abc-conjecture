import tmp.sheaf.xif.paper.S2597a6BStepActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a6BStepActual
namespace LeanFormal.IUT.XiFPaper.S2597a7BStepActual

lemma hstepB7 : B7 * B7 = F10 * Qbstep7 + B8 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep7,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep7,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep7,
    B7, B8, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep7
