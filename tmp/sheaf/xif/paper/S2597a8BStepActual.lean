import tmp.sheaf.xif.paper.S2597a7BStepActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a7BStepActual
namespace LeanFormal.IUT.XiFPaper.S2597a8BStepActual

lemma hstepB8 : B8 * B8 = F10 * Qbstep8 + B9 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep8,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep8,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep8,
    B8, B9, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep8
