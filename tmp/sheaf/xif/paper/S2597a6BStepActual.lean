import tmp.sheaf.xif.paper.S2597a5BStepActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a5BStepActual
namespace LeanFormal.IUT.XiFPaper.S2597a6BStepActual

lemma hstepB6 : B6 * B6 = F10 * Qbstep6 + B7 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep6,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep6,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep6,
    B6, B7, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep6
