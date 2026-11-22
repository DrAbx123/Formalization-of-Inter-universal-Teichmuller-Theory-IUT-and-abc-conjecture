import tmp.sheaf.xif.paper.S2597a3BStepActualAdapted
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a3BStepActualAdapted
namespace LeanFormal.IUT.XiFPaper.S2597a4BStepActualAdapted

lemma hstepB4 : B4 * B4 = F10 * Qbstep4 + B5 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep4,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep4,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep4,
    B4, B5, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep4
