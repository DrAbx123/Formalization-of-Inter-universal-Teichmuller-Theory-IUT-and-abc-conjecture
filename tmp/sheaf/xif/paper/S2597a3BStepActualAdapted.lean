import tmp.sheaf.xif.paper.S2597a2BStepActualAdapted
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a2BStepActualAdapted
namespace LeanFormal.IUT.XiFPaper.S2597a3BStepActualAdapted

lemma hstepB3 : B3 * B3 = F10 * Qbstep3 + B4 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep3,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep3,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep3,
    B3, B4, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep3
