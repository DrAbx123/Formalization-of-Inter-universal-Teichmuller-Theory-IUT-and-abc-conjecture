import tmp.sheaf.xif.paper.S2597a4BStepActualAdapted
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a4BStepActualAdapted
namespace LeanFormal.IUT.XiFPaper.S2597a5BStepActualAdapted

lemma hstepB5 : B5 * B5 = F10 * Qbstep5 + B6 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep5,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep5,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep5,
    B5, B6, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep5
