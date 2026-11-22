import tmp.sheaf.xif.paper.S2597a1BStepActualAdapted
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a1BStepActualAdapted
namespace LeanFormal.IUT.XiFPaper.S2597a2BStepActualAdapted

lemma hstepB2 : B2 * B2 = F10 * Qbstep2 + B3 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep2,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep2,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep2,
    B2, B3, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep2
