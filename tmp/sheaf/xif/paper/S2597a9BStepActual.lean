import tmp.sheaf.xif.paper.S2597a8BStepActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2597a0BStepActual
open LeanFormal.IUT.XiFPaper.S2597a8BStepActual
namespace LeanFormal.IUT.XiFPaper.S2597a9BStepActual

lemma hstepB9 : B9 * B9 = F10 * Qbstep9 + B10 := by
  simpa only [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Abstep9,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Bbstep9,
    LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Nbstep9,
    B9, B10, F10,
    LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10] using LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.bstep9

lemma hB1 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 2) - B1 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 1) (U := B0) (V := B1) (Q := Qbstep0) hB0 hstepB0
  simpa [show 2 * ((1249 * 1249) * 1249 * 1) = (1249 * 1249) * 1249 * 2 by ring] using h

lemma hB2 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 4) - B2 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 2) (U := B1) (V := B2) (Q := Qbstep1) hB1 hstepB1
  simpa [show 2 * ((1249 * 1249) * 1249 * 2) = (1249 * 1249) * 1249 * 4 by ring] using h

lemma hB3 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 8) - B3 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 4) (U := B2) (V := B3) (Q := Qbstep2) hB2 hstepB2
  simpa [show 2 * ((1249 * 1249) * 1249 * 4) = (1249 * 1249) * 1249 * 8 by ring] using h

lemma hB4 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 16) - B4 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 8) (U := B3) (V := B4) (Q := Qbstep3) hB3 hstepB3
  simpa [show 2 * ((1249 * 1249) * 1249 * 8) = (1249 * 1249) * 1249 * 16 by ring] using h

lemma hB5 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 32) - B5 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 16) (U := B4) (V := B5) (Q := Qbstep4) hB4 hstepB4
  simpa [show 2 * ((1249 * 1249) * 1249 * 16) = (1249 * 1249) * 1249 * 32 by ring] using h

lemma hB6 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 64) - B6 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 32) (U := B5) (V := B6) (Q := Qbstep5) hB5 hstepB5
  simpa [show 2 * ((1249 * 1249) * 1249 * 32) = (1249 * 1249) * 1249 * 64 by ring] using h

lemma hB7 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 128) - B7 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 64) (U := B6) (V := B7) (Q := Qbstep6) hB6 hstepB6
  simpa [show 2 * ((1249 * 1249) * 1249 * 64) = (1249 * 1249) * 1249 * 128 by ring] using h

lemma hB8 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 256) - B8 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 128) (U := B7) (V := B8) (Q := Qbstep7) hB7 hstepB7
  simpa [show 2 * ((1249 * 1249) * 1249 * 128) = (1249 * 1249) * 1249 * 256 by ring] using h

lemma hB9 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 512) - B9 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 256) (U := B8) (V := B9) (Q := Qbstep8) hB8 hstepB8
  simpa [show 2 * ((1249 * 1249) * 1249 * 256) = (1249 * 1249) * 1249 * 512 by ring] using h

lemma hB10 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249 * 1024) - B10 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 1249 * 512) (U := B9) (V := B10) (Q := Qbstep9) hB9 hstepB9
  simpa [show 2 * ((1249 * 1249) * 1249 * 512) = (1249 * 1249) * 1249 * 1024 by ring] using h

end LeanFormal.IUT.XiFPaper.S2597aBChainActual

end


end LeanFormal.IUT.XiFPaper.S2597a9BStepActual
end
