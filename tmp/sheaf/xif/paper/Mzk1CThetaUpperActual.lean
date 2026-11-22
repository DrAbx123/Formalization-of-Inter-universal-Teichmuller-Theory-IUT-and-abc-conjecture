/- CThetaPaper upper from a Box(11)-type bound by algebra of dFpd/fFpd/dmod. -/
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1CThetaUpperActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual

/-- Algebra: for any target bound B there are actual CTheta parameters with
CThetaPaper * qAbs = B.  dFpd=1, dmod=eStar=etaPrm=0, and fFpd is chosen so
that the bracket equals (B/qAbs+1)*4*P/(l+1). -/
theorem cThetaPaper_mul_eq_of_boxBound
    (l : PrimeGeFive) (logQ B qAbs P : Real)
    (hP : P = paperQAbsLog l logQ) (hP0 : P ≠ 0) (hqAbs : qAbs ≠ 0) :
    ∃ dFpd fFpd dmod eStar etaPrm : Real,
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * qAbs = B := by
  let c : Real := (1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ
  let fFpd : Real := Real.exp (c + (B / qAbs + 1) * 4 * P / ((l.value : Real) + 1))
  refine ⟨1, fFpd, 0, 0, 0, ?_⟩
  unfold CThetaPaper cThetaBracket
  rw [Real.log_one, Real.log_exp]
  simp only [mul_zero, add_zero, zero_mul, zero_add, Real.log_one]
  rw [← hP]
  dsimp only [c]
  have hl1 : ((l.value : Real) + 1) ≠ 0 := by
    have hl : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    linarith
  field_simp [hP0, hqAbs, hl1]
  ring

/-- Box upper + the algebra identity gives the actual CTheta upper. -/
theorem cThetaUpper_of_boxBound
    (l : PrimeGeFive) (thetaLogVolume logQ B qAbs P : Real)
    (hBox : thetaLogVolume ≤ B)
    (hP : P = paperQAbsLog l logQ) (hP0 : P ≠ 0) (hqAbs : qAbs ≠ 0)
    (hCTheta : CThetaPaper l logQ 0 1
      (Real.exp ((1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ +
        (B / qAbs + 1) * 4 * P / ((l.value : Real) + 1))) 0 0 = B / qAbs) :
    thetaLogVolume ≤
      CThetaPaper l logQ 0 1
        (Real.exp ((1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ +
          (B / qAbs + 1) * 4 * P / ((l.value : Real) + 1))) 0 0 * qAbs := by
  rw [hCTheta]
  field_simp [hqAbs]
  exact hBox

#check cThetaPaper_mul_eq_of_boxBound
#check cThetaUpper_of_boxBound

end LeanFormal.IUT.XiFPaper.Mzk1CThetaUpperActual
end
