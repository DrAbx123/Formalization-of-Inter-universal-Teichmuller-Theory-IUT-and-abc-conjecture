import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual

namespace LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual

/-- The paper CTheta, with the correct factor (l+1)/(4*|log q|). -/
def CThetaPaper (l : PrimeGeFive)
    (logQ dmod dFpd fFpd eStar etaPrm : Real) : Real :=
  (((l.value : Real) + 1) / 4 / paperQAbsLog l logQ) *
    cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm - 1

theorem CThetaPaper_def_eq (l : PrimeGeFive)
    (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm =
      (((l.value : Real) + 1) / 4 / paperQAbsLog l logQ) *
        cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm - 1 := rfl

/-- Correct-scale factor is positive for |log q| > 0. -/
theorem cThetaPaperFactor_pos (l : PrimeGeFive) {logQ : Real} (hlogQ : 0 < logQ) :
    0 < ((l.value : Real) + 1) / 4 / paperQAbsLog l logQ := by
  have hA : 0 < paperQAbsLog l logQ := paperQAbsLog_pos l hlogQ
  have hl : (0 : Real) ≤ (l.value : Real) := by exact_mod_cast Nat.zero_le l.value
  have h1 : (0 : Real) < ((l.value : Real) + 1) / 4 := by linarith
  exact div_pos h1 hA

/-- Exact algebraic relation to the old S2691 CTheta: the old formula
multiplies by |log q|, so it differs by the square of |log q|. -/
theorem CThetaPaper_eq_S2691CTheta_scale
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hA : paperQAbsLog l logQ ≠ 0) :
    CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm =
      (CTheta l logQ dmod dFpd fFpd eStar etaPrm + 1) /
        (paperQAbsLog l logQ) ^ 2 - 1 := by
  unfold CThetaPaper CTheta
  field_simp [hA]
  ring

/-- Paper-scale bracket equivalence: CThetaPaper >= -1 iff the bracket
inequality of IUT IV Theorem 1.10 holds. -/
theorem CThetaPaper_ge_neg_one_iff
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hlogQ : 0 < logQ) :
    -1 ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm ↔
      (1 / 6) * (1 - 12 / ((l.value : Real)) ^ 2) * logQ ≤
        (1 + 12 * dmod / (l.value : Real)) *
            (Real.log dFpd + Real.log fFpd) +
          10 * (eStar * (l.value : Real) + etaPrm) := by
  have hfac := cThetaPaperFactor_pos l hlogQ
  have hdef := CThetaPaper_def_eq l logQ dmod dFpd fFpd eStar etaPrm
  constructor
  · intro h
    rw [hdef] at h
    have h0 : 0 ≤ (((l.value : Real) + 1) / 4 /
        paperQAbsLog l logQ) *
        cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm := by
      linarith
    have hb : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm :=
      (mul_nonneg_iff_of_pos_left hfac).mp h0
    unfold cThetaBracket at hb
    linarith
  · intro hb
    have hb' : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm := by
      unfold cThetaBracket
      linarith
    rw [hdef]
    have h0 : 0 ≤ (((l.value : Real) + 1) / 4 /
        paperQAbsLog l logQ) *
        cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm :=
      mul_nonneg (le_of_lt hfac) hb'
    linarith

/-- Consumer interface with the actual Step (xi-f) arithmetic: from the paper
upper bound and the ray inclusion, conclude -1 <= CThetaPaper. -/
theorem CThetaPaper_lowerBound_of_thetaHull_upper
    {thetaLogVolume qParameter : Real}
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ thetaLogVolume)
    (hupper : thetaLogVolume ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm *
      |Real.log qParameter|) :
    -1 ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm :=
  cor312CThetaLowerBound hq hincl hupper

/-- Same consumer, stated with the paper normalized |log q| explicitly. -/
theorem CThetaPaper_lowerBound_of_paperAbsLog
    {thetaLogVolume qParameter : Real}
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ thetaLogVolume)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hupper : thetaLogVolume ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm *
      paperQAbsLog l logQ) :
    -1 ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm :=
  CThetaPaper_lowerBound_of_thetaHull_upper hq hincl (by rwa [habs])

#check CThetaPaper
#check CThetaPaper_eq_S2691CTheta_scale
#check CThetaPaper_ge_neg_one_iff
#check CThetaPaper_lowerBound_of_thetaHull_upper
#check CThetaPaper_lowerBound_of_paperAbsLog
#print axioms CThetaPaper_eq_S2691CTheta_scale
#print axioms CThetaPaper_ge_neg_one_iff
#print axioms CThetaPaper_lowerBound_of_thetaHull_upper
#print axioms CThetaPaper_lowerBound_of_paperAbsLog

end LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
end
