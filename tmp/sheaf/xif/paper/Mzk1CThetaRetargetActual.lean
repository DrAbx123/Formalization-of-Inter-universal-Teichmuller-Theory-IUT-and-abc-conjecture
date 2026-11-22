import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.S2714CThetaUpperInventoryActual
import Mathlib.Tactic

/-!
# A1046: retarget the CTheta scalar upper from CThetaPaper to paper CTheta

The current hscalar target uses CThetaPaper * paperQAbsLog, while the paper
CTheta is S2691.CTheta.  This file proves the conditional comparison

  CThetaPaper * A ≤ CTheta * A   when 1 ≤ A and 0 ≤ B,

and uses it to turn an upper with CThetaPaper * A into the paper upper with
CTheta * A.  The lower-bound consumer S2714_cThetaLowerBound_of_upper then gives
-1 ≤ CTheta.

No fake equality CThetaPaper = CTheta is asserted.  The comparison is false in
general; the hypotheses 1 ≤ A and 0 ≤ B are essential.
-/

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual

/-- Conditional comparison: CThetaPaper * A ≤ CTheta * A for 1 ≤ A, 0 ≤ B. -/
theorem CThetaPaper_mul_A_le_CTheta_mul_A
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm *
        paperQAbsLog l logQ ≤
      CTheta l logQ dmod dFpd fFpd eStar etaPrm *
        paperQAbsLog l logQ := by
  let A : Real := paperQAbsLog l logQ
  let B : Real := cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hfac : 0 ≤ ((l.value : Real) + 1) / 4 := by positivity
  have hdiff : CTheta l logQ dmod dFpd fFpd eStar etaPrm * A -
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * A =
      ((l.value : Real) + 1) / 4 * B * (A ^ 2 - 1) := by
    unfold CTheta CThetaPaper
    field_simp [hApos.ne']
    ring
  have hnonneg : 0 ≤ ((l.value : Real) + 1) / 4 * B * (A ^ 2 - 1) := by
    have hA2 : 0 ≤ A ^ 2 - 1 := by
      nlinarith [hA]
    exact mul_nonneg (mul_nonneg hfac hB) hA2
  nlinarith

/-- An upper with CThetaPaper * A implies the paper upper with CTheta * A,
under the same hypotheses. -/
theorem upper_CTheta_of_upper_CThetaPaper
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {thetaLogVolume : Real}
    (hupper : thetaLogVolume ≤
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm *
        paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    thetaLogVolume ≤
      CTheta l logQ dmod dFpd fFpd eStar etaPrm *
        paperQAbsLog l logQ :=
  hupper.trans (CThetaPaper_mul_A_le_CTheta_mul_A l logQ dmod dFpd fFpd eStar etaPrm hA hB)

/-- The lower-bound consumer: a CThetaPaper upper plus the q-ray inclusion and
the normalization |log q| = A yields -1 ≤ CTheta (paper constant). -/
theorem CTheta_ge_neg_one_of_upper_CThetaPaper
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    {thetaLogVolume qParameter : Real}
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| ≤ thetaLogVolume)
    (habs : |Real.log qParameter| = paperQAbsLog l logQ)
    (hupper : thetaLogVolume ≤
      CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm *
        paperQAbsLog l logQ)
    (hA : 1 ≤ paperQAbsLog l logQ)
    (hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm) :
    -1 ≤ CTheta l logQ dmod dFpd fFpd eStar etaPrm := by
  apply S2714_cThetaLowerBound_of_upper hq hincl
  rw [habs]
  exact upper_CTheta_of_upper_CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm hupper hA hB

end LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual
