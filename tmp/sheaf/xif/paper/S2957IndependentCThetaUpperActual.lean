import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2957IndependentCThetaUpperActual

/-- The procession-normalized theta upper expression (same linear expression as
S2919/S2933). -/
noncomputable def S2957ThetaUpper (n D Q S T : Real) : Real :=
  ((2 * n + 1) + 1) / 4 *
    ((1 + 4 / (2 * n + 1)) * D - Q / 6 +
      4 / (2 * n + 1) * S + 20 / 3 * T)

/-- Actual StepVProcessionAverage upper bound: the average of collectionBounds
is at most S2957ThetaUpper. -/
theorem S2957_processionAverage_le
    (n : Nat) (hn : 2 <= n) (D Q S T : Real)
    (hD : 0 <= D) (hS : 0 <= S) (hT : 0 <= T) :
    (1 / (n : Real)) *
        Finset.sum (Icc 1 n) (fun j => collectionBound (2 * (n : Real) + 1) D Q S T j)
      <= S2957ThetaUpper n D Q S T :=
  processionAverage_le n hn D Q S T hD hS hT

/-- Independent upper bound for CThetaPaper from the printed S2691 formula:
if the bracket is at most B and the paper factor is nonnegative, then
CThetaPaper is at most factor * B - 1. -/
theorem S2957_CThetaPaper_upper_of_bracket
    (l : PrimeGeFive) (logQ dmod dFpd fFpd eStar etaPrm B : Real)
    (hfac : 0 <= ((l.value : Real) + 1) / 4 / paperQAbsLog l logQ)
    (hB : cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm <= B) :
    CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm <=
      (((l.value : Real) + 1) / 4 / paperQAbsLog l logQ) * B - 1 := by
  unfold CThetaPaper
  have hmul := mul_le_mul_of_nonneg_left hB hfac
  linarith

/-- Same upper bound with the actual procession expression as B. -/
theorem S2957_CThetaPaper_upper_of_procession
    (l : PrimeGeFive) (n : Nat) (hn : 2 <= n)
    (logQ dmod dFpd fFpd eStar etaPrm D Q S T : Real)
    (hD : 0 <= D) (hS : 0 <= S) (hT : 0 <= T)
    (hfac : 0 <= ((l.value : Real) + 1) / 4 / paperQAbsLog l logQ)
    (hB : cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm <=
      S2957ThetaUpper n D Q S T) :
    CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm <=
      (((l.value : Real) + 1) / 4 / paperQAbsLog l logQ) *
        S2957ThetaUpper n D Q S T - 1 :=
  S2957_CThetaPaper_upper_of_bracket l logQ dmod dFpd fFpd eStar etaPrm
    (S2957ThetaUpper n D Q S T) hfac hB

#check S2957ThetaUpper
#check S2957_processionAverage_le
#check S2957_CThetaPaper_upper_of_bracket
#check S2957_CThetaPaper_upper_of_procession
#print axioms S2957_processionAverage_le
#print axioms S2957_CThetaPaper_upper_of_bracket

end LeanFormal.IUT.XiFPaper.S2957IndependentCThetaUpperActual
end