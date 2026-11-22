/- hbad target: coefficient-2 version => paper 2*d_mod version (d_mod >= 1, X >= 0).
   With primorial sQPaper (reading I), proving
     log sQ <= 2 * X   (X = Sum_{vQ} (localLogD_vQ + localLogF_vQ))
   yields log sQ <= 2 * d_mod * X since d_mod >= 1, X >= 0.
   No identification log d_Ftpd = Sum (1/p) log d_vQ is needed. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadPaperCoeffActual

/-- coeff2 => paper form: 2*X <= 2*dmod*X (1 <= dmod, 0 <= X). -/
theorem two_mul_le_two_dmod_mul (X dmod : ℝ) (hdmod : 1 ≤ dmod) (hX : 0 ≤ X) :
    2 * X ≤ 2 * dmod * X := by
  nlinarith [hdmod, hX]

/-- 由 coeff-2 界推出 paper 的 2 d_mod 界（X = 局部 d+f 之和）。 -/
theorem hbad_paper_of_coeff2 (logSQ X dmod : ℝ)
    (h2 : logSQ ≤ 2 * X) (hdmod : 1 ≤ dmod) (hX : 0 ≤ X) :
    logSQ ≤ 2 * dmod * X := by
  have h := two_mul_le_two_dmod_mul X dmod hdmod hX
  linarith

#print axioms two_mul_le_two_dmod_mul
#print axioms hbad_paper_of_coeff2

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadPaperCoeffActual
