import Mathlib

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Laichunwing Unit M: global IUT inequality for 11a1 at l = 13

The explicit numeric instance of [IUT IV] Theorem 1.10 used in
`13_global_iut_inequality.txt`: deg(q)=5 log 11, deg(f)=log 11,
deg(d)=0, d_mod=1, e_mod=1, e_mod* = 2^12*3^3*5. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LaichunwingGlobalInequalityActual

/-- The explicit constant `e_mod* = 2^12 * 3^3 * 5 * e_mod` at `e_mod = 1`. -/
def eModStar : Nat := 2 ^ 12 * 3 ^ 3 * 5

theorem eModStar_eq : eModStar = 552960 := by
  norm_num [eModStar]

theorem global_iut_inequality_11a1 :
    (1 / 6 : Real) * (5 * Real.log 11) ≤=
      (1 + 20 * (1 : Real) / 13) * (0 + Real.log 11) +
        20 * (eModStar : Real) * 13 := by
  have hlog : 0 ≤ Real.log 11 := Real.log_nonneg (by norm_num)
  have hE : (eModStar : Real) = 552960 := by exact_mod_cast eModStar_eq
  rw [hE]
  nlinarith [hlog]

end LeanFormal.IUT.XiFPaper.Mzk1LaichunwingGlobalInequalityActual

end
