import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4HeightRegionNumericsActual (stage4 lane; unique filename)

A572 module: stage4-lane numeric content of the ABC height-region stage (mined
laichunwing Unit M, IUT IV Theorem 1.10 instance for 11a1 at l = 13): the curve
invariants, the constant `e_mod^* = 2^12 * 3^3 * 5 = 552960`, and the numeric
Theorem 1.10 inequality.  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual

/-- The l = 13 height-region constant `e_mod^* = 2^12 * 3^3 * 5`. -/
def eModStar : Nat := 2 ^ 12 * 3 ^ 3 * 5

/-- Numeric value `e_mod^* = 552960`. -/
theorem eModStar_eq : eModStar = 552960 := by
  unfold eModStar
  norm_num

/-- The 11a1 height-region data at p = 11, l = 13: q-degree `5 log 11`. -/
noncomputable def degQ11 : Real := 5 * Real.log (11 : Real)

/-- The conductor degree at p = 11: `log 11`. -/
noncomputable def degF11 : Real := Real.log (11 : Real)

/-- The different degree over Q: `0`. -/
noncomputable def degD11 : Real := 0

/-- The l = 13 modular degrees: `d_mod = 1`, `e_mod = 1`. -/
def dMod : Nat := 1
def eMod : Nat := 1

/-- The numeric Theorem 1.10 right-hand side for 11a1 at l = 13. -/
noncomputable def theorem110RHS : Real :=
  (1 + 20 * (dMod : Real) / 13) * (degD11 + degF11) +
    20 * (eModStar : Real) * 13

/-- The log-bound used for the numeric comparison: `log 11 < 11`. -/
theorem log_eleven_bound : Real.log (11 : Real) < 11 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 11 by norm_num)
  linarith

/-- The numeric Theorem 1.10 inequality for 11a1 at l = 13:
`(1/6) deg q <= (1 + 20 d_mod/l)(deg d + deg f) + 20 e_mod^* l`. -/
theorem theorem110_11a1_l13 :
    (1 / 6 : Real) * degQ11 <= theorem110RHS :=
  by
  have hlog := log_eleven_bound
  have hlog0 : (0 : Real) <= Real.log (11 : Real) :=
    Real.log_nonneg (by norm_num)
  unfold degQ11 theorem110RHS degD11 degF11 dMod eModStar
  norm_num
  nlinarith

#check eModStar
#check eModStar_eq
#check degQ11
#check theorem110RHS
#check log_eleven_bound
#check theorem110_11a1_l13

end LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual
end
