import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1LaichunwingLogUnitBoundsGlueActual — arithmetic glue from the mined Unit C

Small arithmetic module (no new mathematics): transcribes the *numerical* content of the
independent verification script `03_log_unit_bounds` (laichunwing, IUT-Verification):
the IUT IV Prop 1.2(i) upper-bound coefficient `b = 1 - 1/e` for `e = 1, 2`, and its
relation to the Prop 1.4(ii) log-volume coefficient.  Pure real arithmetic.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LaichunwingLogUnitBoundsGlueActual

/-- The Unit C upper-bound coefficient `b = 1 - 1/e`. -/
noncomputable def logUnitUpperCoefficient (e : Nat) : Real :=
  1 - (1 : Real) / (e : Real)

/-- The Unit C lower-radius exponent `k = ceil(e/(p-2))` (recorded as the real value). -/
noncomputable def logUnitLowerExponent (e p : Nat) : Real :=
  (e : Real) / ((p : Real) - 2)

/-- Nonnegativity of `b` for `e ≥ 1`. -/
theorem logUnitUpperCoefficient_nonneg {e : Nat} (he : 0 < e) :
    0 <= logUnitUpperCoefficient e := by
  unfold logUnitUpperCoefficient
  have heR : (1 : Real) <= (e : Real) := by exact_mod_cast he
  have h : (1 : Real) / (e : Real) <= 1 := by
    rw [div_le_one (by linarith)]
    exact heR
  linarith

/-- Unramified case `e = 1`: `b = 0` (the `pℤ_p` radius). -/
theorem logUnitUpperCoefficient_unramified :
    logUnitUpperCoefficient 1 = 0 := by
  unfold logUnitUpperCoefficient
  norm_num

/-- Tame ramified case `e = 2`: `b = 1/2` (the `Q_11(√11)` sample of Unit C). -/
theorem logUnitUpperCoefficient_quadratic :
    logUnitUpperCoefficient 2 = 1 / 2 := by
  unfold logUnitUpperCoefficient
  norm_num

/-- The Unit K coefficient is the negative lower-radius coefficient at `m = 0`. -/
theorem logVolumeCoefficient_at_m_zero (e : Nat) (he : 0 < e) :
    -(1 / (e : Real)) = -(1 - logUnitUpperCoefficient e) := by
  unfold logUnitUpperCoefficient
  ring

/-- Unit C boundary comparison at `p = 11`, `e = 2`: coefficient `1/2` multiplies log 11. -/
theorem logUnitUpperCoefficient_quadratic_mul_log_eleven :
    logUnitUpperCoefficient 2 * Real.log (11 : Real) =
      (1 / 2 : Real) * Real.log (11 : Real) := by
  rw [logUnitUpperCoefficient_quadratic]

#check logUnitUpperCoefficient
#check logUnitUpperCoefficient_nonneg
#check logUnitUpperCoefficient_unramified
#check logUnitUpperCoefficient_quadratic
#check logVolumeCoefficient_at_m_zero

end LeanFormal.IUT.XiFPaper.Mzk1LaichunwingLogUnitBoundsGlueActual
end
