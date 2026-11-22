import tmp.sheaf.xif.paper.Mzk1LaichunwingLogUnitBoundsGlueActual

/-! # Mzk1LogUnitCoefficientConsumerGlueActual — consumer inequalities for Unit C coefficients

Small glue module (no new mathematics): derives monotonicity/bounds for the IUT IV
Prop 1.2(i) upper-bound coefficient `b = 1 - 1/e` from the arithmetic already proved in
`Mzk1LaichunwingLogUnitBoundsGlueActual`.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogUnitCoefficientConsumerGlueActual

open LeanFormal.IUT.XiFPaper.Mzk1LaichunwingLogUnitBoundsGlueActual

/-- `b < 1` for every `e ≥ 1`. -/
theorem logUnitUpperCoefficient_lt_one {e : Nat} (he : 0 < e) :
    logUnitUpperCoefficient e < 1 := by
  unfold logUnitUpperCoefficient
  have heR : (0 : Real) < (e : Real) := by exact_mod_cast he
  have h : (0 : Real) < (1 : Real) / (e : Real) := div_pos one_pos heR
  linarith

/-- Monotonicity of `b` in `e`: larger ramification index gives a larger upper bound. -/
theorem logUnitUpperCoefficient_le_of_le {e e' : Nat} (he : 0 < e) (hee' : e <= e') :
    logUnitUpperCoefficient e <= logUnitUpperCoefficient e' := by
  unfold logUnitUpperCoefficient
  have heR : (0 : Real) < (e : Real) := by exact_mod_cast he
  have heR' : (0 : Real) < (e' : Real) := by exact_mod_cast (lt_of_lt_of_le he hee')
  have hle : (e : Real) <= (e' : Real) := by exact_mod_cast hee'
  have h : (1 : Real) / (e' : Real) <= (1 : Real) / (e : Real) :=
    one_div_le_one_div_of_le heR hle
  linarith

/-- At `e = 2` the coefficient is `1/2` and hence is strictly positive. -/
theorem logUnitUpperCoefficient_quadratic_pos :
    0 < logUnitUpperCoefficient 2 := by
  rw [logUnitUpperCoefficient_quadratic]
  norm_num

/-- The tame case `e = 2` dominates the unramified case. -/
theorem logUnitUpperCoefficient_unramified_le_quadratic :
    logUnitUpperCoefficient 1 <= logUnitUpperCoefficient 2 := by
  rw [logUnitUpperCoefficient_unramified, logUnitUpperCoefficient_quadratic]
  norm_num

#check logUnitUpperCoefficient_lt_one
#check logUnitUpperCoefficient_le_of_le
#check logUnitUpperCoefficient_quadratic_pos
#check logUnitUpperCoefficient_unramified_le_quadratic

end LeanFormal.IUT.XiFPaper.Mzk1LogUnitCoefficientConsumerGlueActual
end
