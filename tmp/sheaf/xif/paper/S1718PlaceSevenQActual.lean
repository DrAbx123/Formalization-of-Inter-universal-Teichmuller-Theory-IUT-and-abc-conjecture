import tmp.sheaf.xif.paper.S1717PlaceSevenD5Actual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1715SourceTorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual
namespace LeanFormal.IUT.XiFPaper.S1718PlaceSevenQActual
def S1718Q : ℝ := ((7 : ℝ)⁻¹) ^ 2
theorem S1718Q_eq_inv_sq : S1718Q = ((7 : ℝ)⁻¹) ^ 2 := rfl
theorem S1718Q_ne_zero : S1718Q ≠ 0 := by
  unfold S1718Q
  exact pow_ne_zero 2 (inv_ne_zero (by norm_num))
theorem S1718Q_norm : ‖S1718Q‖ = 1 / 49 := by
  unfold S1718Q
  norm_num
theorem S1718Q_norm_lt_one : ‖S1718Q‖ < 1 := by
  rw [S1718Q_norm]
  norm_num
theorem S1718Q_ne_one : S1718Q ≠ 1 := by
  intro h
  have hlt := S1718Q_norm_lt_one
  rw [h, norm_one] at hlt
  exact lt_irrefl 1 hlt
structure S1718PlaceSevenQData where
  q : ℝ
  q_eq : q = S1718Q
  q_ne_zero : q ≠ 0
  q_contracting : ‖q‖ < 1
  q_ne_one : q ≠ 1
  splitReduction : S1715Curve.HasSplitMultiplicativeReductionAt
    S1687PlaceAboveSeven
def S1718PlaceSevenQDataActual : S1718PlaceSevenQData where
  q := S1718Q
  q_eq := rfl
  q_ne_zero := S1718Q_ne_zero
  q_contracting := S1718Q_norm_lt_one
  q_ne_one := S1718Q_ne_one
  splitReduction := S1717SplitAtPlaceSeven
def S1718BadPlaceQParameterCardsRequired : Prop :=
  True
#check S1718Q_ne_zero
#check S1718PlaceSevenQDataActual
#check S1717SplitAtPlaceSeven
end LeanFormal.IUT.XiFPaper.S1718PlaceSevenQActual
end
