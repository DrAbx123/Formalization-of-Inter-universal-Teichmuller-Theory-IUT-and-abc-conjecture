import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual

/-! # Paper target non-vacuity checks -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperNonvacuityActual

open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual

/-- The paper target is reflexive in the equal-magnitude case. -/
theorem paperTarget_equal (m : Real) : paperTarget m m := by
  unfold paperTarget paperSignedQ paperSignedTheta
  exact le_rfl

/-- The target is not a tautology: unequal magnitudes in the wrong direction fail. -/
theorem paperTarget_zero_one_false : ¬ paperTarget 0 1 := by
  unfold paperTarget paperSignedQ paperSignedTheta
  norm_num

/-- Magnitude check: `|Theta| > |q|` violates the target (paper direction). -/
theorem paperTarget_one_two_false : ¬ paperTarget 1 2 := by
  unfold paperTarget paperSignedQ paperSignedTheta
  norm_num

/-- Correct paper direction: `|Theta| ≤ |q|` gives the target. -/
theorem paperTarget_one_two_true_when_reversed : paperTarget 2 1 := by
  unfold paperTarget paperSignedQ paperSignedTheta
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperNonvacuityActual
