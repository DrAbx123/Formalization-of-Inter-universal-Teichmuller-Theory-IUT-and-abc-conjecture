import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exponential

#check @Real.pi_gt_three
#check @Real.pi_gt_three
#check @Real.three_lt_pi
#check @Real.pi_gt_d20
#check @Real.one_lt_pi
#check @Real.pi_pos
#check @Real.add_one_le_exp
#check @Real.exp_pos
#check @Real.le_exp
#check @Real.lt_exp
#check @Real.exp_lt_exp
example : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
example : (2:ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
example : Real.pi < Real.exp Real.pi := by
  have h := Real.add_one_le_exp Real.pi
  linarith [Real.pi_gt_three]
