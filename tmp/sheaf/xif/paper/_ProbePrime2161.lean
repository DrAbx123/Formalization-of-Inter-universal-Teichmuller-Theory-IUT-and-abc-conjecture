import Mathlib.Tactic
set_option maxRecDepth 100000
example : Nat.Prime 2161 := by norm_num [Nat.Prime]
