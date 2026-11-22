import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5

example : Nat.card GL2 = 480 := by
  rw [Matrix.card_GL_field (𝔽 := K5) (n := 2)]
  norm_num [ZMod.card]

