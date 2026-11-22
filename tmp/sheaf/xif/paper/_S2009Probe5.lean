import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5

#check @Equiv.Perm.mul_apply
#check @Equiv.Perm.coe_mul
#check @Matrix.GeneralLinearGroup.val_mkOfDetNeZero
#check @Matrix.GeneralLinearGroup.mkOfDetNeZero
example (g : GL2) : ((g : Matrix (Fin 2) (Fin 2) K5)) = g.1 := rfl
example (A : Matrix (Fin 2) (Fin 2) K5) (h : A.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero A h : GL2) : Matrix (Fin 2) (Fin 2) K5) = A := rfl
example : (Equiv.swap (10 : Fin 12) (11 : Fin 12) * Equiv.swap (10 : Fin 12) (11 : Fin 12)) = 1 := by decide
example (x : Fin 12) : ((Equiv.swap (10 : Fin 12) (11 : Fin 12) * Equiv.swap (10 : Fin 12) (11 : Fin 12)) x) = x := by simp
