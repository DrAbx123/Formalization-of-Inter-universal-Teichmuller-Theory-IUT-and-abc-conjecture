/-
S2009 probe 1: basic APIs for GL_2(F_5), pairs, cycle type.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix

namespace S2009Probe1

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev V2 := Fin 2 → K5

#synth Field K5
#synth NoZeroDivisors K5

example : Function.Surjective (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)) :=
  Matrix.GeneralLinearGroup.det_surjective

example (g : GL2) (v : V2) (hv : v ≠ 0) : (g : Matrix (Fin 2) (Fin 2) K5) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  exact Matrix.eq_zero_of_mulVec_eq_zero (Matrix.GeneralLinearGroup.det_ne_zero g) h

-- test GL action notation
example (g : GL2) (v : V2) : g • v = (g : Matrix (Fin 2) (Fin 2) K5) *ᵥ v := by
  rfl

-- field computations
example : ((2 : K5) + 3) = 0 := by norm_num
example : (5 : K5) = 0 := by norm_num

end S2009Probe1
