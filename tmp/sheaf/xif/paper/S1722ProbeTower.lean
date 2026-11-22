import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Perfect

noncomputable section
open Polynomial

namespace ProbeTower

example : let L := AlgebraicClosure ℚ
    let x : L := Classical.choose (IsAlgClosed.exists_pow_nat_eq (-1 : L) (by norm_num : 0 < 2))
    let K0 : IntermediateField ℚ L := ⊥
    let K1 : IntermediateField ℚ L := (IntermediateField.adjoin K0 {x}).restrictScalars ℚ
    Module.finrank K0 K1 = Module.finrank K0 (IntermediateField.adjoin K0 {x}) := by
  intro L x K0 K1
  rfl

example : let L := AlgebraicClosure ℚ
    let x : L := Classical.choose (IsAlgClosed.exists_pow_nat_eq (-1 : L) (by norm_num : 0 < 2))
    let K0 : IntermediateField ℚ L := ⊥
    let K1 : IntermediateField ℚ L := (IntermediateField.adjoin K0 {x}).restrictScalars ℚ
    Module.finrank ℚ K1 = Module.finrank ℚ K0 * Module.finrank K0 K1 := by
  intro L x K0 K1
  exact Module.finrank_mul_finrank ℚ K0 K1

end ProbeTower
