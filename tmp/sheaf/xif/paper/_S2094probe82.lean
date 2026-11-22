import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section

def f : (ZMod 29)[X] := X^10 + 1

example (hf : f.Monic) (hdeg : f.natDegree = 10) : CharP (AdjoinRoot f) 29 := by
  have hdeg0 : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf.ne_zero, hdeg]
    norm_num
  have hinj : Function.Injective (algebraMap (ZMod 29) (AdjoinRoot f)) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg0
  exact charP_of_injective_algebraMap hinj 29
