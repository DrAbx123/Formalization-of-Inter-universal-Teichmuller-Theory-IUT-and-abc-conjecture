import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section

def f : (ZMod 29)[X] := X^10 + 1

example (hf : f.Monic) (hdeg : f.natDegree = 10) : CharP (AdjoinRoot f) 29 := by
  haveI : Nontrivial (AdjoinRoot f) := by
    apply AdjoinRoot.nontrivial (R := ZMod 29) (f := f)
    rw [degree_eq_natDegree hf.ne_zero, hdeg]
    norm_num
  rw [CharP.charP_iff_prime_eq_zero (by norm_num)]
  change (algebraMap (ZMod 29) (AdjoinRoot f)) (29 : ZMod 29) = 0
  rw [show (29 : ZMod 29) = 0 by norm_num, map_zero]
