import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section

def f : (ZMod 29)[X] := X^10 + 1

example : CharP (AdjoinRoot f) 29 := inferInstance
example : Algebra (ZMod 29) (AdjoinRoot f) := inferInstance
