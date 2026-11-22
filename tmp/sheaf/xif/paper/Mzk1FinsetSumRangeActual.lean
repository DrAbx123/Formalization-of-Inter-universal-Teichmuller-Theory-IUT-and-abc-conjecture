/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: sum over initial ranges -/

namespace LeanFormal.IUT.XiFPaper.FinsetSumRangeActual

open BigOperators

theorem sum_range_succ' (f : Nat → Nat) (n : Nat) :
    (∑ i in Finset.range (n + 1), f i) = (∑ i in Finset.range n, f i) + f n :=
  Finset.sum_range_succ f n

theorem sum_range_zero' (f : Nat → Nat) : (∑ i in Finset.range 0, f i) = 0 := by
  simp

theorem sum_range_one' (f : Nat → Nat) : (∑ i in Finset.range 1, f i) = f 0 := by
  simp

end LeanFormal.IUT.XiFPaper.FinsetSumRangeActual
