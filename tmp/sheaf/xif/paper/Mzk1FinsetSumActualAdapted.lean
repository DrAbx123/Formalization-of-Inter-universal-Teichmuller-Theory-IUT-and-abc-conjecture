/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: Finset-sum laws for strip degrees -/

namespace LeanFormal.IUT.XiFPaper.FinsetSumActual

open BigOperators

variable {ι : Type*} {α : Type*} [AddCommMonoid α]

theorem sum_singleton' (f : ι → α) (i : ι) : ∑ j in ({i} : Finset ι), f j = f i :=
  Finset.sum_singleton

theorem sum_insert' {s : Finset ι} {i : ι} (hi : i ∉ s) (f : ι → α) :
    ∑ j in insert i s, f j = f i + ∑ j in s, f j := Finset.sum_insert hi

theorem sum_zero' (s : Finset ι) : ∑ _j in s, (0 : α) = 0 := Finset.sum_const_zero

theorem sum_congr' (s : Finset ι) {f g : ι → α} (h : ∀ j ∈ s, f j = g j) :
    ∑ j in s, f j = ∑ j in s, g j := Finset.sum_congr rfl h

theorem sum_le_sum' (s : Finset ι) {f g : ι → α} [PartialOrder α] [IsOrderedAddMonoid α]
    (h : ∀ j ∈ s, f j ≤ g j) : ∑ j in s, f j ≤ ∑ j in s, g j := Finset.sum_le_sum h

end LeanFormal.IUT.XiFPaper.FinsetSumActual
