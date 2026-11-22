/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Frobenius picture: permutation-group laws for graph automorphisms -/

namespace LeanFormal.IUT.XiFPaper.PermGroupLawsActual

variable {α : Type*}

theorem perm_pow_succ (sigma : Equiv.Perm α) (n : Nat) :
    sigma ^ (n + 1) = sigma ^ n * sigma := pow_succ sigma n

theorem perm_pow_succ' (sigma : Equiv.Perm α) (n : Nat) :
    sigma ^ (n + 1) = sigma * sigma ^ n := pow_succ' sigma n

theorem perm_inv_mul_cancel (sigma : Equiv.Perm α) : sigma⁻¹ * sigma = 1 := 
  inv_mul_cancel sigma

theorem perm_mul_inv_cancel (sigma : Equiv.Perm α) : sigma * sigma⁻¹ = 1 := 
  mul_inv_cancel sigma

theorem perm_inv_inv' (sigma : Equiv.Perm α) : sigma⁻¹⁻¹ = sigma := inv_inv sigma

theorem perm_pow_two (sigma : Equiv.Perm α) : sigma ^ 2 = sigma * sigma := pow_two sigma

theorem perm_pow_three (sigma : Equiv.Perm α) : sigma ^ 3 = sigma * sigma * sigma := by
  rw [show (3 : Nat) = 2 + 1 by norm_num, pow_add, perm_pow_two]
  rfl

end LeanFormal.IUT.XiFPaper.PermGroupLawsActual
