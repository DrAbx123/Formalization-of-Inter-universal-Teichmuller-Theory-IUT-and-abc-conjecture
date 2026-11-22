/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction

/-! # Frobenius-picture graph automorphisms: group closure -/

namespace LeanFormal.IUT

theorem FrobeniusPictureGraphAut_inv {sigma : Equiv.Perm Int}
    (h : FrobeniusPictureGraphAut sigma) : FrobeniusPictureGraphAut sigma⁻¹ := by
  intro n m
  have hh := h (sigma⁻¹ n) (sigma⁻¹ m)
  simpa using hh.symm

theorem FrobeniusPictureGraphAut_mul {sigma tau : Equiv.Perm Int}
    (h1 : FrobeniusPictureGraphAut sigma) (h2 : FrobeniusPictureGraphAut tau) :
    FrobeniusPictureGraphAut (sigma * tau) := by
  intro n m
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [h2 n m, h1 (tau n) (tau m)]

theorem FrobeniusPictureGraphAut_pow {sigma : Equiv.Perm Int}
    (h : FrobeniusPictureGraphAut sigma) (n : Nat) :
    FrobeniusPictureGraphAut (sigma ^ n) := by
  induction n with
  | zero => simpa using graphAut_one
  | succ k ih =>
      rw [pow_succ]
      exact FrobeniusPictureGraphAut_mul ih h

end LeanFormal.IUT
-- force-fresh-recompile
