/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FrobeniusGraphAutClosureActual

/-! # Reuse: corollaries of the graph-automorphism closure laws -/

namespace LeanFormal.IUT

theorem frobeniusPictureGraphAut_inv_inv {sigma : Equiv.Perm Int}
    (h : FrobeniusPictureGraphAut sigma) : FrobeniusPictureGraphAut sigma⁻¹⁻¹ := by
  simpa using h

theorem frobeniusPictureGraphAut_pow_two {sigma : Equiv.Perm Int}
    (h : FrobeniusPictureGraphAut sigma) : FrobeniusPictureGraphAut (sigma ^ 2) :=
  FrobeniusPictureGraphAut_pow h 2

theorem frobeniusPictureGraphAut_pow_succ {sigma : Equiv.Perm Int}
    (h : FrobeniusPictureGraphAut sigma) (n : Nat) :
    FrobeniusPictureGraphAut (sigma ^ (n + 1)) :=
  FrobeniusPictureGraphAut_pow h (n + 1)

theorem frobeniusPictureGraphAut_mul_left {sigma tau : Equiv.Perm Int}
    (h1 : FrobeniusPictureGraphAut sigma) (h2 : FrobeniusPictureGraphAut tau) :
    FrobeniusPictureGraphAut (tau * sigma) :=
  FrobeniusPictureGraphAut_mul h2 h1

theorem frobeniusPictureGraphAut_inv_iff {sigma : Equiv.Perm Int} :
    FrobeniusPictureGraphAut sigma⁻¹ ↔ FrobeniusPictureGraphAut sigma := 
  ⟨fun h => by simpa using FrobeniusPictureGraphAut_inv h, FrobeniusPictureGraphAut_inv⟩

end LeanFormal.IUT
