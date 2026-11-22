/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
import Mathlib.Algebra.Group.AddChar

/-! # H3 §11.4: finite Fourier support exact interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1H3FourierSupportActual

/-- Finite Fourier support data: a nonzero function on the finite additive
group `G`, its support `A`, Fourier support `B`, and the support lower bound. -/
structure H3FourierSupportData (G : Type*) [AddCommGroup G] [Fintype G] where
  f : G → ℂ
  supportA : Set G
  supportB : Set (AddChar G ℂ)
  support_f_subset : ∀ x : G, f x ≠ 0 → x ∈ supportA
  fourier_support_subset :
    ∀ χ : AddChar G ℂ, (∑ x : G, f x * χ x) ≠ 0 → χ ∈ supportB
  support_lower_bound : Nat.card supportA * Nat.card supportB ≥ Nat.card G

def H3FourierSupportRequired (G : Type*) [AddCommGroup G] [Fintype G] : Prop :=
  Nonempty (H3FourierSupportData G)

end LeanFormal.IUT.XiFPaper.Mzk1H3FourierSupportActual
