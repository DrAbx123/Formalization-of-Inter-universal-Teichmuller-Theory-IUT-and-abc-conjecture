/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # IUT 3.12 target: typed abc statement interface (paper layer) -/

namespace LeanFormal.IUT.XiFPaper.PaperTargetStatementsActual

/-- The radical of a natural number: product of the distinct prime factors. -/
def radical (n : Nat) : Nat := (n.primeFactors).prod (fun p => p)

@[simp] theorem radical_zero : radical 0 = 1 := by
  simp [radical]

theorem radical_pos (n : Nat) : 0 < radical n := by
  unfold radical
  exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)

/-- The abc conjecture statement (typed, as the IUT 3.12 target conclusion shape). -/
def ABCConjectureStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : Nat, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (a : ℝ) ≤ C * ((radical (a * b * c) : Nat) : ℝ) ^ (1 + ε)

/-- The IUT 3.12 conclusion shape: a universal bound with the given constant. -/
def Cor312BoundShape (C : ℝ) : Prop :=
  0 < C ∧ ∀ a b c : Nat, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (a : ℝ) ≤ C * ((radical (a * b * c) : Nat) : ℝ)

theorem cor312BoundShape_pos {C : ℝ} (h : Cor312BoundShape C) : 0 < C := h.1

theorem abc_of_cor312_forall :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, Cor312BoundShape C) → ABCConjectureStatement :=
  fun h ε hε => h ε hε

end LeanFormal.IUT.XiFPaper.PaperTargetStatementsActual
