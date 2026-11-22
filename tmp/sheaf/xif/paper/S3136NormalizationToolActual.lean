import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-! # Generic finite-weight normalization tools

Reusable tools for normalized finite weight families: for a finite nonempty
family with positive real weights, the normalized weights (weight divided by
the total) are positive and sum to one, and pointwise equality of two raw
families gives pointwise equality (and equal total readings) of the normalized
families.  Generic, fully proved; consumers supply the instantiation.

TOOL: no Stage-4 data; instantiations are separate. -/

open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.NormalizationToolActual

variable {α : Type*} [Fintype α]

/-- The normalized positive weights of a finite nonempty family sum to one. -/
theorem sum_normalized_eq_one (w : α → ℝ) [Nonempty α] (hpos : ∀ a, 0 < w a) :
    (∑ a, w a / (∑ a, w a)) = 1 := by
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty))

/-- Each normalized weight of a finite nonempty positive family is positive. -/
theorem normalized_pos (w : α → ℝ) [Nonempty α] (hpos : ∀ a, 0 < w a)
    (a : α) : 0 < w a / (∑ b, w b) := by
  exact div_pos (hpos a) (Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty)

/-- Pointwise agreement of raw weights implies pointwise agreement of the
normalized weights. -/
theorem normalized_eq_of_agree (w w' : α → ℝ)
    (h : ∀ a, w a = w' a) (a : α) :
    w a / (∑ b, w b) = w' a / (∑ b, w' b) := by
  rw [show (∑ b, w b) = ∑ b, w' b from Finset.sum_congr rfl (fun b _ => h b), h a]

/-- Pointwise agreement of raw weights implies equality of the normalized
total readings. -/
theorem sum_normalized_eq_of_agree (w w' : α → ℝ) (h : ∀ a, w a = w' a) :
    (∑ a, w a / (∑ b, w b)) = (∑ a, w' a / (∑ b, w' b)) := by
  rw [show (∑ b, w b) = ∑ b, w' b from Finset.sum_congr rfl (fun b _ => h b)]
  exact Finset.sum_congr rfl (fun a _ => by rw [h a])

#check sum_normalized_eq_one
#check normalized_pos
#check normalized_eq_of_agree
#check sum_normalized_eq_of_agree

end LeanFormal.IUT.XiFPaper.NormalizationToolActual