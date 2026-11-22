import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3ExponentTelescopeActual
theorem sum_range_telescope (f : Nat → ℝ) (n : Nat) :
    (Finset.range n).sum (fun i => f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
end LeanFormal.IUT.XiFPaper.Mzk1P3ExponentTelescopeActual
end