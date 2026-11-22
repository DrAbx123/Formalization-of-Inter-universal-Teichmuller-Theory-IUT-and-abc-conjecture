import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
  A small order-theoretic kernel for the approximation reading of C1.
  It is deliberately independent of IUT carriers: if every epsilon has an
  output value within epsilon of Q and every output is bounded by Theta, then
  Q <= Theta.  This does not produce an output whose value is exactly Q.
-/

namespace LeanFormal.IUT.N8Closure.C1ApproxOrder

theorem le_of_approx_le {Q Theta : ℝ}
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ z : ℝ,
      |z - Q| < ε ∧ z ≤ Theta) :
    Q ≤ Theta := by
  by_contra hnot
  have hgap : 0 < Q - Theta := sub_pos.mpr (lt_of_not_ge hnot)
  let ε : ℝ := (Q - Theta) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨z, hzQ, hzΘ⟩ := happrox ε hε
  have hz_lower : Q - ε < z := by
    have := (abs_lt.mp hzQ).1
    linarith
  have hbad : Theta < Q - ε := by
    dsimp [ε]
    linarith
  linarith

end LeanFormal.IUT.N8Closure.C1ApproxOrder
