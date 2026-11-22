import PadicField.FieldNorm
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedBridgeActual
open scoped WithZero

variable {p : Nat} [Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]
variable [Valued K (WithZero (Multiplicative ℤ))]

/-- Coherence between the local-CFT integer valuation `PadicField.v` and the
`Valued.v` valuation: on nonzero elements `Valued.v` is the exponential of
the negative integer valuation.  This is an explicit bridge input, not an
inhabitant assertion. -/
structure PadicValuedCoherence where
  v_eq : ∀ x : K, x ≠ 0 →
    (Valued.v x : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(PadicField.v p x))

/-- Transfer of the strict `< 1` condition from `Valued.v` to `PadicField.v`. -/
theorem valued_lt_one_iff_padicField_v_neg
    (h : PadicValuedCoherence (p := p) (K := K)) {x : K} (hx : x ≠ 0) :
    (Valued.v x : WithZero (Multiplicative ℤ)) < 1 ↔
      0 < PadicField.v p x := by
  rw [h.v_eq x hx]
  rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
    WithZero.exp_zero.symm]
  rw [WithZero.exp_lt_exp]
  omega

#print axioms valued_lt_one_iff_padicField_v_neg
end LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedBridgeActual