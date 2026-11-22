import tmp.sheaf.xif.paper.Mzk1PadicFieldValuedBridgeActual
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedQpActual
open scoped WithZero
open LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedBridgeActual

variable {p : Nat} [Fact p.Prime]

instance : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
  Valued.mk' (Padic.mulValuation (p := p))

theorem valuedQp_apply {x : ℚ_[p]} (hx : x ≠ 0) :
    (Valued.v x : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(Padic.valuation (p := p) x)) := by
  change Padic.mulValuation (p := p) x = _
  rw [Padic.mulValuation]
  simp [hx]

/-- The missing local-CFT normalization: `PadicField.v` is the `p`-adic
integer valuation on `ℚ_[p]`. -/
structure PadicFieldQpCoherence where
  v_eq : ∀ x : ℚ_[p], PadicField.v p x = Padic.valuation (p := p) x

theorem padicValuedCoherence_of_qp (h : PadicFieldQpCoherence (p := p)) :
    PadicValuedCoherence (p := p) (K := ℚ_[p]) where
  v_eq x hx := by
    rw [valuedQp_apply (p := p) hx, h.v_eq x]


theorem padicField_v_eq_valuation (x : ℚ_[p]) :
    PadicField.v p x = Padic.valuation (p := p) x := by
  have hexpo : PadicField.expo p ℚ_[p] = 1 := by
    simp [PadicField.expo, Module.finrank_self]
  have hnrm (y : ℚ_[p]) : PadicField.nrm p ℚ_[p] y = ‖y‖ := by
    simpa using (PadicField.nrm_algebraMap (p := p) (K := ℚ_[p]) y)
  have hwp : PadicField.wval p ((p : ℚ_[p])) = 1 := by
    rw [PadicField.wval_eq_iff (p := p) (K := ℚ_[p])
      (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero) 1]
    rw [hexpo, pow_one, hnrm]
    rw [Padic.norm_eq_zpow_neg_valuation (p := p)
      (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero), Padic.valuation_p]
  have hvalGen : PadicField.valGen p ℚ_[p] = 1 := by
    have h1 := PadicField.valGen_le p ℚ_[p] one_pos
      (PadicField.natCast_p_ne_zero (p := p) (K := ℚ_[p])) (by rw [hwp]; rfl)
    have h0 := PadicField.valGen_pos p ℚ_[p]
    omega
  by_cases hx : x = 0
  · subst x
    rw [PadicField.v]
    have hw0 : PadicField.wval p (0 : ℚ_[p]) = 0 := by
      simp [PadicField.wval]
    rw [hw0]
    simp
  · have hwval : PadicField.wval p x = Padic.valuation (p := p) x := by
      rw [PadicField.wval_eq_iff (p := p) (K := ℚ_[p]) hx]
      rw [hexpo, pow_one, hnrm, Padic.norm_eq_zpow_neg_valuation (p := p) hx]
    rw [PadicField.v, hwval, hvalGen]
    exact Int.ediv_one _

noncomputable def padicFieldQpCoherence : PadicFieldQpCoherence (p := p) where
  v_eq := padicField_v_eq_valuation (p := p)

theorem padicValuedCoherence_qp : PadicValuedCoherence (p := p) (K := ℚ_[p]) :=
  padicValuedCoherence_of_qp (padicFieldQpCoherence (p := p))

#print axioms padicField_v_eq_valuation
#print axioms padicFieldQpCoherence
#print axioms padicValuedCoherence_qp

#print axioms valuedQp_apply
#print axioms padicValuedCoherence_of_qp
end LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedQpActual