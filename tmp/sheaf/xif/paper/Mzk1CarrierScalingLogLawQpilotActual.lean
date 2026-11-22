/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1CarrierScalingLogLawQpilotActual — carrier scaling log law (A664)

Log laws for the carrier bad-inverse scaling factor, the real-level form of the
mainline product-Haar law under `ENNReal.toReal`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawQpilotActual

universe u

open scoped BigOperators

/-- Log of an inverse product factor: `log(a⁻¹·b) = log b − log a`. -/
theorem log_inv_mul {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a⁻¹ * b) = Real.log b - Real.log a := by
  rw [inv_eq_one_div, div_mul_eq_mul_div, one_mul,
    Real.log_div (ne_of_gt hb) (ne_of_gt ha)]

/-- Log of a finite inverse product of powers: `−∑ e_i·log f_i`. -/
theorem log_prod_inv_pow {ι : Type u} [Fintype ι] (f : ι → Real) (e : ι → Nat)
    (hf : ∀ i, 0 < f i) :
    Real.log (∏ i, (f i ^ e i)⁻¹) = -∑ i, (e i : Real) * Real.log (f i) := by
  have hpos : ∀ i, 0 < (f i ^ e i)⁻¹ := fun i => inv_pos.mpr (pow_pos (hf i) _)
  rw [Real.log_prod (fun i _ => ne_of_gt (hpos i))]
  have hterm : ∀ i, Real.log ((f i ^ e i)⁻¹) = -((e i : Real) * Real.log (f i)) := by
    intro i
    rw [Real.log_inv, Real.log_pow]
  simp only [hterm]
  rw [Finset.sum_neg_distrib]

/-- Carrier log law: log of the scaled product volume factor times a base volume. -/
theorem log_prod_inv_pow_mul_base {ι : Type u} [Fintype ι] (f : ι → Real)
    (e : ι → Nat) (hf : ∀ i, 0 < f i) {base : Real} (hb : 0 < base) :
    Real.log ((∏ i, (f i ^ e i)⁻¹) * base) =
      Real.log base - ∑ i, (e i : Real) * Real.log (f i) := by
  have hprodpos : 0 < ∏ i, (f i ^ e i)⁻¹ :=
    Finset.prod_pos (fun i _ => inv_pos.mpr (pow_pos (hf i) _))
  rw [Real.log_mul (ne_of_gt hprodpos) (ne_of_gt hb), log_prod_inv_pow f e hf]
  ring

/-- Rows for the carrier scaling log law. -/
def carrierScalingLogRows : List (String × String) :=
  [ ("log(a⁻¹ b) = log b - log a", "PROVED"),
    ("log prod inverse powers", "PROVED"),
    ("log of scaled base product", "PROVED") ]

theorem carrierScalingLogRows_length : carrierScalingLogRows.length = 3 := rfl

#check log_inv_mul
#check log_prod_inv_pow
#check log_prod_inv_pow_mul_base
#check carrierScalingLogRows_length

end LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawQpilotActual
end
