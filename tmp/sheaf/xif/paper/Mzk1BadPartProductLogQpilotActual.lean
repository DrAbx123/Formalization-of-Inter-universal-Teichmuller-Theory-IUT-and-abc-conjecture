/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1BadPartProductLogQpilotActual — bad-part product log law (A661)

Product form of the bad-part logarithmic scaling: the log of the product of scaled
positive radii is the sum over the bad places of `log‖λ_b‖ + log R_b`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BadPartProductLogQpilotActual

universe u

open scoped BigOperators

/-- Log of a finite product of positive real factors is the sum of logs. -/
theorem log_prod_pos {ι : Type u} [Fintype ι] (f : ι → Real)
    (hf : ∀ i, 0 < f i) :
    Real.log (∏ i, f i) = ∑ i, Real.log (f i) := by
  rw [Real.log_prod (fun i _ => ne_of_gt (hf i))]

/-- Log of the product of scaled radii: sum of log-norms plus sum of log-radii. -/
theorem log_prod_scaled {ι : Type u} [Fintype ι] (lam R : ι → Real)
    (hlam : ∀ i, lam i ≠ 0) (hR : ∀ i, 0 < R i) :
    Real.log (∏ i, ‖lam i‖ * R i) =
      (∑ i, Real.log ‖lam i‖) + ∑ i, Real.log (R i) := by
  have hprod : (∏ i, ‖lam i‖ * R i) = (∏ i, ‖lam i‖) * (∏ i, R i) := by
    rw [Finset.prod_mul_distrib]
  have hpos1 : 0 < ∏ i, ‖lam i‖ := Finset.prod_pos (fun i _ => norm_pos_iff.mpr (hlam i))
  have hpos2 : 0 < ∏ i, R i := Finset.prod_pos (fun i _ => hR i)
  rw [hprod, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2),
    log_prod_pos (fun i => ‖lam i‖) (fun i => norm_pos_iff.mpr (hlam i)),
    log_prod_pos R hR]

/-- Normalized product law: the `R`-normalized log is the sum of the log-norms. -/
theorem log_normalized_prod {ι : Type u} [Fintype ι] (lam R : ι → Real)
    (hlam : ∀ i, lam i ≠ 0) (hR : ∀ i, 0 < R i) :
    Real.log ((∏ i, ‖lam i‖ * R i) / (∏ i, R i)) =
      ∑ i, Real.log ‖lam i‖ := by
  have hprod : (∏ i, ‖lam i‖ * R i) = (∏ i, ‖lam i‖) * (∏ i, R i) := by
    rw [Finset.prod_mul_distrib]
  have hpos2 : 0 < ∏ i, R i := Finset.prod_pos (fun i _ => hR i)
  rw [hprod, mul_div_cancel_right₀ _ (ne_of_gt hpos2),
    log_prod_pos (fun i => ‖lam i‖) (fun i => norm_pos_iff.mpr (hlam i))]

/-- Rows for the bad-part product log. -/
def badPartProdLogRows : List (String × String) :=
  [ ("log of product = sum of logs", "PROVED"),
    ("scaled product log decomposition", "PROVED"),
    ("normalized product log = sum log-norms", "PROVED") ]

theorem badPartProdLogRows_length : badPartProdLogRows.length = 3 := rfl

#check log_prod_scaled
#check log_normalized_prod
#check badPartProdLogRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BadPartProductLogQpilotActual
end
