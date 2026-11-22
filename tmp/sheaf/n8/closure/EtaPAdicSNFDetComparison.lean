import Mathlib
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula

/-!
# Eta p-adic SNF determinant comparison

Pure matrix Smith-normal-form determinant computation:

if A = U * diagonal(a) * V with U, V determinant units over Z_p, then

  det A = unit * prod_i a_i,

and the p-adic norm of det A equals the norm of prod_i a_i.  If
a_i = w_i * p^(k_i), this norm is (p^(sum k_i))^{-1}, i.e. the inverse of the
p-power lattice index (index = p^(sum k_i)).

This is the actual pure matrix/SNF determinant comparison.  The remaining gap
is only the production basis-change theorem identifying an arbitrary Q_p-linear
map with such an SNF matrix, together with Haar uniqueness.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option linter.deprecated false

open Matrix
open scoped BigOperators

namespace LeanFormal.IUT.N8Closure.EtaPAdicSNFDetComparison

variable {p : Nat} [Fact p.Prime]

/-- Pure matrix SNF determinant: det(U diag(a) V) = unit * prod a. -/
theorem det_snf_eq_unit_mul_prod {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℤ_[p]) (a : n → ℤ_[p])
    (hU : IsUnit U.det) (hV : IsUnit V.det) :
    ∃ u : ℤ_[p]ˣ,
      (U * Matrix.diagonal a * V).det = (u : ℤ_[p]) * ∏ i, a i := by
  let uU := hU.unit
  let uV := hV.unit
  refine ⟨uU * uV, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hUval : (uU : ℤ_[p]) = U.det := IsUnit.unit_spec hU
  have hVval : (uV : ℤ_[p]) = V.det := IsUnit.unit_spec hV
  rw [← hUval, ← hVval]
  simp [Units.val_mul, mul_assoc, mul_comm]

/-- The p-adic norm of the SNF determinant is the norm of the product of the
Smith coefficients. -/
theorem norm_det_snf_eq_prod_norm {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℤ_[p]) (a : n → ℤ_[p])
    (hU : IsUnit U.det) (hV : IsUnit V.det) :
    ‖(((U * Matrix.diagonal a * V).det : ℤ_[p]) : ℚ_[p])‖ =
      ‖(((∏ i, a i : ℤ_[p])) : ℚ_[p])‖ := by
  obtain ⟨u, hu⟩ := det_snf_eq_unit_mul_prod U V a hU hV
  have huQ : (((U * Matrix.diagonal a * V).det : ℤ_[p]) : ℚ_[p]) =
      ((u : ℤ_[p]) : ℚ_[p]) * (((∏ i, a i : ℤ_[p])) : ℚ_[p]) := by
    rw [hu]
    push_cast
    rfl
  rw [huQ, norm_mul, PadicInt.padic_norm_e_of_padicInt, PadicInt.norm_units, one_mul]

/-- Pure p-power SNF norm: if a_i = w_i p^(k_i), then
‖det A‖ = (p^(sum k_i))^{-1}. -/
theorem norm_det_snf_eq_pow_neg_sum {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix n n ℤ_[p]) (a : n → ℤ_[p])
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (w : n → ℤ_[p]ˣ) (k : n → ℕ)
    (ha : ∀ i, a i = (w i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) :
    ‖(((U * Matrix.diagonal a * V).det : ℤ_[p]) : ℚ_[p])‖ =
      ((p : ℝ) ^ (∑ i, k i))⁻¹ := by
  rw [norm_det_snf_eq_prod_norm U V a hU hV]
  have hPprod : (∏ i, a i : ℤ_[p]) =
      (∏ i, (w i : ℤ_[p])) * (p : ℤ_[p]) ^ (∑ i, k i) := by
    rw [Finset.prod_congr rfl (fun i _ => ha i)]
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum Finset.univ k (p : ℤ_[p])]
  have hP : (((∏ i, a i : ℤ_[p])) : ℚ_[p]) =
      ((↑(∏ i, (w i : ℤ_[p])) : ℚ_[p])) *
        (((p : ℤ_[p]) : ℚ_[p]) ^ (∑ i, k i)) := by
    rw [hPprod]
    push_cast
    rfl
  rw [hP, norm_mul]
  have hw : ‖((↑(∏ i, (w i : ℤ_[p])) : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    induction (Finset.univ : Finset n) using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.prod_insert hx, norm_mul, ih, PadicInt.norm_units, one_mul]
  rw [hw, one_mul]
  rw [norm_pow]
  change ‖((p : ℤ_[p]) : ℚ_[p])‖ ^ (∑ i, k i) = ((p : ℝ) ^ (∑ i, k i))⁻¹
  rw [PadicInt.padic_norm_e_of_padicInt, PadicInt.norm_p, inv_pow]

end LeanFormal.IUT.N8Closure.EtaPAdicSNFDetComparison
