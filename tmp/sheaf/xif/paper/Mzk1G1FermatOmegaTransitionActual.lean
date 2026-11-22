/- G1-B Fermat omega transition x^(n-3): scalar identity for the overlap coordinate change (A1/A3). -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatOmegaTransitionActual

/-- Exact transition identity A3 for the two local bases of the Fermat differential:
with r = x⁻¹, s = y/x the coefficient of dx changes by x^(n-3).  This is the scalar
content of ω∞ = x^(n-3) ω₀ (route §3.1 (A3)); the differential-form version in the
actual localized Ω-module is proved on top of this identity. -/
theorem fermatOmegaTransition
    {K : Type*} [Field K]
    (x y r s : K) (n : Nat) (hn : 3 ≤ n) (hx : x ≠ 0) (hy : y ≠ 0)
    (hr : r = x⁻¹) (hs : s = y / x) :
    (1 / s ^ (n - 1)) * (-1 / x ^ 2) = - x ^ (n - 3) * (1 / y ^ (n - 1)) := by
  subst hr hs
  have hxn : x ^ (n - 1) ≠ 0 := pow_ne_zero _ hx
  have hyn : y ^ (n - 1) ≠ 0 := pow_ne_zero _ hy
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero _ hx
  have hkey : x ^ 2 * (y / x) ^ (n - 1) * x ^ (n - 3) = y ^ (n - 1) := by
    have hx1 : x ^ 2 * x ^ (n - 3) = x ^ (n - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hxin : x ^ (n - 1) * (x⁻¹) ^ (n - 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
    calc
      x ^ 2 * (y / x) ^ (n - 1) * x ^ (n - 3)
          = (x ^ 2 * x ^ (n - 3)) * (y ^ (n - 1) * (x⁻¹) ^ (n - 1)) := by
              rw [div_pow, div_eq_mul_inv, inv_pow]
              ring
      _ = x ^ (n - 1) * (y ^ (n - 1) * (x⁻¹) ^ (n - 1)) := by rw [hx1]
      _ = y ^ (n - 1) * (x ^ (n - 1) * (x⁻¹) ^ (n - 1)) := by ring
      _ = y ^ (n - 1) := by rw [hxin, mul_one]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  field_simp [hxn, hyn, hx2]
  rw [hkey]

#print axioms fermatOmegaTransition
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatOmegaTransitionActual
