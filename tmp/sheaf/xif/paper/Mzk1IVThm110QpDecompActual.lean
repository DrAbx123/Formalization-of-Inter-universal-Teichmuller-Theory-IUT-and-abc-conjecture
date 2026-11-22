import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
/-! Qp unit decomposition lam = p^k * u. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110QpDecompActual
open LeanFormal.IUT
variable {p : Nat} [Fact p.Prime]
/-- Every nonzero Qp element is p^k times a Zp-unit. -/
theorem exists_pow_mul_zpUnit (lam : ℚ_[p]) (h : lam ≠ 0) :
    ∃ (k : ℤ) (u : ℤ_[p]ˣ), lam = (p : ℚ_[p]) ^ k * (u : ℚ_[p]) := by
  let k : ℤ := lam.valuation
  let u0 : ℚ_[p] := lam * (p : ℚ_[p]) ^ (-k)
  have hp : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hk : (p : ℚ_[p]) ^ k ≠ 0 := zpow_ne_zero k hp
  have hnk : (p : ℚ_[p]) ^ (-k) ≠ 0 := zpow_ne_zero (-k) hp
  have hu0 : u0 ≠ 0 := mul_ne_zero h hnk
  have hu0val : u0.valuation = 0 := by
    rw [Padic.valuation_mul h hnk, Padic.valuation_zpow, Padic.valuation_p]
    ring
  have hu0norm : ‖u0‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation hu0, hu0val, neg_zero, zpow_zero]
  have hinvnorm : ‖u0⁻¹‖ ≤ 1 := by
    rw [norm_inv, hu0norm]
    norm_num
  let uZ : ℤ_[p] := ⟨u0, by rw [hu0norm]⟩
  let u : ℤ_[p]ˣ :=
    { val := uZ
      inv := ⟨u0⁻¹, hinvnorm⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ hu0)
      inv_val := Subtype.ext (inv_mul_cancel₀ hu0) }
  refine ⟨k, u, ?_⟩
  change lam = (p : ℚ_[p]) ^ k * u0
  rw [show u0 = lam * (p : ℚ_[p]) ^ (-k) by rfl]
  have hpk : (p : ℚ_[p]) ^ k * (p : ℚ_[p]) ^ (-k) = 1 := by
    rw [← zpow_add₀ hp]
    simp
  calc lam = 1 * lam := (one_mul lam).symm
    _ = ((p : ℚ_[p]) ^ k * (p : ℚ_[p]) ^ (-k)) * lam := by rw [hpk]
    _ = (p : ℚ_[p]) ^ k * (lam * (p : ℚ_[p]) ^ (-k)) := by
      rw [mul_assoc, mul_comm ((p : ℚ_[p]) ^ (-k)) lam]
#check exists_pow_mul_zpUnit
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110QpDecompActual
end