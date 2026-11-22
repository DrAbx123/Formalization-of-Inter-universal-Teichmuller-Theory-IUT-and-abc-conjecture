import Mathlib
import LeanFormal.IUT.Foundations.LocalFields.PadicFiniteCoordinateHaarScaling
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2734DecompUnitActual
open MeasureTheory
open scoped NNReal
variable {p : ℕ} [Fact p.Prime]
variable (u : ℚ_[p]ˣ)

/-- Decomposition unit part: u * p^(-valuation u). -/
def decompV : ℚ_[p] :=
  (u : ℚ_[p]) * (p : ℚ_[p]) ^ (-((u : ℚ_[p]).valuation))

theorem decompV_norm_eq_one : ‖decompV (p := p) u‖ = 1 := by
  unfold decompV
  have hu : (u : ℚ_[p]) ≠ 0 := Units.ne_zero u
  have hpn : (p : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hu, norm_zpow, Padic.norm_p]
  set K : ℤ := (u : ℚ_[p]).valuation
  rw [inv_zpow, ← zpow_neg]
  have hsum : -K + (- -K) = 0 := by ring
  have hnn : (p : ℝ≥0) ^ (-K) * (p : ℝ≥0) ^ (- -K) = 1 := by
    rw [← zpow_add₀ (a := (p : ℝ≥0)) hpn, hsum, zpow_zero]
  have hpR : (p : ℝ) = ((p : ℝ≥0) : ℝ) := by norm_num
  rw [hpR]
  rw [← NNReal.coe_zpow, ← NNReal.coe_zpow, ← NNReal.coe_mul]
  rw [hnn]
  simp

/-- Unit part as a unit of ℚ_[p], directly u * p^(-K). -/
def decompVUnit : ℚ_[p]ˣ :=
  u * (PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit (p := p)) ^ (-((u : ℚ_[p]).valuation))


theorem decompV_ne_zero (u : ℚ_[p]ˣ) : decompV (p := p) u ≠ 0 := by
  intro h
  have hnorm := decompV_norm_eq_one (p := p) u
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

/-- decompV as an element of the p-adic integers. -/
noncomputable def zv (u : ℚ_[p]ˣ) : PadicInt p :=
  ⟨decompV (p := p) u, by
    rw [decompV_norm_eq_one]⟩

/-- Inverse of decompV as an element of the p-adic integers. -/
noncomputable def zvInv (u : ℚ_[p]ˣ) : PadicInt p :=
  ⟨(decompV (p := p) u)⁻¹, by
    rw [norm_inv, decompV_norm_eq_one]
    norm_num⟩

/-- Unit part as a unit of the p-adic integers. -/
noncomputable def decompVUnitInt (u : ℚ_[p]ˣ) : (PadicInt p)ˣ :=
  Units.mk (zv (p := p) u) (zvInv (p := p) u)
    (by
      apply Subtype.ext
      change (decompV (p := p) u) * ((decompV (p := p) u)⁻¹) = (1 : ℚ_[p])
      field_simp [decompV_ne_zero (p := p) u])
    (by
      apply Subtype.ext
      change ((decompV (p := p) u)⁻¹) * (decompV (p := p) u) = (1 : ℚ_[p])
      field_simp [decompV_ne_zero (p := p) u])

#check decompVUnitInt

#check decompVUnit
#check decompV_norm_eq_one
end LeanFormal.IUT.XiFPaper.S2734DecompUnitActual
end
