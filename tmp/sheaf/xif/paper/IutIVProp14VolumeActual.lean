/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: d = ef from Haar scaling and residue counts -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.IutIVProp14VolumeActual

theorem d_eq_e_mul_f_of_pow_eq (p : ℝ) (hp0 : 0 < p) (hp1 : p ≠ 1)
    (d e f : ℕ) (h : p ^ d = (p ^ f) ^ e) : d = e * f := by
  rw [← pow_mul] at h
  have hmul : d = f * e := (pow_right_injective₀ hp0 hp1) h
  simpa [Nat.mul_comm] using hmul

/-- Haar scaling comparison: from `μ(O) = q^e μ(pO)` and
`μ(pO) = p^{-d} μ(O)` with `q = p^f`, conclude `d = e*f`. -/
theorem d_eq_ef_of_haar_scaling (p q : ℝ) (hp0 : 0 < p) (hp1 : p ≠ 1)
    (d e f : ℕ) (hq : q = p ^ f) (μO μpO : ℝ)
    (hcard : μO = q ^ e * μpO) (hscale : μpO = (p ^ d)⁻¹ * μO)
    (hμO : μO ≠ 0) : d = e * f := by
  have hpd : p ^ d ≠ 0 := pow_ne_zero d (ne_of_gt hp0)
  have hqpow : q ^ e = (p ^ f) ^ e := by rw [hq]
  have hratio : μO = (q ^ e * (p ^ d)⁻¹) * μO := by
    calc
      μO = q ^ e * μpO := hcard
      _ = q ^ e * ((p ^ d)⁻¹ * μO) := by rw [hscale]
      _ = (q ^ e * (p ^ d)⁻¹) * μO := by ring
  have hcancel : 1 = q ^ e * (p ^ d)⁻¹ := by
    field_simp at hratio ⊢
    exact hratio
  have hpoweq : p ^ d = q ^ e := by
    rw [eq_comm] at hcancel
    field_simp [hpd] at hcancel
    exact hcancel.symm
  apply d_eq_e_mul_f_of_pow_eq p hp0 hp1 d e f
  rw [← hqpow]
  exact hpoweq

theorem volume_ratio_eq_pow (p : ℝ) (hp : 0 < p)
    (d s h f m : ℕ) (μO μΛ μL : ℝ)
    (hexp : h + f + m = s * d)
    (hμΛ : μΛ = p ^ h * μO)
    (hL : μL = (p : ℝ) ^ (-(s * d : ℤ)) * μΛ) :
    μL = (p : ℝ) ^ (-(f + m : ℤ)) * μO := by
  have hz : (-(s * d : ℤ) + h : ℤ) = -(f + m : ℤ) := by omega
  calc
    μL = (p : ℝ) ^ (-(s * d : ℤ)) * μΛ := hL
    _ = (p : ℝ) ^ (-(s * d : ℤ)) * (p ^ h * μO) := by rw [hμΛ]
    _ = ((p : ℝ) ^ (-(s * d : ℤ)) * (p : ℝ) ^ h) * μO := by ring
    _ = (p : ℝ) ^ (-(s * d : ℤ) + h) * μO := by
        rw [← zpow_natCast (p : ℝ) h, ← zpow_add₀ (ne_of_gt hp)]
    _ = (p : ℝ) ^ (-(f + m : ℤ)) * μO := by rw [hz]

theorem volume_ratio_le_pow (p : ℝ) (hp : 1 < p)
    (d s h f : ℕ) (μO μΛ μL : ℝ)
    (hμO : 0 ≤ μO)
    (hbound : h + f ≤ s * d)
    (hμΛ : μΛ = p ^ h * μO)
    (hL : μL = (p : ℝ) ^ (-(s * d : ℤ)) * μΛ) :
    μL ≤ (p : ℝ) ^ (-(f : ℤ)) * μO := by
  have hexp : (-(s * d : ℤ) + h : ℤ) ≤ -(f : ℤ) := by omega
  have hpowle : (p : ℝ) ^ (-(s * d : ℤ) + h) ≤ (p : ℝ) ^ (-(f : ℤ)) :=
    zpow_le_zpow_right₀ (le_of_lt hp) hexp
  have hEq : μL = (p : ℝ) ^ (-(s * d : ℤ) + h) * μO := by
    calc
      μL = (p : ℝ) ^ (-(s * d : ℤ)) * μΛ := hL
      _ = (p : ℝ) ^ (-(s * d : ℤ)) * (p ^ h * μO) := by rw [hμΛ]
      _ = ((p : ℝ) ^ (-(s * d : ℤ)) * (p : ℝ) ^ h) * μO := by ring
      _ = (p : ℝ) ^ (-(s * d : ℤ) + h) * μO := by
          rw [← zpow_natCast (p : ℝ) h, ← zpow_add₀ (ne_of_gt (lt_trans zero_lt_one hp))]
  rw [hEq]
  exact mul_le_mul_of_nonneg_right hpowle hμO

theorem p14ii_logVolume_cond (p : ℝ) (hp : 1 < p)
    (d e f m : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) (hd : d = e * f)
    (μL μO : ℝ) (hμL : 0 < μL) (hμO : 0 < μO)
    (hratio : μL = (p : ℝ) ^ (-(f + m : ℤ)) * μO) :
    (Real.log μL - Real.log μO) / (d : ℝ) =
      -(((f + m : ℝ) / (e * f : ℝ)) * Real.log p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hzpos : (0 : ℝ) < (p : ℝ) ^ (-(f + m : ℤ)) := zpow_pos hp0 _
  have hlog : Real.log μL = (-(f + m : ℤ) : ℝ) * Real.log p + Real.log μO := by
    rw [hratio, Real.log_mul (ne_of_gt hzpos) (ne_of_gt hμO), Real.log_zpow]
    push_cast
    ring
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by
      rw [hd]
      exact Nat.mul_pos (lt_of_lt_of_le zero_lt_one he) (lt_of_lt_of_le zero_lt_one hf)
    exact_mod_cast this
  have hcast : (d : ℝ) = (e : ℝ) * (f : ℝ) := by exact_mod_cast hd
  rw [hlog]
  rw [hcast]
  field_simp
  push_cast
  ring

end LeanFormal.IUT.XiFPaper.IutIVProp14VolumeActual
