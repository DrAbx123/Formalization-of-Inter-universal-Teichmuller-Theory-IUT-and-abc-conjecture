import tmp.sheaf.xif.paper.S2570TateIntegralModelActual
import Mathlib.Analysis.Normed.Group.Ultra

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S2572TateDeltaNormActual

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem S2572_delta_formula (a4 a6 : K) :
    (WeierstrassCurve.mk 1 0 0 a4 a6).Δ =
      -a6 + a4 ^ 2 - 64 * a4 ^ 3 - 432 * a6 ^ 2 + 72 * a4 * a6 := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem S2572_norm_lt_one_of_norm_lt_one
    {x1 x2 x3 x4 x5 : K}
    (h1 : ‖x1‖ < 1) (h2 : ‖x2‖ < 1) (h3 : ‖x3‖ < 1)
    (h4 : ‖x4‖ < 1) (h5 : ‖x5‖ < 1) :
    ‖x1 + x2 + x3 + x4 + x5‖ < 1 := by
  have h12 : ‖x1 + x2‖ < 1 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  have h123 : ‖x1 + x2 + x3‖ < 1 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h12 h3)
  have h1234 : ‖x1 + x2 + x3 + x4‖ < 1 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h123 h4)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1234 h5)

theorem S2572_delta_norm_lt_one {a4 a6 : K}
    (h4 : ‖a4‖ < 1) (h6 : ‖a6‖ < 1) :
    ‖(WeierstrassCurve.mk 1 0 0 a4 a6).Δ‖ < 1 := by
  rw [S2572_delta_formula]
  have h4sq : ‖a4 ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg a4) h4 (by norm_num)
  have h4cube : ‖(64 : K) * a4 ^ 3‖ < 1 := by
    have hnat : ‖(64 : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K 64
    have hpow : ‖a4‖ ^ 3 < 1 := pow_lt_one₀ (norm_nonneg a4) h4 (by norm_num)
    calc ‖(64 : K) * a4 ^ 3‖
        = ‖(64 : K)‖ * ‖a4 ^ 3‖ := norm_mul _ _
      _ = ‖(64 : K)‖ * ‖a4‖ ^ 3 := by rw [norm_pow]
      _ ≤ 1 * ‖a4‖ ^ 3 := by gcongr
      _ = ‖a4‖ ^ 3 := one_mul _
      _ < 1 := hpow
  have h6sq : ‖(432 : K) * a6 ^ 2‖ < 1 := by
    have hnat : ‖(432 : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K 432
    have hpow : ‖a6‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg a6) h6 (by norm_num)
    calc ‖(432 : K) * a6 ^ 2‖
        = ‖(432 : K)‖ * ‖a6 ^ 2‖ := norm_mul _ _
      _ = ‖(432 : K)‖ * ‖a6‖ ^ 2 := by rw [norm_pow]
      _ ≤ 1 * ‖a6‖ ^ 2 := by gcongr
      _ = ‖a6‖ ^ 2 := one_mul _
      _ < 1 := hpow
  have h46 : ‖(72 : K) * a4 * a6‖ < 1 := by
    rw [norm_mul, norm_mul]
    have hnat : ‖(72 : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K 72
    calc ‖(72 : K)‖ * ‖a4‖ * ‖a6‖
        ≤ 1 * 1 * ‖a6‖ := by gcongr
      _ = ‖a6‖ := by ring
      _ < 1 := h6
  have h4cubeNeg : ‖-((64 : K) * a4 ^ 3)‖ < 1 := by simpa using h4cube
  have h6sqNeg : ‖-((432 : K) * a6 ^ 2)‖ < 1 := by simpa using h6sq
  have h6Neg : ‖-a6‖ < 1 := by simpa using h6
  simpa only [sub_eq_add_neg] using
    S2572_norm_lt_one_of_norm_lt_one h6Neg h4sq h4cubeNeg h6sqNeg h46

theorem S2572_c4_norm_eq_one {a4 : K} (h4 : ‖a4‖ < 1) :
    ‖(WeierstrassCurve.mk 1 0 0 a4 0).c₄‖ = 1 := by
  have hc : (WeierstrassCurve.mk 1 0 0 a4 0).c₄ = 1 - 48 * a4 := by
    simp [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  rw [hc]
  have h48 : ‖(48 : K) * a4‖ < 1 := by
    calc ‖(48 : K) * a4‖ = ‖(48 : K)‖ * ‖a4‖ := norm_mul _ _
      _ ≤ 1 * ‖a4‖ := by
        gcongr
        exact IsUltrametricDist.norm_natCast_le_one K 48
      _ = ‖a4‖ := one_mul _
      _ < 1 := h4
  apply le_antisymm
  · have h := IsUltrametricDist.norm_add_le_max (1 : K) (-(48 * a4))
    have h' : ‖(1 : K) - 48 * a4‖ ≤ max 1 ‖(48 : K) * a4‖ := by
      simpa [sub_eq_add_neg, norm_neg] using h
    exact h'.trans (by rw [max_eq_left h48.le])
  · by_contra hlt
    have h1 : ‖(1 : K) - 48 * a4‖ < 1 := lt_of_not_ge hlt
    have h := IsUltrametricDist.norm_add_le_max ((1 : K) - 48 * a4) (48 * a4)
    rw [sub_add_cancel, norm_one] at h
    have hmaxlt : max ‖(1 : K) - 48 * a4‖ ‖(48 : K) * a4‖ < 1 :=
      max_lt h1 h48
    linarith

theorem S2572_c4_isUnit {a4 : K} (h4 : ‖a4‖ < 1) :
    IsUnit (WeierstrassCurve.mk 1 0 0 a4 0).c₄ :=
  isUnit_iff_ne_zero.mpr (by
    intro hzero
    have h := S2572_c4_norm_eq_one h4
    rw [hzero, norm_zero] at h
    exact zero_ne_one h)

#check S2572_delta_norm_lt_one
#check S2572_c4_isUnit
#print axioms S2572_delta_norm_lt_one
#print axioms S2572_c4_isUnit
end LeanFormal.IUT.XiFPaper.S2572TateDeltaNormActual
end