import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import tmp.sheaf.takkun.IutLean.Padic.LogShellRadius

namespace IUT.Padic

section OddPrime

variable {p e : ℕ}

private lemma hp1R (hp : 2 < p) : (0 : ℝ) < (p : ℝ) - 1 := by
  have h : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  linarith

private lemma heR (he : 1 ≤ e) : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he

/-- **順分岐の等式(a 側)**: `p > 2`, `e ≤ p−1` ⟹ `a = 1/e`
(`0 < e/(p−1) ≤ 1` ゆえ `⌈e/(p−1)⌉ = 1`)。 -/
theorem aRadius_tame (hp : 2 < p) (he : 1 ≤ e) (h : e + 1 ≤ p) :
    aRadius p e = 1 / e := by
  unfold aRadius
  rw [if_neg (by omega)]
  have hp1 := hp1R hp
  have he0 := heR he
  have hceil : ⌈(e : ℝ) / ((p : ℝ) - 1)⌉₊ = 1 := by
    have h1 : (0 : ℝ) < (e : ℝ) / ((p : ℝ) - 1) := by positivity
    have h2 : (e : ℝ) / ((p : ℝ) - 1) ≤ 1 := by
      rw [div_le_one hp1]
      have hc : (e : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h
      linarith
    refine le_antisymm (Nat.ceil_le.mpr (by simpa using h2)) (Nat.one_le_ceil_iff.mpr h1)
  rw [hceil]
  norm_num

/-- **順分岐の等式(b 側)**: `p > 2`, `e ≤ p−2` ⟹ `b = −1/e`
(`1 ≤ p·e/(p−1) < p` ゆえ床が 0)。境界 `e = p−1` では `p·e/(p−1) = p` となり
床が 1 に跳ね、等式は破れる ―― `e ≤ p−2` が本質的。 -/
theorem bRadius_tame (hp : 2 < p) (he : 1 ≤ e) (h : e + 2 ≤ p) :
    bRadius p e = -(1 / e) := by
  unfold bRadius
  have hp1 := hp1R hp
  have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hpR : (1 : ℝ) < (p : ℝ) := by
    have h3 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    linarith
  have hfloor : ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    have hlogp : 0 < Real.log p := Real.log_pos hpR
    constructor
    · apply div_nonneg _ hlogp.le
      apply Real.log_nonneg
      rw [le_div_iff₀ hp1, one_mul]
      have hpe : (p : ℝ) ≤ (p : ℝ) * e := le_mul_of_one_le_right (by linarith) he1
      linarith
    · rw [div_lt_one hlogp]
      apply Real.log_lt_log (by positivity)
      rw [div_lt_iff₀ hp1]
      have he2 : (e : ℝ) < (p : ℝ) - 1 := by
        have hc : (e : ℝ) + 2 ≤ (p : ℝ) := by exact_mod_cast h
        linarith
      exact mul_lt_mul_of_pos_left he2 (by linarith)
  rw [hfloor]
  norm_num

/-- **順分岐の等式(両側)**: `p > 2`, `e ≤ p−2` ⟹ `a = 1/e ∧ b = −1/e`
([IUT-IV] Prop 1.2 の「Thus, if `p > 2` and `eᵢ ≤ p−2`, then `aᵢ = 1/eᵢ = −bᵢ`」)。 -/
theorem radius_tame (hp : 2 < p) (he : 1 ≤ e) (h : e + 2 ≤ p) :
    aRadius p e = 1 / e ∧ bRadius p e = -(1 / e) :=
  ⟨aRadius_tame hp he (by omega), bRadius_tame hp he h⟩

/-- `1/e ≤ a`([IUT-IV] p.15 の「`aᵢ ≥ 1/eᵢ`」―― Thm 1.10 の定数評価で使用)。 -/
theorem one_div_le_aRadius (hp : 2 < p) (he : 1 ≤ e) : 1 / (e : ℝ) ≤ aRadius p e := by
  unfold aRadius
  rw [if_neg (by omega)]
  have hp1 := hp1R hp
  have he0 := heR he
  have h1 : (1 : ℝ) ≤ (⌈(e : ℝ) / ((p : ℝ) - 1)⌉₊ : ℝ) := by
    exact_mod_cast Nat.one_le_ceil_iff.mpr (show (0 : ℝ) < (e : ℝ) / ((p : ℝ) - 1) by positivity)
  gcongr

/-- `1/(p−1) ≤ a`(収束半径側)。原文 [IUT-IV] p.11 は「`aᵢ > 1/(p−1)`」を主張するが、
これは `(p−1) ∤ e` のときのみ厳密(例: `p = 5`, `e = 4` では `a = 1/4 = 1/(p−1)`)――
一般に真なのはこの `≤` である(honest 注記)。 -/
theorem le_aRadius (hp : 2 < p) (he : 1 ≤ e) : 1 / ((p : ℝ) - 1) ≤ aRadius p e := by
  unfold aRadius
  rw [if_neg (by omega)]
  have hp1 := hp1R hp
  have he0 := heR he
  have hkey : ((e : ℝ) / ((p : ℝ) - 1)) / e = 1 / ((p : ℝ) - 1) := by
    rw [div_div, mul_comm ((p : ℝ) - 1) (e : ℝ), ← div_div, div_self he0.ne']
  rw [← hkey]
  gcongr
  exact Nat.le_ceil _

/-- `a < 1/(p−1) + 1/e`([IUT-IV] p.16 の「`aᵢ − 1/eᵢ ≤ 1/(p−1)`」の厳密版 ――
`⌈x⌉ < x + 1` による)。 -/
theorem aRadius_lt (hp : 2 < p) (he : 1 ≤ e) :
    aRadius p e < 1 / ((p : ℝ) - 1) + 1 / e := by
  unfold aRadius
  rw [if_neg (by omega)]
  have hp1 := hp1R hp
  have he0 := heR he
  rw [div_lt_iff₀ he0]
  calc (⌈(e : ℝ) / ((p : ℝ) - 1)⌉₊ : ℝ) < (e : ℝ) / ((p : ℝ) - 1) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
    _ = (1 / ((p : ℝ) - 1) + 1 / e) * e := by
        rw [add_mul, one_div_mul_cancel he0.ne', div_mul_eq_mul_div, one_mul]

/-- `−1/e ≤ b`(床の非負性 ―― `p·e/(p−1) ≥ 1`)。 -/
theorem neg_one_div_le_bRadius (hp : 2 < p) (he : 1 ≤ e) :
    -(1 / (e : ℝ)) ≤ bRadius p e := by
  unfold bRadius
  have hp1 := hp1R hp
  have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hpR : (1 : ℝ) < (p : ℝ) := by
    have h3 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    linarith
  have h0 : (0 : ℤ) ≤ ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ := by
    apply Int.floor_nonneg.mpr
    apply div_nonneg _ (Real.log_pos hpR).le
    apply Real.log_nonneg
    rw [le_div_iff₀ hp1, one_mul]
    have hpe : (p : ℝ) ≤ (p : ℝ) * e := le_mul_of_one_le_right (by linarith) he1
    linarith
  have h0R : (0 : ℝ) ≤ ((⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ : ℤ) : ℝ) := by
    exact_mod_cast h0
  linarith

/-- **非分岐の半径**(`e = 1`, `p > 2`): `a = 1` ―― `PadicLog.lean` の
`norm_logOnePlus`(殻 `pℤ_p` のノルム保存)が実現する半径。 -/
theorem aRadius_one (hp : 2 < p) : aRadius p 1 = 1 := by
  rw [aRadius_tame hp le_rfl (by omega)]
  norm_num

/-- **非分岐の半径**(`e = 1`, `p > 2`): `b = −1` ―― `log(1+pℤ_p) ⊆ p^{−(−1)}·ℤ_p = pℤ_p`
(`PadicLog.lean` の `norm_logOnePlus_le`)。 -/
theorem bRadius_one (hp : 2 < p) : bRadius p 1 = -1 := by
  rw [bRadius_tame hp le_rfl (by omega)]
  norm_num

end OddPrime

end IUT.Padic

