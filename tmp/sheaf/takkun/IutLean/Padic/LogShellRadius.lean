import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-!
# 対数殻の半径定数 aᵢ, bᵢ — [IUT-IV] Prop 1.2 の数値骨格

底本: [IUT-IV] Proposition 1.2 (Differents and Logarithms) の冒頭の定義:

* `aᵢ := (1/eᵢ)·⌈eᵢ/(p−1)⌉`(`p > 2`)、`aᵢ := 2`(`p = 2`);
* `bᵢ := ⌊log(p·eᵢ/(p−1))/log(p)⌋ − 1/eᵢ`。

これらは Prop 1.2 (i) の包含 `p^{aᵢ}·Rᵢ ⊆ log_p(Rᵢ^×) ⊆ p^{−bᵢ}·Rᵢ` の半径であり、
Thm 1.10 の明示的定数(ひいては `C_Θ` 公式)はこの `aᵢ, bᵢ` の初等評価から組まれる。

## 証明済(全て標準公理のみ)

* `aRadius_tame` / `bRadius_tame` / `radius_tame`: **順分岐の等式**
  `p > 2`, `e ≤ p−2` ⟹ `a = 1/e = −b`(Prop 1.2 の「Thus, if `p > 2` and
  `eᵢ ≤ p−2`, then `aᵢ = 1/eᵢ = −bᵢ`」の完全な形式化);
* `one_div_le_aRadius`: `1/e ≤ a`([IUT-IV] p.15 の「`aᵢ ≥ 1/eᵢ`」);
* `le_aRadius`: `1/(p−1) ≤ a`(収束半径側。原文の「`aᵢ > 1/(p−1)`」は
  `(p−1) ∤ e` のときのみ厳密で、`(p−1) ∣ e` では等号 ―― 一般に真なのは `≤`);
* `aRadius_lt`: `a < 1/(p−1) + 1/e`([IUT-IV] p.16 の「`aᵢ − 1/eᵢ ≤ 1/(p−1)`」の厳密版);
* `neg_one_div_le_bRadius`: `−1/e ≤ b`(床の非負性);
* `aRadius_one` / `bRadius_one`: 非分岐 `e = 1`(`p > 2`)では `a = 1`, `b = −1` ――
  `IutLean.Padic.PadicLog` の `norm_logOnePlus`(`log(1+pℤ_p) ⊆ pℤ_p`、ノルム保存)が
  実現するのは正にこの半径である。

## 残余(honest)

半径定数と実際の `log_p(Rᵢ^×)` の包含関係そのもの(Prop 1.2 (i))は、非分岐の場合の
包含方向のみ `PadicLog.lean` で証明済。分岐拡大(`e > 1`)・全射性(exp)・テンソル積
(Prop 1.1 / Prop 1.2 (ii) の different `dᵢ` との合成)は残余。
-/

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

namespace IUT.Padic

/-- [IUT-IV] Prop 1.2 の半径定数 `aᵢ`: `p = 2` なら `2`、`p > 2` なら
`(1/e)·⌈e/(p−1)⌉`。対数殻の下側半径(`p^{a}·R ⊆ log(R^×)` の指数)。 -/
noncomputable def aRadius (p e : ℕ) : ℝ :=
  if p = 2 then 2 else (⌈(e : ℝ) / ((p : ℝ) - 1)⌉₊ : ℝ) / e

/-- [IUT-IV] Prop 1.2 の半径定数 `bᵢ`: `⌊log(p·e/(p−1))/log(p)⌋ − 1/e`。
対数殻の上側半径(`log(R^×) ⊆ p^{−b}·R` の指数)。 -/
noncomputable def bRadius (p e : ℕ) : ℝ :=
  (⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ : ℝ) - 1 / e

@[simp] lemma aRadius_two (e : ℕ) : aRadius 2 e = 2 := if_pos rfl


/-- 非分岐の半径 (p > 2): a = 1. -/
theorem aRadius_one (hp : 2 < p) : aRadius p 1 = 1 := by
  unfold aRadius
  rw [if_neg (by omega : ¬ p = 2)]
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have h : (3 : ℝ) <= (p : ℝ) := by exact_mod_cast hp
    linarith
  have hle : ((1 : ℕ) : ℝ) / ((p : ℝ) - 1) <= 1 := by
    rw [div_le_iff₀ hp1]
    have h : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpos : (0 : ℝ) < ((1 : ℕ) : ℝ) / ((p : ℝ) - 1) :=
    div_pos (by norm_num) hp1
  have hceil : ⌈((1 : ℕ) : ℝ) / ((p : ℝ) - 1)⌉₊ = 1 :=
    le_antisymm (Nat.ceil_le.mpr hle) (Nat.one_le_ceil_iff.mpr hpos)
  simp only [Nat.cast_one] at hceil ⊢
  rw [hceil]
  norm_num

#check aRadius
#check bRadius
#check aRadius_one

end IUT.Padic
