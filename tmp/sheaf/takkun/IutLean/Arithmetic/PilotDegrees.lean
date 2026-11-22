import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.Cor312

/-!
# 標対象の算術的次数 — 実際の q-parameter からの Gauss 因子の計算

底本: [IUT-I] Example 3.2 (iv)(`q̲_v` = q-parameter の `2l` 乗根)/ [IUT-IV] p.23
(`|log(q)|_{Cor 3.12} = (1/2l)·log(q)`)/ [IUT-III] Remark 3.1.1(プロセッション正規化)。

判定テスト(`Arithmetic/AdjudicationTest.lean`)を**本物の算術値**で実施するための計算層:

* q標対象の受信側正規化体積 `|log q| = (1/2l)·v(q)·log N(v)`;
* Θ標対象の送信側正規化体積 = テータ値 `q^{j²}`(`j = 1,…,l⋆`)のプロセッション正規化平均
  `(1/l⋆)·∑ j²·|log q|`;
* **算術的 Gauss 因子** `(1/l⋆)·∑_{j=1}^{l⋆} j² = l(l+1)/12`(`twelve_mul_thetaPilotDegree`
  からの実数版)―― 送信側/受信側の体積比 `factor` の**実際の値**。

これにより `TwoSidedLink.lean` の抽象的 `factor` が、楕円曲線の q-parameter の付値という
実データから計算される具体的な `l(l+1)/12` にピン留めされる。
-/

namespace IUT.Arithmetic

open IUT IUT.Multiradial

/-- **プロセッション正規化テータ次数の実数値**: `(∑_{j=1}^{l⋆} j²)/l⋆ = l(l+1)/12`。
Θ標対象の送信側体積が q標対象の受信側体積の `l(l+1)/12` 倍であること ―― 判定テストの
`factor` の実際の値([IUT-IV] Thm 1.10 の `(l+1)/4·|log q|` 係数の源)。 -/
theorem thetaPilotDegree_div_lStar (l : ℕ) (hodd : Odd l) (hl : 7 ≤ l) :
    (thetaPilotDegree l : ℝ) / (lStar l : ℝ) = ((l : ℝ) * ((l : ℝ) + 1)) / 12 := by
  have h12 := twelve_mul_thetaPilotDegree l hodd
  have hstar : 1 ≤ lStar l := by unfold lStar; omega
  have hs : (0 : ℝ) < (lStar l : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hstar
  have hcast : (12 : ℝ) * (thetaPilotDegree l : ℝ)
      = (lStar l : ℝ) * ((l : ℝ) * ((l : ℝ) + 1)) := by exact_mod_cast h12
  field_simp
  linear_combination hcast

/-- **算術的 Gauss 因子は 1 より大きい**: `l ≥ 7` のとき `l(l+1)/12 ≥ 56/12 > 1`。
判定テストの well-posedness(`factor > 1` が空虚性・崩壊定理の適用条件)。 -/
theorem arithFactor_gt_one (l : ℕ) (hl : 7 ≤ l) :
    (1 : ℝ) < ((l : ℝ) * ((l : ℝ) + 1)) / 12 := by
  have h : (7 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  nlinarith

end IUT.Arithmetic
