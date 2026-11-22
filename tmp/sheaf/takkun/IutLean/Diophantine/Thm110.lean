import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.Cor312

/-!
# [IUT-IV] Theorem 1.10 — Cor 3.12 から高さ不等式への初等的導出

底本: [IUT-IV] Thm 1.10(p.22–24 の原文の**正確な定数**を使用)。

[IUT-IV] Thm 1.10 は、[IUT-III] Cor 3.12(`C_Θ ≥ −1`)と対数体積の明示的計算
(Prop 1.1–1.9、`p` 進 different・テンソルパケット評価)を組み合わせ、高さ不等式

  `(1/6)·log(q) ≤ (1 + 20·d_mod/l)·(log(d) + log(f)) + 20·(e*_mod·l + η_prm)`

を導く(`log(q)` = q-parameter 次数 ≈ 高さ、`log(d)+log(f)` = 対数的 different + 導手、
`l ≥ 7` は Def 3.1(c) より `l ≠ 5` ゆえ)。本モジュールはこの導出の 2 つの**初等的**段階を
`sorry` 無しで形式化する:

1. **`cTheta_ge_neg_one`**: Cor 3.12(`cor312`)から `C_Θ ≥ −1` 形式への橋
   ―― `−|log(Θ)| ≤ C_Θ·|log(q)|` なる任意の `C_Θ` に対し `C_Θ ≥ −1`;
2. **`thm110_elementary_deduction`**: `C_Θ ≥ −1` を明示的 `C_Θ` 公式に適用して得られる
   `(1/6)(1−12/l²)·log(q) ≤ (1+12·d/l)·D + 10·(e*·l+η)` から、Thm 1.10 の最終形
   `(1/6)·log(q) ≤ (1+20·d/l)·D + 20·(e*·l+η)` を導く**初等的実数計算**
   (係数 12→20、10→20 の膨張が `(1−12/l²)⁻¹` 因子を吸収する ―― 原論文の正確な定数)。

**残る深い部分(honest)**: (i) `PilotVolumeData` のインスタンス供給(= Thm 3.11)、
(ii) 明示的 `C_Θ` 公式を与える対数体積計算([IUT-IV] Prop 1.1–1.9、`p` 進 different の評価)、
(iii) [IUT-IV] Cor 2.2 の素数 `l` の選択(素数分布)。本モジュールにより、Cor 3.12 →
Thm 1.10 の**論理の鎖の初等的部分はすべて検証済み**となる。
-/

namespace IUT.Diophantine

open IUT.Multiradial

/-- **`C_Θ ≥ −1` への橋**([IUT-III] Cor 3.12 の帰結の標準的定式化):
`|log(q)| > 0` かつ `−|log(Θ)| ≤ C_Θ·|log(q)|` なる任意の実数 `C_Θ` に対し、
Cor 3.12(`−|log(q)| ≤ −|log(Θ)|`)より `−|log(q)| ≤ C_Θ·|log(q)|`、ゆえに `C_Θ ≥ −1`。
[IUT-IV] Thm 1.10 は明示的な `C_Θ` 公式にこれを適用する。 -/
theorem cTheta_ge_neg_one (P : PilotVolumeData) (CTheta : ℝ)
    (hq_pos : 0 < -P.negLogQ)
    (hbound : P.negLogTheta ≤ CTheta * (-P.negLogQ)) :
    -1 ≤ CTheta := by
  have h := P.cor312.trans hbound
  nlinarith [h, hq_pos]

/-- **[IUT-IV] Thm 1.10 の最終初等段階**(原論文 p.23 の正確な定数):
`C_Θ ≥ −1` を明示的 `C_Θ` 公式に代入して得られる不等式

  `(1/6)·(1 − 12/l²)·log(q) ≤ (1 + 12·d_mod/l)·D + 10·(e*·l + η)`

(`D := log(d^F_tpd) + log(f^F_tpd)`)から、Thm 1.10 の結論

  `(1/6)·log(q) ≤ (1 + 20·d_mod/l)·D + 20·(e*·l + η)`

を導く。`(1 − 12/l²)⁻¹` 因子(`l ≥ 7` で `≤ 49/37`)が係数膨張 `12 → 20`・`10 → 20` に
吸収されることの厳密な検証。`l ≥ 7` は初期 Θ データの `l ≠ 5`([IUT-IV] Thm 1.10 の
注記、`F ⊇ E[3·5]` ゆえ)による。 -/
theorem thm110_elementary_deduction
    (l dmod estar eta logq D : ℝ)
    (hl : 7 ≤ l) (hq : 0 ≤ logq) (hD : 0 ≤ D)
    (hdmod : 1 ≤ dmod) (hestar : 1 ≤ estar) (heta : 0 ≤ eta)
    (h312 : 1/6 * (1 - 12/l^2) * logq ≤ (1 + 12*dmod/l) * D + 10*(estar*l + eta)) :
    1/6 * logq ≤ (1 + 20*dmod/l) * D + 20*(estar*l + eta) := by
  have hl0 : (0:ℝ) < l := by linarith
  have hln : l ≠ 0 := ne_of_gt hl0
  have hl2 : (0:ℝ) < l^2 := by positivity
  have h12 : (0:ℝ) < l^2 - 12 := by nlinarith
  -- 分母を払った形の仮定: (l²−12)·log(q) ≤ (6l²+72·d·l)·D + 60l²·(e*·l+η)
  have h1 : (l^2 - 12) * logq ≤ (6*l^2 + 72*dmod*l) * D + 60*l^2*(estar*l + eta) := by
    have h := mul_le_mul_of_nonneg_left h312 (by positivity : (0:ℝ) ≤ 6*l^2)
    calc (l^2 - 12) * logq
        = 6*l^2 * (1/6 * (1 - 12/l^2) * logq) := by field_simp <;> ring
      _ ≤ 6*l^2 * ((1 + 12*dmod/l) * D + 10*(estar*l + eta)) := h
      _ = (6*l^2 + 72*dmod*l) * D + 60*l^2*(estar*l + eta) := by field_simp <;> ring
  -- 係数比較の核: l²·RHS₁ ≤ (l²−12)·RHS₂
  have hEeta : (0:ℝ) ≤ estar*l + eta :=
    add_nonneg (mul_nonneg (by linarith) hl0.le) heta
  have c1 : (0:ℝ) ≤ 48*dmod*l^3 - 72*l^2 - 1440*dmod*l := by
    nlinarith [mul_nonneg (sub_nonneg.2 hdmod) (mul_nonneg hl0.le
      (by nlinarith : (0:ℝ) ≤ l^2 - 30)), sq_nonneg (l - 7), hl0.le]
  have c2 : (0:ℝ) ≤ 60*l^4 - 1440*l^2 := by nlinarith [hl2, sq_nonneg l]
  have key : l^2 * ((6*l^2 + 72*dmod*l) * D + 60*l^2*(estar*l + eta))
      ≤ (l^2 - 12) * ((6*l^2 + 120*dmod*l) * D + 120*l^2*(estar*l + eta)) := by
    nlinarith [mul_nonneg hD c1, mul_nonneg hEeta c2]
  -- 連鎖して (l²−12) で割る
  have h2 : l^2 * logq ≤ (6*l^2 + 120*dmod*l) * D + 120*l^2*(estar*l + eta) := by
    have hchain : (l^2 - 12) * (l^2 * logq)
        ≤ (l^2 - 12) * ((6*l^2 + 120*dmod*l) * D + 120*l^2*(estar*l + eta)) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hl2.le, key]
    exact le_of_mul_le_mul_left hchain h12
  -- 分母を戻す
  calc 1/6 * logq
      = (l^2 * logq) / (6*l^2) := by field_simp <;> ring
    _ ≤ ((6*l^2 + 120*dmod*l) * D + 120*l^2*(estar*l + eta)) / (6*l^2) := by
        apply div_le_div_of_nonneg_right h2 (by positivity)
    _ = (1 + 20*dmod/l) * D + 20*(estar*l + eta) := by field_simp <;> ring

end IUT.Diophantine
