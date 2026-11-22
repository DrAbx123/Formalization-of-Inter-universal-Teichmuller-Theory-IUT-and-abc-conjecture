import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.TwoSidedLink
import tmp.sheaf.takkun.IutLean.Diophantine.Thm110
import tmp.sheaf.takkun.IutLean.Arithmetic.PilotDegrees

/-!
# 判定テスト (Adjudication Test) — 係争を判定するための完全なテストハーネス

底本: [IUT-III] Cor 3.12 / [IUT-IV] Thm 1.10(原文の正確な定数・公式)/
Scholze–Stix (2018) / 本プロジェクトの 2 側形式化(`TwoSidedLink.lean`)。

**これが「テスト」の正確な仕様である。** 楕円曲線の実データ(`ArithmeticData`: bad 素点での
q-parameter の付値 `v(q)`、剰余体ノルムの対数、次数・分岐の誤差項)から:

* 受信側体積 `|log q| = v(q)·log N(v)/(2l)`([IUT-IV] p.23 の正確な正規化);
* 送信側体積 = `arithFactor · |log q|`、`arithFactor = l(l+1)/12`(`PilotDegrees.lean` で
  テータ値 `q^{j²}` のプロセッション正規化から**計算**された実際の値);
* 包の体積上界 = **`C_Θ` 公式**([IUT-IV] Thm 1.10 原文そのまま)

にピン留めされた 2 側比較データ(`ThetaLinkComparison`)の存在 ―― `AdjudicationTest` ―― を問う。

**検証済みの帰結(本モジュールの定理、全て `sorry` 無し)**:

1. **`adjudication_implies_height`(テスト通過 ⟹ 高さ不等式)**: テストが通れば、その曲線
   について [IUT-IV] Thm 1.10 の高さ不等式が従う ―― Cor 3.12 → C_Θ ≥ −1 → 初等的導出の
   **完全に検証された連鎖**。望月の証明の転写がこのテストを通せば、ABC への道が開通する。
2. **`adjudication_not_relabeling`(テストは同一視では通せない)**: テストを実現する任意の
   比較データは `IsRelabeling` であり得ない ―― 「ℝ の同一視」で型を通す道は**閉じている**。
3. **`adjudication_distortion`(通過の定量的代価)**: テストを実現する比較データの Θリンクは、
   標対象において体積歪み `≥ (l(l+1)/12 − 1)·|log q|` を持たねばならない ―― 実現すべき
   「同一視ならざる比較」の大きさの厳密な下界。
4. **`adjudication_toSupply`**: テストは `TwoSidedSupply`(係争の残余主張)の算術的
   インスタンスそのもの。

**判定の実施**: 望月の証明([IUT-III] Thm 3.11 + Cor 3.12 の証明文)を実際の Hodge 劇場の上で
転写し、`A.AdjudicationTest` 型の項の構成を試みる。構成できれば望月の勝利(定理 1 により
高さ不等式まで自動)、構成が必然的に `IsRelabeling` を経由するなら空虚(定理 2 により排除
済みの道)、構成不能の証明ができれば Scholze–Stix の完全勝利。本モジュールは**採点基準の
全部**であり、テストの実施(転写)は幾何学的実体化(実際の Hodge 劇場・エタールテータ・
対数 Kummer)を要する残存作業である。
-/

namespace IUT.Arithmetic

open IUT.Multiradial

/-- **算術データ**: 判定テストの入力となる楕円曲線の実データ ――
素数 `l ≥ 7`(奇、[IUT-IV] Thm 1.10 の `l ≠ 5`)、bad 素点での q-parameter の付値
`v(q) ≥ 1`(乗法的還元 ⟹ 非単数)、剰余体ノルムの対数 `log N(v) > 0`、
誤差項データ(`d_mod ≥ 1` 次数、`e* ≥ 1` 分岐、`η ≥ 0`、`D = log(d)+log(f) ≥ 0`
different + 導手)。 -/
structure ArithmeticData where
  /-- 素数 `l`(`≥ 7`、奇)。 -/
  l : ℕ
  hl : 7 ≤ l
  hodd : Odd l
  /-- bad 素点での q-parameter の付値 `v(q) ≥ 1`。 -/
  vq : ℕ
  hvq : 1 ≤ vq
  /-- 剰余体ノルムの対数 `log N(v) > 0`。 -/
  logNv : ℝ
  hlogNv : 0 < logNv
  /-- `d_mod = [F_mod : ℚ] ≥ 1`。 -/
  dmod : ℝ
  hdmod : 1 ≤ dmod
  /-- `e*_mod ≥ 1`(分岐指数項)。 -/
  estar : ℝ
  hestar : 1 ≤ estar
  /-- `η_prm ≥ 0`([IUT-IV] Prop 1.6)。 -/
  eta : ℝ
  heta : 0 ≤ eta
  /-- `D = log(d^F_tpd) + log(f^F_tpd) ≥ 0`(対数的 different + 導手)。 -/
  D : ℝ
  hD : 0 ≤ D

namespace ArithmeticData

variable (A : ArithmeticData)

/-- 完全な `log(q) = v(q)·log N(v)`(q-parameter の数論的次数)。 -/
def logq : ℝ := (A.vq : ℝ) * A.logNv

theorem logq_pos : 0 < A.logq := by
  have h1 : (1 : ℝ) ≤ (A.vq : ℝ) := by exact_mod_cast A.hvq
  have := A.hlogNv
  unfold logq
  nlinarith

theorem l_cast_ge : (7 : ℝ) ≤ (A.l : ℝ) := by exact_mod_cast A.hl

theorem l_cast_pos : (0 : ℝ) < (A.l : ℝ) := by linarith [A.l_cast_ge]

/-- **受信側の q標対象体積** `|log q|_{Cor 3.12} = log(q)/(2l)`([IUT-IV] p.23 の正確な正規化)。 -/
noncomputable def qVol : ℝ := A.logq / (2 * A.l)

theorem qVol_pos : 0 < A.qVol :=
  div_pos A.logq_pos (by linarith [A.l_cast_pos])

/-- **算術的 Gauss 因子** `l(l+1)/12`(`PilotDegrees.lean` でテータ値のプロセッション正規化
から計算された、送信側/受信側の体積比の実際の値)。 -/
noncomputable def arithFactor : ℝ := ((A.l : ℝ) * ((A.l : ℝ) + 1)) / 12

theorem arithFactor_gt_one : 1 < A.arithFactor :=
  IUT.Arithmetic.arithFactor_gt_one A.l A.hl

/-- **`C_Θ` 公式**([IUT-IV] Thm 1.10 原文): `(l+1)/(4·|log q|)·{(1+12·d_mod/l)·D +
10·(e*·l+η) − (1/6)(1−12/l²)·log q} − 1`(`|log q| = log q/(2l)` を代入し
`(l+1)·l/(2·log q)` に整理)。 -/
noncomputable def cThetaFormula : ℝ :=
  ((A.l : ℝ) + 1) * (A.l : ℝ) / (2 * A.logq) *
    ((1 + 12 * A.dmod / (A.l : ℝ)) * A.D + 10 * (A.estar * (A.l : ℝ) + A.eta)
      - 1 / 6 * (1 - 12 / (A.l : ℝ) ^ 2) * A.logq) - 1

/-- **判定テスト**: 実データ `A` にピン留めされた 2 側比較データの存在 ――
(i) 受信側 q標体積 = 実際の `−|log q|`; (ii) 送信側 Θ標体積 = `l(l+1)/12` 倍(実際の
Gauss 因子); (iii) 受信側の包が転送された全可能像を含む; (iv) **包の受信側体積が
`C_Θ` 公式で上から抑えられる**(= [IUT-IV] Prop 1.1–1.9 の対数体積計算の主張)。

これの構成可能性が係争の全部である。 -/
def AdjudicationTest : Prop :=
  ∃ (T : ThetaLinkComparison.{0, 0, 0}) (hullR : T.Recv),
    T.volR T.qPilot = -A.qVol ∧
    T.volS T.thetaPilot = A.arithFactor * T.volR T.qPilot ∧
    (∀ g : T.Γ, T.link (g • T.thetaPilot) ≤ hullR) ∧
    T.volR hullR ≤ A.cThetaFormula * A.qVol

/-- **定理 1(テスト通過 ⟹ 高さ不等式)**: 判定テストが通れば、その曲線について
[IUT-IV] Thm 1.10 の高さ不等式

  `(1/6)·log(q) ≤ (1 + 20·d_mod/l)·D + 20·(e*·l + η)`

が従う ―― Cor 3.12(包含+単調性)→ `C_Θ ≥ −1` → 初等的導出、の**完全に検証された連鎖**。 -/
theorem adjudication_implies_height (h : A.AdjudicationTest) :
    1 / 6 * A.logq
      ≤ (1 + 20 * A.dmod / (A.l : ℝ)) * A.D + 20 * (A.estar * (A.l : ℝ) + A.eta) := by
  obtain ⟨T, hullR, hpin, hdeg, hcontain, hbound⟩ := h
  -- Cor 3.12 の導出: q標 ≤ 包(g = 1 の像が q標)、体積単調性
  have h1 : T.qPilot ≤ hullR := by
    have hg := hcontain 1
    rwa [one_smul, T.link_pilot] at hg
  have h2 : T.volR T.qPilot ≤ T.volR hullR := T.volR_mono h1
  -- −|log q| ≤ C_Θ·|log q|
  have h3 : -A.qVol ≤ A.cThetaFormula * A.qVol := by
    have := h2.trans hbound
    rwa [hpin] at this
  -- C_Θ 公式の括弧内 X が非負であることを導く
  have hqv := A.qVol_pos
  have hlq := A.logq_pos
  have hl0 := A.l_cast_pos
  have hK : (0 : ℝ) < ((A.l : ℝ) + 1) * (A.l : ℝ) / (2 * A.logq) :=
    div_pos (mul_pos (by linarith) hl0) (by linarith)
  have hKq : (0 : ℝ) < ((A.l : ℝ) + 1) * (A.l : ℝ) / (2 * A.logq) * A.qVol :=
    mul_pos hK hqv
  have hXnn : (0 : ℝ)
      ≤ (1 + 12 * A.dmod / (A.l : ℝ)) * A.D + 10 * (A.estar * (A.l : ℝ) + A.eta)
        - 1 / 6 * (1 - 12 / (A.l : ℝ) ^ 2) * A.logq := by
    by_contra hneg
    push_neg at hneg
    have hlt := mul_neg_of_pos_of_neg hKq hneg
    simp only [cThetaFormula] at h3
    nlinarith [h3, hlt]
  -- 初等的導出([IUT-IV] Thm 1.10 の最終段階、検証済み)へ接続
  have h312 : 1 / 6 * (1 - 12 / (A.l : ℝ) ^ 2) * A.logq
      ≤ (1 + 12 * A.dmod / (A.l : ℝ)) * A.D + 10 * (A.estar * (A.l : ℝ) + A.eta) := by
    linarith [hXnn]
  exact IUT.Diophantine.thm110_elementary_deduction (A.l : ℝ) A.dmod A.estar A.eta A.logq A.D
    A.l_cast_ge A.logq_pos.le A.hD A.hdmod A.hestar A.heta h312

/-- **定理 2(テストは同一視では通せない)**: テストのピン留め条件を満たす任意の比較データは
`IsRelabeling`(体積を保つ「ℝ の同一視」)であり得ない ―― 型を通す近道は存在しない。 -/
theorem adjudication_not_relabeling (T : ThetaLinkComparison.{0, 0, 0})
    (hpin : T.volR T.qPilot = -A.qVol)
    (hdeg : T.volS T.thetaPilot = A.arithFactor * T.volR T.qPilot) :
    ¬ T.IsRelabeling := by
  intro hrel
  have hq : T.volR T.qPilot < 0 := by
    rw [hpin]
    linarith [A.qVol_pos]
  exact T.link_not_isometric A.arithFactor A.arithFactor_gt_one hq hdeg (hrel T.thetaPilot)

/-- **定理 3(通過の定量的代価)**: テストのピン留め条件を満たす比較データの Θリンクは、
標対象において体積歪み `≥ (l(l+1)/12 − 1)·|log q|` を持たねばならない ――
「同一視ならざる比較」が実現すべき歪みの大きさの厳密な下界(高さに比例して増大)。 -/
theorem adjudication_distortion (T : ThetaLinkComparison.{0, 0, 0})
    (hpin : T.volR T.qPilot = -A.qVol)
    (hdeg : T.volS T.thetaPilot = A.arithFactor * T.volR T.qPilot) :
    (A.arithFactor - 1) * A.qVol
      ≤ |T.volR (T.link T.thetaPilot) - T.volS T.thetaPilot| := by
  have h := T.bounded_distortion_bounds_height A.arithFactor
    (|T.volR (T.link T.thetaPilot) - T.volS T.thetaPilot|)
    A.arithFactor_gt_one hdeg (le_refl _)
  rw [hpin, neg_neg] at h
  have hf1 : (0 : ℝ) < A.arithFactor - 1 := by linarith [A.arithFactor_gt_one]
  rw [le_div_iff₀ hf1] at h
  nlinarith [h]

/-- **定理 4**: 判定テストは `TwoSidedSupply`(係争の残余主張)の算術的インスタンスそのもの。 -/
theorem adjudication_toSupply (h : A.AdjudicationTest) :
    TwoSidedSupply A.arithFactor A.cThetaFormula := by
  obtain ⟨T, hullR, hpin, hdeg, hcontain, hbound⟩ := h
  refine ⟨T, hullR, ?_, hdeg, hcontain, ?_⟩
  · rw [hpin]
    linarith [A.qVol_pos]
  · rw [hpin, neg_neg]
    exact hbound

end ArithmeticData

end IUT.Arithmetic
