import Mathlib
import tmp.sheaf.takkun.IutLean.Arithmetic.ExamAttempt

/-!
# 実曲線インスタンス — 曲線 11a3 による受験の続行

本モジュールは受験(`ExamAttempt.lean`)の続行として、**実在の楕円曲線**から判定テストの
入力データを構成する。対象は導手 11 の楕円曲線 **11a3**: `y² + y = x³ − x²`。

## 実際に計算・証明される曲線データ

* **`curve11a3_Δ : Δ = −11`**(判別式、Mathlib の Weierstrass 理論で計算);
* **`curve11a3_c₄ : c₄ = 16`**(c-不変量);
* ゆえに `v₁₁(Δ) = 1`, `v₁₁(c₄) = 0` ―― Tate の理論(`v(q) = v(Δ)`、`c₄` が単数の
  乗法的還元)により **`v₁₁(q) = 1`**。[Tate の q-展開理論そのものは Mathlib 未整備のため、
  この最後の一歩は引用であり、`Δ`・`c₄` の計算は完全に形式的。]
* `l = 7`(`7 ∤ Δ = −11` ゆえ 7 は good、`l ≥ 7` 奇 ✓)、`d_mod = 1`(`F_mod = ℚ(j) = ℚ`)、
  **`e* = 2¹²·3³·5·1 = 552960`**([IUT-IV] Thm 1.10 の真の値)。

## 受験結果と、その意味の形式的確定

* **`curve11a3_exam_passes`**: 曲線 11a3 のデータで判定テストは**合格する**(証明済み)。
* **しかし**閾値定理(`exam_passes_below_threshold` / `exam_fails_at_large_height`)が示す通り、
  固定された `(曲線, l)` での合格は**数値的閾値の問題**であり(架空の高さ `m ≤ 10⁷` でも通り、
  `m = 10⁹` では落ちる)、Szpiro/ABC の内容を**一切含まない**。ABC の内容は Cor 2.2 の
  **一様性**(曲線族全体、`l ∼ √(高さ)` のスケーリング)にのみ存する ――
  「単一曲線の合格 = 自明領域の合格」という事実の `sorry` 無しの確定。

すなわち受験の現状: **実曲線データの供給ラインは開通した**が、意味のある試験(一様な族の
試験)には Cor 2.2 の素数選択と、高さ・導手を曲線の幾何が結び付ける実装が必要である。
-/

namespace IUT.Arithmetic

open IUT.Multiradial

/-! ## 曲線 11a3 の形式的データ -/

/-- **楕円曲線 11a3**: `y² + y = x³ − x²`(`(a₁,a₂,a₃,a₄,a₆) = (0,−1,1,0,0)`、導手 11)。 -/
def curve11a3 : WeierstrassCurve ℚ := ⟨0, -1, 1, 0, 0⟩

/-- **判別式の計算**: `Δ(11a3) = −11`。ゆえに 11a3 は 11 の外で good reduction、
11 で `v₁₁(Δ) = 1`。 -/
theorem curve11a3_Δ : curve11a3.Δ = -11 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve11a3]
  norm_num

/-- **c₄ 不変量の計算**: `c₄(11a3) = 16`、特に `11 ∤ c₄` ―― `v₁₁(Δ) = 1` と併せ、
11 での還元は乗法的(node)で Tate の q-parameter は `v₁₁(q) = v₁₁(Δ) = 1`。 -/
theorem curve11a3_c₄ : curve11a3.c₄ = 16 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curve11a3]
  norm_num

/-! ## 数値評価(`log 11` の厳密な範囲) -/

theorem log_eleven_pos : 0 < Real.log 11 :=
  Real.log_pos (by norm_num)

theorem log_eleven_lt_four : Real.log 11 < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : (7 : ℝ) < Real.exp 1 * Real.exp 1 := by nlinarith
  have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
    simp only [← Real.exp_add]; norm_num
  rw [h4]
  nlinarith [h2]

theorem two_lt_log_eleven : 2 < Real.log 11 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_one_gt_d9]

/-! ## 11a3 の判定テストデータと受験 -/

/-- **曲線 11a3 の算術データ**: `l = 7`(`7 ∤ Δ` ✓)、`v(q) = 1`(`Δ = −11`, `c₄ = 16` の
計算による)、`log N(v) = log 11`、`d_mod = 1`(`F_mod = ℚ`)、`e* = 552960`
(`= 2¹²·3³·5·1`、[IUT-IV] の真の値)。`η ≥ 0`(η_prm)と `D ≥ 0`(different+導手)は
パラメータとして受け取る。 -/
noncomputable def curve11a3Data (eta D : ℝ) (heta : 0 ≤ eta) (hD : 0 ≤ D) : ArithmeticData where
  l := 7
  hl := le_refl 7
  hodd := Nat.odd_iff.mpr rfl
  vq := 1
  hvq := le_refl 1
  logNv := Real.log 11
  hlogNv := log_eleven_pos
  dmod := 1
  hdmod := le_refl 1
  estar := 552960
  hestar := by norm_num
  eta := eta
  heta := heta
  D := D
  hD := hD

/-- **受験合格(曲線 11a3)**: 実曲線データで判定テストは通る。

**ただし**(退化定理と下の閾値定理により)これは「固定曲線・固定 `l` では誤差項
`20·e*·l ≈ 7.7×10⁷` が高さ `(1/6)·log 11 ≈ 0.4` を圧倒する」という自明領域の合格であり、
Szpiro/ABC の内容を含まない。意味のある試験は曲線族への一様な試験(Cor 2.2)である。 -/
theorem curve11a3_exam_passes (eta D : ℝ) (heta : 0 ≤ eta) (hD : 0 ≤ D) :
    (curve11a3Data eta D heta hD).AdjudicationTest := by
  rw [ArithmeticData.adjudicationTest_iff_cTheta]
  set A := curve11a3Data eta D heta hD
  have hlogq : A.logq = Real.log 11 := by
    show ((1 : ℕ) : ℝ) * Real.log 11 = Real.log 11
    norm_num
  have hl : (A.l : ℝ) = 7 := by norm_num [A, curve11a3Data]
  have hd : A.dmod = 1 := rfl
  have he : A.estar = 552960 := rfl
  have het : A.eta = eta := rfl
  have hDD : A.D = D := rfl
  simp only [ArithmeticData.cThetaFormula, hlogq, hl, hd, he, het, hDD]
  have h4 := log_eleven_lt_four
  have h0 := log_eleven_pos
  have hK : (0 : ℝ) < (7 + 1) * 7 / (2 * Real.log 11) := by positivity
  have hX : (0 : ℝ) ≤ (1 + 12 * 1 / 7) * D + 10 * (552960 * 7 + eta)
      - 1 / 6 * (1 - 12 / 7 ^ 2) * Real.log 11 := by nlinarith
  nlinarith [mul_nonneg hK.le hX]

/-! ## 閾値定理 — 固定 (曲線, l) の合格が ABC の内容を含まないことの確定 -/

/-- 架空の高さ `m` を持つ 11a3 型データ(`η = D = 0`、閾値解析用)。 -/
noncomputable def heightVariedData (m : ℕ) (hm : 1 ≤ m) : ArithmeticData where
  l := 7
  hl := le_refl 7
  hodd := Nat.odd_iff.mpr rfl
  vq := m
  hvq := hm
  logNv := Real.log 11
  hlogNv := log_eleven_pos
  dmod := 1
  hdmod := le_refl 1
  estar := 552960
  hestar := by norm_num
  eta := 0
  heta := le_refl 0
  D := 0
  hD := le_refl 0

/-- **閾値定理(下)**: 架空の高さ `m ≤ 10⁷` まで判定テストは通り続ける ――
固定 `(曲線, l)` の合格は高さの実際の値にほぼ無関心(誤差項が圧倒する自明領域)。 -/
theorem exam_passes_below_threshold (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 10 ^ 7) :
    (heightVariedData m hm).AdjudicationTest := by
  rw [ArithmeticData.adjudicationTest_iff_cTheta]
  set A := heightVariedData m hm
  have hmr : (m : ℝ) ≤ 10 ^ 7 := by exact_mod_cast hm'
  have hmr1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogq : A.logq = (m : ℝ) * Real.log 11 := rfl
  have hl : (A.l : ℝ) = 7 := by norm_num [A, heightVariedData]
  have hd : A.dmod = 1 := rfl
  have he : A.estar = 552960 := rfl
  have het : A.eta = 0 := rfl
  have hDD : A.D = 0 := rfl
  simp only [ArithmeticData.cThetaFormula, hlogq, hl, hd, he, het, hDD]
  have h4 := log_eleven_lt_four
  have h0 := log_eleven_pos
  have hK : (0 : ℝ) < (7 + 1) * 7 / (2 * ((m : ℝ) * Real.log 11)) := by positivity
  have hX : (0 : ℝ) ≤ (1 + 12 * 1 / 7) * 0 + 10 * (552960 * 7 + 0)
      - 1 / 6 * (1 - 12 / 7 ^ 2) * ((m : ℝ) * Real.log 11) := by nlinarith
  nlinarith [mul_nonneg hK.le hX]

/-- **閾値定理(上)**: 架空の高さ `m = 10⁹` で判定テストは**証明可能に落ちる**。
下の閾値定理と併せ: 固定 `(曲線, l)` での合否は数値的閾値の問題に過ぎず、
Szpiro/ABC の内容(実曲線の高さが導手・different を追い越せないこと)を一切含まない ――
**意味のある試験は Cor 2.2 の一様な族の試験のみ**であることの形式的確定。 -/
theorem exam_fails_at_large_height :
    ¬ (heightVariedData (10 ^ 9) (by norm_num)).AdjudicationTest := by
  rw [ArithmeticData.adjudicationTest_iff_cTheta, not_le]
  set A := heightVariedData (10 ^ 9) (by norm_num)
  have hlogq : A.logq = ((10 ^ 9 : ℕ) : ℝ) * Real.log 11 := rfl
  have hl : (A.l : ℝ) = 7 := by norm_num [A, heightVariedData]
  have hd : A.dmod = 1 := rfl
  have he : A.estar = 552960 := rfl
  have het : A.eta = 0 := rfl
  have hDD : A.D = 0 := rfl
  simp only [ArithmeticData.cThetaFormula, hlogq, hl, hd, he, het, hDD]
  have h2 := two_lt_log_eleven
  have h0 := log_eleven_pos
  have hcast : ((10 ^ 9 : ℕ) : ℝ) = 10 ^ 9 := by norm_num
  rw [hcast]
  have hK : (0 : ℝ) < (7 + 1) * 7 / (2 * ((10 : ℝ) ^ 9 * Real.log 11)) := by positivity
  have hX : (1 + 12 * 1 / 7) * 0 + 10 * (552960 * 7 + 0)
      - 1 / 6 * (1 - 12 / 7 ^ 2) * ((10 : ℝ) ^ 9 * Real.log 11) < 0 := by nlinarith
  nlinarith [mul_neg_of_pos_of_neg hK hX]

end IUT.Arithmetic
