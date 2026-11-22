import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
/-!
# p 進対数 — [IUT-IV] Prop 1.2 (i) の解析的核心(非分岐の場合)

底本: [IUT-IV] Proposition 1.2 (Differents and Logarithms), (i):
`p^{aᵢ}·Rᵢ ⊆ log_p(Rᵢ^×) ⊆ p^{−bᵢ}·Rᵢ`(`p > 2` かつ `eᵢ ≤ p−2` なら両方等号)。
その証明は「p 進対数・指数の周知の理論 [cf. [Kobl], p. 81]」を引く ―― Mathlib には
p 進対数が存在しないため、本モジュールで**一から構築**する。

## 証明済(本モジュールの内容、全て標準公理のみ)

* `logTerm` / `logOnePlus`: 級数 `log(1+x) = ∑_{n≥0} (−1)ⁿ xⁿ⁺¹/(n+1)` の定義;
* `summable_logTerm`: `‖x‖ < 1` での**無条件収束**(非アルキメデス完備群の総和判定
  `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` + 幾何級数×多項式の消滅);
* `norm_logOnePlus`: **ノルム保存** `‖log(1+x)‖ = ‖x‖`(`p > 2`, `‖x‖ ≤ 1/p`)――
  首項 `x` が残りの全項を厳密に支配する(ultrametric の等号 `add_eq_max_of_ne`)。
  これは Prop 1.2 (i) の非分岐の場合(`e = 1`, `a = 1 = −b`)の
  **包含 `log(1+pℤ_p) ⊆ pℤ_p` + 対数殻の体積公式の核**である:
  `log` は各殻 `pᵏℤ_p`(`k ≥ 1`)をノルムを変えずに写す = **対数は体積を保存する**
  (対数殻の log-volume 正規化 [IUT-IV] §1 の根拠)。
* `logOnePlus_shell`: 整構造 `ℤ_[p]` 上の殻の言明 ――
  `log(1 + p·y) = p·z` かつ `‖z‖ = ‖y‖`(`y ∈ ℤ_[p]`)。

## 残余(honest、本モジュールでは主張しない)

* `log` の**準同型性** `log(uv) = log u + log v`(形式冪級数の合成恒等式が必要);
* `p^{a}·R ⊆ log(R^×)` の**全射性**(p 進指数 `exp` の構築と `log∘exp = id` が必要);
* 分岐拡大 `e > 1` の場合(`ℚ_p` の有限拡大とその付値・分岐理論が必要 ――
  受け皿として Mathlib の `PadicAlgCl p`(スペクトルノルム付き代数閉包、
  `Mathlib.NumberTheory.Padics.Complex`)が使える);
* Teichmüller 分解 `R^× = μ × (1+m)`(`log(R^×) = log(1+m)` の同定に必要)。

半径定数 `aᵢ, bᵢ` の数値骨格は `IutLean.Padic.LogShellRadius` を見よ。
-/

namespace IUT.Padic

open Filter Topology IsUltrametricDist

variable {p : ℕ} [hp : Fact p.Prime]

/-- p 進対数級数の第 `n` 項: `(−1)ⁿ · xⁿ⁺¹ / (n+1)`。 -/
noncomputable def logTerm (x : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  (-1) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : ℚ_[p])

/-- 首項は `x` そのもの。 -/
@[simp] lemma logTerm_zero (x : ℚ_[p]) : logTerm x 0 = x := by
  simp [logTerm]

/-- `x = 0` では全項が消える。 -/
@[simp] lemma logTerm_of_zero (n : ℕ) : logTerm (0 : ℚ_[p]) n = 0 := by
  simp [logTerm]

/-- 自然数の p 進ノルムの厳密値: `‖m‖ = p^{−v_p(m)}`(`m ≠ 0`)。 -/
lemma norm_natCast_eq (m : ℕ) (hm : m ≠ 0) :
    ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
  have h0 : ((m : ℚ) : ℚ_[p]) = (m : ℚ_[p]) := by norm_cast
  rw [← h0, Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm), padicValRat.of_nat]
  push_cast
  rfl

/-- 自然数の p 進ノルムの下界: `1/m ≤ ‖m‖`(`p^{v_p(m)} ∣ m` ゆえ)。
対数級数の分母 `n+1` の暴れを制御する基本評価。 -/
lemma inv_le_norm_natCast (m : ℕ) (hm : m ≠ 0) : ((m : ℝ))⁻¹ ≤ ‖(m : ℚ_[p])‖ := by
  rw [norm_natCast_eq m hm, zpow_neg, zpow_natCast]
  have h1 : (p : ℝ) ^ padicValNat p m ≤ (m : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm) pow_padicValNat_dvd
  have h2 : (0 : ℝ) < (p : ℝ) ^ padicValNat p m := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
    exact pow_pos hp0 _
  gcongr

/-- 対数級数の項の粗い評価: `‖logTerm x n‖ ≤ (n+1)·‖x‖ⁿ⁺¹`(収束の判定に十分)。 -/
lemma norm_logTerm_le (x : ℚ_[p]) (n : ℕ) :
    ‖logTerm x n‖ ≤ ((n : ℝ) + 1) * ‖x‖ ^ (n + 1) := by
  have hm : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  have hpos : (0 : ℝ) < ‖((n + 1 : ℕ) : ℚ_[p])‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hm
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkey : (1 : ℝ) ≤ ((n : ℝ) + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖ := by
    have h1 := inv_le_norm_natCast (p := p) (n + 1) hm
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    calc (1 : ℝ) = ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := (mul_inv_cancel₀ hn1.ne').symm
      _ ≤ ((n : ℝ) + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖ := by
          apply mul_le_mul_of_nonneg_left _ hn1.le
          rw [← hcast]; exact h1
  unfold logTerm
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    div_le_iff₀ hpos]
  calc ‖x‖ ^ (n + 1) = ‖x‖ ^ (n + 1) * 1 := (mul_one _).symm
    _ ≤ ‖x‖ ^ (n + 1) * (((n : ℝ) + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖) := by
        apply mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((n : ℝ) + 1) * ‖x‖ ^ (n + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖ := by ring

/-- **p 進対数級数の無条件収束**(`‖x‖ < 1`): 非アルキメデス完備群では
「項が 0 に収束」だけで総和可能(アルキメデスとの決定的な差)。 -/
theorem summable_logTerm {x : ℚ_[p]} (hx : ‖x‖ < 1) : Summable (logTerm x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  have hr : ‖(‖x‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_norm]
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ‖x‖ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  simp only [pow_one] at hs
  have hg : Tendsto (fun n : ℕ => (n : ℝ) * ‖x‖ ^ n) atTop (𝓝 0) := hs.tendsto_atTop_zero
  have hg1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ‖x‖ ^ (n + 1)) atTop (𝓝 0) := by
    have h := hg.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  exact squeeze_zero_norm (norm_logTerm_le x) hg1

/-- **p 進対数** `log(1+x) := ∑_{n≥0} (−1)ⁿ xⁿ⁺¹/(n+1)`。
`‖x‖ < 1` で収束(`summable_logTerm`)、それ以外では `tsum` 既定値 0。 -/
noncomputable def logOnePlus (x : ℚ_[p]) : ℚ_[p] := ∑' n, logTerm x n

@[simp] lemma logOnePlus_zero : logOnePlus (0 : ℚ_[p]) = 0 := by
  simp [logOnePlus]

/-- 補助数値評価: `n + 2 < 3ⁿ⁺¹`(奇素数の分母の暴れが幾何減衰に負けることの源)。 -/
private lemma add_two_lt_three_pow (n : ℕ) : n + 2 < 3 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h : 3 ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by rw [pow_succ]; ring
    omega

/-- **尾部の一様評価**(`p` 奇素数, `‖x‖ ≤ 1/p`): 第 2 項以降は全て
`‖logTerm x (n+1)‖ ≤ ‖x‖/p` ―― 首項 `x` より一様に p 倍小さい。
`p = 2` ではこの評価は破綻する(`x²/2` が首項と同じ大きさになり得る ――
[IUT-IV] Prop 1.2 で `p = 2` のとき `aᵢ = 2` と特別扱いされる理由)。 -/
lemma norm_logTerm_succ_le {x : ℚ_[p]} (hp3 : 3 ≤ p) (hx : ‖x‖ ≤ (p : ℝ)⁻¹) (n : ℕ) :
    ‖logTerm x (n + 1)‖ ≤ ‖x‖ * (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  -- 鍵: v_p(n+2) ≤ n(さもなくば p^{n+1} ≤ n+2 < 3^{n+1} ≤ p^{n+1} で矛盾)
  have hvle : padicValNat p (n + 1 + 1) ≤ n := by
    by_contra hcon
    have hcon' : n < padicValNat p (n + 1 + 1) := Nat.lt_of_not_le hcon
    have h1 : p ^ (n + 1) ∣ (n + 1 + 1) :=
      dvd_trans (pow_dvd_pow p hcon') pow_padicValNat_dvd
    have h2 : p ^ (n + 1) ≤ n + 1 + 1 := Nat.le_of_dvd (by omega) h1
    have h3 : 3 ^ (n + 1) ≤ p ^ (n + 1) := Nat.pow_le_pow_left hp3 _
    have h4 : n + 2 < 3 ^ (n + 1) := add_two_lt_three_pow n
    omega
  unfold logTerm
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_natCast_eq (n + 1 + 1) (by omega), zpow_neg, zpow_natCast,
    div_eq_mul_inv, inv_inv]
  calc ‖x‖ ^ (n + 1 + 1) * (p : ℝ) ^ padicValNat p (n + 1 + 1)
      = ‖x‖ * (‖x‖ ^ (n + 1) * (p : ℝ) ^ padicValNat p (n + 1 + 1)) := by ring
    _ ≤ ‖x‖ * (((p : ℝ)⁻¹) ^ (n + 1) * (p : ℝ) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
        apply mul_le_mul
        · exact pow_le_pow_left₀ (norm_nonneg x) hx _
        · exact pow_le_pow_right₀ hp1 hvle
        · positivity
        · positivity
    _ = ‖x‖ * (p : ℝ)⁻¹ := by
        congr 1
        rw [inv_pow, pow_succ]
        field_simp
    _ ≤ ‖x‖ * (p : ℝ)⁻¹ := le_refl _

/-- **ノルム保存 = 対数殻の体積公式の核**([IUT-IV] Prop 1.2 (i)、非分岐 `e = 1`,
`p > 2`, 包含方向): `‖log(1+x)‖ = ‖x‖`(`‖x‖ ≤ 1/p`)。

首項 `x` が尾部(`norm_logTerm_succ_le` で一様に `‖x‖/p` 以下)を厳密に支配するので、
ultrametric の等号 `‖x + T‖ = max(‖x‖,‖T‖) = ‖x‖` が成立する。したがって
`log` は `1 + pᵏℤ_p` を `pᵏℤ_p` の中へ**各殻の深さを保って**写す ――
対数殻の log-volume が well-defined である(体積を保存する)ことの解析的内容。
全射性(= 等号 `log(1+pℤ_p) = pℤ_p` の残り半分)は `exp` の構築を要する(残余)。 -/
theorem norm_logOnePlus {x : ℚ_[p]} (hp2 : p ≠ 2) (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
    ‖logOnePlus x‖ = ‖x‖ := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.out.two_le
    omega
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx (inv_lt_one_of_one_lt₀ hpR)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hsum : Summable (logTerm x) := summable_logTerm hx1
  rw [logOnePlus, hsum.tsum_eq_zero_add, logTerm_zero]
  have htail : Summable (fun n : ℕ => logTerm x (n + 1)) :=
    hsum.comp_injective (fun a b h => Nat.succ_injective h)
  have hTle : ‖∑' n, logTerm x (n + 1)‖ ≤ ‖x‖ * (p : ℝ)⁻¹ := by
    refine le_of_tendsto_of_tendsto' htail.hasSum.norm tendsto_const_nhds ?_
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
      positivity
    · exact norm_sum_le_of_forall_le_of_nonneg (by positivity)
        (fun n _ => norm_logTerm_succ_le hp3 hx n)
  have hTlt : ‖∑' n, logTerm x (n + 1)‖ < ‖x‖ := by
    apply lt_of_le_of_lt hTle
    have h0x : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    calc ‖x‖ * (p : ℝ)⁻¹ < ‖x‖ * 1 := by
          apply mul_lt_mul_of_pos_left (inv_lt_one_of_one_lt₀ hpR) h0x
      _ = ‖x‖ := mul_one _
  rw [Padic.add_eq_max_of_ne hTlt.ne']
  exact max_eq_left hTlt.le

/-- 包含方向の系: `log(1+x) ∈ pℤ_p`(ノルムの言葉で)。
[IUT-IV] Prop 1.2 (i) の上側包含 `log_p(1+pℤ_p) ⊆ p^{−b}·R`(`e=1`, `b=−1`, `p>2`)。 -/
theorem norm_logOnePlus_le {x : ℚ_[p]} (hp2 : p ≠ 2) (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
    ‖logOnePlus x‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_logOnePlus hp2 hx]; exact hx

/-- **整構造 `ℤ_[p]` 上の対数殻**(`p > 2`): 任意の `y ∈ ℤ_[p]` に対し
`log(1 + p·y) = p·z` なる `z ∈ ℤ_[p]` が存在し、しかも `‖z‖ = ‖y‖`(殻の深さの保存)。
`realHodgeTheater` の局所対象(`ℚ_[p]` とその整構造)の上での Prop 1.2 (i) の実現。 -/
theorem logOnePlus_shell (hp2 : p ≠ 2) (y : ℤ_[p]) :
    ∃ z : ℤ_[p], logOnePlus ((p : ℚ_[p]) * (y : ℚ_[p])) = (p : ℚ_[p]) * (z : ℚ_[p]) ∧
      ‖(z : ℚ_[p])‖ = ‖(y : ℚ_[p])‖ := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := by
    have : (p : ℕ) ≠ 0 := hp.out.ne_zero
    exact_mod_cast this
  have hy1 : ‖(y : ℚ_[p])‖ ≤ 1 := by
    rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one y
  have hxnorm : ‖(p : ℚ_[p]) * (y : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, Padic.norm_p]
    exact mul_le_of_le_one_right (by positivity) hy1
  have hnorm := norm_logOnePlus hp2 hxnorm
  have hpnorm : ‖(p : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
  have hnz : ‖logOnePlus ((p : ℚ_[p]) * (y : ℚ_[p])) / (p : ℚ_[p])‖ = ‖(y : ℚ_[p])‖ := by
    rw [norm_div, hnorm, norm_mul, mul_div_cancel_left₀ _ hpnorm]
  refine ⟨⟨logOnePlus ((p : ℚ_[p]) * (y : ℚ_[p])) / (p : ℚ_[p]), by rw [hnz]; exact hy1⟩,
    ?_, hnz⟩
  change logOnePlus ((p : ℚ_[p]) * (y : ℚ_[p]))
      = (p : ℚ_[p]) * (logOnePlus ((p : ℚ_[p]) * (y : ℚ_[p])) / (p : ℚ_[p]))
  rw [mul_comm ((p : ℚ_[p])) (logOnePlus ((p : ℚ_[p]) * (y : ℚ_[p])) / (p : ℚ_[p])),
    div_mul_cancel₀ _ hp0]

end IUT.Padic
