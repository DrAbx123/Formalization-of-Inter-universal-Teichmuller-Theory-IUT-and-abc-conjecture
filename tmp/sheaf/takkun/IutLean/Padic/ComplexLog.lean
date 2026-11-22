import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Finset.Basic
import tmp.sheaf.takkun.IutLean.Padic.PadicLog

/-!
# 一般の完備非アルキメデス的 ℚ_p-代数上の p 進対数 — 分岐拡大への拡張

底本: [IUT-IV] Proposition 1.2 (i)(分岐指数 `e ≥ 1` の局所体 `k_i` の対数殻)。

`PadicLog.lean` は `ℚ_p` 上(非分岐 `e = 1`)で対数を構築した。本モジュールはその構成を
**ノルムが `ℚ_p` のノルムを延長する任意の完備非アルキメデス的 `ℚ_p`-代数 `K`** に一般化する
(級数・収束・尾部評価・ノルム保存の全証明が逐語的に通る ―― 必要だったのは
`‖(n : K)‖ = p^{−v_p(n)}` だけであり、これはノルム延長から従う)。

実装は `K = ℂ_[p]`(`PadicComplex`、`ℚ̄_p` の完備化 ―― Mathlib の
`Mathlib.NumberTheory.Padics.Complex`、完備 + ultrametric + スペクトルノルム延長)。
**任意の有限拡大 `L/ℚ_p` は `ℚ̄_p ⊂ ℂ_p` に埋め込まれる**ので、これで分岐 `e > 1` の
局所体の対数殻がノルムのレベルで一挙にカバーされる:

## 証明済(全て標準公理のみ)

* `summable_logTermK` / `logOnePlusK`: 級数 `log(1+x)` の `K` 上の無条件収束と定義;
* `norm_logOnePlusK`: **ノルム保存** `‖log(1+x)‖ = ‖x‖`(`p > 2`, `‖x‖ ≤ 1/p`);
* `norm_extends_QC`: `ℚ_p → ℂ_[p]` のノルム延長(`IsScalarTower` 経由);
* `norm_complexLog` / `norm_complexLog_algebraic`: `ℂ_[p]` 上・および **`ℚ̄_p` の元**
  (= 実 Hodge 劇場 `Mon = ℚ̄_pˣ` の住人)に対するノルム保存 ――
  分岐拡大の主単数 `u`(`‖u−1‖ ≤ 1/p`)の対数が体積を保って定義される
  (log-link の実対象上の芽)。

さらに **鋭い収束半径**も証明済(`norm_logOnePlusK_sharp` / `norm_complexLog_sharp`):
仮定を `‖x‖ ≤ 1/p` から **`‖x‖^{p−1} < 1/p`(⟺ `ord(x) > 1/(p−1)`)** に弱める ――
これは [IUT-IV] Prop 1.2 (i) の下側半径 `aᵢ = ⌈e/(p−1)⌉/e` が(`(p−1) ∤ e` のとき)
保証する条件そのものであり、`p = 2` も含む(`ord > 1` ⟺ `a = 2` の `ℚ_2` 上の読みと整合)。
尾部の一様評価は境界で破綻するため、**「項は 0 に収束し各項は厳密に小さい ⟹ 上限も厳密に
小さい」**(`nnnorm_tsum_lt_of_forall_lt`、有限個の最大項論法)で置き換える。
境界 `ord = 1/(p−1)`(`(p−1) ∣ e` の場合に生じ得る)では `log ζ_p = 0` ゆえ
ノルム保存は**偽**であり、厳密不等号が本質的(`LogShellRadius.lean` の honest 注記と同源)。

## 残余(honest)

* log の像が `ℚ̄_p` に入ること(代数性の保存)は別の議論(有限拡大の完備性)を要する;
* 準同型性・exp(全射性)は `PadicLog.lean` と同じく残余;
* `ord` の言葉での鋭い半径(`aRadius` との形式的接続)は拡大体の付値の形式化が前提。
-/

namespace IUT.Padic

open Filter Topology IsUltrametricDist

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [Algebra ℚ_[p] K]

/-- 対数級数の第 `n` 項(一般の `ℚ_p`-代数 `K` 上): `(−1)ⁿ · xⁿ⁺¹ / (n+1)`。 -/
noncomputable def logTermK (x : K) (n : ℕ) : K :=
  (-1) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K)

omit [IsUltrametricDist K] in
@[simp] lemma logTermK_zero (x : K) : logTermK x 0 = x := by
  simp [logTermK]

omit [IsUltrametricDist K] in
@[simp] lemma logTermK_of_zero (n : ℕ) : logTermK (0 : K) n = 0 := by
  simp [logTermK]

section NormExtends

variable (hext : ∀ y : ℚ_[p], ‖algebraMap ℚ_[p] K y‖ = ‖y‖)
include hext

omit [IsUltrametricDist K] in
/-- ノルム延長のもとで自然数のノルムは `ℚ_p` と同一: `‖m‖ = p^{−v_p(m)}`。 -/
lemma norm_natCastK (m : ℕ) (hm : m ≠ 0) :
    ‖(m : K)‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
  rw [← map_natCast (algebraMap ℚ_[p] K) m, hext, norm_natCast_eq m hm]

omit [IsUltrametricDist K] in
/-- 対数級数の項の粗い評価(収束判定用): `‖logTermK x n‖ ≤ (n+1)·‖x‖ⁿ⁺¹`。 -/
lemma norm_logTermK_le (x : K) (n : ℕ) :
    ‖logTermK x n‖ ≤ ((n : ℝ) + 1) * ‖x‖ ^ (n + 1) := by
  have hm : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  have hpos : (0 : ℝ) < ‖((n + 1 : ℕ) : K)‖ := by
    rw [norm_natCastK hext (n + 1) hm]
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
    exact zpow_pos hp0 _
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkey : (1 : ℝ) ≤ ((n : ℝ) + 1) * ‖((n + 1 : ℕ) : K)‖ := by
    have h1 : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ ‖((n + 1 : ℕ) : K)‖ := by
      rw [← map_natCast (algebraMap ℚ_[p] K) (n + 1), hext]
      exact inv_le_norm_natCast (n + 1) hm
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    calc (1 : ℝ) = ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := (mul_inv_cancel₀ hn1.ne').symm
      _ ≤ ((n : ℝ) + 1) * ‖((n + 1 : ℕ) : K)‖ := by
          apply mul_le_mul_of_nonneg_left _ hn1.le
          rw [← hcast]; exact h1
  unfold logTermK
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    div_le_iff₀ hpos]
  calc ‖x‖ ^ (n + 1) = ‖x‖ ^ (n + 1) * 1 := (mul_one _).symm
    _ ≤ ‖x‖ ^ (n + 1) * (((n : ℝ) + 1) * ‖((n + 1 : ℕ) : K)‖) := by
        apply mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((n : ℝ) + 1) * ‖x‖ ^ (n + 1) * ‖((n + 1 : ℕ) : K)‖ := by ring

/-- **無条件収束**(`‖x‖ < 1`、`K` 完備): 非アルキメデス完備群の総和判定による。 -/
theorem summable_logTermK [CompleteSpace K] {x : K} (hx : ‖x‖ < 1) :
    Summable (logTermK x) := by
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
  exact squeeze_zero_norm (norm_logTermK_le hext x) hg1

omit [IsUltrametricDist K] in
/-- **尾部の一様評価**(`p` 奇素数, `‖x‖ ≤ 1/p`): 第 2 項以降は一様に
`‖logTermK x (n+1)‖ ≤ ‖x‖/p`(`PadicLog.lean` と同じ数値核 `v_p(n+2) ≤ n`)。 -/
lemma norm_logTermK_succ_le (hp3 : 3 ≤ p) {x : K} (hx : ‖x‖ ≤ (p : ℝ)⁻¹) (n : ℕ) :
    ‖logTermK x (n + 1)‖ ≤ ‖x‖ * (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  have hvle : padicValNat p (n + 1 + 1) ≤ n := by
    by_contra hcon
    have hcon' : n < padicValNat p (n + 1 + 1) := Nat.lt_of_not_le hcon
    have h1 : p ^ (n + 1) ∣ (n + 1 + 1) :=
      dvd_trans (pow_dvd_pow p hcon') pow_padicValNat_dvd
    have h2 : p ^ (n + 1) ≤ n + 1 + 1 := Nat.le_of_dvd (by omega) h1
    have h3 : 3 ^ (n + 1) ≤ p ^ (n + 1) := Nat.pow_le_pow_left hp3 _
    have h4 : n + 2 < 3 ^ (n + 1) := by
      clear hcon hcon' h1 h2 h3 hx hext
      induction n with
      | zero => norm_num
      | succ k ih =>
        have h : 3 ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by rw [pow_succ]; ring
        omega
    omega
  unfold logTermK
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_natCastK hext (n + 1 + 1) (by omega), zpow_neg, zpow_natCast,
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

end NormExtends

/-- **`K` 上の p 進対数** `log(1+x) := ∑_{n≥0} (−1)ⁿ xⁿ⁺¹/(n+1)`。 -/
noncomputable def logOnePlusK (x : K) : K := ∑' n, logTermK x n

omit [IsUltrametricDist K] in
@[simp] lemma logOnePlusK_zero : logOnePlusK (0 : K) = 0 := by
  simp [logOnePlusK]

/-- **ノルム保存**(一般の完備非アルキメデス的 `ℚ_p`-代数、`p > 2`, `‖x‖ ≤ 1/p`):
`‖log(1+x)‖ = ‖x‖`。`PadicLog.lean` の `norm_logOnePlus` の一般化 ―― ultrametric の
二項等号は `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` による。 -/
theorem norm_logOnePlusK [CompleteSpace K]
    (hext : ∀ y : ℚ_[p], ‖algebraMap ℚ_[p] K y‖ = ‖y‖)
    (hp2 : p ≠ 2) {x : K} (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
    ‖logOnePlusK x‖ = ‖x‖ := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.out.two_le
    omega
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx (inv_lt_one_of_one_lt₀ hpR)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hsum : Summable (logTermK x) := summable_logTermK hext hx1
  rw [logOnePlusK, hsum.tsum_eq_zero_add, logTermK_zero]
  have hTle : ‖∑' n, logTermK x (n + 1)‖ ≤ ‖x‖ * (p : ℝ)⁻¹ := by
    apply norm_tsum_le_of_forall_le_of_nonneg
    · positivity
    · exact fun n => norm_logTermK_succ_le hext hp3 hx n
  have hTlt : ‖∑' n, logTermK x (n + 1)‖ < ‖x‖ := by
    apply lt_of_le_of_lt hTle
    have h0x : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    calc ‖x‖ * (p : ℝ)⁻¹ < ‖x‖ * 1 := by
          apply mul_lt_mul_of_pos_left (inv_lt_one_of_one_lt₀ hpR) h0x
      _ = ‖x‖ := mul_one _
  rw [norm_add_eq_max_of_norm_ne_norm hTlt.ne']
  exact max_eq_left hTlt.le

/-! ## `ℂ_[p]` での実装 — 分岐拡大の対数殻 -/

/-- `ℚ_p → ℂ_[p]` の代数射はノルムを延長する(`IsScalarTower` + スペクトルノルム延長
+ 完備化のノルム延長の合成)。 -/
lemma norm_extends_QC (y : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] y‖ = ‖y‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p] y, ← PadicComplex.coe_eq,
    PadicComplex.norm_extends]
  exact PadicAlgCl.norm_extends p y

/-- `ℂ_[p]` 上の対数級数の無条件収束(`‖x‖ < 1`)。 -/
theorem summable_logTermC {x : ℂ_[p]} (hx : ‖x‖ < 1) : Summable (logTermK x) :=
  summable_logTermK (norm_extends_QC (p := p)) hx

/-- **`ℂ_[p]` 上のノルム保存**(`p > 2`, `‖x‖ ≤ 1/p`): `‖log(1+x)‖ = ‖x‖`。 -/
theorem norm_complexLog {x : ℂ_[p]} (hp2 : p ≠ 2) (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
    ‖logOnePlusK x‖ = ‖x‖ :=
  norm_logOnePlusK (norm_extends_QC (p := p)) hp2 hx

/-- **分岐拡大の対数殻(ノルムレベル)**: `ℚ̄_p` の元 `x`(任意の有限拡大 `L/ℚ_p` の元は
ここに埋め込まれる ―― 実 Hodge 劇場 `Mon = ℚ̄_pˣ` の住人)に対し、`‖x‖ ≤ 1/p` なら
`log(1+x) ∈ ℂ_[p]` が定義されノルムを保存する。[IUT-IV] Prop 1.2 (i) の分岐 `e > 1` の
場合の半径 `a = 1` での包含+体積保存(鋭い半径は `norm_complexLog_algebraic_sharp`)。
実 Hodge 劇場の主単数 `u`(`‖u−1‖ ≤ 1/p`)に `x := u−1` として適用すれば
**log-link の実対象上の芽**を与える。 -/
theorem norm_complexLog_algebraic {x : PadicAlgCl p} (hp2 : p ≠ 2)
    (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
    ‖logOnePlusK ((x : ℂ_[p]))‖ = ‖x‖ := by
  rw [norm_complexLog hp2 (by rw [PadicComplex.norm_extends]; exact hx),
    PadicComplex.norm_extends]

/-! ## 鋭い収束半径 — `‖x‖^{p−1} < 1/p`(⟺ `ord(x) > 1/(p−1)`) -/

/-- ℕ の Bernoulli 型評価: `v·(p−1) + 1 ≤ p^v`(`p ≥ 2`)。
`v_p(m+1) = v` ⟹ `p^v ≤ m+1` ⟹ `v·(p−1) ≤ m` の鎖に使う。 -/
private lemma nat_bernoulli (p : ℕ) (hp2 : 2 ≤ p) (v : ℕ) : v * (p - 1) + 1 ≤ p ^ v := by
  induction v with
  | zero => simp
  | succ k ih =>
    have h : p ^ (k + 1) = p * p ^ k := by rw [pow_succ]; ring
    have h2 : p * (k * (p - 1) + 1) ≤ p * p ^ k := Nat.mul_le_mul_left p ih
    have h3 : (k + 1) * (p - 1) + 1 ≤ p * (k * (p - 1) + 1) := by
      have e1 : (k + 1) * (p - 1) = k * (p - 1) + (p - 1) := by rw [Nat.succ_mul]
      have e2 : p * (k * (p - 1) + 1) = p * (k * (p - 1)) + p := by
        rw [Nat.mul_add, Nat.mul_one]
      have e3 : k * (p - 1) ≤ p * (k * (p - 1)) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega

omit hp in
/-- 実数の初等補題: `r^{p−1} < 1/p` かつ `r ≥ 0` なら `r < 1`(`p ≥ 2`)。 -/
private lemma lt_one_of_sharp {p : ℕ} (hp2 : 2 ≤ p) {r : ℝ}
    (hx : r ^ (p - 1) < (p : ℝ)⁻¹) : r < 1 := by
  by_contra hge
  have h1 : (1 : ℝ) ≤ r ^ (p - 1) := one_le_pow₀ (not_lt.mp hge)
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have h2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpR
  linarith

/-- **有限個の最大項論法**(ultrametric の厳密上限): 項が 0 に収束し各項が `c` より
厳密に小さいなら、総和のノルムも `c` より厳密に小さい(尾部は `c/2` 以下、頭部は
有限個の最大値 `< c`)。鋭い収束半径で尾部の一様評価が使えないことの代替。 -/
lemma nnnorm_tsum_lt_of_forall_lt {f : ℕ → K} (hf : Tendsto f atTop (𝓝 0))
    {c : NNReal} (hc : 0 < c) (h : ∀ n, ‖f n‖₊ < c) : ‖∑' n, f n‖₊ < c := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hf ((c : ℝ) / 2)
    (by positivity)
  have hbound : ∀ n, ‖f n‖₊ ≤ (Finset.range (N + 1)).sup (fun k => ‖f k‖₊) ⊔ c / 2 := by
    intro n
    rcases lt_or_ge n (N + 1) with hn | hn
    · exact le_sup_of_le_left
        (Finset.le_sup (f := fun k => ‖f k‖₊) (Finset.mem_range.mpr hn))
    · refine le_sup_of_le_right ?_
      have hd := hN n (by omega)
      rw [dist_zero_right] at hd
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hd.le
  have hlt : (Finset.range (N + 1)).sup (fun k => ‖f k‖₊) ⊔ c / 2 < c := by
    apply sup_lt_iff.mpr
    constructor
    · rw [Finset.sup_lt_iff hc]
      exact fun k _ => h k
    · exact NNReal.half_lt_self hc.ne'
  exact lt_of_le_of_lt (nnnorm_tsum_le_of_forall_le hbound) hlt

omit [IsUltrametricDist K] in
/-- **鋭い半径での尾部の項別厳密評価**: `‖x‖^{p−1} < 1/p` なら第 2 項以降は
`‖logTermK x (n+1)‖ < ‖x‖`(一様でない ―― 境界に近いと比が 1 に近づく)。
核心: `v := v_p(n+2)` に対し `v(p−1) ≤ p^v − 1 ≤ n+1`(Bernoulli)ゆえ
`‖x‖^{n+1}·p^v ≤ (‖x‖^{p−1}·p)^v · ‖x‖^{n+1−v(p−1)} < 1`。 -/
lemma norm_logTermK_succ_lt_sharp (hext : ∀ y : ℚ_[p], ‖algebraMap ℚ_[p] K y‖ = ‖y‖)
    {x : K} (hx0 : x ≠ 0) (hx : ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹) (n : ℕ) :
    ‖logTermK x (n + 1)‖ < ‖x‖ := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hxlt1 : ‖x‖ < 1 := lt_one_of_sharp hp2 hx
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hnorm : ‖logTermK x (n + 1)‖
      = ‖x‖ ^ (n + 1 + 1) * (p : ℝ) ^ padicValNat p (n + 1 + 1) := by
    unfold logTermK
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_natCastK hext (n + 1 + 1) (by omega), zpow_neg, zpow_natCast,
      div_eq_mul_inv, inv_inv]
  rw [hnorm]
  set v := padicValNat p (n + 1 + 1) with hv
  have hkey : ‖x‖ ^ (n + 1) * (p : ℝ) ^ v < 1 := by
    have hple : p ^ v ≤ n + 1 + 1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hbern := nat_bernoulli p hp2 v
    have hvpm : v * (p - 1) ≤ n + 1 := by omega
    rcases Nat.eq_zero_or_pos v with hv0 | hv1
    · rw [hv0, pow_zero, mul_one]
      exact pow_lt_one₀ (norm_nonneg x) hxlt1 (by omega)
    · have hcomm : (p - 1) * v = v * (p - 1) := Nat.mul_comm _ _
      have hexp : (p - 1) * v + (n + 1 - v * (p - 1)) = n + 1 := by omega
      have hfac : ‖x‖ ^ (p - 1) * (p : ℝ) < 1 := by
        calc ‖x‖ ^ (p - 1) * (p : ℝ) < (p : ℝ)⁻¹ * (p : ℝ) :=
              mul_lt_mul_of_pos_right hx hp0
          _ = 1 := inv_mul_cancel₀ hp0.ne'
      calc ‖x‖ ^ (n + 1) * (p : ℝ) ^ v
          = (‖x‖ ^ ((p - 1) * v) * ‖x‖ ^ (n + 1 - v * (p - 1))) * (p : ℝ) ^ v := by
            rw [← pow_add, hexp]
        _ = ((‖x‖ ^ (p - 1) * (p : ℝ)) ^ v) * ‖x‖ ^ (n + 1 - v * (p - 1)) := by
            rw [mul_pow, pow_mul]
            ring
        _ ≤ ((‖x‖ ^ (p - 1) * (p : ℝ)) ^ v) * 1 := by
            apply mul_le_mul_of_nonneg_left
              (pow_le_one₀ (norm_nonneg x) hxlt1.le) (by positivity)
        _ = (‖x‖ ^ (p - 1) * (p : ℝ)) ^ v := mul_one _
        _ < 1 := pow_lt_one₀ (by positivity) hfac (by omega)
  calc ‖x‖ ^ (n + 1 + 1) * (p : ℝ) ^ v = ‖x‖ * (‖x‖ ^ (n + 1) * (p : ℝ) ^ v) := by ring
    _ < ‖x‖ * 1 := mul_lt_mul_of_pos_left hkey hxpos
    _ = ‖x‖ := mul_one _

/-- **鋭い収束半径でのノルム保存**([IUT-IV] Prop 1.2 (i) の真の半径):
`‖x‖^{p−1} < 1/p`(⟺ `ord(x) > 1/(p−1)`)なら `‖log(1+x)‖ = ‖x‖`。
`p = 2` も含む(条件は `ord > 1`)。分岐 `e > 1` の下側半径 `a = ⌈e/(p−1)⌉/e` は
`(p−1) ∤ e` のときこの条件を保証する(`LogShellRadius.le_aRadius` の honest 注記と対)。
境界 `ord = 1/(p−1)` では `log ζ_p = 0` ゆえ**偽** ―― 厳密不等号が本質的。 -/
theorem norm_logOnePlusK_sharp [CompleteSpace K]
    (hext : ∀ y : ℚ_[p], ‖algebraMap ℚ_[p] K y‖ = ‖y‖)
    {x : K} (hx : ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹) :
    ‖logOnePlusK x‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxlt1 : ‖x‖ < 1 := lt_one_of_sharp hp.out.two_le hx
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hsum : Summable (logTermK x) := summable_logTermK hext hxlt1
  rw [logOnePlusK, hsum.tsum_eq_zero_add, logTermK_zero]
  have hshift : Summable (fun n => logTermK x (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  have hT : ‖∑' n, logTermK x (n + 1)‖₊ < ‖x‖₊ := by
    apply nnnorm_tsum_lt_of_forall_lt hshift.tendsto_atTop_zero
    · exact_mod_cast hxpos
    · intro n
      rw [← NNReal.coe_lt_coe]
      push_cast
      exact norm_logTermK_succ_lt_sharp hext hx0 hx n
  have hTlt : ‖∑' n, logTermK x (n + 1)‖ < ‖x‖ := by exact_mod_cast hT
  rw [norm_add_eq_max_of_norm_ne_norm hTlt.ne']
  exact max_eq_left hTlt.le

/-- `ℂ_[p]` 上の鋭い半径でのノルム保存。 -/
theorem norm_complexLog_sharp {x : ℂ_[p]} (hx : ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹) :
    ‖logOnePlusK x‖ = ‖x‖ :=
  norm_logOnePlusK_sharp (norm_extends_QC (p := p)) hx

/-- **分岐拡大の鋭い対数殻**: `ℚ̄_p` の元 `x` に対し `‖x‖^{p−1} < 1/p`
(⟺ `ord(x) > 1/(p−1)` = Prop 1.2 (i) の真の下側半径条件)なら
`log(1+x) ∈ ℂ_[p]` がノルムを保存する ―― 実 Hodge 劇場の対象上の対数殻の
体積保存が、分岐拡大でも鋭い半径で成立する。 -/
theorem norm_complexLog_algebraic_sharp {x : PadicAlgCl p}
    (hx : ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹) :
    ‖logOnePlusK ((x : ℂ_[p]))‖ = ‖x‖ := by
  rw [norm_complexLog_sharp (by rw [PadicComplex.norm_extends]; exact hx),
    PadicComplex.norm_extends]

end IUT.Padic
