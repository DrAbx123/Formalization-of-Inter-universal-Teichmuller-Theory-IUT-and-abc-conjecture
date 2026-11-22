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
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Finset.Basic
import tmp.sheaf.takkun.IutLean.Padic.ComplexLog

/-!
# p 進指数関数 — Phase R1(hull_bound 非同一視導出ロードマップの第 1 部品)

底本: [IUT-IV] Prop 1.2 (i) の全射性側([Kobl] p.81 の p 進 exp/log 理論)。

`hull_bound` の非同一視導出(ROADMAP Phase R)には対数リンク単数部の**加法性**
(p 進 log の準同型性)が要る。その標準的経路は **p 進指数関数** `exp x = Σ xⁿ/n!` である:
exp の加法性は二項定理 + 非アルキメデス Cauchy 積で得られ(log の直接の合成恒等式より
はるかに容易)、そこから `log∘exp = id` 経由で log の加法性へ到達する(Phase R2)。

## 本スライス(R1 前半)で証明済(全て標準公理のみ)

* `one_le_digits_sum` / `padicValNat_factorial_le`: **Legendre 評価**
  `(p−1)·v_p(n!) ≤ n−1`(`n ≥ 1`; Mathlib の
  `sub_one_mul_padicValNat_factorial` = `(p−1)·v_p(n!) = n − s_p(n)` と桁和 `≥ 1`);
* `norm_expTerm`: 項の厳密ノルム `‖xⁿ/n!‖ = ‖x‖ⁿ·p^{v_p(n!)}`;
* `summable_expTerm`: **収束**(`p > 2`, `‖x‖ ≤ 1/p`)―― 分母 `n!` の暴れ
  `p^{v_p(n!)}` は Legendre 評価により幾何減衰 `p^{−(n+1)/2}` に負ける;
* `expK` の定義と `expK 0 = 1`。

## R1 後半(次セッション、部品は Mathlib に確認済)

* **加法性 `exp(x+y) = exp x · exp y`**: `Summable.mul_of_nonarchimedean`(非アルキメデス
  Cauchy 積)+ `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`(対角線再和)+
  二項定理 `Σ_{i+j=n} xⁱ/i!·yʲ/j! = (x+y)ⁿ/n!`(`Nat.cast_choose`);
* ノルム保存 `‖exp x − 1‖ = ‖x‖`(首項支配、`PadicLog` と同型の議論)。
-/

namespace IUT.Padic

open Filter Topology

/-! ## Legendre 評価 -/

/-- `n ≠ 0` なら `p` 進桁和は `≥ 1`(最上位桁が非零)。 -/
lemma one_le_digits_sum {p n : ℕ} (hn : n ≠ 0) : 1 ≤ (p.digits n).sum := by
  have hne : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (p.digits n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero p hn
  have hle : (p.digits n).getLast hne ≤ (p.digits n).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.getLast_mem hne)
  omega

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Legendre 評価**: `(p−1)·v_p(n!) ≤ n − 1`(`n ≥ 1`)。
指数関数の分母 `n!` の p 進的暴れの上界 ―― 収束半径 `ord > 1/(p−1)` の源。 -/
lemma padicValNat_factorial_le {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial ≤ n - 1 := by
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have h1 := one_le_digits_sum (p := p) hn
  omega

/-! ## 指数関数の項と収束 -/

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [Algebra ℚ_[p] K]

/-- 指数級数の第 `n` 項 `xⁿ/n!`。 -/
noncomputable def expTerm (x : K) (n : ℕ) : K := x ^ n / (n.factorial : K)

omit [IsUltrametricDist K] in
@[simp] lemma expTerm_zero (x : K) : expTerm x 0 = x ^ 0 / 1 := by
  simp [expTerm, Nat.factorial]

section NormExtends

variable (hext : ∀ y : ℚ_[p], ‖algebraMap ℚ_[p] K y‖ = ‖y‖)
include hext

omit [IsUltrametricDist K] in
/-- 項の厳密ノルム: `‖xⁿ/n!‖ = ‖x‖ⁿ·p^{v_p(n!)}`。 -/
lemma norm_expTerm (x : K) (n : ℕ) :
    ‖expTerm x n‖ = ‖x‖ ^ n * (p : ℝ) ^ padicValNat p n.factorial := by
  unfold expTerm
  rw [norm_div, norm_pow, norm_natCastK hext n.factorial n.factorial_ne_zero,
    zpow_neg, zpow_natCast, div_eq_mul_inv, inv_inv]

omit [IsUltrametricDist K] in
/-- 項の幾何減衰(`p > 2`, `‖x‖ ≤ 1/p`): `‖xⁿ/n!‖ ≤ p^{−⌊(n+1)/2⌋}`
(Legendre 評価 `2·v_p(n!) ≤ n−1` による)。 -/
lemma norm_expTerm_le (hp3 : 3 ≤ p) {x : K} (hx : ‖x‖ ≤ (p : ℝ)⁻¹) (n : ℕ) :
    ‖expTerm x n‖ ≤ ((p : ℝ)⁻¹) ^ ((n + 1) / 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  rw [norm_expTerm hext x n]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.factorial]
  · set v := padicValNat p n.factorial with hv
    have hleg : (p - 1) * v ≤ n - 1 := padicValNat_factorial_le hn
    have h2v : 2 * v ≤ n - 1 :=
      le_trans (Nat.mul_le_mul_right v (by omega : 2 ≤ p - 1)) hleg
    have hvn : v + (n + 1) / 2 ≤ n := by omega
    have h2 : (0 : ℝ) < (p : ℝ) ^ ((n + 1) / 2) := by positivity
    have h3 : (0 : ℝ) < (p : ℝ) ^ n := by positivity
    calc ‖x‖ ^ n * (p : ℝ) ^ v
        ≤ ((p : ℝ)⁻¹) ^ n * (p : ℝ) ^ v := by
          apply mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg x) hx n) (by positivity)
      _ ≤ ((p : ℝ)⁻¹) ^ ((n + 1) / 2) := by
          rw [inv_pow, inv_pow, inv_mul_eq_div, inv_eq_one_div,
            div_le_div_iff₀ h3 h2, one_mul, ← pow_add]
          exact pow_le_pow_right₀ hp1 (by omega)

omit [IsUltrametricDist K] hext in
/-- 幾何減衰の優級数は 0 に収束する。 -/
lemma tendsto_expBound : Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ ((n + 1) / 2))
    atTop (𝓝 0) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hk : Tendsto (fun n : ℕ => (n + 1) / 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (2 * b)] with n hn
    omega
  have hr : Tendsto (fun k : ℕ => ((p : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ hpR)
  have h := hr.comp hk
  simpa [Function.comp_def] using h

/-- **指数級数の収束**(`p > 2`, `‖x‖ ≤ 1/p`): 非アルキメデス完備群の総和判定 +
Legendre 評価による幾何減衰。 -/
theorem summable_expTerm [CompleteSpace K] (hp3 : 3 ≤ p) {x : K}
    (hx : ‖x‖ ≤ (p : ℝ)⁻¹) : Summable (expTerm x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  exact squeeze_zero_norm (norm_expTerm_le hext hp3 hx) tendsto_expBound

end NormExtends

/-- **p 進指数関数** `exp x := Σ_{n≥0} xⁿ/n!`(`‖x‖ ≤ 1/p`, `p > 2` で収束)。 -/
noncomputable def expK (x : K) : K := ∑' n, expTerm x n

omit [IsUltrametricDist K] in
/-- 正規化 `exp 0 = 1`。 -/
@[simp] lemma expK_zero : expK (0 : K) = 1 := by
  unfold expK
  rw [tsum_eq_single 0 (fun n hn => by simp [expTerm, zero_pow hn])]
  simp [expTerm, Nat.factorial]

/-! ## R1 後半: 加法性(非アルキメデス Cauchy 積 + 二項定理) -/

/-- 超距離的ノルム体は非アルキメデス的環(開部分群による 0 の近傍基)。
`Summable.mul_of_nonarchimedean`(Cauchy 積)の前提。 -/
instance : NonarchimedeanRing K :=
  ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩

section Additivity

variable (hext : ∀ y : ℚ_[p], ‖algebraMap ℚ_[p] K y‖ = ‖y‖)
include hext

omit [IsUltrametricDist K] in
/-- ノルム延長を持つ `ℚ_p`-代数は標数 0(延長射が等長ゆえ単射)。 -/
lemma charZero_of_normExtends : CharZero K := by
  have hinj : Function.Injective (algebraMap ℚ_[p] K) := by
    intro a b hab
    have h0 : algebraMap ℚ_[p] K (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h1 : ‖a - b‖ = 0 := by rw [← hext (a - b), h0, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h1)
  exact charZero_of_injective_algebraMap hinj

omit [IsUltrametricDist K] in
/-- **二項恒等式**: 対角線和は `(x+y)ⁿ/n!` に一致
(`Σ_{k+l=n} xᵏ/k! · yˡ/l! = (x+y)ⁿ/n!` ―― `n!/(k!(n−k)!) = C(n,k)` による)。 -/
lemma sum_antidiagonal_expTerm (x y : K) (n : ℕ) :
    ∑ kl ∈ Finset.Nat.antidiagonal n, expTerm x kl.1 * expTerm y kl.2
      = expTerm (x + y) n := by
  haveI : CharZero K := charZero_of_normExtends hext
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold expTerm
  rw [add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : ((k.factorial : K)) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h2 : (((n - k).factorial : K)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have h3 : ((n.factorial : K)) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [Nat.cast_choose K hkn]
  field_simp

/-- **p 進指数関数の加法性(Phase R1 完成)**: `exp(x+y) = exp x · exp y`
(`p > 2`, `‖x‖, ‖y‖ ≤ 1/p`)。証明 = 非アルキメデス Cauchy 積
(`Summable.mul_of_nonarchimedean` ―― 絶対収束を経由しない)+ 対角線再和
(`tsum_mul_tsum_eq_tsum_sum_antidiagonal`)+ 二項恒等式。
**対数の準同型性(Phase R2、`log∘exp = id` 経由)への鍵であり、
対数リンク単数部 = log-Kummer 対応の実配線に向けた核心部品。** -/
theorem expK_add [CompleteSpace K] (hp3 : 3 ≤ p) {x y : K}
    (hx : ‖x‖ ≤ (p : ℝ)⁻¹) (hy : ‖y‖ ≤ (p : ℝ)⁻¹) :
    expK (x + y) = expK x * expK y := by
  have hsx := summable_expTerm hext hp3 hx
  have hsy := summable_expTerm hext hp3 hy
  have hsxy : Summable (fun i : ℕ × ℕ => expTerm x i.1 * expTerm y i.2) :=
    hsx.mul_of_nonarchimedean hsy
  have h := hsx.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsy hsxy
  unfold expK
  rw [h]
  exact tsum_congr fun n => (sum_antidiagonal_expTerm hext x y n).symm

/-! ## R2 前半: exp のノルム保存・等長性・単射性 -/

omit [IsUltrametricDist K] in
/-- 尾部の一様評価: `n ≥ 2` の項は一様に `‖xⁿ/n!‖ ≤ ‖x‖/p`
(Legendre `2·v_p((n+2)!) ≤ n+1` ⟹ `v ≤ n`)。 -/
lemma norm_expTerm_add_two_le (hp3 : 3 ≤ p) {x : K} (hx : ‖x‖ ≤ (p : ℝ)⁻¹) (n : ℕ) :
    ‖expTerm x (n + 1 + 1)‖ ≤ ‖x‖ * (p : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  rw [norm_expTerm hext x (n + 1 + 1)]
  have hleg : (p - 1) * padicValNat p (n + 1 + 1).factorial ≤ n + 1 := by
    have h := padicValNat_factorial_le (p := p) (n := n + 1 + 1) (by omega)
    omega
  have h2v : 2 * padicValNat p (n + 1 + 1).factorial ≤ n + 1 :=
    le_trans (Nat.mul_le_mul_right _ (by omega : 2 ≤ p - 1)) hleg
  have hvn : padicValNat p (n + 1 + 1).factorial ≤ n := by omega
  calc ‖x‖ ^ (n + 1 + 1) * (p : ℝ) ^ padicValNat p (n + 1 + 1).factorial
      = ‖x‖ * (‖x‖ ^ (n + 1) * (p : ℝ) ^ padicValNat p (n + 1 + 1).factorial) := by ring
    _ ≤ ‖x‖ * (((p : ℝ)⁻¹) ^ (n + 1) * (p : ℝ) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
        apply mul_le_mul
        · exact pow_le_pow_left₀ (norm_nonneg x) hx _
        · exact pow_le_pow_right₀ hp1 hvn
        · positivity
        · positivity
    _ = ‖x‖ * (p : ℝ)⁻¹ := by
        congr 1
        rw [inv_pow, pow_succ]
        field_simp

/-- **exp のノルム保存**(Phase R2 前半): `‖exp x − 1‖ = ‖x‖`(`p > 2`, `‖x‖ ≤ 1/p`)
―― 首項 `x` が尾部(一様に `‖x‖/p` 以下)を厳密支配する。`log` のノルム保存
(`norm_logOnePlusK`)と対をなし、exp が殻 `p·O` を主単数 `1 + p·O` へ
**深さを保って**写すことを与える。 -/
theorem norm_expK_sub_one [CompleteSpace K] (hp3 : 3 ≤ p) {x : K}
    (hx : ‖x‖ ≤ (p : ℝ)⁻¹) : ‖expK x - 1‖ = ‖x‖ := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hsum : Summable (expTerm x) := summable_expTerm hext hp3 hx
  have hsum1 : Summable (fun n => expTerm x (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  have hterm0 : expTerm x 0 = 1 := by simp [expTerm, Nat.factorial]
  have hterm1 : expTerm x 1 = x := by simp [expTerm, Nat.factorial]
  have h0 : expK x = 1 + ∑' n, expTerm x (n + 1) := by
    rw [expK, hsum.tsum_eq_zero_add, hterm0]
  have h1 : ∑' n, expTerm x (n + 1) = x + ∑' n, expTerm x (n + 1 + 1) := by
    rw [hsum1.tsum_eq_zero_add, hterm1]
  rw [h0, h1, add_sub_cancel_left]
  have hT : ‖∑' n, expTerm x (n + 1 + 1)‖ ≤ ‖x‖ * (p : ℝ)⁻¹ := by
    apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    · positivity
    · exact fun n => norm_expTerm_add_two_le hext hp3 hx n
  have hTlt : ‖∑' n, expTerm x (n + 1 + 1)‖ < ‖x‖ := by
    apply lt_of_le_of_lt hT
    have h0x : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    calc ‖x‖ * (p : ℝ)⁻¹ < ‖x‖ * 1 :=
          mul_lt_mul_of_pos_left (inv_lt_one_of_one_lt₀ hpR) h0x
      _ = ‖x‖ := mul_one _
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hTlt.ne']
  exact max_eq_left hTlt.le

/-- exp の値は単数(ノルム 1): `‖exp x‖ = 1`。 -/
theorem norm_expK [CompleteSpace K] (hp3 : 3 ≤ p) {x : K}
    (hx : ‖x‖ ≤ (p : ℝ)⁻¹) : ‖expK x‖ = 1 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hlt : ‖expK x - 1‖ < 1 := by
    rw [norm_expK_sub_one hext hp3 hx]
    exact lt_of_le_of_lt hx (inv_lt_one_of_one_lt₀ hpR)
  have hne : ‖expK x - 1‖ ≠ ‖(1 : K)‖ := by rw [norm_one]; exact hlt.ne
  calc ‖expK x‖ = ‖(expK x - 1) + 1‖ := by rw [sub_add_cancel]
    _ = max ‖expK x - 1‖ ‖(1 : K)‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    _ = 1 := by rw [norm_one]; exact max_eq_right hlt.le

/-- **exp の等長性**(加法性 + ノルム保存の帰結): `‖exp x − exp y‖ = ‖x − y‖`。
exp が殻の距離構造(= 体積の層構造)を保つ埋め込みであること。 -/
theorem norm_expK_sub_expK [CompleteSpace K] (hp3 : 3 ≤ p) {x y : K}
    (hx : ‖x‖ ≤ (p : ℝ)⁻¹) (hy : ‖y‖ ≤ (p : ℝ)⁻¹) :
    ‖expK x - expK y‖ = ‖x - y‖ := by
  have hxy : ‖x - y‖ ≤ (p : ℝ)⁻¹ := by
    calc ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
          rw [sub_eq_add_neg]
          exact (IsUltrametricDist.norm_add_le_max x (-y)).trans_eq (by rw [norm_neg])
      _ ≤ (p : ℝ)⁻¹ := max_le hx hy
  have hfact : expK x = expK (x - y) * expK y := by
    rw [← expK_add hext hp3 hxy hy, sub_add_cancel]
  calc ‖expK x - expK y‖
      = ‖(expK (x - y) - 1) * expK y‖ := by
        rw [hfact, show expK (x - y) * expK y - expK y
          = (expK (x - y) - 1) * expK y from by ring]
    _ = ‖expK (x - y) - 1‖ * ‖expK y‖ := norm_mul _ _
    _ = ‖x - y‖ * 1 := by
        rw [norm_expK_sub_one hext hp3 hxy, norm_expK hext hp3 hy]
    _ = ‖x - y‖ := mul_one _

/-- **exp の単射性**(殻の上): 等長性の帰結。`log∘exp = id`(R2 後半)の前提であり、
exp が殻 `p·O` から主単数への 1:1 の体積保存埋め込みであることを確定する。 -/
theorem expK_injective [CompleteSpace K] (hp3 : 3 ≤ p) {x y : K}
    (hx : ‖x‖ ≤ (p : ℝ)⁻¹) (hy : ‖y‖ ≤ (p : ℝ)⁻¹)
    (h : expK x = expK y) : x = y := by
  have hiso := norm_expK_sub_expK hext hp3 hx hy
  rw [h, sub_self, norm_zero] at hiso
  exact sub_eq_zero.mp (norm_eq_zero.mp hiso.symm)

end Additivity

/-! ## R2 後半: exp の全射性(Newton 反復)― log-link 単数部の完成

級数合成 `log∘exp = id` を回避する経路: exp は単射・加法的・ノルム保存(証明済)ゆえ、
**全射性**さえ示せば `exp⁻¹` が自動的に加法的なノルム保存同型 `(1+pO,×) ≅ (pO,+)` となる。
全射性は Newton 反復 `x_{n+1} = x_n + (u·exp(−x_n) − 1)` による ―― 誤差は二次収縮
`‖e_{n+1}‖ ≤ ‖e_n‖²` し、**等長性が連続性の代役**を果たして極限で `exp x = u`。 -/

/-- **Newton 反復列**: `x₀ = 0`, `x_{n+1} = x_n + (u·exp(−x_n) − 1)`。 -/
noncomputable def newton (u : K) : ℕ → K
  | 0 => 0
  | n + 1 => newton u n + (u * expK (-(newton u n)) - 1)

section Surjectivity

variable (hext : ∀ y : ℚ_[p], ‖algebraMap ℚ_[p] K y‖ = ‖y‖)
include hext

omit [IsUltrametricDist K] in
/-- 二次評価の項別版: `n ≥ 2` の項は `‖yⁿ/n!‖ ≤ ‖y‖²`(`v_p(n!) ≤ n−2`)。 -/
lemma norm_expTerm_add_two_le_sq (hp3 : 3 ≤ p) {y : K} (hy : ‖y‖ ≤ (p : ℝ)⁻¹) (n : ℕ) :
    ‖expTerm y (n + 1 + 1)‖ ≤ ‖y‖ ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  rw [norm_expTerm hext y (n + 1 + 1)]
  have hleg : (p - 1) * padicValNat p (n + 1 + 1).factorial ≤ n + 1 := by
    have h := padicValNat_factorial_le (p := p) (n := n + 1 + 1) (by omega)
    omega
  have h2v : 2 * padicValNat p (n + 1 + 1).factorial ≤ n + 1 :=
    le_trans (Nat.mul_le_mul_right _ (by omega : 2 ≤ p - 1)) hleg
  have hvn : padicValNat p (n + 1 + 1).factorial ≤ n := by omega
  calc ‖y‖ ^ (n + 1 + 1) * (p : ℝ) ^ padicValNat p (n + 1 + 1).factorial
      = ‖y‖ ^ 2 * (‖y‖ ^ n * (p : ℝ) ^ padicValNat p (n + 1 + 1).factorial) := by ring
    _ ≤ ‖y‖ ^ 2 * (((p : ℝ)⁻¹) ^ n * (p : ℝ) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul
        · exact pow_le_pow_left₀ (norm_nonneg y) hy _
        · exact pow_le_pow_right₀ hp1 hvn
        · positivity
        · positivity
    _ = ‖y‖ ^ 2 := by
        rw [inv_pow, inv_mul_cancel₀ (by positivity), mul_one]

/-- **二次評価**: `‖exp y − 1 − y‖ ≤ ‖y‖²`(Newton 反復の収縮の源)。 -/
theorem norm_expK_sub_one_sub [CompleteSpace K] (hp3 : 3 ≤ p) {y : K}
    (hy : ‖y‖ ≤ (p : ℝ)⁻¹) : ‖expK y - 1 - y‖ ≤ ‖y‖ ^ 2 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hy1 : ‖y‖ < 1 := lt_of_le_of_lt hy (inv_lt_one_of_one_lt₀ hpR)
  have hsum : Summable (expTerm y) := summable_expTerm hext hp3 hy
  have hsum1 : Summable (fun n => expTerm y (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  have hterm0 : expTerm y 0 = 1 := by simp [expTerm, Nat.factorial]
  have hterm1 : expTerm y 1 = y := by simp [expTerm, Nat.factorial]
  have h0 : expK y = 1 + ∑' n, expTerm y (n + 1) := by
    rw [expK, hsum.tsum_eq_zero_add, hterm0]
  have h1 : ∑' n, expTerm y (n + 1) = y + ∑' n, expTerm y (n + 1 + 1) := by
    rw [hsum1.tsum_eq_zero_add, hterm1]
  rw [h0, h1, show (1 : K) + (y + ∑' n, expTerm y (n + 1 + 1)) - 1 - y
    = ∑' n, expTerm y (n + 1 + 1) from by ring]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
  exact fun n => norm_expTerm_add_two_le_sq hext hp3 hy n

/-- **Newton 反復の不変量**: 反復列は殻に留まり、誤差 `e_n = u·exp(−x_n) − 1` は
幾何級数的に減衰する(`‖e_n‖ ≤ p^{−(n+1)}` ―― 実際は二次収縮 `‖e_{n+1}‖ ≤ ‖e_n‖²`)。 -/
lemma newton_invariant [CompleteSpace K] (hp3 : 3 ≤ p) {u : K}
    (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) (n : ℕ) :
    ‖newton u n‖ ≤ (p : ℝ)⁻¹ ∧
      ‖u * expK (-(newton u n)) - 1‖ ≤ ((p : ℝ)⁻¹) ^ (n + 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hpinv1 : (p : ℝ)⁻¹ ≤ 1 := le_of_lt (inv_lt_one_of_one_lt₀ hpR)
  induction n with
  | zero =>
    constructor
    · change ‖(0 : K)‖ ≤ (p : ℝ)⁻¹
      rw [norm_zero]
      positivity
    · change ‖u * expK (-(0 : K)) - 1‖ ≤ ((p : ℝ)⁻¹) ^ 1
      rw [neg_zero, expK_zero, mul_one, pow_one]
      exact hu
  | succ n ih =>
    obtain ⟨hxn, hen⟩ := ih
    set e := u * expK (-(newton u n)) - 1 with he
    have hen' : ‖e‖ ≤ (p : ℝ)⁻¹ := by
      refine le_trans hen ?_
      calc ((p : ℝ)⁻¹) ^ (n + 1) ≤ ((p : ℝ)⁻¹) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) hpinv1 (by omega)
        _ = (p : ℝ)⁻¹ := pow_one _
    have hnegx : ‖-(newton u n)‖ ≤ (p : ℝ)⁻¹ := by rwa [norm_neg]
    have hnege : ‖-e‖ ≤ (p : ℝ)⁻¹ := by rwa [norm_neg]
    have hstep : newton u (n + 1) = newton u n + e := by
      change newton u n + (u * expK (-(newton u n)) - 1) = newton u n + e
      rw [he]
    constructor
    · rw [hstep]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hxn hen')
    · have h1e : u * expK (-(newton u n)) = 1 + e := by rw [he]; ring
      have hsplit : expK (-(newton u (n + 1)))
          = expK (-(newton u n)) * expK (-e) := by
        rw [hstep, neg_add, expK_add hext hp3 hnegx hnege]
      have hkey : u * expK (-(newton u (n + 1))) - 1
          = (expK (-e) - 1 - (-e)) + e * (expK (-e) - 1) := by
        rw [hsplit, ← mul_assoc, h1e]
        ring
      rw [hkey]
      have h1 : ‖expK (-e) - 1 - (-e)‖ ≤ ‖e‖ ^ 2 := by
        have h := norm_expK_sub_one_sub hext hp3 hnege
        rwa [norm_neg] at h
      have h2 : ‖e * (expK (-e) - 1)‖ ≤ ‖e‖ ^ 2 := by
        rw [norm_mul, norm_expK_sub_one hext hp3 hnege, norm_neg, ← sq]
      calc ‖(expK (-e) - 1 - (-e)) + e * (expK (-e) - 1)‖
          ≤ ‖e‖ ^ 2 := le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h1 h2)
        _ ≤ (((p : ℝ)⁻¹) ^ (n + 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hen 2
        _ ≤ ((p : ℝ)⁻¹) ^ (n + 1 + 1) := by
            rw [← pow_mul]
            exact pow_le_pow_of_le_one (by positivity) hpinv1 (by omega)

/-- **exp の全射性(Phase R2 完成)**: 任意の主単数 `u`(`‖u−1‖ ≤ 1/p`)は
`u = exp x`(`x` は殻の元)。Newton 反復の Cauchy 列の極限で、**等長性
(`norm_expK_sub_expK`)が連続性の代役**を果たす。単射性(`expK_injective`)と併せて
**exp : `(p·O, +) ≅ (1+p·O, ×)` は全単射・加法的・ノルム保存 ―― その逆写像が
log-link 単数部**であり、逆写像の加法性は準同型の逆として自動的に従う
(級数 log との一致は独立の残余)。 -/
theorem expK_surjective [CompleteSpace K] (hp3 : 3 ≤ p) {u : K}
    (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ∃ x : K, ‖x‖ ≤ (p : ℝ)⁻¹ ∧ expK x = u := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
  have hp3' : 3 ≤ p := hp3
  have hcau : CauchySeq (newton u) := by
    apply cauchySeq_of_le_geometric ((p : ℝ)⁻¹) ((p : ℝ)⁻¹)
      (inv_lt_one_of_one_lt₀ hpR)
    intro n
    rw [dist_eq_norm]
    have hdiff : newton u n - newton u (n + 1)
        = -(u * expK (-(newton u n)) - 1) := by
      change newton u n - (newton u n + (u * expK (-(newton u n)) - 1)) = _
      ring
    rw [hdiff, norm_neg]
    calc ‖u * expK (-(newton u n)) - 1‖ ≤ ((p : ℝ)⁻¹) ^ (n + 1) :=
          (newton_invariant hext hp3 hu n).2
      _ = (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := by rw [pow_succ, mul_comm]
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  have hxs : ‖x‖ ≤ (p : ℝ)⁻¹ := by
    have hnorm : Tendsto (fun n => ‖newton u n‖) atTop (𝓝 ‖x‖) := hx.norm
    exact le_of_tendsto hnorm
      (Filter.Eventually.of_forall fun n => (newton_invariant hext hp3 hu n).1)
  refine ⟨x, hxs, ?_⟩
  have h1 : Tendsto (fun n => expK (newton u n)) atTop (𝓝 (expK x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have heq : ∀ n, ‖expK (newton u n) - expK x‖ = ‖newton u n - x‖ := fun n =>
      norm_expK_sub_expK hext hp3 (newton_invariant hext hp3 hu n).1 hxs
    simp_rw [heq]
    rw [← tendsto_iff_norm_sub_tendsto_zero]
    exact hx
  have h2 : Tendsto (fun n => expK (newton u n)) atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have heq : ∀ n, ‖expK (newton u n) - u‖
        = ‖u * expK (-(newton u n)) - 1‖ := by
      intro n
      have hxn := (newton_invariant hext hp3 hu n).1
      have hnegx : ‖-(newton u n)‖ ≤ (p : ℝ)⁻¹ := by rwa [norm_neg]
      have hinv : expK (newton u n) * expK (-(newton u n)) = 1 := by
        rw [← expK_add hext hp3 hxn hnegx, add_neg_cancel, expK_zero]
      have hfac : expK (newton u n) * (u * expK (-(newton u n)) - 1)
          = u - expK (newton u n) := by
        rw [mul_sub, mul_one, mul_left_comm, hinv, mul_one]
      calc ‖expK (newton u n) - u‖ = ‖-(u - expK (newton u n))‖ := by rw [neg_sub]
        _ = ‖u - expK (newton u n)‖ := norm_neg _
        _ = ‖expK (newton u n)‖ * ‖u * expK (-(newton u n)) - 1‖ := by
            rw [← hfac, norm_mul]
        _ = ‖u * expK (-(newton u n)) - 1‖ := by
            rw [norm_expK hext hp3 hxn, one_mul]
    simp_rw [heq]
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (newton_invariant hext hp3 hu n).2)
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0:ℝ) ≤ (p:ℝ)⁻¹) (inv_lt_one_of_one_lt₀ hpR)).comp
      (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using h
  exact tendsto_nhds_unique h1 h2

/-- **一意存在**(R2 の総括): 各主単数は殻のただ一つの元の exp である ――
`exp : (p·O, +) → (1+p·O, ×)` は全単射。 -/
theorem expK_existsUnique [CompleteSpace K] (hp3 : 3 ≤ p) {u : K}
    (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ∃! x : K, ‖x‖ ≤ (p : ℝ)⁻¹ ∧ expK x = u := by
  obtain ⟨x, hxs, hxe⟩ := expK_surjective hext hp3 hu
  exact ⟨x, ⟨hxs, hxe⟩, fun y ⟨hys, hye⟩ =>
    expK_injective hext hp3 hys hxs (by rw [hye, hxe])⟩

end Surjectivity

end IUT.Padic
