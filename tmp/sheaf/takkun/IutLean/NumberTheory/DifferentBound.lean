import Mathlib

/-!
# Different の定量評価 — [IUT-IV] Prop 1.1 / Prop 1.3 への Mathlib 現状の橋

底本: [IUT-IV] Proposition 1.1 (Multiple Tensor Products and Differents) /
Proposition 1.3 (Estimates of Differents)。

Prop 1.1 の包含 `p^{d_{I∖{∗}}}·(R_I)~ ⊆ R_I` と Thm 1.10 の定数は、各局所拡大の
different 指数 `d` の**定量評価**(下界 `d ≥ (e−1)/e`・上界 `d ≤ e−1+v(e)·e` の
`ord` 正規化)を要する。Mathlib の `differentIdeal` の現状:

* **ある**: 下界 `P^{e−1} ∣ 𝔡`(`pow_sub_one_dvd_differentIdeal`)、
  不分岐判定 `¬P ∣ 𝔡 ↔ IsUnramifiedAt`(`not_dvd_differentIdeal_iff`)、
  推移性・conductor 公式;
* **ない**: 順分岐の上界 `𝔡 ∣ P^e`(⟹ `d = e−1`)、暴分岐の定量上界
  `d ≤ e−1+v_p(e)·e`(Serre, Local Fields III §6 Prop 13 相当 ―― 局所体の
  単生成性 `B = A[π]` と Eisenstein 多項式の微分の付値評価が必要)。

## 本モジュールの内容(全て標準公理のみ)

* `DifferentUpperBound`: Prop 1.1 が要求する定量上界 `𝔡 ∣ P^{e−1+e·v}` を
  **精密な残余命題**として単離(名前を与え、何が証明済で何が残余かを固定);
* `differentIdeal_eq_top_of_isUnramifiedAt`: **非分岐の場合の完全解決** ――
  局所 Dedekind(DVR)拡大で不分岐なら `𝔡 = ⊤`、すなわち `d = 0`;
* `differentUpperBound_of_isUnramifiedAt`: 非分岐 ⟹ `DifferentUpperBound`(`e = 1`,
  `v = 0`)―― 半安定楕円曲線の good な素点での Prop 1.1 の入力が確定;
* `different_lower_bound`: Mathlib の下界の再輸出(Prop 1.3 (i) の `k₀ = ℚ_p` 順分岐
  等号の下半分に相当)。

## 残余(honest)

順分岐上界(`𝔡 ∣ P^e`)・暴分岐上界(`d ≤ e−1+e·v_p(e)`)は `DifferentUpperBound` の
一般形として単離済 ―― 解消には完備 DVR 上の単生成性(`B = A[π]`、全分岐は Eisenstein)
と `𝔡 = (f'(π))`(Mathlib の `conductor_mul_differentIdeal` が使える)、および
Eisenstein 微分の付値の項別評価(最小項の一意性)が必要。
-/

namespace IUT.NumberTheory

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable [Module.Finite A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- **[IUT-IV] Prop 1.1 の定量的 different 上界**(精密な残余命題):
分岐指数 `e`・暴分岐寄与 `v = v_p(e)` に対し `𝔡_{B/A} ∣ P^{e−1+e·v}`。
`ord` 正規化(`ord(p) = 1`)では `d ≤ (e−1)/e + v_p(e)` に相当し、Thm 1.10 の
定数評価が要求する上界そのもの。非分岐(`e = 1`, `v = 0`)は
`differentUpperBound_of_isUnramifiedAt` で証明済;順分岐・暴分岐は残余。 -/
def DifferentUpperBound (P : Ideal B) (e v : ℕ) : Prop :=
  differentIdeal A B ∣ P ^ (e - 1 + e * v)

/-- **非分岐 ⟹ different 自明**(局所 Dedekind = DVR の場合): `B` が局所環で
極大イデアル `P` において不分岐なら `𝔡_{B/A} = ⊤`、すなわち different 指数 `d = 0`。
Prop 1.1 の入力のうち、半安定楕円曲線の good な素点(不分岐)での場合を完全解決。 -/
theorem differentIdeal_eq_top_of_isUnramifiedAt [IsLocalRing B]
    (H : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal B)) :
    differentIdeal A B = ⊤ := by
  by_contra hne
  have hle : differentIdeal A B ≤ IsLocalRing.maximalIdeal B :=
    IsLocalRing.le_maximalIdeal hne
  have hdvd : IsLocalRing.maximalIdeal B ∣ differentIdeal A B :=
    Ideal.dvd_iff_le.mpr hle
  exact (not_dvd_differentIdeal_iff.mpr H) hdvd

/-- **非分岐の場合の Prop 1.1 上界**: 不分岐(`e = 1`, `v = 0`)なら
`DifferentUpperBound` が成立(`𝔡 ∣ P^0 = ⊤` ⟺ `𝔡 = ⊤`)。 -/
theorem differentUpperBound_of_isUnramifiedAt [IsLocalRing B]
    (H : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal B)) :
    DifferentUpperBound A B (IsLocalRing.maximalIdeal B) 1 0 := by
  unfold DifferentUpperBound
  rw [differentIdeal_eq_top_of_isUnramifiedAt A B H]
  norm_num

/-- **different の下界**(Mathlib `pow_sub_one_dvd_differentIdeal` の再輸出):
`P^e ∣ p·B` ⟹ `P^{e−1} ∣ 𝔡`。[IUT-IV] Prop 1.3 (i)(`k₀ = ℚ_p`)の
順分岐等号 `d = (e−1)/e` の下半分に相当。上界(`DifferentUpperBound`)と併せて
順分岐で等号が確定する(上界は残余)。 -/
theorem different_lower_bound {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : ℕ)
    (hp : p ≠ ⊥) (hP : P ^ e ∣ p.map (algebraMap A B)) :
    P ^ (e - 1) ∣ differentIdeal A B :=
  pow_sub_one_dvd_differentIdeal A P e hp hP

/-- 不分岐 ⟺ `P ∤ 𝔡`(Mathlib `not_dvd_differentIdeal_iff` の再輸出、素イデアル版)。
`DifferentUpperBound` の文脈での不分岐性の判定に使う。 -/
theorem not_dvd_different_iff_unramified {P : Ideal B} [P.IsPrime] :
    ¬ P ∣ differentIdeal A B ↔ Algebra.IsUnramifiedAt A P :=
  not_dvd_differentIdeal_iff

/-! ## 順分岐上界 — Phase R6 第一切片([IUT-IV] Prop 1.3 (i) 順分岐等式の上半分)

論文が主張する順分岐等式 `d = e−1`(`ord` 正規化で `d = (e−1)/e`)のうち、
下界は Mathlib(`pow_sub_one_dvd_differentIdeal`)、**上界 `P^e ∤ 𝔡` は本節で新規に証明**する。
鍵 = トレースの単数性: 全分岐 `P^e = pB` で階数 `n`(全分岐なら `n = e`)が剰余標数の外
(`(n : A) ∉ p` = 順分岐)なら、`trace(1) = n` が `p` に落ちないため、Mathlib の trace 判定
`not_dvd_differentIdeal_of_intTrace_not_mem`(`Q := ⊤`, `x := 1`)が発動する。 -/

omit [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- 整トレースの `1` での値 = 階数(`B` が自由 `A`-加群のとき ―― DVR 上の有限
ねじれなし加群は自由ゆえ、局所的設定では常に成立)。 -/
theorem intTrace_one [Module.Free A B] :
    Algebra.intTrace A B 1 = (Module.finrank A B : A) := by
  rw [Algebra.intTrace_eq_trace, ← map_one (algebraMap A B), Algebra.trace_algebraMap]
  simp [nsmul_eq_mul]

/-- **順分岐(トレース単数性)上界**: `P^e = pB`(全分岐)かつ階数が `p` の外
(全分岐なら階数 `= e` ゆえ「剰余標数 ∤ e」= 順分岐)なら **`P^e ∤ 𝔡`**。
[IUT-IV] Prop 1.3 (i) の順分岐等式の上半分(Mathlib に無かった定量上界)。 -/
theorem not_pow_dvd_differentIdeal_of_trace_unit [Module.Free A B]
    {p : Ideal A} {P : Ideal B} {e : ℕ}
    (hP : P ^ e = p.map (algebraMap A B))
    (htame : ((Module.finrank A B : ℕ) : A) ∉ p) :
    ¬ P ^ e ∣ differentIdeal A B := by
  apply not_dvd_differentIdeal_of_intTrace_not_mem A (P ^ e) ⊤
    (by rw [Ideal.mul_top]; exact hP) 1 Submodule.mem_top
  rwa [intTrace_one A B]

/-- **順分岐の different の両側評価**([IUT-IV] Prop 1.3 (i) の順分岐等式 `d = e−1` の
divisibility 形): `P^{e−1} ∣ 𝔡`(下界、Mathlib)**かつ** `P^e ∤ 𝔡`(上界、新規)。
`d = e−1` が付値のレベルで確定 ―― Thm 1.10 の C_Θ 台帳の順分岐項の供給源。 -/
theorem tame_different_bounds [Module.Free A B]
    {p : Ideal A} [p.IsMaximal] {P : Ideal B} {e : ℕ}
    (hp : p ≠ ⊥) (hP : P ^ e = p.map (algebraMap A B))
    (htame : ((Module.finrank A B : ℕ) : A) ∉ p) :
    P ^ (e - 1) ∣ differentIdeal A B ∧ ¬ P ^ e ∣ differentIdeal A B :=
  ⟨pow_sub_one_dvd_differentIdeal A P e hp (dvd_of_eq hP),
   not_pow_dvd_differentIdeal_of_trace_unit A B hP htame⟩

/-- DVR の非零イデアルは極大イデアルの巾(イデアル分類)。 -/
lemma dvr_ideal_eq_maximalIdeal_pow [IsDiscreteValuationRing B] {I : Ideal B} (hI : I ≠ ⊥) :
    ∃ k, I = (IsLocalRing.maximalIdeal B) ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  exact ⟨k, by rw [hk, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

/-- **順分岐上界の `DifferentUpperBound` 充足**(局所 DVR): 順分岐なら
`𝔡 ∣ P^{e−1}`(= `d ≤ e−1`、暴分岐項 `v = 0`)。DVR のイデアル鎖により
`P^e ∤ 𝔡` から従う ―― [IUT-IV] Prop 1.1 の要求する定量上界の順分岐の場合の完全解決。 -/
theorem differentUpperBound_of_tame [Module.Free A B] [IsDiscreteValuationRing B]
    {p : Ideal A} {e : ℕ}
    (hP : (IsLocalRing.maximalIdeal B) ^ e = p.map (algebraMap A B))
    (htame : ((Module.finrank A B : ℕ) : A) ∉ p) :
    DifferentUpperBound A B (IsLocalRing.maximalIdeal B) e 0 := by
  unfold DifferentUpperBound
  rw [Nat.mul_zero, Nat.add_zero]
  obtain ⟨k, hk⟩ := dvr_ideal_eq_maximalIdeal_pow (B := B)
    (differentIdeal_ne_bot (A := A) (B := B))
  have hne : ¬ (IsLocalRing.maximalIdeal B) ^ e ∣ differentIdeal A B :=
    not_pow_dvd_differentIdeal_of_trace_unit A B hP htame
  rw [hk] at hne ⊢
  have hk_lt : k < e := by
    by_contra h
    exact hne (Ideal.dvd_iff_le.mpr (Ideal.pow_le_pow_right (by omega)))
  exact Ideal.dvd_iff_le.mpr (Ideal.pow_le_pow_right (by omega))

/-- **暴分岐上界への主還元**([IUT-IV] Prop 1.3 (i) の `dᵢ − d₀ = ord(f′(πᵢ))` の
`≤` 半分): 分数体を生成する任意の整元 `x` に対し **`𝔡 ∣ (f′(x))`**(`f = minpoly`)。
Mathlib の `aeval_derivative_mem_differentIdeal`(conductor 公式の帰結)による ――
単生成性(monogenicity)は不要で、生成元の存在だけでよい。これにより暴分岐上界
`d ≤ e−1+e·v_p(e)` は「`v(f′(π)) ≤ e−1+e·v_p(e)` なる生成元 `π`(全分岐なら
Eisenstein 一意化元)の存在」という付値計算に還元される(R6 残)。 -/
theorem differentIdeal_dvd_span_derivative (x : B)
    (hx : Algebra.adjoin (FractionRing A)
      {algebraMap B (FractionRing B) x} = ⊤) :
    differentIdeal A B ∣
      Ideal.span {Polynomial.aeval x (Polynomial.derivative (minpoly A x))} := by
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact aeval_derivative_mem_differentIdeal (A := A) (K := FractionRing A)
    (L := FractionRing B) x hx

/-! ## 支配項の道具と暴分岐上界の完全還元

Eisenstein 微分 `f′(π) = e·π^{e−1} + Σᵢ i·aᵢ·πⁱ⁻¹` の付値評価
`v(f′(π)) ≤ e−1+e·v_p(e)` は「唯一の最小付値項が和を支配する」議論で行う。
その骨格(支配項補題)と、非所属 `f′(π) ∉ P^{D+1}` から `DifferentUpperBound` への
橋(DVR の span-巾評価)をここで用意する。 -/

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- 支配項補題(二項版): `x ∉ I`, `y ∈ I` なら `x + y ∉ I`。 -/
lemma add_notMem_of_notMem {I : Ideal B} {x y : B} (hx : x ∉ I) (hy : y ∈ I) :
    x + y ∉ I :=
  fun h => hx (by simpa using I.sub_mem h hy)

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- **支配項補題**(有限和版): 唯一の項 `x i₀ ∉ I` を除き全ての項が `I` に属するなら、
和は `I` に属さない ―― 相異なる付値を持つ項の和の付値 = 最小付値(最小項の一意性)の
イデアル論的形。Eisenstein 微分の項別評価の核。 -/
lemma sum_notMem_of_unique {ι : Type*} {I : Ideal B} {s : Finset ι} {x : ι → B}
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hx : x i₀ ∉ I)
    (hother : ∀ j ∈ s, j ≠ i₀ → x j ∈ I) :
    ∑ j ∈ s, x j ∉ I := by
  classical
  rw [← Finset.add_sum_erase s x hi₀]
  apply add_notMem_of_notMem (B := B) hx
  exact Submodule.sum_mem _ fun j hj =>
    hother j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)

omit [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- DVR の span-巾評価: `x ≠ 0` かつ `x ∉ P^{D+1}` なら `(x) ∣ P^D`
(`(x) = P^m` で `m ≤ D` が強制される)。 -/
lemma span_singleton_dvd_pow_of_notMem [IsDiscreteValuationRing B] {x : B} {D : ℕ}
    (hx0 : x ≠ 0) (hx : x ∉ (IsLocalRing.maximalIdeal B) ^ (D + 1)) :
    Ideal.span {x} ∣ (IsLocalRing.maximalIdeal B) ^ D := by
  have hbot : Ideal.span {x} ≠ (⊥ : Ideal B) := by
    simpa [Ideal.span_singleton_eq_bot] using hx0
  obtain ⟨m, hm⟩ := dvr_ideal_eq_maximalIdeal_pow (B := B) hbot
  have hxm : x ∈ (IsLocalRing.maximalIdeal B) ^ m :=
    hm ▸ Ideal.mem_span_singleton_self x
  have hmD : m ≤ D := by
    by_contra h
    exact hx (Ideal.pow_le_pow_right (by omega) hxm)
  rw [hm]
  exact Ideal.dvd_iff_le.mpr (Ideal.pow_le_pow_right hmD)

/-- **暴分岐上界の完全還元(R6 の主定理)**: 分数体生成元 `x` の微分値が
`f′(x) ≠ 0` かつ `f′(x) ∉ P^{D+1}`(= `v(f′(x)) ≤ D`)なら **`𝔡 ∣ P^D`**。
`D := e−1+e·v_p(e)`・`x :=` 全分岐 Eisenstein 一意化元 とすれば [IUT-IV] Prop 1.3 の
暴分岐上界そのもの ―― 残る義務は非所属 `f′(π) ∉ P^{D+1}` のみで、それは
`sum_notMem_of_unique`(支配項 = `e·π^{e−1}`、他項は Eisenstein 性より深い)で
討ち取る形に整っている(付値の相異は指数の mod `e` 剰余の相異による)。 -/
theorem differentIdeal_dvd_pow_of_derivative_notMem [IsDiscreteValuationRing B]
    (x : B)
    (hx : Algebra.adjoin (FractionRing A)
      {algebraMap B (FractionRing B) x} = ⊤)
    {D : ℕ}
    (hne : Polynomial.aeval x (Polynomial.derivative (minpoly A x)) ≠ 0)
    (hnot : Polynomial.aeval x (Polynomial.derivative (minpoly A x))
      ∉ (IsLocalRing.maximalIdeal B) ^ (D + 1)) :
    differentIdeal A B ∣ (IsLocalRing.maximalIdeal B) ^ D :=
  dvd_trans (differentIdeal_dvd_span_derivative A B x hx)
    (span_singleton_dvd_pow_of_notMem (B := B) hne hnot)

/-- 暴分岐上界の `DifferentUpperBound` 形(`D = e−1+e·v`)。 -/
theorem differentUpperBound_of_derivative_notMem [IsDiscreteValuationRing B]
    (x : B)
    (hx : Algebra.adjoin (FractionRing A)
      {algebraMap B (FractionRing B) x} = ⊤)
    {e v : ℕ}
    (hne : Polynomial.aeval x (Polynomial.derivative (minpoly A x)) ≠ 0)
    (hnot : Polynomial.aeval x (Polynomial.derivative (minpoly A x))
      ∉ (IsLocalRing.maximalIdeal B) ^ (e - 1 + e * v + 1)) :
    DifferentUpperBound A B (IsLocalRing.maximalIdeal B) e v :=
  differentIdeal_dvd_pow_of_derivative_notMem A B x hx hne hnot

/-! ## 微分の項別展開と支配項データへの最終還元 -/

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- **微分値の項別展開**: `f′(x) = Σ_{i<deg f} (f.coeff(i+1)·(i+1)) • xⁱ`
(Eisenstein 微分 `f′(π) = e·π^{e−1} + Σ i·aᵢ·πⁱ⁻¹` の一般形)。 -/
lemma aeval_derivative_eq_sum (x : B) {f : Polynomial A} (hf : f.natDegree ≠ 0) :
    Polynomial.aeval x (Polynomial.derivative f)
      = ∑ i ∈ Finset.range f.natDegree,
          (f.coeff (i + 1) * ((i : A) + 1)) • x ^ i := by
  rw [Polynomial.aeval_eq_sum_range' (Polynomial.natDegree_derivative_lt hf) x]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.coeff_derivative]

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- **支配項による微分値の非所属**: 展開の唯一の項 `i₀` が `I` の外(支配項 = 最小付値項)、
他の全項が `I` の中なら、`f′(x) ∉ J`(`J ⊆ I` なる任意の深いイデアル)。 -/
theorem aeval_derivative_notMem (x : B) {f : Polynomial A} (hf : f.natDegree ≠ 0)
    {I J : Ideal B} (hJI : J ≤ I)
    {i₀ : ℕ} (hi₀ : i₀ ∈ Finset.range f.natDegree)
    (hdom : (f.coeff (i₀ + 1) * ((i₀ : A) + 1)) • x ^ i₀ ∉ I)
    (hothers : ∀ j ∈ Finset.range f.natDegree, j ≠ i₀ →
      (f.coeff (j + 1) * ((j : A) + 1)) • x ^ j ∈ I) :
    Polynomial.aeval x (Polynomial.derivative f) ∉ J := by
  intro hmem
  have h1 := hJI hmem
  rw [aeval_derivative_eq_sum A B x hf] at h1
  exact sum_notMem_of_unique (B := B) hi₀ hdom hothers h1

/-- **暴分岐上界の支配項データへの最終還元(R6 総組立)**: 生成元 `x` の微分展開に
**支配項データ**(添字 `i₀`・深さ `k ≤ e−1+e·v` で、`i₀` 項だけが `P^{k+1}` の外、
他項は全て中)が存在すれば `DifferentUpperBound`(`𝔡 ∣ P^{e−1+e·v}`)が成立する。

Eisenstein 一意化元では: 支配項 = 最小付値項(付値は mod `e` 剰余の相異により
一意に最小)、`k` = その付値 `≤ e·v_p(e)+e−1`(先頭項 `e·π^{e−1}` の付値が上界)――
残る義務はこの**元レベルの付値算術**(DVR の積の付値の乗法性)のみ。 -/
theorem differentUpperBound_of_dominant [IsDiscreteValuationRing B]
    (x : B)
    (hgen : Algebra.adjoin (FractionRing A)
      {algebraMap B (FractionRing B) x} = ⊤)
    {e v : ℕ}
    (hdeg : (minpoly A x).natDegree ≠ 0)
    (hne : Polynomial.aeval x (Polynomial.derivative (minpoly A x)) ≠ 0)
    {k : ℕ} (hk : k ≤ e - 1 + e * v)
    {i₀ : ℕ} (hi₀ : i₀ ∈ Finset.range (minpoly A x).natDegree)
    (hdom : ((minpoly A x).coeff (i₀ + 1) * ((i₀ : A) + 1)) • x ^ i₀
      ∉ (IsLocalRing.maximalIdeal B) ^ (k + 1))
    (hothers : ∀ j ∈ Finset.range (minpoly A x).natDegree, j ≠ i₀ →
      ((minpoly A x).coeff (j + 1) * ((j : A) + 1)) • x ^ j
        ∈ (IsLocalRing.maximalIdeal B) ^ (k + 1)) :
    DifferentUpperBound A B (IsLocalRing.maximalIdeal B) e v :=
  differentUpperBound_of_derivative_notMem A B x hgen hne
    (aeval_derivative_notMem A B x hdeg
      (Ideal.pow_le_pow_right (by omega)) hi₀ hdom hothers)

/-! ## DVR の ϖ-付値ミクロ理論 — 支配項データ供給の道具(R6 真の最終ピース)

Eisenstein 項 `(i·aᵢ) • πⁱ⁻¹` の正確な深さの計算に要るのは
「積の付値乗法性」`a ∉ P^{s+1} ∧ b ∉ P^{t+1} ⟹ ab ∉ P^{s+t+1}` である。
DVR の単数正規形 `x = u·ϖᵐ` と ϖ-可除性で証明する。 -/

/-- DVR の巾-所属 ⟺ ϖ-可除性(`P^k = (ϖ^k)`)。 -/
lemma mem_maximalIdeal_pow_iff [IsDiscreteValuationRing B] {ϖ : B}
    (hϖ : Irreducible ϖ) {x : B} {k : ℕ} :
    x ∈ (IsLocalRing.maximalIdeal B) ^ k ↔ ϖ ^ k ∣ x := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- 既約元の巾の可除は指数の順序を強制する。 -/
lemma le_of_pow_dvd_pow [IsDiscreteValuationRing B] {ϖ : B}
    (hϖ : Irreducible ϖ) {K N : ℕ} (h : ϖ ^ K ∣ ϖ ^ N) : K ≤ N := by
  by_contra hcon
  have hlt : N < K := Nat.lt_of_not_le hcon
  have h1 : ϖ ^ N * ϖ ^ (K - N) ∣ ϖ ^ N * 1 := by
    rw [mul_one, ← pow_add, show N + (K - N) = K from by omega]
    exact h
  have h2 : ϖ ^ (K - N) ∣ 1 :=
    (mul_dvd_mul_iff_left (pow_ne_zero N hϖ.ne_zero)).mp h1
  have h3 : IsUnit ϖ := (isUnit_pow_iff (by omega : K - N ≠ 0)).mp (isUnit_of_dvd_one h2)
  exact hϖ.not_isUnit h3

/-- **積の付値乗法性(非所属形)**: `a ∉ P^{s+1}`, `b ∉ P^{t+1}` ⟹ `ab ∉ P^{s+t+1}`
(付値 `v(ab) = v(a) + v(b) ≤ s + t` の膜語)。Eisenstein 項の深さ計算の核。 -/
lemma mul_notMem_maximalIdeal_pow [IsDiscreteValuationRing B]
    {a b : B} {s t : ℕ}
    (ha : a ∉ (IsLocalRing.maximalIdeal B) ^ (s + 1))
    (hb : b ∉ (IsLocalRing.maximalIdeal B) ^ (t + 1)) :
    a * b ∉ (IsLocalRing.maximalIdeal B) ^ (s + t + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ zero_mem _)
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hm : m ≤ s := by
    by_contra h
    apply ha
    rw [mem_maximalIdeal_pow_iff (B := B) hϖ]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  have hn : n ≤ t := by
    by_contra h
    apply hb
    rw [mem_maximalIdeal_pow_iff (B := B) hϖ]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  intro hmem
  rw [mem_maximalIdeal_pow_iff (B := B) hϖ] at hmem
  have h1 : (↑u * ϖ ^ m) * (↑w * ϖ ^ n) = ϖ ^ (m + n) * ↑(u * w) := by
    rw [Units.val_mul, pow_add]
    ring
  rw [h1, Units.dvd_mul_right] at hmem
  have := le_of_pow_dvd_pow (B := B) hϖ hmem
  omega

/-- **一意化元の巾の正確な深さ**: `π ∉ P²` ⟹ `πʲ ∉ P^{j+1}`(`v(πʲ) = j` の膜語)。 -/
lemma pow_notMem_maximalIdeal_pow [IsDiscreteValuationRing B]
    {π : B} (hπ : π ∉ (IsLocalRing.maximalIdeal B) ^ 2) (j : ℕ) :
    π ^ j ∉ (IsLocalRing.maximalIdeal B) ^ (j + 1) := by
  induction j with
  | zero =>
    rw [pow_zero, pow_one]
    intro h
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  | succ j ih =>
    have h := mul_notMem_maximalIdeal_pow (B := B) (s := j) (t := 1) ih
      (by simpa using hπ)
    rw [← pow_succ] at h
    exact h

/-- **Eisenstein 支配項データの総組立(R6 完成)**: 一意化元 `π`(`π ∈ P`, `π ∉ P²`)の
minpoly の微分の各項の係数像に**正確な深さの割当** `e·μ j`(全分岐の付値関係
`v_B∘algebraMap = e·v_A` の出力形; 零係数は除外可)が与えられ、先頭項
(`j = e−1`、monic ゆえ係数像 `= (e : B)`)が非零で `μ(e−1) ≤ v` なら、
**`DifferentUpperBound`(`𝔡 ∣ P^{e−1+e·v}`)が成立**する。

証明は完全に実行される: 項の深さ `e·μ j + j` は mod `e` 剰余により**相異**、
`Finset.exists_min_image` で最小項(支配項)を特定、その深さ `k` は先頭項の深さ
`e·μ(e−1)+e−1 ≤ e·v+e−1` 以下、乗法性(`mul_notMem_maximalIdeal_pow` +
`pow_notMem_maximalIdeal_pow`)で支配項の非所属、他項は深さの差で吸収。

`v := v_p(e)` として [IUT-IV] Prop 1.3 (i) の**暴分岐上界 `d ≤ e−1+e·v_p(e)`** の形。
残る外部入力は `hc`(全分岐 Eisenstein 拡大での係数像の深さ ―― `p = (ρ)`,
`algebraMap ρ = unit·ϖ^e` からの標準計算)のみ。 -/
theorem differentUpperBound_of_eisenstein_data [IsDiscreteValuationRing B]
    (π : B)
    (hgen : Algebra.adjoin (FractionRing A)
      {algebraMap B (FractionRing B) π} = ⊤)
    (hπ1 : π ∈ IsLocalRing.maximalIdeal B)
    (hπ2 : π ∉ (IsLocalRing.maximalIdeal B) ^ 2)
    {e v : ℕ} (hdeg : (minpoly A π).natDegree = e) (he : e ≠ 0)
    (μ : ℕ → ℕ)
    (hc : ∀ j ∈ Finset.range e,
      algebraMap A B ((minpoly A π).coeff (j + 1) * ((j : A) + 1)) = 0 ∨
      (algebraMap A B ((minpoly A π).coeff (j + 1) * ((j : A) + 1))
          ∈ (IsLocalRing.maximalIdeal B) ^ (e * μ j) ∧
        algebraMap A B ((minpoly A π).coeff (j + 1) * ((j : A) + 1))
          ∉ (IsLocalRing.maximalIdeal B) ^ (e * μ j + 1)))
    (hlead0 : algebraMap A B
      ((minpoly A π).coeff (e - 1 + 1) * (((e - 1 : ℕ) : A) + 1)) ≠ 0)
    (hlead : μ (e - 1) ≤ v) :
    DifferentUpperBound A B (IsLocalRing.maximalIdeal B) e v := by
  classical
  -- 非零項の集合と最小深さ項(支配項)
  set S : Finset ℕ := (Finset.range e).filter
    (fun j => algebraMap A B ((minpoly A π).coeff (j + 1) * ((j : A) + 1)) ≠ 0) with hS
  have hleadS : e - 1 ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hlead0⟩
  obtain ⟨i₀, hi₀S, hmin⟩ := Finset.exists_min_image S (fun j => e * μ j + j)
    ⟨e - 1, hleadS⟩
  obtain ⟨hi₀e, hi₀0⟩ := Finset.mem_filter.mp hi₀S
  rcases hc i₀ hi₀e with h0 | ⟨hi₀mem, hi₀not⟩
  · exact absurd h0 hi₀0
  -- 支配項の深さは D 以下
  have hkD : e * μ i₀ + i₀ ≤ e - 1 + e * v := by
    have h1 := hmin (e - 1) hleadS
    have h2 : e * μ (e - 1) ≤ e * v := Nat.mul_le_mul_left e hlead
    have h3 : e - 1 < e := by omega
    omega
  -- 支配項の非所属
  have hdom : ((minpoly A π).coeff (i₀ + 1) * ((i₀ : A) + 1)) • π ^ i₀
      ∉ (IsLocalRing.maximalIdeal B) ^ (e * μ i₀ + i₀ + 1) := by
    rw [Algebra.smul_def]
    exact mul_notMem_maximalIdeal_pow (B := B) hi₀not
      (pow_notMem_maximalIdeal_pow (B := B) hπ2 i₀)
  -- 他項の所属
  have hothers : ∀ j ∈ Finset.range e, j ≠ i₀ →
      ((minpoly A π).coeff (j + 1) * ((j : A) + 1)) • π ^ j
        ∈ (IsLocalRing.maximalIdeal B) ^ (e * μ i₀ + i₀ + 1) := by
    intro j hj hjne
    rcases hc j hj with h0 | ⟨hjm, hjn⟩
    · rw [Algebra.smul_def, h0, zero_mul]
      exact zero_mem _
    · have hjS : j ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨hj, fun h => hjn (h ▸ zero_mem _)⟩
      have hge : e * μ i₀ + i₀ ≤ e * μ j + j := hmin j hjS
      have hnedep : e * μ j + j ≠ e * μ i₀ + i₀ := by
        intro heq
        apply hjne
        have hje : j < e := Finset.mem_range.mp hj
        have hi₀lt : i₀ < e := Finset.mem_range.mp hi₀e
        have h1 : (e * μ j + j) % e = j := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hje]
        have h2 : (e * μ i₀ + i₀) % e = i₀ := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi₀lt]
        rw [← h1, heq, h2]
      have hterm : ((minpoly A π).coeff (j + 1) * ((j : A) + 1)) • π ^ j
          ∈ (IsLocalRing.maximalIdeal B) ^ (e * μ j + j) := by
        rw [Algebra.smul_def]
        have h := Ideal.mul_mem_mul hjm (Ideal.pow_mem_pow hπ1 j)
        rwa [← pow_add] at h
      exact Ideal.pow_le_pow_right (by omega) hterm
  -- 組立
  have hdeg' : (minpoly A π).natDegree ≠ 0 := by omega
  have hi₀' : i₀ ∈ Finset.range (minpoly A π).natDegree := by
    rw [hdeg]; exact hi₀e
  have hothers' : ∀ j ∈ Finset.range (minpoly A π).natDegree, j ≠ i₀ →
      ((minpoly A π).coeff (j + 1) * ((j : A) + 1)) • π ^ j
        ∈ (IsLocalRing.maximalIdeal B) ^ (e * μ i₀ + i₀ + 1) := by
    intro j hj hjne
    exact hothers j (by rwa [hdeg] at hj) hjne
  have hnot' := aeval_derivative_notMem A B π hdeg'
    (Ideal.pow_le_pow_right (by omega : e * μ i₀ + i₀ + 1 ≤ e - 1 + e * v + 1))
    hi₀' hdom hothers'
  have hne0 : Polynomial.aeval π (Polynomial.derivative (minpoly A π)) ≠ 0 :=
    fun h0 => hnot' (h0 ▸ zero_mem _)
  exact differentIdeal_dvd_pow_of_derivative_notMem A B π hgen hne0 hnot'

end IUT.NumberTheory
