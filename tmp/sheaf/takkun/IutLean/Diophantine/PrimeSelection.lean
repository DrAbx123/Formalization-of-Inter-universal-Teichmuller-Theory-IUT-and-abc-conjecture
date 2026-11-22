import Mathlib
import tmp.sheaf.takkun.IutLean.Diophantine.LogVolume

/-!
# [IUT-IV] Corollary 2.2 の素数選択 — 一様な族の試験の入口

底本: [IUT-IV] §2, Cor 2.2 / Prop 1.6。

[IUT-IV] Cor 2.2 は Thm 1.10 を曲線族に一様に適用するため、各楕円曲線に対し素数 `l` を
**高さ程度の下界 `n ≈ √h` より大きく、かつ有限個の「悪い素数」(q-parameter を割る素数、
mod-`l` 表現の像が小さい素数 ―― その個数は (E3) `|GL₂(F_p)|` と高さで抑えられる)を
避けて**選ぶ必要がある。悪い素数の集合を「その積(または最小公倍数)`N`」で符号化すると、
必要なのは次の**初等的だが本質的な存在定理**である:

> `n` より大きく `N` を割らない素数 `l` が、`l ≤ 2^{⌊log₂N⌋+1}·n` の範囲に存在する。

**証明**(本モジュールで `sorry` 無しに形式化): 二進区間 `(2ⁱn, 2^{i+1}n]` の各々に
Bertrand の公準で素数を取ると、`k := ⌊log₂N⌋+1` 個の相異なる素数が得られる。すべてが
`N` を割るなら、相異なる素数の積 `≥ 2^k > N` が `N` を割ることになり矛盾。∎

これは Cor 2.2 の素数選択の**論理的核心の全部**である。残る曲線幾何的部分は
「悪い素数の積 `N` を曲線の高さで抑える」こと((E3) `card_GL2` + Galois 像の議論)。
-/

namespace IUT.Diophantine

/-- **素数回避の存在定理**(Cor 2.2 の素数選択カーネル): 任意の下界 `n ≥ 1` と法 `N ≥ 1` に
対し、`n < l ≤ 2^{⌊log₂N⌋+1}·n` かつ `l ∤ N` なる素数 `l` が存在する。

証明: 二進区間ごとの Bertrand + 「相異なる素数 `k` 個の積は `2^k > N`」の鳩の巣。 -/
theorem exists_prime_avoiding (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) :
    ∃ l : ℕ, l.Prime ∧ n < l ∧ l ≤ 2 ^ (Nat.log 2 N + 1) * n ∧ ¬ l ∣ N := by
  set k := Nat.log 2 N + 1 with hk
  -- 各二進ブロック `(2ⁱn, 2^{i+1}n]` に素数(Bertrand)
  have hblock : ∀ i : ℕ, ∃ p : ℕ, p.Prime ∧ 2 ^ i * n < p ∧ p ≤ 2 ^ (i + 1) * n := by
    intro i
    have hpos : 2 ^ i * n ≠ 0 := by positivity
    obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ i * n) hpos
    refine ⟨p, hp, h1, ?_⟩
    calc p ≤ 2 * (2 ^ i * n) := h2
      _ = 2 ^ (i + 1) * n := by ring
  choose p hp hlow hhigh using hblock
  -- ブロックは互いに素 ⟹ 素数は相異なる(狭義単調)
  have hmono : StrictMono p := by
    intro i j hij
    calc p i ≤ 2 ^ (i + 1) * n := hhigh i
      _ ≤ 2 ^ j * n := Nat.mul_le_mul_right n (Nat.pow_le_pow_right (by norm_num) hij)
      _ < p j := hlow j
  by_contra hcon
  push_neg at hcon
  -- 全ブロックの素数が N を割る
  have hdvd : ∀ i < k, p i ∣ N := by
    intro i hik
    refine hcon (p i) (hp i) ?_ ?_
    · calc n = 1 * n := (one_mul n).symm
        _ ≤ 2 ^ i * n := Nat.mul_le_mul_right n Nat.one_le_two_pow
        _ < p i := hlow i
    · calc p i ≤ 2 ^ (i + 1) * n := hhigh i
        _ ≤ 2 ^ k * n := Nat.mul_le_mul_right n (Nat.pow_le_pow_right (by norm_num) hik)
  -- k 個の相異なる素数の集合 ⊆ N の素因数
  have himage : (Finset.range k).image p ⊆ N.primeFactors := by
    intro q hq
    simp only [Finset.mem_image, Finset.mem_range] at hq
    obtain ⟨i, hik, rfl⟩ := hq
    exact Nat.mem_primeFactors.mpr ⟨hp i, hdvd i hik, by omega⟩
  have hcard : ((Finset.range k).image p).card = k := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_range]
  -- 2^k ≤ (相異なる素数の積) ≤ N
  have h2k : 2 ^ k ≤ ∏ q ∈ (Finset.range k).image p, q := by
    calc 2 ^ k = 2 ^ ((Finset.range k).image p).card := by rw [hcard]
      _ ≤ ∏ q ∈ (Finset.range k).image p, q := by
          refine Finset.pow_card_le_prod _ _ _ ?_
          intro q hq
          simp only [Finset.mem_image, Finset.mem_range] at hq
          obtain ⟨i, _, rfl⟩ := hq
          exact (hp i).two_le
  have hprodN : (∏ q ∈ (Finset.range k).image p, q) ∣ N :=
    (Finset.prod_dvd_prod_of_subset _ _ _ himage).trans (Nat.prod_primeFactors_dvd N)
  have hle : (∏ q ∈ (Finset.range k).image p, q) ≤ N := Nat.le_of_dvd (by omega) hprodN
  have hNk : N < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) N
  omega

/-- **Cor 2.2 の素数選択**: 下界 `n ≥ 6` に対し、選ばれる素数は自動的に `l ≥ 7` かつ奇
―― `ArithmeticData.l` の要求(`7 ≤ l`, `Odd l`)をすべて満たす素数が、悪い素数
(`N` の素因数)を避けて存在する。**一様な族の試験の `l`-入力の供給定理**。 -/
theorem cor22_prime_selection (n N : ℕ) (hn : 6 ≤ n) (hN : 1 ≤ N) :
    ∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ Odd l ∧ n < l ∧
      l ≤ 2 ^ (Nat.log 2 N + 1) * n ∧ ¬ l ∣ N := by
  obtain ⟨l, hp, hlt, hle, hnd⟩ := exists_prime_avoiding n N (by omega) hN
  exact ⟨l, hp, by omega, hp.odd_of_ne_two (by omega), hlt, hle, hnd⟩

end IUT.Diophantine
