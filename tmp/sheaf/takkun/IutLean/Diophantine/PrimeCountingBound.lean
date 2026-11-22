import Mathlib
import tmp.sheaf.takkun.IutLean.Diophantine.LogVolume

/-!
# [IUT-IV] Prop 1.6 の Chebyshev 版 — 素数計数関数の明示的上界

底本: [IUT-IV] Prop 1.6(素数定理: `π(η) ≤ 4η/(3·log η)`)。

**honest 注記**: Prop 1.6 の定数 `4/3` は素数定理(PNT)強度であり、PNT は現行 Mathlib 核に
未収録である。本モジュールは Mathlib にある **Chebyshev 型の入力**(`primorial n ≤ 4ⁿ`、
Bertrand の証明の基盤)から、**明示的な弱定数版**

  `π(n) ≤ √n + 1 + 4·n / log n`(`n ≥ 2`)

を `sorry` 無しで証明する。Cor 2.2 の構造(ε-形式)はこの弱定数版で十分機能し、
定数のみが劣化する。定数 `4/3` への精密化は PNT の形式化(将来の Mathlib)に還元される。

**証明**: (1) `θ(n) = Σ_{p ≤ n} log p = log(primorial n) ≤ n·log 4`(Chebyshev 上界);
(2) `√n` より大きい素数は各々 `log p ≥ (1/2)·log n` を寄与するので、その個数は
`≤ 2n·log4/log n ≤ 4n/log n`; (3) `√n` 以下の素数は高々 `√n + 1` 個。∎
-/

namespace IUT.Diophantine

open Finset

/-- **Chebyshev の θ-上界**: `θ(n) = Σ_{p ≤ n} log p ≤ n·log 4`
(Mathlib の `primorial_le_four_pow` から)。 -/
theorem theta_le (n : ℕ) :
    ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime), Real.log p ≤ n * Real.log 4 := by
  have hne : ∀ p ∈ (range (n + 1)).filter (fun p => p.Prime), ((p : ℝ)) ≠ 0 := by
    intro p hp
    simp only [mem_filter] at hp
    exact_mod_cast hp.2.pos.ne'
  have h1 : ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime), Real.log p
      = Real.log ((primorial n : ℕ) : ℝ) := by
    unfold primorial
    push_cast
    exact (Real.log_prod hne).symm
  have hpos : 0 < primorial n := by
    apply Finset.prod_pos
    intro p hp
    simp only [mem_filter] at hp
    exact hp.2.pos
  rw [h1]
  calc Real.log ((primorial n : ℕ) : ℝ)
      ≤ Real.log (((4 ^ n : ℕ) : ℝ)) := by
        apply Real.log_le_log (by exact_mod_cast hpos)
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by
        push_cast
        rw [Real.log_pow]

/-- **Prop 1.6 の Chebyshev 版**: `π(n) ≤ √n + 1 + 4·n/log n`(`n ≥ 2`)。
原論文の `4η/(3·log η)` は PNT 強度ゆえ、Mathlib の Chebyshev 入力による
明示的弱定数版(Cor 2.2 の ε-形式にはこれで十分、定数のみ劣化)。 -/
theorem primeCounting_le_chebyshev (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 + 4 * n / Real.log n := by
  set k := Nat.sqrt n with hk
  set P := (range (n + 1)).filter (fun p => p.Prime) with hP
  set Q := P.filter (fun p => k + 1 ≤ p) with hQ
  -- π n = |P|
  have hπ : Nat.primeCounting n = P.card := by
    rw [hP]
    show Nat.count Nat.Prime (n + 1) = _
    rw [Nat.count_eq_card_filter_range]
  -- |P| ≤ |Q| + (k+1)(√n 以下の素数は高々 k+1 個)
  have hsplit : P.card ≤ Q.card + (k + 1) := by
    have hsub : P ⊆ Q ∪ range (k + 1) := by
      intro p hp
      by_cases hpk : k + 1 ≤ p
      · exact Finset.mem_union_left _ (by rw [hQ]; exact Finset.mem_filter.mpr ⟨hp, hpk⟩)
      · exact Finset.mem_union_right _ (by simp only [mem_range]; omega)
    calc P.card ≤ (Q ∪ range (k + 1)).card := Finset.card_le_card hsub
      _ ≤ Q.card + (range (k + 1)).card := Finset.card_union_le _ _
      _ = Q.card + (k + 1) := by rw [Finset.card_range]
  -- log n > 0
  have hlogn : (0 : ℝ) < Real.log n :=
    Real.log_pos (by exact_mod_cast hn)
  -- √n < k+1 ⟹ log n / 2 ≤ log(k+1)
  have hsqrtlog : Real.log n / 2 ≤ Real.log ((k : ℝ) + 1) := by
    have h1 : Real.sqrt n < (k : ℝ) + 1 := by
      rw [Real.sqrt_lt' (by positivity)]
      exact_mod_cast Nat.lt_succ_sqrt' n
    calc Real.log n / 2
        = Real.log (Real.sqrt n) := (Real.log_sqrt (by positivity)).symm
      _ ≤ Real.log ((k : ℝ) + 1) := by
          apply Real.log_le_log _ h1.le
          apply Real.sqrt_pos.mpr
          have : (0:ℕ) < n := by omega
          exact_mod_cast this
  -- Q の各素数は log n / 2 以上を寄与
  have hQlb : ∀ q ∈ Q, Real.log n / 2 ≤ Real.log q := by
    intro q hq
    simp only [hQ, hP, mem_filter] at hq
    refine hsqrtlog.trans (Real.log_le_log (by positivity) ?_)
    exact_mod_cast hq.2
  have hQsum : (Q.card : ℝ) * (Real.log n / 2) ≤ ∑ q ∈ Q, Real.log q := by
    have h := Finset.card_nsmul_le_sum Q (fun q => Real.log (q : ℝ)) (Real.log n / 2) hQlb
    simpa [nsmul_eq_mul] using h
  have hQP : ∑ q ∈ Q, Real.log q ≤ ∑ p ∈ P, Real.log p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p hp _
    simp only [hP, mem_filter] at hp
    apply Real.log_nonneg
    exact_mod_cast hp.2.one_lt.le
  -- log 4 ≤ 2
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    linarith [log_two_le_one]
  -- |Q| ≤ 4n/log n
  have hQbound : (Q.card : ℝ) ≤ 4 * n / Real.log n := by
    have hθ := theta_le n
    rw [le_div_iff₀ hlogn]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hQsum, hQP, hθ, hlog4, hn0]
  -- 合成
  have hπr : (Nat.primeCounting n : ℝ) = (P.card : ℝ) := by exact_mod_cast hπ
  have hsplit' : (P.card : ℝ) ≤ (Q.card : ℝ) + ((k : ℝ) + 1) := by exact_mod_cast hsplit
  calc (Nat.primeCounting n : ℝ)
      = (P.card : ℝ) := hπr
    _ ≤ (Q.card : ℝ) + ((k : ℝ) + 1) := hsplit'
    _ ≤ 4 * n / Real.log n + ((k : ℝ) + 1) := by linarith [hQbound]
    _ = (k : ℝ) + 1 + 4 * n / Real.log n := by ring

end IUT.Diophantine
