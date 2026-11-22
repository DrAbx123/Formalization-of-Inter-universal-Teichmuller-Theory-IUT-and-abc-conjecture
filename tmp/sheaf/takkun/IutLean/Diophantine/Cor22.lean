import Mathlib
import tmp.sheaf.takkun.IutLean.Arithmetic.AdjudicationTest
import tmp.sheaf.takkun.IutLean.Diophantine.PrimeSelection

/-!
# [IUT-IV] Corollary 2.2 の合成 — ε-形式の一様な高さ不等式

底本: [IUT-IV] §2, Cor 2.2。

これまでに検証した全部品 ―― 素数選択(`cor22_prime_selection`)・判定テスト
(`AdjudicationTest`)・Thm 1.10 の初等的導出(`adjudication_implies_height`)―― を、
Cor 2.2 の **ε-形式の一様な Szpiro 型不等式**に合成する:

1. **`cor22_epsilon_form`(ε-抽出)**: テストが通り、素数 `l` が窓
   `20·d_mod/ε ≤ l` かつ `20(e*·l+η) ≤ ε·log q` に入っていれば、
   `(1/6 − ε)·log(q) ≤ (1+ε)·D` ―― `l`-依存の係数と誤差項が `ε` に吸収される。
2. **`cor22_uniform`(一様合成)**: 有界な不変量(`d_mod ≤ d_max` 等)を持つ**任意の**曲線
   データと悪い素数の法 `N` に対し、良い素数での**一様なテスト供給**(仮定 ―― 係争点)から、
   `∃ C, (1/6 − ε)·log(q) ≤ (1+ε)·D + C·N` ―― `l` の選択(素数選択カーネル)・場合分け
   (高さが閾値以下なら定数に吸収)込みの完全な合成。

**残る 2 つの入力(honest)**: (i) テストの一様供給 = Thm 3.11 + Prop 1.1–1.9(係争点)、
(ii) `N`(悪い素数の積)を高さで抑える評価((E3) `card_GL2` + [GenEll] の Galois 像議論、
および `C·N` 項を吸収する精密な素数計数 = Prop 1.6 の `η_prm`)。これらが供給されれば、
本定理の結論は既存の `SzpiroStatement`(→ ABC)の形に達する。
-/

namespace IUT.Diophantine

open IUT.Arithmetic

/-- **ε-抽出定理**(Cor 2.2 の単一曲線段階): テストが通り、素数 `l` が窓
`20·d_mod ≤ ε·l`(下)かつ `20(e*·l+η) ≤ ε·log q`(上)に入っていれば、
`l`-依存項がすべて `ε` に吸収されて `(1/6 − ε)·log(q) ≤ (1+ε)·D`。 -/
theorem cor22_epsilon_form (A : ArithmeticData) (ε : ℝ) (hε : 0 < ε)
    (hpass : A.AdjudicationTest)
    (hlow : 20 * A.dmod ≤ ε * (A.l : ℝ))
    (hhigh : 20 * (A.estar * (A.l : ℝ) + A.eta) ≤ ε * A.logq) :
    (1 / 6 - ε) * A.logq ≤ (1 + ε) * A.D := by
  have h := A.adjudication_implies_height hpass
  have hl0 := A.l_cast_pos
  have hdiv : 20 * A.dmod / (A.l : ℝ) ≤ ε := by
    rw [div_le_iff₀ hl0]
    linarith
  have h1 : (1 + 20 * A.dmod / (A.l : ℝ)) * A.D ≤ (1 + ε) * A.D := by
    apply mul_le_mul_of_nonneg_right _ A.hD
    linarith
  nlinarith [h, h1, hhigh]

/-- **Cor 2.2 の一様合成**: 有界な不変量を持つ任意の曲線データ・任意の悪い素数の法 `N` に
対し、**良い素数での一様なテスト供給**(仮定 `hsupply` ―― 係争点そのもの)から、
素数選択カーネルで `l` を選び、ε-抽出と閾値場合分けにより

  `(1/6 − ε)·log(q) ≤ (1+ε)·D + C·N`

を導く(`C` は `ε` と不変量の上界のみに依存する明示的な定数)。
残る作業 = `hsupply` の証明(係争点)と `N ≲ 高さ` の評価(Galois 像・素数計数)。 -/
theorem cor22_uniform (ε dmax emax ηmax : ℝ)
    (hε : 0 < ε) (hdmax : 1 ≤ dmax) (hemax : 1 ≤ emax) (hηmax : 0 ≤ ηmax) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (vq : ℕ) (hvq : 1 ≤ vq) (logNv : ℝ) (hlogNv : 0 < logNv)
        (dmod estar eta D : ℝ)
        (hdmod : 1 ≤ dmod) (hestar : 1 ≤ estar) (heta : 0 ≤ eta) (hD : 0 ≤ D)
        (_hdle : dmod ≤ dmax) (hele : estar ≤ emax) (hetale : eta ≤ ηmax)
        (N : ℕ) (hN : 1 ≤ N),
        (∀ (l : ℕ), l.Prime → (h7 : 7 ≤ l) → (ho : Odd l) → ¬ l ∣ N →
          (ArithmeticData.mk l h7 ho vq hvq logNv hlogNv dmod hdmod estar hestar
            eta heta D hD).AdjudicationTest) →
        (1 / 6 - ε) * ((vq : ℝ) * logNv) ≤ (1 + ε) * D + C * N := by
  classical
  set n₀ : ℕ := max 6 ⌈20 * dmax / ε⌉₊ with hn₀def
  have hn₀6 : 6 ≤ n₀ := le_max_left _ _
  have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
  have hn₀1 : (1 : ℝ) ≤ (n₀ : ℝ) := by
    have : (1 : ℕ) ≤ n₀ := by omega
    exact_mod_cast this
  refine ⟨(40 * emax * (n₀ : ℝ) + 20 * ηmax) / ε, ?_, ?_⟩
  · apply div_nonneg _ hε.le
    nlinarith
  intro vq hvq logNv hlogNv dmod estar eta D hdmod hestar heta hD _hdle hele hetale
    N hN hsupply
  -- 素数選択カーネルで l を選ぶ
  obtain ⟨l, hp, h7, hodd, hlt, hle, hnd⟩ :=
    cor22_prime_selection n₀ N hn₀6 hN
  set A := ArithmeticData.mk l h7 hodd vq hvq logNv hlogNv dmod hdmod estar hestar
    eta heta D hD with hA
  have hpass := hsupply l hp h7 hodd hnd
  have hAlogq : A.logq = (vq : ℝ) * logNv := rfl
  have hAD : A.D = D := rfl
  have hlq_pos : (0 : ℝ) < (vq : ℝ) * logNv := by
    have h1 : (1 : ℝ) ≤ (vq : ℝ) := by exact_mod_cast hvq
    nlinarith
  -- l の実数評価: n₀ < l ≤ 2·N·n₀
  have hn₀l : (n₀ : ℝ) < (l : ℝ) := by exact_mod_cast hlt
  have hl2Nn : (l : ℝ) ≤ 2 * (N : ℝ) * (n₀ : ℝ) := by
    have h2 : 2 ^ (Nat.log 2 N + 1) ≤ 2 * N := by
      have h3 := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
      have h4 : (2 : ℕ) ^ (Nat.log 2 N + 1) = 2 ^ Nat.log 2 N * 2 := pow_succ 2 _
      omega
    have h5 : l ≤ 2 * N * n₀ := le_trans hle (Nat.mul_le_mul_right n₀ h2)
    exact_mod_cast h5
  -- 下側の窓: 20·d_mod ≤ ε·l
  have hceil : 20 * dmax ≤ ε * (n₀ : ℝ) := by
    have h1 : 20 * dmax / ε ≤ (⌈20 * dmax / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈20 * dmax / ε⌉₊ : ℕ) : ℝ) ≤ (n₀ : ℝ) := by
      exact_mod_cast le_max_right 6 ⌈20 * dmax / ε⌉₊
    rw [div_le_iff₀ hε] at h1
    nlinarith
  have hlow : 20 * A.dmod ≤ ε * (A.l : ℝ) := by
    show 20 * dmod ≤ ε * (l : ℝ)
    nlinarith [hn₀l, hε.le, _hdle]
  -- 上側の窓での場合分け
  by_cases hcase : 20 * (A.estar * (A.l : ℝ) + A.eta) ≤ ε * A.logq
  · -- 窓内: ε-抽出定理
    have h := cor22_epsilon_form A ε hε hpass hlow hcase
    rw [hAlogq, hAD] at h
    have hCN : (0 : ℝ) ≤ (40 * emax * (n₀ : ℝ) + 20 * ηmax) / ε * (N : ℝ) := by
      apply mul_nonneg (div_nonneg _ hε.le) (Nat.cast_nonneg _)
      nlinarith
    linarith
  · -- 窓外: 高さが閾値以下 ⟹ 定数 C·N に吸収
    push_neg at hcase
    rw [hAlogq] at hcase
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
    have hel : estar * (l : ℝ) ≤ emax * (2 * (N : ℝ) * (n₀ : ℝ)) := by
      apply mul_le_mul hele hl2Nn hl0
      linarith
    have hbound : ε * ((vq : ℝ) * logNv)
        < (N : ℝ) * (40 * emax * (n₀ : ℝ) + 20 * ηmax) := by
      have hηN : 20 * ηmax ≤ 20 * (N : ℝ) * ηmax := by nlinarith
      nlinarith [hcase, hel, hetale]
    have hdiv : (vq : ℝ) * logNv
        ≤ (N : ℝ) * (40 * emax * (n₀ : ℝ) + 20 * ηmax) / ε := by
      rw [le_div_iff₀ hε]
      nlinarith [hbound]
    have hDpos : (0 : ℝ) ≤ (1 + ε) * D := by
      apply mul_nonneg _ hD
      linarith
    have hfinal : (1 / 6 - ε) * ((vq : ℝ) * logNv)
        ≤ (40 * emax * (n₀ : ℝ) + 20 * ηmax) / ε * (N : ℝ) := by
      have h16 : (1 / 6 - ε) * ((vq : ℝ) * logNv) ≤ (vq : ℝ) * logNv := by
        nlinarith [hlq_pos.le, hε]
      calc (1 / 6 - ε) * ((vq : ℝ) * logNv)
          ≤ (vq : ℝ) * logNv := h16
        _ ≤ (N : ℝ) * (40 * emax * (n₀ : ℝ) + 20 * ηmax) / ε := hdiv
        _ = (40 * emax * (n₀ : ℝ) + 20 * ηmax) / ε * (N : ℝ) := by ring
    linarith

end IUT.Diophantine
