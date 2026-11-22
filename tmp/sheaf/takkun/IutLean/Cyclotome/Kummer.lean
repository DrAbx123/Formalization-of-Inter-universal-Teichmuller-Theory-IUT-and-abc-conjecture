import Mathlib
import tmp.sheaf.takkun.IutLean.Cyclotome.Frobenius

/-!
# Kummer 類 — theta/Kummer 両立性の実機構(最終脱ブラックボックス化の核)

底本: [IUT-II] §3(Galois 的テータ評価)、[IUT-II] Cor 4.6/4.8(Kummer 同型)、
[IUT-III] Prop 3.5 / Thm 3.11 (ii)(log-Kummer 対応)。

IUT の Kummer 理論は「Frobenius 的対象(モノイド `M` の元、テータ値・q-parameter)」を
「エタール的対象(Galois 群 `G` の円分物 `Λ(M)` 係数コホモロジー類)」へ結ぶ:
元 `m ∈ M` の**両立的巾根系** `{m^{1/n}}_n` を選ぶと、`G` の各元 `σ` に対し
`σ(m^{1/n})/m^{1/n} ∈ μ_n(M)` の族が円分物 `Λ(M) = lim μ_n` の元を定め(`kummerClass`)、
これは **1-コサイクル**(交差準同型、`kummerClass_mul`)であり、巾根系の取り替えで
**1-コバウンダリしか動かない**(`kummerClass_diff` ―― `H¹(G, Λ(M))` の類が well-defined)。

## 証明済(全て標準公理のみ)

* `RootSystem m`: 両立的巾根系(`root 1 = m`, `(root(nk))^k = root n`);
* `kummerClass`: `G`-不変元 `m` の巾根系が定める写像 `G → Λ(M)`;
* **`kummerClass_mul`(コサイクル律)**: `c(στ) = σ·c(τ) · c(σ)`(`σ·` は円分指標
  `cyclotomicAut` による作用)―― Kummer 類が `Λ(M)`-係数 1-コサイクルであること;
* **`kummerClass_diff`(well-definedness)**: 巾根系の差は `Λ(M)` の元 `δ` を定め
  (`rootSystemDiff`)、Kummer 類は `σ·δ/δ`(1-コバウンダリ)しか変わらない;
* `RootSystem.pow`: `m` の巾根系から `m^e` の巾根系(**テータ値 `q^{j²}` の Kummer 類は
  q-parameter の巾根系から一斉に得られる**);
* `rootSystemOfAlgClosed`: **代数閉体では全ての単元が巾根系を持つ**(階乗鎖
  `m^{1/k!}` を逐次選択 ―― `ℚ̄_p` = 実 Hodge 劇場の `Mon` に適用可能);
* `frobeniusCyclotome_nontrivial`: `Λ(ℂ)` の**非自明性**の明示的 witness
  `(e^{2πi/n})_n`(`Cyclotome/Frobenius.lean` の 2026-07-06 退化修正の検証)。

## 残余(honest)

* Kummer **同型**の全体(コサイクルから `H¹` 類への昇格と、その単射性/全射性 ――
  Hilbert 90 と円分剛性同型 `Λ(M) ≅ Λ(G)` を要する);
* log-Kummer 対応の「1 の巾根は log で 0 に行く=不定性なし」条項([IUT-III]
  Thm 3.11 (ii))の本モジュールの類との配線;
* 実 Galois 群での Kummer 類の非自明性(`ℚ_p(p^{1/n})/ℚ_p` の分岐理論)。

実 Hodge 劇場(`ℚ̄_p`、実 Galois 作用、実 q-parameter)へのインスタンス化は
`Arithmetic/RealKummer.lean`。
-/

namespace IUT.Cyclotome

/-! ## 両立的巾根系 -/

variable {M : Type*} [CommGroup M]

/-- **両立的巾根系**: `m ∈ M` の全ての `n` 乗根の整合的な選択
(`root n = m^{1/n}`、`(root(n·k))^k = root n`)。Kummer 類の生成データ。 -/
structure RootSystem (m : M) where
  /-- `n` 乗根の選択(`root 0` は自明値でよい)。 -/
  root : ℕ → M
  /-- 正規化: `root 1 = m`。 -/
  root_one : root 1 = m
  /-- 両立性: `(root (n·k))^k = root n`(`k ≠ 0`)。 -/
  compat : ∀ n k : ℕ, k ≠ 0 → root (n * k) ^ k = root n

namespace RootSystem

variable {m : M} (r : RootSystem m)

/-- 巾根系の根は実際に根: `(root n)^n = m`(`n ≠ 0`)。 -/
theorem pow_self (n : ℕ) (hn : n ≠ 0) : r.root n ^ n = m := by
  have h := r.compat 1 n hn
  rwa [Nat.one_mul, r.root_one] at h

/-- **巾の巾根系**: `m` の巾根系から `m^e` の巾根系(`root n := (root n)^e`)。
テータ値 `q^{j²}` の Kummer 類が q-parameter の一つの巾根系から一斉に得られる仕組み。 -/
def pow (e : ℕ) : RootSystem (m ^ e) where
  root n := r.root n ^ e
  root_one := by rw [r.root_one]
  compat n k hk := by
    rw [pow_right_comm, r.compat n k hk]

end RootSystem

/-! ## Kummer 類: 巾根系が定める円分物値コサイクル -/

section KummerClass

variable {G : Type*} [Group G] (ρ : G →* MulAut M)
variable {m : M} (r : RootSystem m)

/-- 固定元の巾は固定される(テータ値 `q^{j²}` の `G`-不変性の供給源)。 -/
theorem fixes_pow (hfix : ∀ σ : G, ρ σ m = m) (e : ℕ) (σ : G) :
    ρ σ (m ^ e) = m ^ e := by
  rw [map_pow, hfix]

/-- **Kummer 類**(コサイクルレベル): `G`-不変元 `m` の巾根系 `r` に対し、
`σ ↦ (σ(m^{1/n})/m^{1/n})_n ∈ Λ(M)`。Frobenius 的対象(モノイドの元)から
エタール的対象(円分物値の Galois データ)への橋 ―― Kummer 理論の核。 -/
noncomputable def kummerClass (hfix : ∀ σ : G, ρ σ m = m) (σ : G) :
    FrobeniusCyclotome M :=
  ⟨fun n => ⟨toUnits (ρ σ (r.root n) / r.root n), by
    rw [mem_rootsOfUnity, ← map_pow]
    have hy : (ρ σ (r.root n) / r.root n) ^ n = 1 := by
      rcases eq_or_ne n 0 with rfl | hn
      · exact pow_zero _
      · rw [div_pow, ← map_pow, r.pow_self n hn, hfix σ, div_self']
    rw [hy, map_one]⟩,
   by
    intro n k hk
    apply Subtype.ext
    apply Units.ext
    change (ρ σ (r.root (n * k)) / r.root (n * k)) ^ k = ρ σ (r.root n) / r.root n
    rw [div_pow, ← map_pow, r.compat n k hk]⟩

@[simp] theorem kummerClass_coe (hfix : ∀ σ : G, ρ σ m = m) (σ : G) (n : ℕ) :
    (((kummerClass ρ r hfix σ).1 n : Mˣ) : M) = ρ σ (r.root n) / r.root n := rfl

/-- **コサイクル律**(交差準同型): `c(στ) = σ·c(τ) · c(σ)`(`σ·` は円分指標
`cyclotomicAut` による `Λ(M)` への作用)。Kummer 類が Galois コホモロジーの
1-コサイクルであること ―― [IUT-II] の Kummer 理論が「Galois 作用と両立する」ことの
群論的内容そのもの。 -/
theorem kummerClass_mul (hfix : ∀ σ : G, ρ σ m = m) (σ τ : G) :
    kummerClass ρ r hfix (σ * τ)
      = cyclotomicAut M (ρ σ) (kummerClass ρ r hfix τ) * kummerClass ρ r hfix σ := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  apply Units.ext
  change ρ (σ * τ) (r.root n) / r.root n
      = ρ σ (ρ τ (r.root n) / r.root n) * (ρ σ (r.root n) / r.root n)
  rw [map_mul ρ σ τ, MulAut.mul_apply, map_div]
  exact (div_mul_div_cancel _ _ _).symm

@[simp] theorem kummerClass_one (hfix : ∀ σ : G, ρ σ m = m) :
    kummerClass ρ r hfix 1 = 1 := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  apply Units.ext
  change ρ 1 (r.root n) / r.root n = 1
  rw [map_one]
  change r.root n / r.root n = 1
  exact div_self' _

/-! ## Well-definedness: 巾根系の取り替えは 1-コバウンダリ -/

/-- **巾根系の差**: 同じ `m` の 2 つの巾根系の比 `(r'ₙ/rₙ)_n` は円分物 `Λ(M)` の元
(各比は `μ_n` に属し遷移両立)。 -/
noncomputable def rootSystemDiff (r r' : RootSystem m) : FrobeniusCyclotome M :=
  ⟨fun n => ⟨toUnits (r'.root n / r.root n), by
    rw [mem_rootsOfUnity, ← map_pow]
    have hy : (r'.root n / r.root n) ^ n = 1 := by
      rcases eq_or_ne n 0 with rfl | hn
      · exact pow_zero _
      · rw [div_pow, r.pow_self n hn, r'.pow_self n hn, div_self']
    rw [hy, map_one]⟩,
   by
    intro n k hk
    apply Subtype.ext
    apply Units.ext
    change (r'.root (n * k) / r.root (n * k)) ^ k = r'.root n / r.root n
    rw [div_pow, r.compat n k hk, r'.compat n k hk]⟩

/-- **Kummer 類の well-definedness**(1-コバウンダリ関係、乗法形): 巾根系を `r` から
`r'` に取り替えると、Kummer 類は差 `δ = rootSystemDiff r r'` の 1-コバウンダリ
(`c'(σ)·δ = c(σ)·(σ·δ)`)しか変わらない。すなわち `H¹(G, Λ(M))` の類は巾根系の
選択に依らない ―― Kummer 理論の正準性。 -/
theorem kummerClass_diff (hfix : ∀ σ : G, ρ σ m = m) (r r' : RootSystem m) (σ : G) :
    kummerClass ρ r' hfix σ * rootSystemDiff r r'
      = kummerClass ρ r hfix σ * cyclotomicAut M (ρ σ) (rootSystemDiff r r') := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  apply Units.ext
  change ρ σ (r'.root n) / r'.root n * (r'.root n / r.root n)
      = ρ σ (r.root n) / r.root n * ρ σ (r'.root n / r.root n)
  rw [map_div, div_mul_div_cancel, div_mul_div_cancel']

end KummerClass

/-! ## 代数閉体上の存在: 階乗鎖による巾根系の構成 -/

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- 代数閉体の単元は任意の `n ≠ 0` 乗根(単元)を持つ。 -/
theorem exists_pow_root (u : Kˣ) (n : ℕ) (hn : n ≠ 0) : ∃ v : Kˣ, v ^ n = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hz
    exact (Units.ne_zero u) hz.symm
  exact ⟨Units.mk0 z hz0, by apply Units.ext; rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]⟩

/-- **階乗鎖** `chainRoot m k = m^{1/k!}`: 各段で `k+1` 乗根を逐次選択。 -/
noncomputable def chainRoot (m : Kˣ) : ℕ → Kˣ
  | 0 => m
  | (k + 1) => (exists_pow_root (chainRoot m k) (k + 1) (Nat.succ_ne_zero k)).choose

theorem chainRoot_spec (m : Kˣ) (k : ℕ) :
    chainRoot m (k + 1) ^ (k + 1) = chainRoot m k :=
  (exists_pow_root (chainRoot m k) (k + 1) (Nat.succ_ne_zero k)).choose_spec

/-- 階乗鎖の望遠鏡則: `j ≤ i` なら `(chainRoot m i)^{i!/j!} = chainRoot m j`。 -/
theorem chainRoot_telescope (m : Kˣ) {j i : ℕ} (hji : j ≤ i) :
    chainRoot m i ^ (i.factorial / j.factorial) = chainRoot m j := by
  induction i, hji using Nat.le_induction with
  | base => rw [Nat.div_self j.factorial_pos, pow_one]
  | succ i hji ih =>
    have hdvd : j.factorial ∣ i.factorial := Nat.factorial_dvd_factorial hji
    have hexp : (i + 1).factorial / j.factorial = (i + 1) * (i.factorial / j.factorial) := by
      rw [Nat.factorial_succ, Nat.mul_div_assoc _ hdvd]
    rw [hexp, pow_mul, chainRoot_spec, ih]

/-- **代数閉体上の巾根系の存在**(構成的): `root n := (chainRoot m n)^{n!/n}`。
`ℚ̄_p`(実 Hodge 劇場の `Mon`)の任意の元 ―― 特に実 q-parameter とテータ値 ――
が両立的巾根系を持ち、Kummer 類が構成できる。 -/
noncomputable def rootSystemOfAlgClosed (m : Kˣ) : RootSystem m where
  root n := if n = 0 then 1 else chainRoot m n ^ (n.factorial / n)
  root_one := by
    rw [if_neg one_ne_zero, Nat.factorial_one, Nat.div_one, pow_one]
    have h := chainRoot_spec m 0
    rwa [pow_one] at h
  compat n k hk := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.zero_mul, if_pos rfl, one_pow]
    · have hnk : n * k ≠ 0 := Nat.mul_ne_zero hn hk
      rw [if_neg hnk, if_neg hn]
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hk0 : 0 < k := Nat.pos_of_ne_zero hk
      have hnk0 : 0 < n * k := Nat.mul_pos hn0 hk0
      have hle : n ≤ n * k := Nat.le_mul_of_pos_right n hk0
      -- 指数の恒等式 (両辺に n を掛けて検証)
      have hd1 : (n * k) ∣ (n * k).factorial := Nat.dvd_factorial hnk0 le_rfl
      have hd2 : n ∣ (n * k).factorial :=
        dvd_trans (Dvd.intro k rfl) hd1
      have hd3 : n ∣ n.factorial := Nat.dvd_factorial hn0 le_rfl
      have hd4 : n.factorial ∣ (n * k).factorial := Nat.factorial_dvd_factorial hle
      have hexp1 : (n * k).factorial / (n * k) * k = (n * k).factorial / n := by
        apply Nat.eq_of_mul_eq_mul_right hn0
        rw [Nat.div_mul_cancel hd2, mul_assoc, mul_comm k n, Nat.div_mul_cancel hd1]
      have hexp2 : (n * k).factorial / n.factorial * (n.factorial / n)
          = (n * k).factorial / n := by
        apply Nat.eq_of_mul_eq_mul_right hn0
        rw [Nat.div_mul_cancel hd2, mul_assoc, Nat.div_mul_cancel hd3,
          Nat.div_mul_cancel hd4]
      rw [← pow_mul, hexp1, ← hexp2, pow_mul, chainRoot_telescope m hle]

end AlgClosed

/-! ## 非自明性の検証: `Λ(ℂ)` の明示的 witness `(e^{2πi/n})_n` -/

section Nontrivial

/-- `Λ(ℂ)` の明示的な元 `(e^{2πi/n})_n`(両立性は `(e^{2πi/nk})^k = e^{2πi/n}`)。 -/
noncomputable def complexWitness : FrobeniusCyclotome ℂ :=
  ⟨fun n => ⟨Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n))
      (Complex.exp_ne_zero _), by
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rcases eq_or_ne n 0 with rfl | hn
    · exact pow_zero _
    · rw [← Complex.exp_nat_mul]
      have harg : (n : ℂ) * (2 * Real.pi * Complex.I / n) = 2 * Real.pi * Complex.I := by
        have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        field_simp
      rw [harg, Complex.exp_two_pi_mul_I]⟩,
   by
    intro n k hk
    apply Subtype.ext
    apply Units.ext
    rw [rouTransition_coe, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]
    rw [← Complex.exp_nat_mul]
    congr 1
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      push_cast
      field_simp⟩

/-- **`Λ(ℂ)` は非自明**: witness の第 2 成分は `e^{πi} = −1 ≠ 1`。
(`FrobeniusCyclotome` の 2026-07-06 退化修正(`m ≠ 0` ガード)が、円分物を
自明化させずに正しい逆極限を与えていることの検証。) -/
theorem frobeniusCyclotome_nontrivial : ∃ f : FrobeniusCyclotome ℂ, f ≠ 1 := by
  refine ⟨complexWitness, fun h => ?_⟩
  have h2 := congrArg (fun f : FrobeniusCyclotome ℂ => ((f.1 2 : ℂˣ) : ℂ)) h
  simp only [complexWitness, Units.val_mk0, OneMemClass.coe_one] at h2
  have harg : 2 * (Real.pi : ℂ) * Complex.I / ((2 : ℕ) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_pi_mul_I] at h2
  norm_num at h2

end Nontrivial

end IUT.Cyclotome
