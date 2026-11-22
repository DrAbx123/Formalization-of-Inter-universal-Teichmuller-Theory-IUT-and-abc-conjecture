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
import tmp.sheaf.takkun.IutLean.Padic.PadicExp
import tmp.sheaf.takkun.IutLean.Padic.LogVolume

/-!
# 殻の輸送 — Phase R3(非分岐テンソルパケット上の Prop 1.2 (ii))

底本: [IUT-IV] Prop 1.2 (ii)(殻の輸送 `φ(p^λ R_I) ⊆ p^{⌈λ−d_I−a_I⌉−b_I} R_I`)の
**非分岐の場合**(全 `e_i = 1`)。このときテンソルパケットは
`R_I = ℤ_p ⊗_{ℤ_p} ⋯ ⊗_{ℤ_p} ℤ_p ≅ ℤ_p` に退化し(Prop 1.1 は `d = 0` で解決済 ――
`NumberTheory/DifferentBound.lean`)、殻の議論は `ℚ_p` の**実際の殻**
`S_λ = {x : ‖x‖ ≤ p^{−λ}}` の上で行える。半径定数は `a = 1`, `b = −1`
(`LogShellRadius.aRadius_one`/`bRadius_one`)ゆえ、整数レベル `λ` では
`⌈λ−d−a⌉−b = λ − 1 + 1 = λ` ―― **輸送は無損失**である。

## 証明済(全て標準公理のみ、実際の `Set ℚ_[p]` の上で)

* `shell p λ`: 実際の殻(`Set ℚ_[p]`)、`shell_subset_iff`(**指数が包含順序を忠実に
  表現する** ―― witness は `p^λ` 自身)、`mul_mem_shell`(積の殻演算);
* **`expQ_mem_shell` / `expQ_shell_surjective` / `expQ_shell_existsUnique`**:
  **全レベル `λ ≥ 1` での exp の殻全単射性** ―― `exp : S_λ ≅ (1 + S_λ)`。
  [IUT-IV] Prop 1.2 (i) の非分岐の場合が**全ての殻の深さで**(両包含+一意性まで)
  成立する。逆写像 = log-link 単数部は各殻を深さを保って写す;
* `unit_mul_shell` / `le_one_mul_shell`: **(Ind2) 型の輸送** ―― 単数スカラーは殻を保存
  (非分岐・整数レベルの Prop 1.2 (ii) は無損失; 一般の分岐の場合の損失
  `⌈λ−d−a⌉−b` は `LogShellRadius` の半径定数が記録する);
* `logVol_shell_gen`: 殻の生成元の正規化対数体積 `= −λ·log p`(体積の線形階層)。

## 残余(honest)

* 分岐テンソルパケット(`e > 1`、`k₁⊗k₂` の étale 分解と different 損失)= Phase R6–R7;
* アルキメデス素点の殻(Prop 1.2 の実素点版)。

次: Phase R4 = この殻語彙で実 `LogKummerCorrespondence` を構成(単数部 = `exp⁻¹`、
値群部 = 付値、上半両立性 = 殻の包含)。
-/

namespace IUT.Padic

variable (p : ℕ) [hp : Fact p.Prime]

/-- ℚ_p の恒等代数射はノルムを延長する(汎用 `expK`/`logOnePlusK` 定理の
`K := ℚ_[p]` インスタンス化に使う)。 -/
lemma normExtends_id : ∀ y : ℚ_[p], ‖algebraMap ℚ_[p] ℚ_[p] y‖ = ‖y‖ := fun y => by
  rw [Algebra.algebraMap_self, RingHom.id_apply]

/-- **実際の殻** `S_λ = {x ∈ ℚ_p : ‖x‖ ≤ p^{−λ}} = p^λ·ℤ_p`(`λ ∈ ℤ`)。
非分岐テンソルパケット `R_I ≅ ℤ_p` の分数イデアル階層。 -/
def shell (lam : ℤ) : Set ℚ_[p] := {x | ‖x‖ ≤ (p : ℝ) ^ (-lam)}

@[simp] lemma mem_shell {lam : ℤ} {x : ℚ_[p]} :
    x ∈ shell p lam ↔ ‖x‖ ≤ (p : ℝ) ^ (-lam) := Iff.rfl

lemma one_lt_pR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt

/-- **殻の包含は指数の順序を忠実に表現する**: `S_λ ⊆ S_μ ↔ μ ≤ λ`
(witness は `p^λ` 自身、ノルムは `Padic.norm_p_zpow` で厳密値)。
指数によるブックキーピングが実際の p 進領域の順序と同型であることの証明 ――
Phase R4 の受信側容器 `D` の実在化の根拠。 -/
theorem shell_subset_iff {lam mu : ℤ} : shell p lam ⊆ shell p mu ↔ mu ≤ lam := by
  have hpR := one_lt_pR p
  constructor
  · intro h
    have hmem : ((p : ℚ_[p])) ^ lam ∈ shell p lam := by
      rw [mem_shell, Padic.norm_p_zpow]
    have h2 := h hmem
    rw [mem_shell, Padic.norm_p_zpow] at h2
    have h3 := (zpow_le_zpow_iff_right₀ hpR).mp h2
    omega
  · intro h x hx
    rw [mem_shell] at hx ⊢
    exact le_trans hx (zpow_le_zpow_right₀ (le_of_lt hpR) (by omega))

/-- 積の殻演算: `S_λ · S_μ ⊆ S_{λ+μ}`(体積の加法性の集合版)。 -/
theorem mul_mem_shell {lam mu : ℤ} {x y : ℚ_[p]}
    (hx : x ∈ shell p lam) (hy : y ∈ shell p mu) : x * y ∈ shell p (lam + mu) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans one_pos (one_lt_pR p)
  rw [mem_shell] at hx hy ⊢
  rw [norm_mul]
  calc ‖x‖ * ‖y‖ ≤ (p : ℝ) ^ (-lam) * (p : ℝ) ^ (-mu) :=
        mul_le_mul hx hy (norm_nonneg y) (zpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (-(lam + mu)) := by rw [← zpow_add₀ hp0.ne', neg_add]

/-- 深い殻は浅い(`λ ≥ 1` なら `S_λ ⊆ S_1`、特に `‖x‖ ≤ p⁻¹`)。 -/
lemma shell_le_one {lam : ℤ} (hlam : 1 ≤ lam) {x : ℚ_[p]} (hx : x ∈ shell p lam) :
    ‖x‖ ≤ (p : ℝ)⁻¹ := by
  have h := (shell_subset_iff p).mpr hlam hx
  rwa [mem_shell, zpow_neg, zpow_one] at h

/-! ## exp の殻全単射性 — Prop 1.2 (i) 非分岐・全レベル -/

/-- **exp は殻を殻へ写す**(深さ保存、`λ ≥ 1`): `x ∈ S_λ ⟹ exp x − 1 ∈ S_λ`。 -/
theorem expQ_mem_shell (hp3 : 3 ≤ p) {lam : ℤ} (hlam : 1 ≤ lam) {x : ℚ_[p]}
    (hx : x ∈ shell p lam) : expK x - 1 ∈ shell p lam := by
  rw [mem_shell]
  rw [norm_expK_sub_one (normExtends_id p) hp3 (shell_le_one p hlam hx)]
  exact hx

/-- **exp は各殻の上で全射**(`λ ≥ 1`): `u − 1 ∈ S_λ` なる任意の `u` は
`u = exp x`(`x ∈ S_λ`)―― ノルム保存が全射性の witness の深さを自動的に整える。 -/
theorem expQ_shell_surjective (hp3 : 3 ≤ p) {lam : ℤ} (hlam : 1 ≤ lam) {u : ℚ_[p]}
    (hu : u - 1 ∈ shell p lam) : ∃ x ∈ shell p lam, expK x = u := by
  have hu1 : ‖u - 1‖ ≤ (p : ℝ)⁻¹ := shell_le_one p hlam hu
  obtain ⟨x, hxs, hxe⟩ := expK_surjective (normExtends_id p) hp3 hu1
  refine ⟨x, ?_, hxe⟩
  rw [mem_shell]
  have hnorm : ‖x‖ = ‖u - 1‖ := by
    rw [← norm_expK_sub_one (normExtends_id p) hp3 hxs, hxe]
  rw [hnorm]
  exact hu

/-- **exp の殻全単射性(Prop 1.2 (i) 非分岐・全レベル、一意性込み)**:
各主単数 `u`(`u − 1 ∈ S_λ`, `λ ≥ 1`)はちょうど一つの `x ∈ S_λ` の exp。
`exp : S_λ ≅ 1 + S_λ` ―― 逆写像(log-link 単数部)は**全ての殻の深さを保つ**。 -/
theorem expQ_shell_existsUnique (hp3 : 3 ≤ p) {lam : ℤ} (hlam : 1 ≤ lam) {u : ℚ_[p]}
    (hu : u - 1 ∈ shell p lam) : ∃! x, x ∈ shell p lam ∧ expK x = u := by
  obtain ⟨x, hxs, hxe⟩ := expQ_shell_surjective p hp3 hlam hu
  refine ⟨x, ⟨hxs, hxe⟩, fun y ⟨hys, hye⟩ => ?_⟩
  exact expK_injective (normExtends_id p) hp3
    (shell_le_one p hlam hys) (shell_le_one p hlam hxs) (by rw [hye, hxe])

/-! ## (Ind2) 型の輸送 — 単数スカラーは殻を保存(非分岐は無損失) -/

/-- 単数スカラー(`‖c‖ = 1`)は各殻を保存する ―― 非分岐・整数レベルの
Prop 1.2 (ii) 輸送は**無損失**(`⌈λ−d−a⌉−b = λ`、`d=0`, `a=1`, `b=−1`)。 -/
theorem unit_mul_shell {c : ℚ_[p]} (hc : ‖c‖ = 1) {lam : ℤ} {x : ℚ_[p]}
    (hx : x ∈ shell p lam) : c * x ∈ shell p lam := by
  rw [mem_shell] at hx ⊢
  rw [norm_mul, hc, one_mul]
  exact hx

/-- 整スカラー(`‖c‖ ≤ 1`)は殻を殻の中へ写す((Ind2) の「into」版)。 -/
theorem le_one_mul_shell {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {lam : ℤ} {x : ℚ_[p]}
    (hx : x ∈ shell p lam) : c * x ∈ shell p lam := by
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans one_pos (one_lt_pR p)
  rw [mem_shell] at hx ⊢
  rw [norm_mul]
  calc ‖c‖ * ‖x‖ ≤ 1 * ((p : ℝ) ^ (-lam)) :=
        mul_le_mul hc hx (norm_nonneg x) one_pos.le
    _ = (p : ℝ) ^ (-lam) := one_mul _

/-! ## 体積 — 殻の生成元の正規化対数体積 -/

/-- **殻の体積の線形階層**: 生成元 `p^λ` の正規化対数体積 `= −λ·log p`
([IUT-IV] Prop 1.4 (i) の正規化と整合、`LogVolume.lean` の `μ_log` の zpow 版)。 -/
theorem logVol_shell_gen (lam : ℤ) :
    logVol ((p : ℚ_[p]) ^ lam) = -(lam : ℝ) * Real.log p := by
  unfold logVol
  rw [Padic.norm_p_zpow, Real.log_zpow]
  push_cast
  ring

end IUT.Padic
