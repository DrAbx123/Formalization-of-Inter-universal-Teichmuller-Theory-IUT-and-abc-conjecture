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
import tmp.sheaf.takkun.IutLean.Padic.PadicLog
import tmp.sheaf.takkun.IutLean.Padic.LogShellRadius
import tmp.sheaf.takkun.IutLean.Arithmetic.CurveInstance

/-!
# 正規化対数体積 — [IUT-IV] Prop 1.4 (i)(ii) の非分岐層と実 q-殻の配線

底本: [IUT-IV] Proposition 1.4 (Nonarchimedean Normalized Log-volume Estimates):

* (i) 正規化対数体積 `μ_log(−)`: `μ_log(R_i) = 0`, `μ_log(p·R_i) = −log(p)`;
* (ii) **対数殻の体積公式** `μ_log(log_p(R_i^×)) = −(1/e_i + m_i/(e_i f_i))·log(p)`
  (`p^{f_i}` = 剰余体位数、`p^{m_i}` = `μ(R_i)` の p-部分の位数)。

## 証明済(全て標準公理のみ)

* `logVol x := log‖x‖` = 主分数イデアル(殻)`x·ℤ_p` の正規化対数体積
  (Haar 測度は乗法で `‖x‖` 倍にスケール ―― `μ_log(x·R) = log‖x‖` は標準実現。
  本モジュールは主殻の上でこれを定義として採用)。正規化 `logVol 1 = 0`,
  `logVol p = −log p` は Prop 1.4 (i) と一致;
* `logVol_mul`/`logVol_pow`: **体積の加法性**(Thm 1.10 の体積和計算の代数核);
* `logVol_logOnePlus`: **対数写像は体積を保存する**(`PadicLog.lean` のノルム保存の
  体積読み ―― 対数殻の log-volume が well-defined であることの内容);
* `logShell_vol_boundary` / `logShell_vol_eq_formula`: 殻境界(`‖x‖ = 1/p`)での
  log-像の体積 = `−aRadius·log p = −(1/e + m/(ef))·log p`(`e = f = 1`, `m = 0`)――
  **Prop 1.4 (ii) の非分岐の場合の体積公式**(`m = 0` ⟺ `p > 2` で `ℚ_p` は
  p-冪根の 1 を含まない);
* `curve11a3_qShell_logVol`: **実配線** ―― 実曲線 11a3 の Tate parameter の殻
  `q·ℤ₁₁ = 11·ℤ₁₁`(`v₁₁(q) = 1` は計算済)の対数体積 = `−log 11 = −logq`
  (`ArithmeticData.logq`)。判定テストの受信側ピン `−qVol` は
  この実 p 進体積の `1/(2l)` 正規化である(`curve11a3_qShell_logVol_qVol`)。

## 残余(honest)

* 一般のコンパクト開集合上の `μ_log`(Haar 測度そのもの)と、`log_p(R^×)` の**集合として
  の**体積(exp = 全射性を要する);
* 分岐 `e > 1`・剰余次数 `f > 1`・`m > 0` の場合(`ℚ_p` の有限拡大の形式化が前提);
* テンソルパケット `(R_E)~` の体積(Prop 1.4 (iii)、Prop 1.1 の different 上界が前提)。
-/

namespace IUT.Padic

open IUT.Arithmetic

variable {p : ℕ} [hp : Fact p.Prime]

/-- **正規化対数体積**: 殻 `x·ℤ_p` の対数体積 `μ_log(x·ℤ_p) = log‖x‖`。
[IUT-IV] Prop 1.4 (i) の正規化(`μ_log(ℤ_p) = 0`, `μ_log(p·ℤ_p) = −log p`)を満たす。 -/
noncomputable def logVol (x : ℚ_[p]) : ℝ := Real.log ‖x‖

/-- 正規化 `μ_log(ℤ_p) = 0`(Prop 1.4 (i))。 -/
@[simp] lemma logVol_one : logVol (1 : ℚ_[p]) = 0 := by
  simp [logVol]

/-- 正規化 `μ_log(p·ℤ_p) = −log p`(Prop 1.4 (i))。 -/
@[simp] lemma logVol_p : logVol ((p : ℚ_[p])) = -Real.log p := by
  unfold logVol
  rw [Padic.norm_p, Real.log_inv]

/-- **体積の加法性**: `μ_log(xy·ℤ_p) = μ_log(x·ℤ_p) + μ_log(y·ℤ_p)`。
Thm 1.10 の体積和計算(次数の加法性 `totalDegree_mul` の解析版)。 -/
theorem logVol_mul {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    logVol (x * y) = logVol x + logVol y := by
  unfold logVol
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]

/-- 巾の体積: `μ_log(xⁿ·ℤ_p) = n·μ_log(x·ℤ_p)`(テータ値 `q^{j²}` の体積計算の形)。 -/
theorem logVol_pow (x : ℚ_[p]) (n : ℕ) : logVol (x ^ n) = n * logVol x := by
  unfold logVol
  rw [norm_pow, Real.log_pow]

/-- 殻 `pⁿℤ_p` の体積 `= −n·log p`。 -/
theorem logVol_p_pow (n : ℕ) : logVol ((p : ℚ_[p]) ^ n) = -(n : ℝ) * Real.log p := by
  rw [logVol_pow, logVol_p]
  ring

/-- 体積の単調性(殻の包含 ⟹ 体積の順序)。 -/
theorem logVol_mono {x y : ℚ_[p]} (hx : x ≠ 0) (h : ‖x‖ ≤ ‖y‖) : logVol x ≤ logVol y :=
  Real.log_le_log (norm_pos_iff.mpr hx) h

/-- **対数写像は体積を保存する**([IUT-IV] Prop 1.2/1.4 の核、`p > 2`・`‖x‖ ≤ 1/p`):
`μ_log(log(1+x)·ℤ_p) = μ_log(x·ℤ_p)`。`PadicLog.lean` のノルム保存の体積読み。 -/
theorem logVol_logOnePlus (hp2 : p ≠ 2) {x : ℚ_[p]} (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
    logVol (logOnePlus x) = logVol x := by
  unfold logVol
  rw [norm_logOnePlus hp2 hx]

/-- **対数殻の境界体積 = 半径定数**: 殻境界の主単数 `1+x`(`‖x‖ = 1/p`)の log-像は
体積 `−aRadius·log p` の殻を生成する ―― `LogShellRadius.lean` の半径定数
`aRadius p 1 = 1` が実現する体積。 -/
theorem logShell_vol_boundary (hp2 : p ≠ 2) {x : ℚ_[p]} (hx : ‖x‖ = (p : ℝ)⁻¹) :
    logVol (logOnePlus x) = -(aRadius p 1) * Real.log p := by
  have hp3 : 2 < p := by
    have := hp.out.two_le
    omega
  rw [aRadius_one hp3, logVol_logOnePlus hp2 (le_of_eq hx)]
  unfold logVol
  rw [hx, Real.log_inv]
  ring

/-- [IUT-IV] Prop 1.4 (ii) の体積公式値 `−(1/e + m/(e·f))·log p`。 -/
noncomputable def logShellVolFormula (p e f m : ℕ) : ℝ :=
  -((1 / (e : ℝ)) + (m : ℝ) / ((e : ℝ) * (f : ℝ))) * Real.log p

omit hp in
/-- 非分岐(`e = f = 1`, `m = 0`)での公式値 `= −log p`。 -/
theorem logShellVolFormula_unramified :
    logShellVolFormula p 1 1 0 = -Real.log p := by
  unfold logShellVolFormula
  norm_num

/-- **Prop 1.4 (ii) の非分岐の場合**: 殻境界での log-像の体積は体積公式
`−(1/e + m/(e·f))·log p`(`e = f = 1`, `m = 0`)に一致する。`m = 0` は `p > 2` で
`ℚ_p` が p-冪根の 1 を含まないことに対応(`PadicLog.lean` の `p = 2` 破綻と同源)。
集合 `log(ℤ_p^×)` そのものの体積との同定は exp(全射性)を要する(残余)。 -/
theorem logShell_vol_eq_formula (hp2 : p ≠ 2) {x : ℚ_[p]} (hx : ‖x‖ = (p : ℝ)⁻¹) :
    logVol (logOnePlus x) = logShellVolFormula p 1 1 0 := by
  rw [logShellVolFormula_unramified, logShell_vol_boundary hp2 hx]
  have hp3 : 2 < p := by
    have := hp.out.two_le
    omega
  rw [aRadius_one hp3]
  ring

/-! ## 実配線 — 曲線 11a3 の Tate parameter の殻の体積 -/

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- **実配線(11a3)**: 実曲線 11a3 の素点 11 での Tate parameter は `v₁₁(q) = 1`
(`Δ = −11` の計算済)ゆえ、その殻は `11·ℤ₁₁` ―― その正規化対数体積は
`−log 11 = −logq`(判定テストの `ArithmeticData.logq`)。
**判定テストの体積データが実際の p 進体積として実現された。** -/
theorem curve11a3_qShell_logVol (eta D : ℝ) (heta : 0 ≤ eta) (hD : 0 ≤ D) :
    logVol (((11 : ℕ) : ℚ_[11])) = -(curve11a3Data eta D heta hD).logq := by
  have hq : (curve11a3Data eta D heta hD).logq = Real.log 11 := by
    unfold ArithmeticData.logq curve11a3Data
    norm_num
  rw [hq, logVol_p (p := 11)]
  norm_num

/-- **実配線(受信側ピン)**: 11a3 の q-殻の体積は判定テストの受信側単位 `−qVol` の
`2l = 14` 倍 ―― `Thm311Transcription.q_vol`(受信側ピン `volR(q標) = −qVol`)の
プロセッション正規化 `1/(2l)` を外した生の p 進体積が `logVol(11·ℤ₁₁)` である。 -/
theorem curve11a3_qShell_logVol_qVol (eta D : ℝ) (heta : 0 ≤ eta) (hD : 0 ≤ D) :
    logVol (((11 : ℕ) : ℚ_[11]))
      = -(2 * 7 : ℝ) * (curve11a3Data eta D heta hD).qVol := by
  rw [curve11a3_qShell_logVol eta D heta hD]
  have hq : (curve11a3Data eta D heta hD).qVol
      = (curve11a3Data eta D heta hD).logq / (2 * 7 : ℝ) := by
    unfold ArithmeticData.qVol
    have hl : ((curve11a3Data eta D heta hD).l : ℝ) = 7 := by
      unfold curve11a3Data
      norm_num
    rw [hl]
  rw [hq]
  ring

end IUT.Padic
