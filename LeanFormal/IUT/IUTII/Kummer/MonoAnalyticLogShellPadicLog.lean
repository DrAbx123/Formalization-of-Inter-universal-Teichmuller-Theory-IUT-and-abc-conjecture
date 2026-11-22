/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.MonoAnalyticLogShellCompactCarrier
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.MaxPowDiv

/-!
# IUT-II mono-analytic log-shell：p 进 log 级数数据源（candidate A pass，L1+L2 部分）

对位 `logs/coordination/monoanalytic-logshell-exploration-20261016.md` §8.6 缺件卡 M-1
（Mathlib 无 p 进 log）。本文件在 Mathlib v4.32.2 上建立：

* L1（形式层复用；已证）：`PowerSeries.log` 系数公式桥 `padicFormalLog_coeff`、
  导数实例化（`PowerSeries.derivative (log ℚ_[p])`，`padicFormalLog_derivative`）、
  `HasSubst`（`padicFormalLog_hasSubst`）、`exp_mul_exp_eq_exp_add` 实例化
  （`padicFormalExp_rescale_add`）。如实：Mathlib **无**形式乘性
  （`PowerSeries.logOf_mul` 0 命中；`log_mul` 仅见于实/复分析）——L3 卡（报告 §9）。
* L2a（收敛；已证）：项 `padicLogTerm`、级数 `padicLogSeries`；分母范数估计
  `padicLog_denom_norm_inv_le`（`pow_padicValNat_dvd` + `Padic.norm_eq_zpow_neg_valuation`）；
  优函数 `padicLogMajorant` 可和（`padicLogMajorant_summable`）；`Summable`/`HasSum`
  （`padicLogSeries_summable`/`padicLogSeries_hasSum`，条件 `‖x‖ < 1`）。
* L2b（连续；已证）：`padicLogSeries_continuousOn_closedBall`（`r < 1` 闭球，经
  `continuousOn_tsum` 一致优界）、`padicLogSeries_continuousOn_ball`（开单位球）、
  `padicLogSeries_continuousAt_of_norm_lt_one`。
* L2c（乘性 `log(1+a)+log(1+b)=log(1+a+b+ab)`；**未证，park**）：三路线受阻（形式乘性
  缺失；p 进幂级数逐项微分/链式法则缺失；截断多项式+组合恒等未形式化）。因此本文件
  **不升级** `MonoAnalyticLogShellCompactCarrier` 的 ℤ_[p] 校准：`logMap` 仍为合同参数
  （非平凡 logMap 需要 L2c）。精确缺件卡与失败点见报告 §9。

未接入任何生产 import 图；未修改任何他人文件。
-/

namespace LeanFormal.IUT

namespace MonoAnalyticLogShellPadicLog

open scoped Topology

/-! ## 1. 形式层（L1）：`PowerSeries.log/exp` 的实例化复用 -/

section FormalLayer

variable (p : ℕ) [Fact p.Prime]

/-- L1 桥：`PowerSeries.log` 的第 `k` 个系数与解析级数第 `k` 个系数一致（`k = 0` 记 0）。 -/
theorem padicFormalLog_coeff (k : ℕ) :
    (PowerSeries.log ℚ_[p]).coeff k =
      if k = 0 then 0 else ((-1 : ℚ_[p]) ^ (k + 1)) / (k : ℚ_[p]) := by
  rw [PowerSeries.coeff_log]
  split_ifs with hk
  · rfl
  · rw [map_div₀, map_pow, map_neg, map_one, map_natCast]

/-- L1 复用：形式上 `d/dX log(1+X) = ∑ (-1)^n X^n`（`PowerSeries.deriv_log` 实例化）。 -/
theorem padicFormalLog_derivative :
    PowerSeries.derivative ℚ_[p] (PowerSeries.log ℚ_[p]) =
      PowerSeries.mk (fun n : ℕ => (-1 : ℚ_[p]) ^ n) := by
  simpa using PowerSeries.deriv_log (A := ℚ_[p])

/-- L1 复用：形式 `log(1+X)` 可代换（`HasSubst`）。 -/
theorem padicFormalLog_hasSubst : PowerSeries.HasSubst (PowerSeries.log ℚ_[p]) :=
  PowerSeries.HasSubst.log

/-- L1 复用：形式 exp 加法性（`PowerSeries.exp_mul_exp_eq_exp_add` 实例化）。 -/
theorem padicFormalExp_rescale_add (a b : ℚ_[p]) :
    PowerSeries.rescale a (PowerSeries.exp ℚ_[p]) *
        PowerSeries.rescale b (PowerSeries.exp ℚ_[p]) =
      PowerSeries.rescale (a + b) (PowerSeries.exp ℚ_[p]) :=
  PowerSeries.exp_mul_exp_eq_exp_add a b

end FormalLayer

/-! ## 2. 分析层（L2a/L2b）：log 级数的收敛与连续 -/

section AnalyticLayer

variable (p : ℕ) [Fact p.Prime]

/-- log 级数项：`(-1)^(n+1) x^(n+1) / (n+1)`（对应 `log(1+x)` 的 `x^(n+1)` 项）。 -/
noncomputable def padicLogTerm (x : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  ((-1 : ℚ_[p]) ^ (n + 1) * x ^ (n + 1)) / (n + 1 : ℚ_[p])

/-- log 级数（逐点 tsum；`‖x‖ < 1` 时收敛，见 `padicLogSeries_summable`）。 -/
noncomputable def padicLogSeries (x : ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, padicLogTerm p x n

/-- 分母范数估计：`k ≠ 0` 时 `‖(k : ℚ_[p])‖⁻¹ = p^{v_p(k)} ≤ k`。
（`pow_padicValNat_dvd` 给整除，`Padic.norm_eq_zpow_neg_valuation` 给范数。） -/
theorem padicLog_denom_norm_inv_le {k : ℕ} (hk : k ≠ 0) :
    ‖(k : ℚ_[p])‖⁻¹ ≤ (k : ℝ) := by
  have hne : (k : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hk
  have hnorm : ‖(k : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p k : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
  have hpv : (p : ℝ) ^ (padicValNat p k) ≤ (k : ℝ) := by
    have hdiv : p ^ padicValNat p k ∣ k := pow_padicValNat_dvd
    have hle : p ^ padicValNat p k ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdiv
    exact_mod_cast hle
  rw [hnorm, (inv_zpow (p : ℝ) (-(padicValNat p k : ℤ))).symm, inv_zpow', neg_neg,
    zpow_natCast]
  exact hpv

/-- 优函数：`u n = (n+1) r^{n+1}`。 -/
noncomputable def padicLogMajorant (r : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * r ^ (n + 1)

/-- 优函数可和（`0 ≤ r < 1`）：几何级数 × 线性因子的标准可和性。 -/
theorem padicLogMajorant_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (padicLogMajorant r) := by
  have hnorm : ‖r‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hgeo : Summable fun n : ℕ => r ^ n := summable_geometric_of_norm_lt_one hnorm
  have hpoly : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r) hnorm
  have hmain : Summable fun n : ℕ => r * ((n : ℝ) * r ^ n + r ^ n) :=
    (hpoly.add hgeo).mul_left r
  refine hmain.congr fun n => ?_
  simp only [padicLogMajorant, pow_succ]
  ring

/-- 项范数上界：`‖x‖ ≤ r` 时 `‖padicLogTerm x n‖ ≤ (n+1) r^{n+1}`。 -/
theorem padicLogTerm_norm_le (x : ℚ_[p]) {r : ℝ} (hr0 : 0 ≤ r) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖padicLogTerm p x n‖ ≤ padicLogMajorant r n := by
  have hden : ‖((n + 1 : ℕ) : ℚ_[p])‖⁻¹ ≤ ((n : ℝ) + 1) := by
    have := padicLog_denom_norm_inv_le (p := p) (k := n + 1) (Nat.succ_ne_zero n)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hterm : ‖padicLogTerm p x n‖ =
      ‖x‖ ^ (n + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖⁻¹ := by
    rw [padicLogTerm, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one,
      div_eq_mul_inv]
    norm_num
  calc ‖padicLogTerm p x n‖
      = ‖x‖ ^ (n + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖⁻¹ := hterm
    _ ≤ r ^ (n + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖⁻¹ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx (n + 1))
          (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ r ^ (n + 1) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hden (pow_nonneg hr0 _)
    _ = padicLogMajorant r n := by
        simp [padicLogMajorant, mul_comm]

/-- 收敛：`‖x‖ < 1` 时 log 级数可和（由优函数 + `Summable.of_norm_bounded`）。 -/
theorem padicLogSeries_summable (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    Summable (padicLogTerm p x) :=
  Summable.of_norm_bounded (padicLogMajorant_summable (norm_nonneg x) hx)
    fun n => padicLogTerm_norm_le p x (norm_nonneg x) le_rfl n

/-- HasSum 形式（四件套验收点：收敛以 `HasSum` 记录）。 -/
theorem padicLogSeries_hasSum (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    HasSum (padicLogTerm p x) (padicLogSeries p x) :=
  (padicLogSeries_summable p x hx).hasSum

/-- `log(1+0) = 0`（级数在 0 处取值 0）。 -/
theorem padicLogSeries_zero : padicLogSeries p (0 : ℚ_[p]) = 0 := by
  have h : (fun n : ℕ => padicLogTerm p (0 : ℚ_[p]) n) = fun _ => 0 := by
    funext n
    simp [padicLogTerm]
  simp [padicLogSeries, h]

/-- 连续（闭球 `‖x‖ ≤ r`，`r < 1`）：一致优界 + `continuousOn_tsum`。 -/
theorem padicLogSeries_continuousOn_closedBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (padicLogSeries p) (Metric.closedBall (0 : ℚ_[p]) r) := by
  change ContinuousOn (fun x => ∑' n, padicLogTerm p x n) (Metric.closedBall (0 : ℚ_[p]) r)
  refine continuousOn_tsum (f := fun n (x : ℚ_[p]) => padicLogTerm p x n)
    (u := padicLogMajorant r) (s := Metric.closedBall (0 : ℚ_[p]) r) ?_ ?_ ?_
  · intro n
    have hc : Continuous fun x : ℚ_[p] =>
        ((-1 : ℚ_[p]) ^ (n + 1) * x ^ (n + 1)) / (n + 1 : ℚ_[p]) := by
      fun_prop
    exact hc.continuousOn
  · exact padicLogMajorant_summable hr0 hr1
  · intro n x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact padicLogTerm_norm_le p x hr0 hx n

/-- 连续（开单位球）：逐点用闭球版本局部化（`continuousOn_of_locally_continuousOn`）。 -/
theorem padicLogSeries_continuousOn_ball :
    ContinuousOn (padicLogSeries p) (Metric.ball (0 : ℚ_[p]) 1) := by
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  rw [Metric.mem_ball, dist_zero_right] at hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  refine ⟨Metric.ball (0 : ℚ_[p]) r, Metric.isOpen_ball, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    exact hxr
  · refine (padicLogSeries_continuousOn_closedBall p
      (le_of_lt (lt_of_le_of_lt (norm_nonneg x) hxr)) hr1).mono ?_
    intro y hy
    have hy2 : y ∈ Metric.ball (0 : ℚ_[p]) r := hy.2
    rw [Metric.mem_ball, dist_zero_right] at hy2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hy2

/-- 逐点连续（`‖x‖ < 1`）。 -/
theorem padicLogSeries_continuousAt_of_norm_lt_one (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    ContinuousAt (padicLogSeries p) x := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 ≤ r := le_of_lt (lt_of_le_of_lt (norm_nonneg x) hxr)
  have hcont := padicLogSeries_continuousOn_closedBall p hr0 hr1
  have hmem : Metric.closedBall (0 : ℚ_[p]) r ∈ 𝓝 x := by
    have hball : Metric.ball (0 : ℚ_[p]) r ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (by
        rw [Metric.mem_ball, dist_zero_right]
        exact hxr)
    refine Filter.mem_of_superset hball ?_
    · intro y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hy
  exact (hcont.continuousWithinAt
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hxr)).continuousAt hmem

end AnalyticLayer

end MonoAnalyticLogShellPadicLog

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：p 进 log 级数数据源（候选 A 第一段：L1 形式复用 + L2a/L2b 收敛/连续；
L2c 乘性 park，不升级校准）。 -/
def monoAnalyticLogShellPadicLogSeries : Obligation :=
  { id := "IUT-II.mono-analytic-log-shell-padic-log-series"
    source := "IUT III, Definition 1.1, (i) (text l.1330-1351); Introduction l.208-226; " ++
      "IUT III, Proposition 1.2, (vi) (l.5740-5785)"
    status := VerificationStatus.conditional
    note :=
      "p-adic log series data source, first segment (candidate A). Proved: formal-layer " ++
        "reuse bridges for PowerSeries.log (coeff formula, derivative, HasSubst, exp " ++
        "additivity instantiation); denominator norm estimate via pow_padicValNat_dvd and " ++
        "Padic.norm_eq_zpow_neg_valuation; geometric majorant summability; Summable/HasSum " ++
        "of the log series for norm < 1; continuity on closed balls (r < 1), on the open " ++
        "unit ball, and pointwise. Not proved (parked): the multiplicativity identity " ++
        "log(1+a) + log(1+b) = log(1+a+b+ab), blocked on the absence of formal log-" ++
        "multiplicativity (no PowerSeries.logOf_mul in Mathlib; log_mul only for " ++
        "real/complex log lemmas), of p-adic termwise " ++
        "differentiation, and of a formalization of the truncated-polynomial route. " ++
        "Consequently the Z_p calibration in MonoAnalyticLogShellCompactCarrier is NOT " ++
        "upgraded (its logMap remains a contract parameter). Not delivered: the " ++
        "multiplicativity passage, hence no nontrivial p-adic log homomorphism yet. " ++
        "See coordination report monoanalytic-logshell-exploration-20261016 section 9."
    dependsOn := [ "IUT-II.mono-analytic-log-shell-compact-carrier" ] }

end LeanFormal.IUT.Audit
