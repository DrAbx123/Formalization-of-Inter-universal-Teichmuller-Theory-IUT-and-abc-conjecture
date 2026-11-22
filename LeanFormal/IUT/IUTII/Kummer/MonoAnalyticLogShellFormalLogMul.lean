/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.MonoAnalyticLogShellPadicLog
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# IUT-II mono-analytic log-shell: formal log-multiplicativity logOf_mul and p-adic transfer (B')

Target: logs/coordination/monoanalytic-logshell-exploration-20261016.md section 9.5 card K-1
(missing formal multiplicativity) and section 9.7 package B'. Built on Mathlib v4.32.2:

* Formal layer: geometric-series bridge geomLog_mul_one_add_X, derivative bridge
  deriv_log_eq_geomLog, geomLog_subst_mul_eq_one, the logarithmic-derivative product form
  derivative_logOf_mul_eq_derivative, the main theorem
  logOf_mul : logOf (f * g) = logOf f + logOf g (for constantCoeff f = constantCoeff g = 1,
  via PowerSeries.derivative.ext derivative-uniqueness), and the corollaries
  logOf_mul_one_add, logOf_subst_add_mul (the log(1+u) + log(1+v) = log(1+u+v+uv) form).
* Numeric transfer: padicLogSeries_add_mul (norm < 1 log-additivity, via rearrangement and
  a truncated-exponential error estimate).
* Principal-unit calibration (K-4): non-trivial continuous log on 1 + p Z_[p]
  (padicIntPrincipalUnitLog, multiplicativity via padicLogSeries_add_mul), the compact
  carrier padicIntPrincipalUnitLogShellCarrier (invariants = top, scaling = identity,
  codomainKummerContained proved), and the non-triviality witness log(1 + p^2) != 0.
  Boundary: carrier API layer only. A multiplication-by-p scaling cannot coexist with the
  non-trivial log under codomainKummerContained, so the frozen trivial-log calibration of
  MonoAnalyticLogShellCompactCarrier is left untouched; the I-layer whole construction
  I(alphaD) subset log(alphaD), the mixed packet I(A, alphaD) and the archimedean
  Psi^cns carrier / Psi-times-log orbit-surjection card remain open (later cards).

No other files modified; not wired into any production import graph.
-/

namespace LeanFormal.IUT

namespace MonoAnalyticLogShellFormalLogMul

open scoped PowerSeries

section GeometricSeries

variable (A : Type*) [CommRing A]

/-- The geometric series sum_n (-1)^n X^n = 1 - X + X^2 - ... (formal bridge between
deriv log and the inverse of 1 + X). -/
noncomputable def geomLog : PowerSeries A :=
  PowerSeries.mk fun n => (-1 : A) ^ n

@[simp]
theorem geomLog_coeff (n : Nat) : (geomLog A).coeff n = (-1 : A) ^ n :=
  PowerSeries.coeff_mk n _

theorem geomLog_mul_one_add_X : geomLog A * (1 + PowerSeries.X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add, geomLog_coeff]
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_mul_X]
      simp
  | succ m =>
      rw [PowerSeries.coeff_succ_mul_X, geomLog_coeff]
      have h1 : (-1 : A) ^ (m + 1) + (-1 : A) ^ m = 0 := by
        rw [pow_succ]
        ring
      rw [h1]
      simp

end GeometricSeries

section FormalLogMul

variable (A : Type*) [Field A] [Algebra ℚ A]

omit [Algebra ℚ A] in
/-- geomLog is the formal inverse of 1 + X. -/
theorem geomLog_eq_inv_one_add_X :
    geomLog A = (1 + PowerSeries.X)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  exact geomLog_mul_one_add_X A

/-- The derivative of the formal logarithm is the geometric series. -/
theorem deriv_log_eq_geomLog :
    d⁄dX A (PowerSeries.log A) = geomLog A := by
  rw [PowerSeries.deriv_log]
  ext n
  rw [geomLog_coeff]
  simp [PowerSeries.coeff_mk]

omit [Algebra ℚ A] in
/-- Key substitution identity: for constantCoeff h = 1, the substituted geometric series
gives the inverse, in product form G(h-1) * h = 1. -/
theorem geomLog_subst_mul_eq_one (h : PowerSeries A)
    (hh : PowerSeries.constantCoeff h = 1) :
    (geomLog A).subst (h - 1) * h = 1 := by
  have hu : PowerSeries.HasSubst (h - 1 : PowerSeries A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hh, map_sub])
  have h1 : (geomLog A * (1 + PowerSeries.X)).subst (h - 1) = 1 := by
    rw [geomLog_mul_one_add_X]
    simpa only [PowerSeries.coe_substAlgHom hu] using
      (map_one (PowerSeries.substAlgHom (R := A) hu))
  have h2 : (geomLog A * (1 + PowerSeries.X)).subst (h - 1) =
      (geomLog A).subst (h - 1) * (1 + (h - 1)) := by
    rw [PowerSeries.subst_mul hu, PowerSeries.subst_add hu, PowerSeries.subst_X hu]
    have hone : (1 : PowerSeries A).subst (h - 1) = 1 := by
      simpa only [PowerSeries.coe_substAlgHom hu] using
        (map_one (PowerSeries.substAlgHom (R := A) hu))
    rw [hone]
  calc (geomLog A).subst (h - 1) * h
      = (geomLog A).subst (h - 1) * (1 + (h - 1)) := by ring
    _ = (geomLog A * (1 + PowerSeries.X)).subst (h - 1) := h2.symm
    _ = 1 := h1

/-- Logarithmic derivative of logOf, product form: (logOf h)' * h = h'. -/
theorem derivative_logOf_mul_eq_derivative (h : PowerSeries A)
    (hh : PowerSeries.constantCoeff h = 1) :
    d⁄dX A (PowerSeries.logOf h) * h = d⁄dX A h := by
  have hu : PowerSeries.HasSubst (h - 1 : PowerSeries A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hh, map_sub])
  have hG : (geomLog A).subst (h - 1) * h = 1 := geomLog_subst_mul_eq_one A h hh
  have hdh : d⁄dX A (h - 1) = d⁄dX A h := by
    have h1 : d⁄dX A (1 : PowerSeries A) = 0 := by
      simp
    rw [sub_eq_add_neg, map_add, map_neg, h1, neg_zero, add_zero]
  calc d⁄dX A (PowerSeries.logOf h) * h
      = ((d⁄dX A (PowerSeries.log A)).subst (h - 1) * d⁄dX A (h - 1)) * h := by
          rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst A hu]
    _ = ((geomLog A).subst (h - 1) * d⁄dX A h) * h := by
          rw [deriv_log_eq_geomLog, hdh]
    _ = ((geomLog A).subst (h - 1) * h) * d⁄dX A h := by ring
    _ = 1 * d⁄dX A h := by rw [hG]
    _ = d⁄dX A h := one_mul _

/-- Logarithmic derivative of logOf, inverse form: (logOf h)' = h⁻¹ * h'. -/
theorem derivative_logOf_eq_mul_inv (h : PowerSeries A)
    (hh : PowerSeries.constantCoeff h = 1) :
    d⁄dX A (PowerSeries.logOf h) = h⁻¹ * d⁄dX A h := by
  have h1 := derivative_logOf_mul_eq_derivative A h hh
  have hh' : PowerSeries.constantCoeff h ≠ 0 := by rw [hh]; exact one_ne_zero
  calc d⁄dX A (PowerSeries.logOf h)
      = (d⁄dX A (PowerSeries.logOf h) * h) * h⁻¹ := by
          rw [mul_assoc, PowerSeries.mul_inv_cancel h hh', mul_one]
    _ = (d⁄dX A h) * h⁻¹ := by rw [h1]
    _ = h⁻¹ * d⁄dX A h := mul_comm _ _

/-- **Formal log-multiplicativity** (card K-1): over a field, logOf is additive under
multiplication of power series with constant coefficient 1. -/
theorem logOf_mul {f g : PowerSeries A}
    (hf : PowerSeries.constantCoeff f = 1) (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.logOf (f * g) = PowerSeries.logOf f + PowerSeries.logOf g := by
  have hfg : PowerSeries.constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, mul_one]
  haveI : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [map_add, derivative_logOf_eq_mul_inv A (f * g) hfg,
      derivative_logOf_eq_mul_inv A f hf, derivative_logOf_eq_mul_inv A g hg]
    rw [Derivation.leibniz, PowerSeries.mul_inv_rev]
    have hf' : PowerSeries.constantCoeff f ≠ 0 := by rw [hf]; exact one_ne_zero
    have hg' : PowerSeries.constantCoeff g ≠ 0 := by rw [hg]; exact one_ne_zero
    simp only [smul_eq_mul]
    calc (g⁻¹ * f⁻¹) * (f * d⁄dX A g + g * d⁄dX A f)
        = g⁻¹ * (f⁻¹ * f) * d⁄dX A g + f⁻¹ * (g⁻¹ * g) * d⁄dX A f := by ring
      _ = g⁻¹ * 1 * d⁄dX A g + f⁻¹ * 1 * d⁄dX A f := by
            rw [PowerSeries.inv_mul_cancel f hf', PowerSeries.inv_mul_cancel g hg']
      _ = f⁻¹ * d⁄dX A f + g⁻¹ * d⁄dX A g := by ring
  · rw [map_add, PowerSeries.constantCoeff_logOf hfg, PowerSeries.constantCoeff_logOf hf,
      PowerSeries.constantCoeff_logOf hg]
    rw [add_zero]

/-- log(1+u) + log(1+v) = log(1+u+v+uv), multiplicative form. -/
theorem logOf_mul_one_add {u v : PowerSeries A}
    (hu : PowerSeries.constantCoeff u = 0) (hv : PowerSeries.constantCoeff v = 0) :
    PowerSeries.logOf ((1 + u) * (1 + v)) =
      PowerSeries.logOf (1 + u) + PowerSeries.logOf (1 + v) := by
  refine logOf_mul A ?_ ?_ <;> simp [hu, hv]

/-- log(1+u) + log(1+v) = log(1+u+v+uv), literal substitution form. -/
theorem logOf_subst_add_mul {u v : PowerSeries A}
    (hu : PowerSeries.constantCoeff u = 0) (hv : PowerSeries.constantCoeff v = 0) :
    (PowerSeries.log A).subst (u + v + u * v) =
      (PowerSeries.log A).subst u + (PowerSeries.log A).subst v := by
  have h := logOf_mul_one_add A hu hv
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq, PowerSeries.logOf_eq] at h
  have harg : (1 + u) * (1 + v) - 1 = u + v + u * v := by ring
  have harg1 : 1 + u - 1 = u := by ring
  have harg2 : 1 + v - 1 = v := by ring
  rwa [harg, harg1, harg2] at h

end FormalLogMul

/-! ## 3. 数值层（B'）：形式 log 乘性到 p 进解析级数乘性

把第 1 节的形式恒等式 `logOf_subst_add_mul` 传输到冻结件
`MonoAnalyticLogShellPadicLog` 的解析级数 `padicLogSeries`：
对 `‖x‖ < 1, ‖y‖ < 1` 证明
`padicLogSeries (x+y+x*y) = padicLogSeries x + padicLogSeries y`。
数学路线：系数逐项恒等式 + 双和重排（有限纤维 + 尾部估计）。
`PowerSeries.eval₂Hom` 路线因 `IsLinearTopology ℚ_[p] ℚ_[p]` 无实例而不可用（报告 §10.6 缺件卡）。
-/

section NumericLogMulTransfer

open scoped Topology

open Filter

open MonoAnalyticLogShellPadicLog

variable {p : ℕ} [Fact p.Prime]

/-- 双项代换序列 `(x+y)·X + (x*y)·X²`，其“在 1 处取值”为 `x + y + x*y`。 -/
noncomputable def twoTermArgSeries (x y : ℚ_[p]) : PowerSeries ℚ_[p] :=
  PowerSeries.C (x + y) * PowerSeries.X + PowerSeries.C (x * y) * PowerSeries.X ^ 2

theorem constantCoeff_twoTermArgSeries (x y : ℚ_[p]) :
    PowerSeries.constantCoeff (twoTermArgSeries x y) = 0 := by
  rw [twoTermArgSeries, map_add, map_mul, map_mul, map_pow,
    PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X]
  ring

/-- 单参数代换 `logSubstOne z = log.subst (z·X)`，返回类型固定为 `PowerSeries`，避免 τ 元变量。 -/
noncomputable def logSubstOne (z : ℚ_[p]) : PowerSeries ℚ_[p] :=
  PowerSeries.subst (PowerSeries.C z * PowerSeries.X) (PowerSeries.log ℚ_[p])

/-- 双项代换 `logSubstTwo x y = log.subst (twoTermArgSeries x y)`。 -/
noncomputable def logSubstTwo (x y : ℚ_[p]) : PowerSeries ℚ_[p] :=
  PowerSeries.subst (twoTermArgSeries x y) (PowerSeries.log ℚ_[p])

/-- 冻结级数按 `k = n + 1` 重指标的桥：`∑ c_k z^k = -padicLogSeries z`（`c_k = log 系数`）。 -/
theorem hasSum_logCoeff_mul_pow (z : ℚ_[p]) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (PowerSeries.log ℚ_[p]).coeff k * z ^ k) (-(padicLogSeries p z)) := by
  have h0 : HasSum (fun n : ℕ => -padicLogTerm p z n) (-(padicLogSeries p z)) :=
    (padicLogSeries_hasSum p z hz).neg
  have hterm : ∀ n : ℕ,
      -padicLogTerm p z n = (PowerSeries.log ℚ_[p]).coeff (n + 1) * z ^ (n + 1) := by
    intro n
    rw [padicLogTerm, padicFormalLog_coeff, if_neg (Nat.succ_ne_zero n),
      div_eq_mul_inv, div_eq_mul_inv]
    have hp : (-1 : ℚ_[p]) ^ (n + 1 + 1) = -((-1 : ℚ_[p]) ^ (n + 1)) := by
      rw [pow_succ]
      ring
    rw [hp]
    push_cast
    ring
  have h1 : HasSum (fun n : ℕ => (PowerSeries.log ℚ_[p]).coeff (n + 1) * z ^ (n + 1))
      (-(padicLogSeries p z)) := by
    simpa only [hterm] using h0
  have hf0 : (PowerSeries.log ℚ_[p]).coeff 0 * z ^ 0 = 0 := by
    rw [padicFormalLog_coeff]
    simp
  have := (hasSum_nat_add_iff
    (f := fun k : ℕ => (PowerSeries.log ℚ_[p]).coeff k * z ^ k) 1).mp h1
  simpa [Finset.sum_range_succ, hf0] using this

theorem coeff_log_subst_C_mul_X (z : ℚ_[p]) (e : ℕ) :
    (logSubstOne z).coeff e = (PowerSeries.log ℚ_[p]).coeff e * z ^ e := by
  have h : logSubstOne z = PowerSeries.rescale z (PowerSeries.log ℚ_[p]) := by
    rw [logSubstOne, PowerSeries.rescale_eq_subst z (PowerSeries.log ℚ_[p]),
      ← PowerSeries.smul_eq_C_mul PowerSeries.X z]
  rw [h, PowerSeries.coeff_rescale]
  exact mul_comm _ _

theorem log_subst_two_term (x y : ℚ_[p]) :
    logSubstTwo x y = logSubstOne x + logSubstOne y := by
  have h := logOf_subst_add_mul (A := ℚ_[p])
      (u := PowerSeries.C x * PowerSeries.X) (v := PowerSeries.C y * PowerSeries.X)
      (by rw [map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, mul_zero])
      (by rw [map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, mul_zero])
  have harg : twoTermArgSeries x y =
      PowerSeries.C x * PowerSeries.X + PowerSeries.C y * PowerSeries.X +
        (PowerSeries.C x * PowerSeries.X) * (PowerSeries.C y * PowerSeries.X) := by
    rw [twoTermArgSeries, map_add, map_mul]
    ring
  rw [logSubstTwo, logSubstOne, logSubstOne, harg]
  exact h

theorem subst_two_term_coeff (x y : ℚ_[p]) (e : ℕ) :
    (logSubstTwo x y).coeff e =
      (PowerSeries.log ℚ_[p]).coeff e * x ^ e + (PowerSeries.log ℚ_[p]).coeff e * y ^ e := by
  rw [log_subst_two_term, map_add, coeff_log_subst_C_mul_X, coeff_log_subst_C_mul_X]

/-- 系数逐项组合：主系数 `A_e` 的级数在 `−S x − S y` 处有 HasSum。 -/
theorem hasSum_mainCoeff (x y : ℚ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun e : ℕ => (logSubstTwo x y).coeff e)
      (-(padicLogSeries p x) - padicLogSeries p y) := by
  have hx' := hasSum_logCoeff_mul_pow (p := p) x hx
  have hy' := hasSum_logCoeff_mul_pow (p := p) y hy
  have h := hx'.add hy'
  have hfun : (fun e : ℕ => (PowerSeries.log ℚ_[p]).coeff e * x ^ e +
        (PowerSeries.log ℚ_[p]).coeff e * y ^ e) =
      fun e : ℕ => (logSubstTwo x y).coeff e :=
    funext fun e => (subst_two_term_coeff x y e).symm
  rw [hfun] at h
  simpa [sub_eq_add_neg] using h

/-- 二项展开：`w^m` 的逐单项式（monomial）分解。 -/
theorem twoTermArgSeries_pow_expand (x y : ℚ_[p]) (m : ℕ) :
    twoTermArgSeries x y ^ m =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.C ((m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j)) *
          PowerSeries.X ^ (m + j) := by
  have h1 : twoTermArgSeries x y =
      PowerSeries.X * (PowerSeries.C (x * y) * PowerSeries.X + PowerSeries.C (x + y)) := by
    rw [twoTermArgSeries]
    ring
  have hv : (PowerSeries.C (x * y) * PowerSeries.X + PowerSeries.C (x + y) :
        PowerSeries ℚ_[p]) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.C ((m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j)) *
          PowerSeries.X ^ j := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← map_pow, ← map_pow]
    rw [show ((m.choose j : ℕ) : PowerSeries ℚ_[p]) =
        PowerSeries.C ((m.choose j : ℕ) : ℚ_[p]) from
      (map_natCast PowerSeries.C (m.choose j)).symm]
    calc PowerSeries.C ((x * y) ^ j) * PowerSeries.X ^ j * PowerSeries.C ((x + y) ^ (m - j)) *
            PowerSeries.C ((m.choose j : ℕ) : ℚ_[p])
        = PowerSeries.C ((x * y) ^ j) * PowerSeries.C ((x + y) ^ (m - j)) *
            PowerSeries.C ((m.choose j : ℕ) : ℚ_[p]) * PowerSeries.X ^ j := by ring
      _ = PowerSeries.C (((x * y) ^ j) *
            (((x + y) ^ (m - j)) * ((m.choose j : ℕ) : ℚ_[p]))) *
            PowerSeries.X ^ j := by
          rw [← map_mul, ← map_mul]
          rw [show ((x * y) ^ j * (x + y) ^ (m - j) * ((m.choose j : ℕ) : ℚ_[p])) =
              ((x * y) ^ j * ((x + y) ^ (m - j) * ((m.choose j : ℕ) : ℚ_[p]))) from by ring]
      _ = PowerSeries.C ((m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j)) *
            PowerSeries.X ^ j := by
          rw [show ((x * y) ^ j) * (((x + y) ^ (m - j)) * ((m.choose j : ℕ) : ℚ_[p])) =
              (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) from by ring]
  rw [h1, mul_pow, hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- 系数公式（j-和形式）：`coeff e (w^m) = ∑_j [e = m+j] C(m,j)·s^{m−j}·t^j`。 -/
theorem coeff_twoTermArgSeries_pow (x y : ℚ_[p]) (m e : ℕ) :
    (twoTermArgSeries x y ^ m).coeff e =
      ∑ j ∈ Finset.range (m + 1),
        if e = m + j then (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 := by
  rw [twoTermArgSeries_pow_expand, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PowerSeries.coeff_C_mul_X_pow]

theorem coeff_twoTermArgSeries_pow_eq_zero_of_lt {x y : ℚ_[p]} {m e : ℕ} (he : e < m) :
    (twoTermArgSeries x y ^ m).coeff e = 0 := by
  rw [coeff_twoTermArgSeries_pow]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg]
  omega

/-- 截断系数和：`∑_{e≤E} coeff e (w^m)` 的显式有限表达式。 -/
theorem sum_coeff_twoTermArgSeries_pow (x y : ℚ_[p]) (m E : ℕ) :
    ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e =
      ∑ j ∈ Finset.range (m + 1),
        if m + j ≤ E then (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 := by
  calc ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e
      = ∑ e ∈ Finset.range (E + 1), ∑ j ∈ Finset.range (m + 1),
          if e = m + j then (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 :=
        Finset.sum_congr rfl fun e _ => coeff_twoTermArgSeries_pow x y m e
    _ = ∑ j ∈ Finset.range (m + 1), ∑ e ∈ Finset.range (E + 1),
          if e = m + j then (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.range (m + 1),
          if m + j ∈ Finset.range (E + 1) then
            (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 :=
        Finset.sum_congr rfl fun j _ =>
          Finset.sum_ite_eq' (Finset.range (E + 1)) (m + j)
            fun _ => (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j)
    _ = ∑ j ∈ Finset.range (m + 1),
          if m + j ≤ E then (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 :=
        Finset.sum_congr rfl fun j _ => by simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- 截断系数和的定值：`2m ≤ E` 时等于 `(x+y+x*y)^m`（“在 1 处取值”）。 -/
theorem sum_coeff_twoTermArgSeries_pow_eq (x y : ℚ_[p]) (m : ℕ) {E : ℕ} (hE : 2 * m ≤ E) :
    ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e = (x + y + x * y) ^ m := by
  rw [sum_coeff_twoTermArgSeries_pow]
  have hall : ∀ j ∈ Finset.range (m + 1), m + j ≤ E := by
    intro j hj
    rw [Finset.mem_range] at hj
    omega
  have hsimp : (∑ j ∈ Finset.range (m + 1),
        if m + j ≤ E then (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0) =
      ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) :=
    Finset.sum_congr rfl fun j hj => if_pos (hall j hj)
  rw [hsimp, add_pow]
  conv_rhs => rw [← Finset.sum_range_reflect
    (fun q => (x + y) ^ q * (x * y) ^ (m - q) * ((m.choose q : ℕ) : ℚ_[p])) (m + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : m + 1 - 1 - j = m - j := by omega
  have h2 : m - (m - j) = j := by omega
  rw [h1, h2, Nat.choose_symm (by omega : j ≤ m)]
  ring

/-- 超度量有限和最大范数引理。 -/
theorem norm_finsetSum_le_of_le_max {ι : Type*} (f : ι → ℚ_[p]) (s : Finset ι) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ s, ‖f i‖ ≤ M) : ‖∑ i ∈ s, f i‖ ≤ M := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hM
  | insert a s ha ih =>
      have h' : ∀ i ∈ s, ‖f i‖ ≤ M := fun i hi => h i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha]
      exact le_trans (IsUltrametricDist.norm_add_le_max (f a) (∑ i ∈ s, f i))
        (max_le (h a (Finset.mem_insert_self a s)) (ih h'))

/-- 一致范数上界：`‖∑_{e≤E} coeff e (w^m)‖ ≤ M^m`，`M = max ‖s‖ ‖t‖`。 -/
theorem norm_sum_coeff_twoTermArgSeries_pow_le (x y : ℚ_[p]) (m E : ℕ) :
    ‖∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e‖ ≤
      (max ‖x + y‖ ‖x * y‖) ^ m := by
  rw [sum_coeff_twoTermArgSeries_pow]
  have hmaxnn : 0 ≤ max ‖x + y‖ ‖x * y‖ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hle : ∀ j ∈ Finset.range (m + 1),
      ‖(if m + j ≤ E then
          (m.choose j : ℚ_[p]) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0)‖ ≤
        (max ‖x + y‖ ‖x * y‖) ^ m := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases h : m + j ≤ E
    · rw [if_pos h, norm_mul]
      have hc : ‖(m.choose j : ℚ_[p])‖ ≤ 1 := by
        have hz := Padic.norm_int_le_one (p := p) (m.choose j : ℤ)
        simpa using hz
      have h1 : ‖(x + y) ^ (m - j) * (x * y) ^ j‖ ≤ (max ‖x + y‖ ‖x * y‖) ^ m := by
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖x + y‖ ^ (m - j) * ‖x * y‖ ^ j
            ≤ (max ‖x + y‖ ‖x * y‖) ^ (m - j) * (max ‖x + y‖ ‖x * y‖) ^ j :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
                (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _)
                (pow_nonneg (norm_nonneg _) _) (pow_nonneg hmaxnn _)
          _ = (max ‖x + y‖ ‖x * y‖) ^ m := by
              rw [← pow_add, show m - j + j = m by omega]
      calc ‖(m.choose j : ℚ_[p])‖ * ‖(x + y) ^ (m - j) * (x * y) ^ j‖
          ≤ 1 * (max ‖x + y‖ ‖x * y‖) ^ m :=
            mul_le_mul hc h1 (norm_nonneg _) zero_le_one
        _ = (max ‖x + y‖ ‖x * y‖) ^ m := one_mul _
    · rw [if_neg h, norm_zero]
      positivity
  exact norm_finsetSum_le_of_le_max _ _ (pow_nonneg hmaxnn m) hle

/-- 部分和恒等式：主级数部分和 = 对 `m` 的截断系数和之和（三角交换）。 -/
theorem sum_mainCoeff_eq_partial (x y : ℚ_[p]) (E : ℕ) :
    ∑ e ∈ Finset.range (E + 1), (logSubstTwo x y).coeff e =
      ∑ m ∈ Finset.range (E + 1), (PowerSeries.log ℚ_[p]).coeff m *
        ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e := by
  have hw : PowerSeries.HasSubst (twoTermArgSeries x y) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_twoTermArgSeries x y)
  have hstep : ∀ e : ℕ,
      (logSubstTwo x y).coeff e =
        ∑ m ∈ Finset.range (e + 1),
          (PowerSeries.log ℚ_[p]).coeff m * (twoTermArgSeries x y ^ m).coeff e := by
    intro e
    rw [logSubstTwo, PowerSeries.coeff_subst' hw]
    have hsupp : Function.support (fun m : ℕ => (PowerSeries.log ℚ_[p]).coeff m •
        (twoTermArgSeries x y ^ m).coeff e) ⊆ (Finset.range (e + 1) : Set ℕ) := by
      intro m hm
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hle
      exact hm (by
        dsimp only
        rw [coeff_twoTermArgSeries_pow_eq_zero_of_lt (by omega : e < m)]
        simp)
    rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
    simp only [smul_eq_mul]
  calc ∑ e ∈ Finset.range (E + 1), (logSubstTwo x y).coeff e
      = ∑ e ∈ Finset.range (E + 1), ∑ m ∈ Finset.range (e + 1),
          (PowerSeries.log ℚ_[p]).coeff m * (twoTermArgSeries x y ^ m).coeff e :=
        Finset.sum_congr rfl fun e _ => hstep e
    _ = ∑ e ∈ Finset.range (E + 1), ∑ m ∈ Finset.range (E + 1),
          (PowerSeries.log ℚ_[p]).coeff m * (twoTermArgSeries x y ^ m).coeff e := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [Finset.mem_range] at he
        refine Finset.sum_subset (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega) ?_
        intro m hmE hme
        rw [Finset.mem_range, not_lt] at hme
        rw [coeff_twoTermArgSeries_pow_eq_zero_of_lt (by omega : e < m)]
        simp
    _ = ∑ m ∈ Finset.range (E + 1), (PowerSeries.log ℚ_[p]).coeff m *
          ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]

/-- 误差项（截断和 − 极限值）趋于 0：尾部几何估计。 -/
theorem tendsto_error_partial (x y : ℚ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Filter.Tendsto (fun E : ℕ => ∑ m ∈ Finset.range (E + 1),
        (PowerSeries.log ℚ_[p]).coeff m *
          ((∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e) -
            (x + y + x * y) ^ m)) atTop (𝓝 0) := by
  have hxy : ‖x * y‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hs : ‖x + y‖ < 1 :=
    lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
  have hsig : ‖x + y + x * y‖ < 1 :=
    lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max (x + y) (x * y)) (max_lt hs hxy)
  have hmax_lt : max (max ‖x + y‖ ‖x * y‖) ‖x + y + x * y‖ < 1 := max_lt (max_lt hs hxy) hsig
  set M' : ℝ := max (max ‖x + y‖ ‖x * y‖) ‖x + y + x * y‖ with hM'def
  have hM'lt : M' < 1 := by rw [hM'def]; exact hmax_lt
  have hM'nn : 0 ≤ M' := by
    rw [hM'def]
    exact le_trans (norm_nonneg _) (le_max_right _ _)
  have hM'norm : ‖M'‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hM'nn]
    exact hM'lt
  have hbase : Summable fun m : ℕ => (m : ℝ) * M' ^ m := by
    have hb := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hM'norm
    simpa using hb
  have hg : Summable fun m : ℕ => (m : ℝ) * M' ^ m + (m : ℝ) * M' ^ m := hbase.add hbase
  have hnonneg : ∀ m : ℕ, 0 ≤ (m : ℝ) * M' ^ m + (m : ℝ) * M' ^ m := fun m =>
    add_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hM'nn m))
      (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hM'nn m))
  let Q : ℕ → ℕ → ℚ_[p] :=
    fun E m => ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e
  let F : ℕ → ℕ → ℚ_[p] :=
    fun E m => (PowerSeries.log ℚ_[p]).coeff m * (Q E m - (x + y + x * y) ^ m)
  have hterm : ∀ E m, ‖F E m‖ ≤ (m : ℝ) * M' ^ m + (m : ℝ) * M' ^ m := by
    intro E m
    change ‖(PowerSeries.log ℚ_[p]).coeff m * (Q E m - (x + y + x * y) ^ m)‖ ≤
      (m : ℝ) * M' ^ m + (m : ℝ) * M' ^ m
    have hcm : ‖(PowerSeries.log ℚ_[p]).coeff m‖ ≤ (m : ℝ) := by
      rw [padicFormalLog_coeff]
      by_cases hm0 : m = 0
      · rw [if_pos hm0]
        simp
      · rw [if_neg hm0, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
        exact padicLog_denom_norm_inv_le p hm0
    have hQ : ‖Q E m‖ ≤ M' ^ m := by
      change ‖(∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e)‖ ≤ M' ^ m
      refine le_trans (norm_sum_coeff_twoTermArgSeries_pow_le x y m E) ?_
      exact pow_le_pow_left₀ (le_trans (norm_nonneg (x + y)) (le_max_left _ _))
        (by rw [hM'def]; exact le_max_left _ _) m
    have hsig_m : ‖(x + y + x * y) ^ m‖ ≤ M' ^ m := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (by rw [hM'def]; exact le_max_right _ _) m
    calc ‖(PowerSeries.log ℚ_[p]).coeff m * (Q E m - (x + y + x * y) ^ m)‖
        = ‖(PowerSeries.log ℚ_[p]).coeff m‖ * ‖Q E m - (x + y + x * y) ^ m‖ := norm_mul _ _
      _ ≤ (m : ℝ) * ‖Q E m - (x + y + x * y) ^ m‖ :=
          mul_le_mul_of_nonneg_right hcm (norm_nonneg _)
      _ ≤ (m : ℝ) * (‖Q E m‖ + ‖(x + y + x * y) ^ m‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Nat.cast_nonneg m)
      _ ≤ (m : ℝ) * (M' ^ m + M' ^ m) :=
          mul_le_mul_of_nonneg_left (add_le_add hQ hsig_m) (Nat.cast_nonneg m)
      _ = (m : ℝ) * M' ^ m + (m : ℝ) * M' ^ m := by ring
  have hvanish : ∀ E m, m ∈ Finset.range (E / 2 + 1) → F E m = 0 := by
    intro E m hm
    rw [Finset.mem_range] at hm
    change (PowerSeries.log ℚ_[p]).coeff m * (Q E m - (x + y + x * y) ^ m) = 0
    have h2m : 2 * m ≤ E := by
      have h1 : m ≤ E / 2 := by omega
      have h2 : 2 * (E / 2) ≤ E := by
        rw [mul_comm]
        exact Nat.div_mul_le_self E 2
      omega
    rw [show Q E m = ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e from rfl,
      sum_coeff_twoTermArgSeries_pow_eq x y m h2m]
    ring
  have hbound : ∀ E : ℕ, ‖∑ m ∈ Finset.range (E + 1), F E m‖ ≤
      ∑ i ∈ Finset.range (E - E / 2),
        (((E / 2 + 1 + i : ℕ) : ℝ) * M' ^ (E / 2 + 1 + i) +
          ((E / 2 + 1 + i : ℕ) : ℝ) * M' ^ (E / 2 + 1 + i)) := by
    intro E
    have hEm : E / 2 + 1 + (E - E / 2) = E + 1 := by
      have h := Nat.add_sub_of_le (Nat.div_le_self E 2)
      omega
    have hsplit : ∑ m ∈ Finset.range (E + 1), F E m =
        (∑ m ∈ Finset.range (E / 2 + 1), F E m) +
          ∑ i ∈ Finset.range (E - E / 2), F E (E / 2 + 1 + i) := by
      rw [show E + 1 = E / 2 + 1 + (E - E / 2) from hEm.symm, Finset.sum_range_add]
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hz : ∑ m ∈ Finset.range (E / 2 + 1), F E m = 0 :=
      Finset.sum_eq_zero fun m hm => hvanish E m hm
    rw [hz, norm_zero, zero_add]
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => hterm E (E / 2 + 1 + i))
  have hgshift : ∀ E : ℕ, Summable fun i : ℕ =>
      ((E / 2 + 1 + i : ℕ) : ℝ) * M' ^ (E / 2 + 1 + i) +
        ((E / 2 + 1 + i : ℕ) : ℝ) * M' ^ (E / 2 + 1 + i) := fun E =>
    ((summable_nat_add_iff (E / 2 + 1)).mpr hg).congr fun i => by
      rw [add_comm i (E / 2 + 1)]
  have htsum : Filter.Tendsto (fun E : ℕ => ∑' i : ℕ,
      (((E / 2 + 1 + i : ℕ) : ℝ) * M' ^ (E / 2 + 1 + i) +
        ((E / 2 + 1 + i : ℕ) : ℝ) * M' ^ (E / 2 + 1 + i))) atTop (𝓝 0) := by
    have hdiv : Filter.Tendsto (fun a : ℕ => a / 2) atTop atTop :=
      le_of_eq (Filter.map_div_atTop_eq_nat 2 (by norm_num))
    have hcomp : Filter.Tendsto (fun E : ℕ => E / 2 + 1) atTop atTop :=
      (Filter.tendsto_add_atTop_nat 1).comp hdiv
    have hshift := (tendsto_sum_nat_add
      (fun m : ℕ => (m : ℝ) * M' ^ m + (m : ℝ) * M' ^ m)).comp hcomp
    refine hshift.congr' (Eventually.of_forall fun E => ?_)
    refine tsum_congr fun k => ?_
    rw [add_comm k (E / 2 + 1)]
  have htail : Filter.Tendsto (fun E : ℕ => ∑ i ∈ Finset.range (E - E / 2),
      (((E / 2 + 1 + i : ℕ) : ℝ) * M' ^ (E / 2 + 1 + i) +
        ((E / 2 + 1 + i : ℕ) : ℝ) * M' ^ (E / 2 + 1 + i))) atTop (𝓝 0) :=
    squeeze_zero (fun E => Finset.sum_nonneg fun i _ => hnonneg (E / 2 + 1 + i))
      (fun E => Summable.sum_le_tsum (Finset.range (E - E / 2))
        (fun i _ => hnonneg (E / 2 + 1 + i)) (hgshift E)) htsum
  have hmain : Filter.Tendsto (fun E : ℕ => ∑ m ∈ Finset.range (E + 1), F E m) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    exact squeeze_zero (fun E => norm_nonneg _) hbound htail
  simpa only [F, Q] using hmain

/-- 主级数部分和收敛到 `−padicLogSeries (x+y+x*y)`。 -/
theorem tendsto_sum_mainCoeff (x y : ℚ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Filter.Tendsto (fun E : ℕ => ∑ e ∈ Finset.range E,
        (logSubstTwo x y).coeff e) atTop
      (𝓝 (-(padicLogSeries p (x + y + x * y)))) := by
  have hsig : ‖x + y + x * y‖ < 1 := by
    have hxy : ‖x * y‖ < 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg x, norm_nonneg y]
    have hs : ‖x + y‖ < 1 :=
      lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max (x + y) (x * y)) (max_lt hs hxy)
  have hT : Filter.Tendsto (fun E : ℕ => ∑ m ∈ Finset.range (E + 1),
      (PowerSeries.log ℚ_[p]).coeff m * (x + y + x * y) ^ m) atTop
      (𝓝 (-(padicLogSeries p (x + y + x * y)))) :=
    ((hasSum_logCoeff_mul_pow (p := p) (x + y + x * y) hsig).tendsto_sum_nat).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hB := tendsto_error_partial (p := p) x y hx hy
  have hpoint : ∀ E : ℕ,
      ∑ e ∈ Finset.range (E + 1),
          (logSubstTwo x y).coeff e
        = (∑ m ∈ Finset.range (E + 1), (PowerSeries.log ℚ_[p]).coeff m * (x + y + x * y) ^ m)
          + (∑ m ∈ Finset.range (E + 1), (PowerSeries.log ℚ_[p]).coeff m *
              ((∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e) -
                (x + y + x * y) ^ m)) := by
    intro E
    rw [sum_mainCoeff_eq_partial, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hmain : Filter.Tendsto (fun E : ℕ => ∑ e ∈ Finset.range (E + 1),
      (logSubstTwo x y).coeff e) atTop
      (𝓝 (-(padicLogSeries p (x + y + x * y)))) := by
    have hsum := hT.add hB
    rw [add_zero] at hsum
    exact Filter.Tendsto.congr' (Eventually.of_forall fun E => (hpoint E).symm) hsum
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => ∑ e ∈ Finset.range n,
    (logSubstTwo x y).coeff e) 1).mp hmain

/-- **数值乘性定理（B' 主定理）**：`‖x‖<1, ‖y‖<1` 时
`padicLogSeries (x+y+x*y) = padicLogSeries x + padicLogSeries y`。 -/
theorem padicLogSeries_add_mul (x y : ℚ_[p]) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    padicLogSeries p (x + y + x * y) = padicLogSeries p x + padicLogSeries p y := by
  have hmul := hasSum_mainCoeff (p := p) x y hx hy
  have hsumm := hmul.summable
  have h2 : HasSum (fun e : ℕ => (logSubstTwo x y).coeff e)
      (-(padicLogSeries p (x + y + x * y))) :=
    (Summable.hasSum_iff_tendsto_nat hsumm).mpr (tendsto_sum_mainCoeff (p := p) x y hx hy)
  have hval : -(padicLogSeries p x) - padicLogSeries p y =
      -(padicLogSeries p (x + y + x * y)) := hmul.unique h2
  have key : -(padicLogSeries p x) - padicLogSeries p y =
      -(padicLogSeries p x + padicLogSeries p y) := by
    rw [neg_add]
    ring
  exact (neg_inj.mp (key.symm.trans hval)).symm

end NumericLogMulTransfer

/-! ## 4. K-4：主单位上的非平凡 log 同态与 ℤ_[p] 校准

padicLogSeries_add_mul（§3）把形式乘性传输到 p 进解析级数；本节用它把冻结件
MonoAnalyticLogShellCompactCarrier 的 ℤ_[p] 校准从平凡 log 升级为非平凡连续 log：

* 主单位子群 padicIntPrincipalUnits p = {u : ℤ_[p]ˣ | ‖u - 1‖ ≤ p⁻¹}（即 1 + pℤ_[p]），
  闭（取值映射连续 + 闭球原像）、紧（紧单位群的闭子群）；
* ℤ_[p] 值 log padicIntPrincipalUnitLog（值落入闭单位球 = ℤ_[p]），加性定理
  padicIntPrincipalUnitLog_mul 由 padicLogSeries_add_mul 给出；
* 连续同态 padicIntPrincipalUnitLogMap、非平凡性见证（log(1+p²) 范数恰为 p⁻²）
  与校准载体 padicIntPrincipalUnitLogShellCarrier。

校准选择（如实标注）：本件取 scaling = AddMonoidHom.id，使具名条件
codomainKummerContained（unitLayer ⊆ logShell）在非平凡 log 下可证；乘 p 缩放替身
与主单位上的非平凡 log 不能同时满足该条件（log(1+p²) 已具小赋值的元素不在
p · log(主单位) 中），故乘 p 缩放保留于冻结件的平凡 log 校准。两件都只是 API
形状校准，不是原文对象（原文含 (p*_v)^{-1} 因子）。
-/

section PrincipalUnitLogCalibration

open Filter
open MonoAnalyticLogShellPadicLog

variable (p : ℕ) [Fact p.Prime]

/-- log 级数项范数公式：‖(-1)^{n+1} x^{n+1}/(n+1)‖ = ‖x‖^{n+1} · ‖(n+1)‖⁻¹。 -/
theorem padicLogTerm_norm_eq (z : ℚ_[p]) (n : ℕ) :
    ‖padicLogTerm p z n‖ = ‖z‖ ^ (n + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖⁻¹ := by
  rw [padicLogTerm, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one,
    div_eq_mul_inv]
  norm_num

/-- 超度量反向三角不等式：‖x‖ ≤ max ‖x + y‖ ‖y‖（尾部支配估计用）。 -/
theorem norm_le_max_norm_add_norm {G : Type*} [SeminormedAddGroup G] [IsUltrametricDist G]
    (x y : G) : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
  simpa [add_assoc, norm_neg] using IsUltrametricDist.norm_add_le_max (x + y) (-y)

/-- ‖z‖ < 1 时 padicLogSeries p z 落在闭单位球内（即 ℤ_[p] 的载体）：
逐项 ≤ 1，部分和经超度量 max 归纳 ≤ 1，极限落闭球。 -/
theorem padicLogSeries_norm_le_one_of_norm_lt_one (z : ℚ_[p]) (hz : ‖z‖ < 1) :
    ‖padicLogSeries p z‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpinv1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hzp : ‖z‖ ≤ (p : ℝ)⁻¹ := by
    have h := (Padic.norm_le_pow_iff_norm_lt_pow_add_one (p := p) z (-1)).mpr
      (by simpa using hz)
    simpa using h
  have hterm : ∀ n : ℕ, ‖padicLogTerm p z n‖ ≤ 1 := by
    intro n
    rw [padicLogTerm_norm_eq]
    have hden : ‖((n + 1 : ℕ) : ℚ_[p])‖⁻¹ ≤ (n : ℝ) + 1 := by
      have h2 := padicLog_denom_norm_inv_le (p := p) (k := n + 1) (Nat.succ_ne_zero n)
      simpa [Nat.cast_add, Nat.cast_one] using h2
    have hpow : ‖z‖ ^ (n + 1) ≤ ((p : ℝ)⁻¹) ^ (n + 1) :=
      pow_le_pow_left₀ (norm_nonneg z) hzp (n + 1)
    have hnat : n + 1 ≤ p ^ (n + 1) := by
      have h2n : n + 1 ≤ 2 ^ (n + 1) :=
        le_of_lt (Nat.lt_two_pow_self : n + 1 < 2 ^ (n + 1))
      exact h2n.trans (Nat.pow_le_pow_left (Nat.Prime.two_le (Fact.out : p.Prime)) (n + 1))
    have hreal : (n : ℝ) + 1 ≤ (p : ℝ) ^ (n + 1) := by exact_mod_cast hnat
    calc ‖z‖ ^ (n + 1) * ‖((n + 1 : ℕ) : ℚ_[p])‖⁻¹
        ≤ ((p : ℝ)⁻¹) ^ (n + 1) * ((n : ℝ) + 1) :=
          mul_le_mul hpow hden (inv_nonneg.mpr (norm_nonneg _))
            (pow_nonneg (le_of_lt (inv_pos.mpr hp0)) _)
      _ = ((n : ℝ) + 1) / (p : ℝ) ^ (n + 1) := by
          rw [inv_pow, div_eq_mul_inv, mul_comm]
      _ ≤ 1 := by
          rw [div_le_one (pow_pos hp0 (n + 1))]
          exact hreal
  have hpartial : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, padicLogTerm p z i‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (hterm m))
  have hmem := IsClosed.mem_of_tendsto Metric.isClosed_closedBall
    (padicLogSeries_hasSum p z hz).tendsto_sum_nat
    (Eventually.of_forall fun n => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hpartial n)
  rwa [Metric.mem_closedBall, dist_zero_right] at hmem

/-- **数值非平凡性核心**：‖padicLogSeries p (p²)‖ = p⁻²。首项 -p² 范数 p⁻²，
尾部各项范数 ≤ p⁻³（严格更小），闭球装置 + 反向三角不等式给出精确范数。 -/
theorem norm_padicLogSeries_prime_sq :
    ‖padicLogSeries p ((p : ℚ_[p]) ^ 2)‖ = (p : ℝ)⁻¹ ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hznorm : ‖(p : ℚ_[p]) ^ 2‖ = (p : ℝ)⁻¹ ^ 2 := by
    rw [norm_pow, Padic.norm_p]
  have hz : ‖(p : ℚ_[p]) ^ 2‖ < 1 := by
    rw [hznorm]
    exact pow_lt_one₀ (le_of_lt (inv_pos.mpr hp0)) hp1 (by norm_num)
  have h0 : padicLogTerm p ((p : ℚ_[p]) ^ 2) 0 = -((p : ℚ_[p]) ^ 2) := by
    simp [padicLogTerm]
  have h0norm : ‖padicLogTerm p ((p : ℚ_[p]) ^ 2) 0‖ = (p : ℝ)⁻¹ ^ 2 := by
    rw [h0, norm_neg, hznorm]
  have htailterm : ∀ m : ℕ,
      ‖padicLogTerm p ((p : ℚ_[p]) ^ 2) (m + 1)‖ ≤ (p : ℝ)⁻¹ ^ 3 := by
    intro m
    rw [padicLogTerm_norm_eq, hznorm]
    have hnat : m + 2 ≤ p ^ (2 * m + 1) := by
      have h1 : m + 2 ≤ 2 ^ (m + 1) := by
        have h : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
        omega
      have h2 : 2 ^ (m + 1) ≤ 2 ^ (2 * m + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact h1.trans (h2.trans (Nat.pow_le_pow_left (Nat.Prime.two_le (Fact.out : p.Prime)) _))
    have hreal : (m : ℝ) + 2 ≤ (p : ℝ) ^ (2 * m + 1) := by exact_mod_cast hnat
    have hden : ‖((m + 1 + 1 : ℕ) : ℚ_[p])‖⁻¹ ≤ (m : ℝ) + 2 := by
      have h2 := padicLog_denom_norm_inv_le (p := p) (k := m + 1 + 1) (by omega)
      have h2' : ‖((m + 1 + 1 : ℕ) : ℚ_[p])‖⁻¹ ≤ ((m : ℝ) + 1) + 1 := by
        simpa [Nat.cast_add, Nat.cast_one] using h2
      linarith
    calc ((p : ℝ)⁻¹ ^ 2) ^ (m + 1 + 1) * ‖((m + 1 + 1 : ℕ) : ℚ_[p])‖⁻¹
        ≤ ((p : ℝ)⁻¹ ^ 2) ^ (m + 1 + 1) * ((m : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hden
            (pow_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hp0)) 2) (m + 1 + 1))
      _ = ((m : ℝ) + 2) / (p : ℝ) ^ (2 * m + 4) := by
          rw [← pow_mul, show 2 * (m + 1 + 1) = 2 * m + 4 by omega, inv_pow,
            div_eq_mul_inv, mul_comm]
      _ ≤ (p : ℝ)⁻¹ ^ 3 := by
          rw [inv_pow, ← one_div,
            div_le_div_iff₀ (pow_pos hp0 (2 * m + 4)) (pow_pos hp0 3)]
          have h3 := mul_le_mul_of_nonneg_right hreal (pow_nonneg (le_of_lt hp0) 3)
          rw [← pow_add, show 2 * m + 1 + 3 = 2 * m + 4 by omega] at h3
          simpa using h3
  have htail : HasSum (fun n : ℕ => padicLogTerm p ((p : ℚ_[p]) ^ 2) (n + 1))
      (padicLogSeries p ((p : ℚ_[p]) ^ 2) - padicLogTerm p ((p : ℚ_[p]) ^ 2) 0) :=
    (hasSum_nat_add_iff (f := padicLogTerm p ((p : ℚ_[p]) ^ 2)) 1).mpr (by
      simpa only [Finset.sum_range_one, sub_add_cancel] using
        (padicLogSeries_hasSum p ((p : ℚ_[p]) ^ 2) hz))
  have htailnorm : ‖padicLogSeries p ((p : ℚ_[p]) ^ 2) -
      padicLogTerm p ((p : ℚ_[p]) ^ 2) 0‖ ≤ (p : ℝ)⁻¹ ^ 3 := by
    have hmem : padicLogSeries p ((p : ℚ_[p]) ^ 2) -
        padicLogTerm p ((p : ℚ_[p]) ^ 2) 0 ∈
        Metric.closedBall (0 : ℚ_[p]) ((p : ℝ)⁻¹ ^ 3) :=
      IsClosed.mem_of_tendsto
        (Metric.isClosed_closedBall (x := (0 : ℚ_[p])) (ε := (p : ℝ)⁻¹ ^ 3))
        htail.tendsto_sum_nat
        (Eventually.of_forall fun n => by
          rw [Metric.mem_closedBall, dist_zero_right]
          induction n with
          | zero =>
              rw [Finset.sum_range_zero, norm_zero]
              exact pow_nonneg (le_of_lt (inv_pos.mpr hp0)) 3
          | succ k ih =>
              rw [Finset.sum_range_succ]
              exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (htailterm k)))
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  have hft : padicLogTerm p ((p : ℚ_[p]) ^ 2) 0 +
      (padicLogSeries p ((p : ℚ_[p]) ^ 2) - padicLogTerm p ((p : ℚ_[p]) ^ 2) 0) =
      padicLogSeries p ((p : ℚ_[p]) ^ 2) := by
    ring
  have hlt : (p : ℝ)⁻¹ ^ 3 < (p : ℝ)⁻¹ ^ 2 := by
    calc (p : ℝ)⁻¹ ^ 3 = (p : ℝ)⁻¹ ^ 2 * (p : ℝ)⁻¹ := by ring
      _ < (p : ℝ)⁻¹ ^ 2 * 1 := mul_lt_mul_of_pos_left hp1 (pow_pos (inv_pos.mpr hp0) 2)
      _ = (p : ℝ)⁻¹ ^ 2 := mul_one _
  have hle : ‖padicLogSeries p ((p : ℚ_[p]) ^ 2)‖ ≤ (p : ℝ)⁻¹ ^ 2 := by
    calc ‖padicLogSeries p ((p : ℚ_[p]) ^ 2)‖
        = ‖padicLogTerm p ((p : ℚ_[p]) ^ 2) 0 +
            (padicLogSeries p ((p : ℚ_[p]) ^ 2) -
              padicLogTerm p ((p : ℚ_[p]) ^ 2) 0)‖ := by rw [hft]
      _ ≤ max ‖padicLogTerm p ((p : ℚ_[p]) ^ 2) 0‖
            ‖padicLogSeries p ((p : ℚ_[p]) ^ 2) -
              padicLogTerm p ((p : ℚ_[p]) ^ 2) 0‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ (p : ℝ)⁻¹ ^ 2 :=
          max_le (le_of_eq h0norm) (lt_of_le_of_lt htailnorm hlt).le
  have hge : (p : ℝ)⁻¹ ^ 2 ≤ ‖padicLogSeries p ((p : ℚ_[p]) ^ 2)‖ := by
    have h := norm_le_max_norm_add_norm
      (x := padicLogTerm p ((p : ℚ_[p]) ^ 2) 0)
      (y := padicLogSeries p ((p : ℚ_[p]) ^ 2) - padicLogTerm p ((p : ℚ_[p]) ^ 2) 0)
    rw [hft, h0norm] at h
    by_contra hcon
    rw [not_le] at hcon
    have h2 : max ‖padicLogSeries p ((p : ℚ_[p]) ^ 2)‖
        ‖padicLogSeries p ((p : ℚ_[p]) ^ 2) - padicLogTerm p ((p : ℚ_[p]) ^ 2) 0‖ <
        (p : ℝ)⁻¹ ^ 2 :=
      max_lt hcon (lt_of_le_of_lt htailnorm hlt)
    linarith
  exact le_antisymm hle hge

/-- 由范数 p⁻² ≠ 0：log 级数在 p² 处不为零。 -/
theorem padicLogSeries_prime_sq_ne_zero :
    padicLogSeries p ((p : ℚ_[p]) ^ 2) ≠ 0 := by
  intro h0
  have hpos : 0 < ‖padicLogSeries p ((p : ℚ_[p]) ^ 2)‖ := by
    rw [norm_padicLogSeries_prime_sq p]
    exact pow_pos (inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)) 2
  rw [h0, norm_zero] at hpos
  exact lt_irrefl 0 hpos

/-! ## 5. 主单位子群 `1 + pℤ_[p]`：闭/紧载体与 ℤ_[p] 值 log

本段把 §3 的数值乘性与 §4 的范数估计落到 ℤ_[p] 校准的非平凡 log：

* 主单位集合 `padicIntPrincipalUnitsCarrier = {u : ℤ_[p]ˣ | ‖u - 1‖ ≤ p⁻¹}`
  （即 `1 + pℤ_[p]` 的单位部分）：含 1、对乘/逆封闭、闭（连续取值映射下闭球的原像）、
  紧（紧单位群的闭子集；实例注册供 `CompactSpace` 子类型综合使用）；
* 主单位上的 ℤ_[p] 值 log `padicIntPrincipalUnitLog`（`padicLogSeries` 的值落闭单位球）
  与乘性定理 `padicIntPrincipalUnitLog_mul`（由 `padicLogSeries_add_mul` 给出）；
* 连续 log 同态 `padicIntPrincipalUnitLogMap : 1 + pℤ_[p] →* Multiplicative ℤ_[p]`。
-/

/-- 主单位集合：`{u : ℤ_[p]ˣ | ‖u - 1‖ ≤ p⁻¹}`（单位群视角的 `1 + pℤ_[p]`）。 -/
def padicIntPrincipalUnitsCarrier : Set ℤ_[p]ˣ :=
  {u | ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹}

/-- ℤ_[p] 层与 ℚ_[p] 层范数的桥：`‖↑u - 1‖_ℚ = ‖↑u - 1‖_ℤ`（`norm_def` + `coe_sub`）。 -/
theorem norm_coe_sub_one_eq (u : ℤ_[p]ˣ) :
    ‖((u : ℤ_[p]) : ℚ_[p]) - 1‖ = ‖(u : ℤ_[p]) - 1‖ := by
  rw [show (((u : ℤ_[p]) : ℚ_[p])) - 1 = (((u : ℤ_[p]) - 1 : ℤ_[p]) : ℚ_[p]) from by
    rw [PadicInt.coe_sub, PadicInt.coe_one],
    ← PadicInt.norm_def]

/-- 主单位集合含 1。 -/
theorem padicIntPrincipalUnitsCarrier_one_mem :
    (1 : ℤ_[p]ˣ) ∈ padicIntPrincipalUnitsCarrier p := by
  change ‖((1 : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹
  rw [Units.val_one, sub_self, norm_zero]
  exact inv_nonneg.mpr (Nat.cast_nonneg p)

/-- 主单位集合对乘法封闭：分解 `ab - 1 = (a-1)(b-1) + (a-1) + (b-1)` + 超度量最大不等式。 -/
theorem padicIntPrincipalUnitsCarrier_mul_mem {u v : ℤ_[p]ˣ}
    (hu : u ∈ padicIntPrincipalUnitsCarrier p)
    (hv : v ∈ padicIntPrincipalUnitsCarrier p) :
    u * v ∈ padicIntPrincipalUnitsCarrier p := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  change ‖((u * v : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹
  have hdecomp : ((u * v : ℤ_[p]ˣ) : ℤ_[p]) - 1 =
      ((u : ℤ_[p]) - 1) * ((v : ℤ_[p]) - 1) + ((u : ℤ_[p]) - 1) + ((v : ℤ_[p]) - 1) := by
    rw [Units.val_mul]
    ring
  rw [hdecomp]
  calc ‖((u : ℤ_[p]) - 1) * ((v : ℤ_[p]) - 1) + ((u : ℤ_[p]) - 1) + ((v : ℤ_[p]) - 1)‖
      ≤ max ‖((u : ℤ_[p]) - 1) * ((v : ℤ_[p]) - 1) + ((u : ℤ_[p]) - 1)‖ ‖(v : ℤ_[p]) - 1‖ :=
        IsUltrametricDist.norm_add_le_max _ _
    _ ≤ (p : ℝ)⁻¹ := by
        refine max_le ?_ hv
        calc ‖((u : ℤ_[p]) - 1) * ((v : ℤ_[p]) - 1) + ((u : ℤ_[p]) - 1)‖
            ≤ max ‖((u : ℤ_[p]) - 1) * ((v : ℤ_[p]) - 1)‖ ‖(u : ℤ_[p]) - 1‖ :=
              IsUltrametricDist.norm_add_le_max _ _
          _ ≤ (p : ℝ)⁻¹ := by
              refine max_le ?_ hu
              calc ‖((u : ℤ_[p]) - 1) * ((v : ℤ_[p]) - 1)‖
                  = ‖(u : ℤ_[p]) - 1‖ * ‖(v : ℤ_[p]) - 1‖ := norm_mul _ _
                _ ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := mul_le_mul hu hv (norm_nonneg _) hp0
                _ ≤ (p : ℝ)⁻¹ := by
                    calc (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ * 1 :=
                          mul_le_mul_of_nonneg_left hp1 hp0
                      _ = (p : ℝ)⁻¹ := mul_one _

/-- 主单位集合对求逆封闭：`u⁻¹ - 1 = -(u⁻¹(u-1))` 且 `‖u⁻¹‖ = 1`（在 ℚ_[p] 中计算）。 -/
theorem padicIntPrincipalUnitsCarrier_inv_mem {u : ℤ_[p]ˣ}
    (hu : u ∈ padicIntPrincipalUnitsCarrier p) :
    u⁻¹ ∈ padicIntPrincipalUnitsCarrier p := by
  change ‖((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹
  rw [← norm_coe_sub_one_eq p (u⁻¹)]
  have hB : (((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    intro h
    have h1 : ‖(((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])‖ = 1 := by
      rw [← PadicInt.norm_def, PadicInt.norm_units]
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hmul1 : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
      (((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  have hinv : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) =
      ((((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))⁻¹ :=
    mul_right_cancel₀ hB (hmul1.trans (inv_mul_cancel₀ hB).symm)
  have hid : ((((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))⁻¹ - 1 =
      -(((((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))⁻¹ *
        ((((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1)) := by
    rw [mul_sub, inv_mul_cancel₀ hB, mul_one, neg_sub]
  have huinv : ‖((((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))⁻¹‖ = 1 := by
    rw [norm_inv, ← PadicInt.norm_def, PadicInt.norm_units, inv_one]
  calc ‖(((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1‖
      = ‖-(((((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))⁻¹ *
          ((((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1))‖ := by
        rw [hinv, hid]
    _ = ‖((((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))⁻¹‖ *
        ‖(((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1‖ := by
        rw [norm_neg, norm_mul]
    _ = ‖(((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1‖ := by rw [huinv, one_mul]
    _ ≤ (p : ℝ)⁻¹ := by
        rw [norm_coe_sub_one_eq]
        exact hu

/-- 主单位子群 `1 + pℤ_[p]`（`u : ℤ_[p]ˣ` 且 `‖u - 1‖ ≤ p⁻¹`）。 -/
def padicIntPrincipalUnits : Subgroup ℤ_[p]ˣ where
  carrier := padicIntPrincipalUnitsCarrier p
  one_mem' := padicIntPrincipalUnitsCarrier_one_mem p
  mul_mem' := fun ha hb => padicIntPrincipalUnitsCarrier_mul_mem p ha hb
  inv_mem' := fun ha => padicIntPrincipalUnitsCarrier_inv_mem p ha

/-- 主单位到 `ℤ_[p]` 的便捷强制（`↥H → ℤ_[p]` 的链式强制不自动）。 -/
instance padicIntPrincipalUnitsCoe : Coe (padicIntPrincipalUnits p) ℤ_[p] :=
  ⟨fun u => ((u : ℤ_[p]ˣ) : ℤ_[p])⟩

/-- 主单位集合闭：连续取值映射下闭球的原像。 -/
theorem padicIntPrincipalUnitsCarrier_isClosed :
    IsClosed (padicIntPrincipalUnitsCarrier p) := by
  have h : IsClosed ((fun u : ℤ_[p]ˣ => (u : ℤ_[p])) ⁻¹'
      Metric.closedBall (1 : ℤ_[p]) (p : ℝ)⁻¹) :=
    Metric.isClosed_closedBall.preimage Units.continuous_val
  have hset : padicIntPrincipalUnitsCarrier p =
      (fun u : ℤ_[p]ˣ => (u : ℤ_[p])) ⁻¹' Metric.closedBall (1 : ℤ_[p]) (p : ℝ)⁻¹ := by
    ext u
    simp [padicIntPrincipalUnitsCarrier, Metric.mem_closedBall, dist_eq_norm]
  rw [hset]
  exact h

/-- 载体闭的实例注册（供 `CompactSpace` 子类型综合使用）。 -/
instance padicIntPrincipalUnits_carrier_isClosed :
    IsClosed ((padicIntPrincipalUnits p) : Set ℤ_[p]ˣ) :=
  padicIntPrincipalUnitsCarrier_isClosed p

/-- 主单位子群紧：紧单位群的闭子群（实例注册）。 -/
instance padicIntPrincipalUnits_compactSpace : CompactSpace (padicIntPrincipalUnits p) :=
  isCompact_iff_compactSpace.mp (padicIntPrincipalUnits_carrier_isClosed (p := p)).isCompact

/-- 主单位 `u` 的 log 参数 `u - 1`（在 `ℚ_[p]` 中）。 -/
noncomputable def padicIntPrincipalUnitLogArg (u : padicIntPrincipalUnits p) : ℚ_[p] :=
  (((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1

/-- 主单位 log 参数范数 < 1（由 `‖u - 1‖ ≤ p⁻¹ < 1`）。 -/
theorem padicIntPrincipalUnitLogArg_norm_lt_one (u : padicIntPrincipalUnits p) :
    ‖padicIntPrincipalUnitLogArg p u‖ < 1 := by
  have hp1 : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  calc ‖padicIntPrincipalUnitLogArg p u‖
      = ‖((u : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ := norm_coe_sub_one_eq p (u : ℤ_[p]ˣ)
    _ ≤ (p : ℝ)⁻¹ := u.2
    _ < 1 := hp1

/-- 主单位 log（ℤ_[p] 值；`padicLogSeries` 在 ‖z‖ < 1 处落闭单位球）。 -/
noncomputable def padicIntPrincipalUnitLog (u : padicIntPrincipalUnits p) : ℤ_[p] :=
  ⟨padicLogSeries p (padicIntPrincipalUnitLogArg p u),
    padicLogSeries_norm_le_one_of_norm_lt_one p (padicIntPrincipalUnitLogArg p u)
      (padicIntPrincipalUnitLogArg_norm_lt_one p u)⟩

/-- 主单位 log 的取值公式（ℚ_[p] 层；定义展开）。 -/
theorem padicIntPrincipalUnitLog_coe (u : padicIntPrincipalUnits p) :
    ((padicIntPrincipalUnitLog p u : ℤ_[p]) : ℚ_[p]) =
      padicLogSeries p (padicIntPrincipalUnitLogArg p u) := rfl

/-- 主单位 log 在 1 处取 0（`padicLogSeries 0 = 0`）。 -/
theorem padicIntPrincipalUnitLog_one :
    padicIntPrincipalUnitLog p (1 : padicIntPrincipalUnits p) = 0 := by
  apply PadicInt.ext
  rw [padicIntPrincipalUnitLog_coe,
    show padicIntPrincipalUnitLogArg p (1 : padicIntPrincipalUnits p) = 0 from by
      simp [padicIntPrincipalUnitLogArg],
    padicLogSeries_zero,
    PadicInt.coe_zero]

/-- log(1+p²) 的参数分解核心：`(uv) - 1` 的展开（由单位乘性 + 环恒等式）。 -/
theorem padicIntPrincipalUnitLogArg_mul (u v : padicIntPrincipalUnits p) :
    padicIntPrincipalUnitLogArg p (u * v) =
      padicIntPrincipalUnitLogArg p u + padicIntPrincipalUnitLogArg p v +
        padicIntPrincipalUnitLogArg p u * padicIntPrincipalUnitLogArg p v := by
  have h1 : padicIntPrincipalUnitLogArg p (u * v) =
      (((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (((v : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1 := by
    unfold padicIntPrincipalUnitLogArg
    rw [show (((u * v : ↥(padicIntPrincipalUnits p)) : ℤ_[p]ˣ) : ℤ_[p]) =
        ((u : ℤ_[p]ˣ) : ℤ_[p]) * ((v : ℤ_[p]ˣ) : ℤ_[p]) from rfl]
    rw [PadicInt.coe_mul]
  calc padicIntPrincipalUnitLogArg p (u * v)
      = (((u : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (((v : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1 := h1
    _ = padicIntPrincipalUnitLogArg p u + padicIntPrincipalUnitLogArg p v +
          padicIntPrincipalUnitLogArg p u * padicIntPrincipalUnitLogArg p v := by
        unfold padicIntPrincipalUnitLogArg
        ring

/-- **K-4 主定理**：主单位 log 乘性（数值乘性 `padicLogSeries_add_mul` 的主单位实现）。 -/
theorem padicIntPrincipalUnitLog_mul (u v : padicIntPrincipalUnits p) :
    padicIntPrincipalUnitLog p (u * v) =
      padicIntPrincipalUnitLog p u + padicIntPrincipalUnitLog p v := by
  apply PadicInt.ext
  simp only [padicIntPrincipalUnitLog_coe, PadicInt.coe_add]
  rw [padicIntPrincipalUnitLogArg_mul p u v]
  rw [padicLogSeries_add_mul (padicIntPrincipalUnitLogArg p u) (padicIntPrincipalUnitLogArg p v)
    (padicIntPrincipalUnitLogArg_norm_lt_one p u) (padicIntPrincipalUnitLogArg_norm_lt_one p v)]

/-- 主单位 log 的连续性（在 `1 + pℤ_[p]` 上；ℚ_[p] 层连续 + 落闭球子类型）。 -/
theorem padicIntPrincipalUnitLog_continuous :
    Continuous fun u : padicIntPrincipalUnits p => padicIntPrincipalUnitLog p u := by
  have harg : Continuous fun u : padicIntPrincipalUnits p => padicIntPrincipalUnitLogArg p u := by
    have h1 : Continuous fun u : padicIntPrincipalUnits p => ((u : ℤ_[p]ˣ) : ℤ_[p]) :=
      Units.continuous_val.comp continuous_subtype_val
    have h2 : Continuous fun z : ℤ_[p] => (z : ℚ_[p]) := continuous_subtype_val
    exact (h2.comp h1).sub continuous_const
  have hlog : Continuous fun u : padicIntPrincipalUnits p =>
      padicLogSeries p (padicIntPrincipalUnitLogArg p u) :=
    (padicLogSeries_continuousOn_ball p).comp_continuous harg (fun u => by
      rw [Metric.mem_ball, dist_zero_right]
      exact padicIntPrincipalUnitLogArg_norm_lt_one p u)
  exact Continuous.subtype_mk hlog fun u =>
    padicLogSeries_norm_le_one_of_norm_lt_one p (padicIntPrincipalUnitLogArg p u)
      (padicIntPrincipalUnitLogArg_norm_lt_one p u)

/-- 主单位 log 同态（包装为 `Multiplicative`，匹配载体 `logMap` 字段类型）。 -/
noncomputable def padicIntPrincipalUnitLogMap :
    padicIntPrincipalUnits p →* Multiplicative ℤ_[p] where
  toFun u := Multiplicative.ofAdd (padicIntPrincipalUnitLog p u)
  map_one' := by
    change Multiplicative.ofAdd (padicIntPrincipalUnitLog p 1) = 1
    rw [padicIntPrincipalUnitLog_one p, ofAdd_zero]
  map_mul' := fun u v => by
    change Multiplicative.ofAdd (padicIntPrincipalUnitLog p (u * v)) =
      Multiplicative.ofAdd (padicIntPrincipalUnitLog p u) *
        Multiplicative.ofAdd (padicIntPrincipalUnitLog p v)
    rw [padicIntPrincipalUnitLog_mul p u v]
    rfl

/-- log 同态连续（底层 `padicIntPrincipalUnitLog` 连续 + `Multiplicative` 恒等桥）。 -/
theorem padicIntPrincipalUnitLogMap_continuous :
    Continuous (padicIntPrincipalUnitLogMap p) := by
  change Continuous fun u : padicIntPrincipalUnits p =>
    Multiplicative.ofAdd (padicIntPrincipalUnitLog p u)
  exact padicIntPrincipalUnitLog_continuous p

/-- **非平凡性核心（几何级）**：`‖1 + p²‖ = 1`（`‖p²‖ = p⁻² < 1` + 超度量等腰律）。 -/
theorem norm_one_add_prime_sq :
    ‖(1 : ℚ_[p]) + (p : ℚ_[p]) ^ 2‖ = 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hp2 : (p : ℝ)⁻¹ ^ 2 < 1 :=
    pow_lt_one₀ (le_of_lt (inv_pos.mpr hp0)) hp1 (by norm_num)
  have hnormp2 : ‖(p : ℚ_[p]) ^ 2‖ = (p : ℝ)⁻¹ ^ 2 := by
    rw [norm_pow, Padic.norm_p]
  calc ‖(1 : ℚ_[p]) + (p : ℚ_[p]) ^ 2‖
      = max ‖(1 : ℚ_[p])‖ ‖(p : ℚ_[p]) ^ 2‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
          rw [hnormp2, norm_one]
          exact ne_of_gt hp2)
    _ = 1 := by
        rw [norm_one, hnormp2]
        exact max_eq_left hp2.le

/-- 主单位 `1 + p²` 的成员性：`‖(1+p²) - 1‖ = p⁻² ≤ p⁻¹`。 -/
theorem padicIntPrimeSqUnit_mem :
    PadicInt.mkUnits (norm_one_add_prime_sq p) ∈ padicIntPrincipalUnitsCarrier p := by
  change ‖(PadicInt.mkUnits (norm_one_add_prime_sq p) : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹
  rw [← norm_coe_sub_one_eq p (PadicInt.mkUnits (norm_one_add_prime_sq p))]
  rw [show ((PadicInt.mkUnits (norm_one_add_prime_sq p) : ℤ_[p]) : ℚ_[p]) =
      (1 : ℚ_[p]) + (p : ℚ_[p]) ^ 2 from
    PadicInt.mkUnits_eq (norm_one_add_prime_sq p)]
  rw [show (1 : ℚ_[p]) + (p : ℚ_[p]) ^ 2 - 1 = (p : ℚ_[p]) ^ 2 by ring,
    norm_pow, Padic.norm_p]
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  calc (p : ℝ)⁻¹ ^ 2 = (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by ring
    _ ≤ (p : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hp1 hp0
    _ = (p : ℝ)⁻¹ := mul_one _

/-- 非平凡见证单位 `1 + p² ∈ 1 + pℤ_[p]`。 -/
noncomputable def padicIntPrimeSqUnit : padicIntPrincipalUnits p :=
  ⟨PadicInt.mkUnits (norm_one_add_prime_sq p), padicIntPrimeSqUnit_mem p⟩

/-- `padicIntPrimeSqUnit` 的 log 参数恰为 `p²`。 -/
theorem padicIntPrincipalUnitLogArg_primeSq :
    padicIntPrincipalUnitLogArg p (padicIntPrimeSqUnit p) = (p : ℚ_[p]) ^ 2 := by
  unfold padicIntPrincipalUnitLogArg
  rw [show (padicIntPrimeSqUnit p : ℤ_[p]ˣ) = PadicInt.mkUnits (norm_one_add_prime_sq p)
    from rfl]
  rw [show ((PadicInt.mkUnits (norm_one_add_prime_sq p) : ℤ_[p]) : ℚ_[p]) =
      (1 : ℚ_[p]) + (p : ℚ_[p]) ^ 2 from
    PadicInt.mkUnits_eq (norm_one_add_prime_sq p)]
  ring

/-- `log(1 + p²) ≠ 0`（其 ℚ_[p] 坐标范数恰为 p⁻²）。 -/
theorem padicIntPrincipalUnitLog_primeSq_ne_zero :
    padicIntPrincipalUnitLog p (padicIntPrimeSqUnit p) ≠ 0 := by
  intro h0
  have hcoe : ((padicIntPrincipalUnitLog p (padicIntPrimeSqUnit p) : ℤ_[p]) : ℚ_[p]) = 0 := by
    rw [h0, PadicInt.coe_zero]
  rw [padicIntPrincipalUnitLog_coe p (padicIntPrimeSqUnit p),
    padicIntPrincipalUnitLogArg_primeSq p] at hcoe
  exact padicLogSeries_prime_sq_ne_zero p hcoe

/-- **K-4 校准载体（非平凡 log 版）**：`M = ℤ_[p]`、`Units = 1 + pℤ_[p]`（主单位子群）、
`invariants = ⊤`、非平凡连续 log `padicIntPrincipalUnitLogMap`、`scaling = id`。
校准选择：`scaling = id` 使 `codomainKummerContained` 在非平凡 log 下可证；乘 p 缩放替身
与主单位非平凡 log 不能同时满足该条件，故保留于冻结件的平凡 log 校准。 -/
noncomputable def padicIntPrincipalUnitLogShellCarrier :
    MonoAnalyticLogShellCompactCarrier where
  p := p
  hp := Fact.out
  M := ℤ_[p]
  Units := padicIntPrincipalUnits p
  invariants := ⊤
  invariants_isClosed := by
    rw [Submonoid.coe_top]
    exact isClosed_univ
  logMap := padicIntPrincipalUnitLogMap p
  continuous_logMap := padicIntPrincipalUnitLogMap_continuous p
  scaling := AddMonoidHom.id ℤ_[p]
  continuous_scaling := continuous_id

/-- 非平凡性见证：`logMap` 不恒为 `1`（取 `1 + p²`，其 log 范数为 p⁻² ≠ 0）。 -/
theorem padicIntPrincipalUnitLogShellCarrier_logMap_nontrivial :
    ∃ u : (padicIntPrincipalUnitLogShellCarrier p).Units,
      (padicIntPrincipalUnitLogShellCarrier p).logMap u ≠ 1 := by
  refine ⟨padicIntPrimeSqUnit p, ?_⟩
  change padicIntPrincipalUnitLogMap p (padicIntPrimeSqUnit p) ≠ 1
  intro h1
  apply padicIntPrincipalUnitLog_primeSq_ne_zero p
  have h2 := congrArg Multiplicative.toAdd h1
  rw [toAdd_one] at h2
  simpa [padicIntPrincipalUnitLogMap, toAdd_ofAdd] using h2

/-- 非平凡载体的具名条件 `codomainKummerContained`（`scaling = id`、`invariants = ⊤` 时
`logShell = preLogShell = unitLayer`）。 -/
theorem padicIntPrincipalUnitLogShellCarrier_codomainKummerContained :
    (padicIntPrincipalUnitLogShellCarrier p).codomainKummerContained := by
  rintro a ⟨u, rfl⟩
  exact ⟨((padicIntPrincipalUnitLogShellCarrier p).logMap u).toAdd,
    ⟨u, Submonoid.mem_top u, rfl⟩, rfl⟩

/-- 非平凡载体经显式具名条件落在冻结有序层接口上（K-4 升级：替换校准时可选用）。 -/
noncomputable def padicIntPrincipalUnitLogShellCarrierUpperSemi :
    NonarchimedeanLogKummerUpperSemi :=
  (padicIntPrincipalUnitLogShellCarrier p).toNonarchimedeanUpperSemi_of_carrier
    (padicIntPrincipalUnitLogShellCarrier_codomainKummerContained p)

end PrincipalUnitLogCalibration

end MonoAnalyticLogShellFormalLogMul

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：形式 log 乘性 + p 进数值传递 + 主单位非平凡 log 校准（B' pass）。 -/
def monoAnalyticLogShellFormalLogMul : Obligation :=
  { id := "IUT-II.mono-analytic-log-shell-formal-log-mul"
    source := "IUT III, Definition 1.1, (i) (text l.1330-1351); Introduction l.208-226; " ++
      "IUT III, Proposition 1.2, (vi) (l.5740-5785)"
    status := VerificationStatus.conditional
    note :=
      "Formal log-multiplicativity and p-adic transfer, with non-trivial principal-unit " ++
        "calibration (B' pass). Proved: PowerSeries-level logOf_mul via derivative " ++
        "uniqueness (PowerSeries.derivative.ext); bridges geomLog_mul_one_add_X, " ++
        "deriv_log_eq_geomLog, geomLog_subst_mul_eq_one, logOf_mul_one_add, " ++
        "logOf_subst_add_mul; numeric transfer padicLogSeries_add_mul for norm < 1 " ++
        "(rearrangement plus truncated exponential error estimate); principal-unit " ++
        "subgroup 1 + p Z_p (closed, compact); Z_p-valued padicIntPrincipalUnitLog " ++
        "with multiplicativity padicIntPrincipalUnitLog_mul; continuous homomorphism " ++
        "padicIntPrincipalUnitLogMap; non-triviality witness log(1 + p^2) with norm " ++
        "p^-2 != 0; upgraded calibration carrier padicIntPrincipalUnitLogShellCarrier " ++
        "(non-trivial logMap, scaling = identity, codomainKummerContained proved) and " ++
        "its assembly into the frozen ordered-layer interface. Boundary: carrier API " ++
        "layer only. A multiplication-by-p scaling cannot coexist with the non-trivial " ++
        "log under codomainKummerContained, so the frozen trivial-log calibration of " ++
        "MonoAnalyticLogShellCompactCarrier is left untouched. Not delivered: the " ++
        "I-layer whole construction I(alphaD_vQ) subset log(alphaD_vQ), the mixed " ++
        "packet I(A, alphaD), the archimedean Psi^cns carrier and the Psi-times-log " ++
        "orbit/surjection card. See coordination report " ++
        "monoanalytic-logshell-exploration-20261016 sections 9-10."
    dependsOn :=
      [ "IUT-II.mono-analytic-log-shell-compact-carrier",
        "IUT-II.mono-analytic-log-shell-padic-log-series" ] }

end LeanFormal.IUT.Audit
