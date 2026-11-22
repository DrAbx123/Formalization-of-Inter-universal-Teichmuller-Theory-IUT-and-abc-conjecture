import LeanFormal.IUT.IUTII.Kummer.MonoAnalyticLogShellFormalLogMul
import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# Analytic logarithms in actual local extension fields

Source prerequisite for IUT III Remark 1.2.2(i): the logarithm defining
`I_k = (p*)⁻¹ log_k(O_kˣ)` must be available in the actual local field, not
only in the base field Qp. This module extends the established series and
coefficient proof to complete nonarchimedean normed Qp-algebras.

The auxiliary negative series uses the sign convention of the existing
base-field implementation. The actual source logarithm is `log1p`, its
negative, so its linear term is +x. No source logarithm is a promised field.
The full unit-group extension and log-shell are constructed downstream.
-/

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.LocalFieldLogarithm

open scoped Topology
open Filter
open MonoAnalyticLogShellFormalLogMul

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

noncomputable def negativeLogTerm (x : K) (n : ℕ) : K :=
  ((-1 : K) ^ (n + 1) * x ^ (n + 1)) / (n + 1 : K)

noncomputable def negativeLogSeries (x : K) : K := ∑' n, negativeLogTerm x n

noncomputable def log1p (x : K) : K := -negativeLogSeries x

theorem localFormalLog_coeff (n : ℕ) :
    (PowerSeries.log K).coeff n =
      if n = 0 then 0 else ((-1 : K) ^ (n + 1)) / (n : K) := by
  rw [PowerSeries.coeff_log]
  split_ifs with hn
  · rfl
  · rw [map_div₀, map_pow, map_neg, map_one, map_natCast]

include localNormedAlgebra in
theorem localLog_denom_norm_inv_le {n : ℕ} (hn : n ≠ 0) :
    ‖(n : K)‖⁻¹ ≤ (n : ℝ) := by
  have heq : ‖(n : K)‖ = ‖(n : ℚ_[p])‖ := by
    simpa only [map_natCast] using norm_algebraMap' K (n : ℚ_[p])
  rw [heq]
  exact MonoAnalyticLogShellPadicLog.padicLog_denom_norm_inv_le p hn

include localNormedAlgebra in
theorem localLog_norm_natCast_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  have heq : ‖(n : K)‖ = ‖(n : ℚ_[p])‖ := by
    simpa only [map_natCast] using norm_algebraMap' K (n : ℚ_[p])
  rw [heq]
  simpa using Padic.norm_int_le_one (p := p) (n : ℤ)

include localNormedAlgebra in
/-- 项范数上界：`‖x‖ ≤ r` 时 `‖negativeLogTerm x n‖ ≤ (n+1) r^{n+1}`。 -/
theorem negativeLogTerm_norm_le (x : K) {r : ℝ} (hr0 : 0 ≤ r) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖negativeLogTerm x n‖ ≤ MonoAnalyticLogShellPadicLog.padicLogMajorant r n := by
  have hden : ‖((n + 1 : ℕ) : K)‖⁻¹ ≤ ((n : ℝ) + 1) := by
    have := localLog_denom_norm_inv_le (K := K) (p := p) (n := n + 1) (Nat.succ_ne_zero n)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hterm : ‖negativeLogTerm x n‖ =
      ‖x‖ ^ (n + 1) * ‖((n + 1 : ℕ) : K)‖⁻¹ := by
    rw [negativeLogTerm, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one,
      div_eq_mul_inv]
    norm_num
  calc ‖negativeLogTerm x n‖
      = ‖x‖ ^ (n + 1) * ‖((n + 1 : ℕ) : K)‖⁻¹ := hterm
    _ ≤ r ^ (n + 1) * ‖((n + 1 : ℕ) : K)‖⁻¹ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx (n + 1))
          (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ r ^ (n + 1) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hden (pow_nonneg hr0 _)
    _ = MonoAnalyticLogShellPadicLog.padicLogMajorant r n := by
        simp [MonoAnalyticLogShellPadicLog.padicLogMajorant, mul_comm]

include localNormedAlgebra in
/-- 收敛：`‖x‖ < 1` 时 log 级数可和（由优函数 + `Summable.of_norm_bounded`）。 -/
theorem negativeLogSeries_summable (x : K) (hx : ‖x‖ < 1) :
    Summable (negativeLogTerm x) :=
  Summable.of_norm_bounded
    (MonoAnalyticLogShellPadicLog.padicLogMajorant_summable (norm_nonneg x) hx)
    fun n => negativeLogTerm_norm_le (p := p) x (norm_nonneg x) le_rfl n

include localNormedAlgebra in
/-- HasSum 形式（四件套验收点：收敛以 `HasSum` 记录）。 -/
theorem negativeLogSeries_hasSum (x : K) (hx : ‖x‖ < 1) :
    HasSum (negativeLogTerm x) (negativeLogSeries x) :=
  (negativeLogSeries_summable (p := p) x hx).hasSum

/-- `log(1+0) = 0`（级数在 0 处取值 0）。 -/
theorem negativeLogSeries_zero : negativeLogSeries (0 : K) = 0 := by
  have h : (fun n : ℕ => negativeLogTerm (0 : K) n) = fun _ => 0 := by
    funext n
    simp [negativeLogTerm]
  simp [negativeLogSeries, h]

include localNormedAlgebra in
/-- 连续（闭球 `‖x‖ ≤ r`，`r < 1`）：一致优界 + `continuousOn_tsum`。 -/
theorem negativeLogSeries_continuousOn_closedBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (negativeLogSeries) (Metric.closedBall (0 : K) r) := by
  change ContinuousOn (fun x => ∑' n, negativeLogTerm x n) (Metric.closedBall (0 : K) r)
  refine continuousOn_tsum (f := fun n (x : K) => negativeLogTerm x n)
    (u := MonoAnalyticLogShellPadicLog.padicLogMajorant r)
    (s := Metric.closedBall (0 : K) r) ?_ ?_ ?_
  · intro n
    have hc : Continuous fun x : K =>
        ((-1 : K) ^ (n + 1) * x ^ (n + 1)) / (n + 1 : K) := by
      fun_prop
    exact hc.continuousOn
  · exact MonoAnalyticLogShellPadicLog.padicLogMajorant_summable hr0 hr1
  · intro n x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact negativeLogTerm_norm_le (p := p) x hr0 hx n

include localNormedAlgebra in
/-- 连续（开单位球）：逐点用闭球版本局部化（`continuousOn_of_locally_continuousOn`）。 -/
theorem negativeLogSeries_continuousOn_ball :
    ContinuousOn (negativeLogSeries) (Metric.ball (0 : K) 1) := by
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  rw [Metric.mem_ball, dist_zero_right] at hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  refine ⟨Metric.ball (0 : K) r, Metric.isOpen_ball, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    exact hxr
  · refine (negativeLogSeries_continuousOn_closedBall (p := p)
      (le_of_lt (lt_of_le_of_lt (norm_nonneg x) hxr)) hr1).mono ?_
    intro y hy
    have hy2 : y ∈ Metric.ball (0 : K) r := hy.2
    rw [Metric.mem_ball, dist_zero_right] at hy2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hy2

include localNormedAlgebra in
/-- 逐点连续（`‖x‖ < 1`）。 -/
theorem negativeLogSeries_continuousAt_of_norm_lt_one (x : K) (hx : ‖x‖ < 1) :
    ContinuousAt (negativeLogSeries) x := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 ≤ r := le_of_lt (lt_of_le_of_lt (norm_nonneg x) hxr)
  have hcont := negativeLogSeries_continuousOn_closedBall (K := K) (p := p) hr0 hr1
  have hmem : Metric.closedBall (0 : K) r ∈ 𝓝 x := by
    have hball : Metric.ball (0 : K) r ∈ 𝓝 x :=
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


variable [IsUltrametricDist K]

/-- 双项代换序列 `(x+y)·X + (x*y)·X²`，其“在 1 处取值”为 `x + y + x*y`。 -/
noncomputable def twoTermArgSeries (x y : K) : PowerSeries K :=
  PowerSeries.C (x + y) * PowerSeries.X + PowerSeries.C (x * y) * PowerSeries.X ^ 2

theorem constantCoeff_twoTermArgSeries (x y : K) :
    PowerSeries.constantCoeff (twoTermArgSeries x y) = 0 := by
  rw [twoTermArgSeries, map_add, map_mul, map_mul, map_pow,
    PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X]
  ring

/-- 单参数代换 `logSubstOne z = log.subst (z·X)`，返回类型固定为 `PowerSeries`，避免 τ 元变量。 -/
noncomputable def logSubstOne (z : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C z * PowerSeries.X) (PowerSeries.log K)

/-- 双项代换 `logSubstTwo x y = log.subst (twoTermArgSeries x y)`。 -/
noncomputable def logSubstTwo (x y : K) : PowerSeries K :=
  PowerSeries.subst (twoTermArgSeries x y) (PowerSeries.log K)

include localNormedAlgebra in
/-- 冻结级数按 `k = n + 1` 重指标的桥：`∑ c_k z^k = -negativeLogSeries z`（`c_k = log 系数`）。 -/
theorem hasSum_logCoeff_mul_pow (z : K) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (PowerSeries.log K).coeff k * z ^ k) (-(negativeLogSeries z)) := by
  have h0 : HasSum (fun n : ℕ => -negativeLogTerm z n) (-(negativeLogSeries z)) :=
    (negativeLogSeries_hasSum (p := p) z hz).neg
  have hterm : ∀ n : ℕ,
      -negativeLogTerm z n = (PowerSeries.log K).coeff (n + 1) * z ^ (n + 1) := by
    intro n
    rw [negativeLogTerm, localFormalLog_coeff, if_neg (Nat.succ_ne_zero n),
      div_eq_mul_inv, div_eq_mul_inv]
    have hp : (-1 : K) ^ (n + 1 + 1) = -((-1 : K) ^ (n + 1)) := by
      rw [pow_succ]
      ring
    rw [hp]
    push_cast
    ring
  have h1 : HasSum (fun n : ℕ => (PowerSeries.log K).coeff (n + 1) * z ^ (n + 1))
      (-(negativeLogSeries z)) := by
    simpa only [hterm] using h0
  have hf0 : (PowerSeries.log K).coeff 0 * z ^ 0 = 0 := by
    rw [localFormalLog_coeff]
    simp
  have := (hasSum_nat_add_iff
    (f := fun k : ℕ => (PowerSeries.log K).coeff k * z ^ k) 1).mp h1
  simpa [Finset.sum_range_succ, hf0] using this

theorem coeff_log_subst_C_mul_X (z : K) (e : ℕ) :
    (logSubstOne z).coeff e = (PowerSeries.log K).coeff e * z ^ e := by
  have h : logSubstOne z = PowerSeries.rescale z (PowerSeries.log K) := by
    rw [logSubstOne, PowerSeries.rescale_eq_subst z (PowerSeries.log K),
      ← PowerSeries.smul_eq_C_mul PowerSeries.X z]
  rw [h, PowerSeries.coeff_rescale]
  exact mul_comm _ _

theorem log_subst_two_term (x y : K) :
    logSubstTwo x y = logSubstOne x + logSubstOne y := by
  have h := logOf_subst_add_mul (A := K)
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

theorem subst_two_term_coeff (x y : K) (e : ℕ) :
    (logSubstTwo x y).coeff e =
      (PowerSeries.log K).coeff e * x ^ e + (PowerSeries.log K).coeff e * y ^ e := by
  rw [log_subst_two_term, map_add, coeff_log_subst_C_mul_X, coeff_log_subst_C_mul_X]

include localNormedAlgebra in
/-- 系数逐项组合：主系数 `A_e` 的级数在 `−S x − S y` 处有 HasSum。 -/
theorem hasSum_mainCoeff (x y : K) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (fun e : ℕ => (logSubstTwo x y).coeff e)
      (-(negativeLogSeries x) - negativeLogSeries y) := by
  have hx' := hasSum_logCoeff_mul_pow (p := p) x hx
  have hy' := hasSum_logCoeff_mul_pow (p := p) y hy
  have h := hx'.add hy'
  have hfun : (fun e : ℕ => (PowerSeries.log K).coeff e * x ^ e +
        (PowerSeries.log K).coeff e * y ^ e) =
      fun e : ℕ => (logSubstTwo x y).coeff e :=
    funext fun e => (subst_two_term_coeff x y e).symm
  rw [hfun] at h
  simpa [sub_eq_add_neg] using h

/-- 二项展开：`w^m` 的逐单项式（monomial）分解。 -/
theorem twoTermArgSeries_pow_expand (x y : K) (m : ℕ) :
    twoTermArgSeries x y ^ m =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.C ((m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j)) *
          PowerSeries.X ^ (m + j) := by
  have h1 : twoTermArgSeries x y =
      PowerSeries.X * (PowerSeries.C (x * y) * PowerSeries.X + PowerSeries.C (x + y)) := by
    rw [twoTermArgSeries]
    ring
  have hv : (PowerSeries.C (x * y) * PowerSeries.X + PowerSeries.C (x + y) :
        PowerSeries K) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.C ((m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j)) *
          PowerSeries.X ^ j := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← map_pow, ← map_pow]
    rw [show ((m.choose j : ℕ) : PowerSeries K) =
        PowerSeries.C ((m.choose j : ℕ) : K) from
      (map_natCast PowerSeries.C (m.choose j)).symm]
    calc PowerSeries.C ((x * y) ^ j) * PowerSeries.X ^ j * PowerSeries.C ((x + y) ^ (m - j)) *
            PowerSeries.C ((m.choose j : ℕ) : K)
        = PowerSeries.C ((x * y) ^ j) * PowerSeries.C ((x + y) ^ (m - j)) *
            PowerSeries.C ((m.choose j : ℕ) : K) * PowerSeries.X ^ j := by ring
      _ = PowerSeries.C (((x * y) ^ j) *
            (((x + y) ^ (m - j)) * ((m.choose j : ℕ) : K))) *
            PowerSeries.X ^ j := by
          rw [← map_mul, ← map_mul]
          rw [show ((x * y) ^ j * (x + y) ^ (m - j) * ((m.choose j : ℕ) : K)) =
              ((x * y) ^ j * ((x + y) ^ (m - j) * ((m.choose j : ℕ) : K))) from by ring]
      _ = PowerSeries.C ((m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j)) *
            PowerSeries.X ^ j := by
          rw [show ((x * y) ^ j) * (((x + y) ^ (m - j)) * ((m.choose j : ℕ) : K)) =
              (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) from by ring]
  rw [h1, mul_pow, hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- 系数公式（j-和形式）：`coeff e (w^m) = ∑_j [e = m+j] C(m,j)·s^{m−j}·t^j`。 -/
theorem coeff_twoTermArgSeries_pow (x y : K) (m e : ℕ) :
    (twoTermArgSeries x y ^ m).coeff e =
      ∑ j ∈ Finset.range (m + 1),
        if e = m + j then (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 := by
  rw [twoTermArgSeries_pow_expand, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PowerSeries.coeff_C_mul_X_pow]

theorem coeff_twoTermArgSeries_pow_eq_zero_of_lt {x y : K} {m e : ℕ} (he : e < m) :
    (twoTermArgSeries x y ^ m).coeff e = 0 := by
  rw [coeff_twoTermArgSeries_pow]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg]
  omega

/-- 截断系数和：`∑_{e≤E} coeff e (w^m)` 的显式有限表达式。 -/
theorem sum_coeff_twoTermArgSeries_pow (x y : K) (m E : ℕ) :
    ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e =
      ∑ j ∈ Finset.range (m + 1),
        if m + j ≤ E then (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 := by
  calc ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e
      = ∑ e ∈ Finset.range (E + 1), ∑ j ∈ Finset.range (m + 1),
          if e = m + j then (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 :=
        Finset.sum_congr rfl fun e _ => coeff_twoTermArgSeries_pow x y m e
    _ = ∑ j ∈ Finset.range (m + 1), ∑ e ∈ Finset.range (E + 1),
          if e = m + j then (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.range (m + 1),
          if m + j ∈ Finset.range (E + 1) then
            (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 :=
        Finset.sum_congr rfl fun j _ =>
          Finset.sum_ite_eq' (Finset.range (E + 1)) (m + j)
            fun _ => (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j)
    _ = ∑ j ∈ Finset.range (m + 1),
          if m + j ≤ E then (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0 :=
        Finset.sum_congr rfl fun j _ => by simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- 截断系数和的定值：`2m ≤ E` 时等于 `(x+y+x*y)^m`（“在 1 处取值”）。 -/
theorem sum_coeff_twoTermArgSeries_pow_eq (x y : K) (m : ℕ) {E : ℕ} (hE : 2 * m ≤ E) :
    ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e = (x + y + x * y) ^ m := by
  rw [sum_coeff_twoTermArgSeries_pow]
  have hall : ∀ j ∈ Finset.range (m + 1), m + j ≤ E := by
    intro j hj
    rw [Finset.mem_range] at hj
    omega
  have hsimp : (∑ j ∈ Finset.range (m + 1),
        if m + j ≤ E then (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0) =
      ∑ j ∈ Finset.range (m + 1),
        (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) :=
    Finset.sum_congr rfl fun j hj => if_pos (hall j hj)
  rw [hsimp, add_pow]
  conv_rhs => rw [← Finset.sum_range_reflect
    (fun q => (x + y) ^ q * (x * y) ^ (m - q) * ((m.choose q : ℕ) : K)) (m + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : m + 1 - 1 - j = m - j := by omega
  have h2 : m - (m - j) = j := by omega
  rw [h1, h2, Nat.choose_symm (by omega : j ≤ m)]
  ring

/-- 超度量有限和最大范数引理。 -/
theorem norm_finsetSum_le_of_le_max {ι : Type*} (f : ι → K) (s : Finset ι) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ s, ‖f i‖ ≤ M) : ‖∑ i ∈ s, f i‖ ≤ M := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hM
  | insert a s ha ih =>
      have h' : ∀ i ∈ s, ‖f i‖ ≤ M := fun i hi => h i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha]
      exact le_trans (IsUltrametricDist.norm_add_le_max (f a) (∑ i ∈ s, f i))
        (max_le (h a (Finset.mem_insert_self a s)) (ih h'))

include localNormedAlgebra in
/-- 一致范数上界：`‖∑_{e≤E} coeff e (w^m)‖ ≤ M^m`，`M = max ‖s‖ ‖t‖`。 -/
theorem norm_sum_coeff_twoTermArgSeries_pow_le (x y : K) (m E : ℕ) :
    ‖∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e‖ ≤
      (max ‖x + y‖ ‖x * y‖) ^ m := by
  rw [sum_coeff_twoTermArgSeries_pow]
  have hmaxnn : 0 ≤ max ‖x + y‖ ‖x * y‖ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hle : ∀ j ∈ Finset.range (m + 1),
      ‖(if m + j ≤ E then
          (m.choose j : K) * ((x + y) ^ (m - j) * (x * y) ^ j) else 0)‖ ≤
        (max ‖x + y‖ ‖x * y‖) ^ m := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases h : m + j ≤ E
    · rw [if_pos h, norm_mul]
      have hc : ‖(m.choose j : K)‖ ≤ 1 := by
        exact localLog_norm_natCast_le_one (p := p) (m.choose j)
      have h1 : ‖(x + y) ^ (m - j) * (x * y) ^ j‖ ≤ (max ‖x + y‖ ‖x * y‖) ^ m := by
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖x + y‖ ^ (m - j) * ‖x * y‖ ^ j
            ≤ (max ‖x + y‖ ‖x * y‖) ^ (m - j) * (max ‖x + y‖ ‖x * y‖) ^ j :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
                (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _)
                (pow_nonneg (norm_nonneg _) _) (pow_nonneg hmaxnn _)
          _ = (max ‖x + y‖ ‖x * y‖) ^ m := by
              rw [← pow_add, show m - j + j = m by omega]
      calc ‖(m.choose j : K)‖ * ‖(x + y) ^ (m - j) * (x * y) ^ j‖
          ≤ 1 * (max ‖x + y‖ ‖x * y‖) ^ m :=
            mul_le_mul hc h1 (norm_nonneg _) zero_le_one
        _ = (max ‖x + y‖ ‖x * y‖) ^ m := one_mul _
    · rw [if_neg h, norm_zero]
      positivity
  exact norm_finsetSum_le_of_le_max _ _ (pow_nonneg hmaxnn m) hle

/-- 部分和恒等式：主级数部分和 = 对 `m` 的截断系数和之和（三角交换）。 -/
theorem sum_mainCoeff_eq_partial (x y : K) (E : ℕ) :
    ∑ e ∈ Finset.range (E + 1), (logSubstTwo x y).coeff e =
      ∑ m ∈ Finset.range (E + 1), (PowerSeries.log K).coeff m *
        ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e := by
  have hw : PowerSeries.HasSubst (twoTermArgSeries x y) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_twoTermArgSeries x y)
  have hstep : ∀ e : ℕ,
      (logSubstTwo x y).coeff e =
        ∑ m ∈ Finset.range (e + 1),
          (PowerSeries.log K).coeff m * (twoTermArgSeries x y ^ m).coeff e := by
    intro e
    rw [logSubstTwo, PowerSeries.coeff_subst' hw]
    have hsupp : Function.support (fun m : ℕ => (PowerSeries.log K).coeff m •
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
          (PowerSeries.log K).coeff m * (twoTermArgSeries x y ^ m).coeff e :=
        Finset.sum_congr rfl fun e _ => hstep e
    _ = ∑ e ∈ Finset.range (E + 1), ∑ m ∈ Finset.range (E + 1),
          (PowerSeries.log K).coeff m * (twoTermArgSeries x y ^ m).coeff e := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [Finset.mem_range] at he
        refine Finset.sum_subset (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega) ?_
        intro m hmE hme
        rw [Finset.mem_range, not_lt] at hme
        rw [coeff_twoTermArgSeries_pow_eq_zero_of_lt (by omega : e < m)]
        simp
    _ = ∑ m ∈ Finset.range (E + 1), (PowerSeries.log K).coeff m *
          ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]

include localNormedAlgebra in
/-- 误差项（截断和 − 极限值）趋于 0：尾部几何估计。 -/
theorem tendsto_error_partial (x y : K) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Filter.Tendsto (fun E : ℕ => ∑ m ∈ Finset.range (E + 1),
        (PowerSeries.log K).coeff m *
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
  let Q : ℕ → ℕ → K :=
    fun E m => ∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e
  let F : ℕ → ℕ → K :=
    fun E m => (PowerSeries.log K).coeff m * (Q E m - (x + y + x * y) ^ m)
  have hterm : ∀ E m, ‖F E m‖ ≤ (m : ℝ) * M' ^ m + (m : ℝ) * M' ^ m := by
    intro E m
    change ‖(PowerSeries.log K).coeff m * (Q E m - (x + y + x * y) ^ m)‖ ≤
      (m : ℝ) * M' ^ m + (m : ℝ) * M' ^ m
    have hcm : ‖(PowerSeries.log K).coeff m‖ ≤ (m : ℝ) := by
      rw [localFormalLog_coeff]
      by_cases hm0 : m = 0
      · rw [if_pos hm0]
        simp
      · rw [if_neg hm0, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
        exact localLog_denom_norm_inv_le (p := p) hm0
    have hQ : ‖Q E m‖ ≤ M' ^ m := by
      change ‖(∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e)‖ ≤ M' ^ m
      refine le_trans (norm_sum_coeff_twoTermArgSeries_pow_le (p := p) x y m E) ?_
      exact pow_le_pow_left₀ (le_trans (norm_nonneg (x + y)) (le_max_left _ _))
        (by rw [hM'def]; exact le_max_left _ _) m
    have hsig_m : ‖(x + y + x * y) ^ m‖ ≤ M' ^ m := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (by rw [hM'def]; exact le_max_right _ _) m
    calc ‖(PowerSeries.log K).coeff m * (Q E m - (x + y + x * y) ^ m)‖
        = ‖(PowerSeries.log K).coeff m‖ * ‖Q E m - (x + y + x * y) ^ m‖ := norm_mul _ _
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
    change (PowerSeries.log K).coeff m * (Q E m - (x + y + x * y) ^ m) = 0
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

include localNormedAlgebra in
/-- 主级数部分和收敛到 `−negativeLogSeries (x+y+x*y)`。 -/
theorem tendsto_sum_mainCoeff (x y : K) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Filter.Tendsto (fun E : ℕ => ∑ e ∈ Finset.range E,
        (logSubstTwo x y).coeff e) atTop
      (𝓝 (-(negativeLogSeries (x + y + x * y)))) := by
  have hsig : ‖x + y + x * y‖ < 1 := by
    have hxy : ‖x * y‖ < 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg x, norm_nonneg y]
    have hs : ‖x + y‖ < 1 :=
      lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max (x + y) (x * y)) (max_lt hs hxy)
  have hT : Filter.Tendsto (fun E : ℕ => ∑ m ∈ Finset.range (E + 1),
      (PowerSeries.log K).coeff m * (x + y + x * y) ^ m) atTop
      (𝓝 (-(negativeLogSeries (x + y + x * y)))) :=
    ((hasSum_logCoeff_mul_pow (p := p) (x + y + x * y) hsig).tendsto_sum_nat).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hB := tendsto_error_partial (p := p) x y hx hy
  have hpoint : ∀ E : ℕ,
      ∑ e ∈ Finset.range (E + 1),
          (logSubstTwo x y).coeff e
        = (∑ m ∈ Finset.range (E + 1), (PowerSeries.log K).coeff m * (x + y + x * y) ^ m)
          + (∑ m ∈ Finset.range (E + 1), (PowerSeries.log K).coeff m *
              ((∑ e ∈ Finset.range (E + 1), (twoTermArgSeries x y ^ m).coeff e) -
                (x + y + x * y) ^ m)) := by
    intro E
    rw [sum_mainCoeff_eq_partial, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hmain : Filter.Tendsto (fun E : ℕ => ∑ e ∈ Finset.range (E + 1),
      (logSubstTwo x y).coeff e) atTop
      (𝓝 (-(negativeLogSeries (x + y + x * y)))) := by
    have hsum := hT.add hB
    rw [add_zero] at hsum
    exact Filter.Tendsto.congr' (Eventually.of_forall fun E => (hpoint E).symm) hsum
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => ∑ e ∈ Finset.range n,
    (logSubstTwo x y).coeff e) 1).mp hmain

include localNormedAlgebra in
/-- **数值乘性定理（B' 主定理）**：`‖x‖<1, ‖y‖<1` 时
`negativeLogSeries (x+y+x*y) = negativeLogSeries x + negativeLogSeries y`。 -/
theorem negativeLogSeries_add_mul (x y : K) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    negativeLogSeries (x + y + x * y) = negativeLogSeries x + negativeLogSeries y := by
  have hmul := hasSum_mainCoeff (p := p) x y hx hy
  have hsumm := hmul.summable
  have h2 : HasSum (fun e : ℕ => (logSubstTwo x y).coeff e)
      (-(negativeLogSeries (x + y + x * y))) :=
    (Summable.hasSum_iff_tendsto_nat hsumm).mpr (tendsto_sum_mainCoeff (p := p) x y hx hy)
  have hval : -(negativeLogSeries x) - negativeLogSeries y =
      -(negativeLogSeries (x + y + x * y)) := hmul.unique h2
  have key : -(negativeLogSeries x) - negativeLogSeries y =
      -(negativeLogSeries x + negativeLogSeries y) := by
    rw [neg_add]
    ring
  exact (neg_inj.mp (key.symm.trans hval)).symm


theorem log1p_zero : log1p (0 : K) = 0 := by
  simp [log1p, negativeLogSeries_zero]

include localNormedAlgebra in
theorem log1p_continuousOn_ball :
    ContinuousOn (log1p : K → K) (Metric.ball (0 : K) 1) :=
  (negativeLogSeries_continuousOn_ball (p := p)).neg

include localNormedAlgebra in
theorem log1p_add_mul (x y : K) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    log1p (x + y + x * y) = log1p x + log1p y := by
  rw [log1p, negativeLogSeries_add_mul (p := p) x y hx hy, neg_add]
  rfl

include localNormedAlgebra in
/-- The actual analytic logarithm commutes with isometric field maps.
This is the source equivariance needed before taking local Galois invariants. -/
theorem log1p_map {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] (e : K →+* L) (he : Isometry e)
    (x : K) (hx : ‖x‖ < 1) : e (log1p x) = log1p (e x) := by
  have hnorm : ‖e x‖ = ‖x‖ := by
    simpa only [map_zero, dist_zero_right] using he.dist_eq x 0
  have hm := (negativeLogSeries_hasSum (p := p) x hx).map e.toAddMonoidHom he.continuous
  have hterm : (fun n => e (negativeLogTerm x n)) =
      fun n => negativeLogTerm (e x) n := by
    funext n
    simp only [negativeLogTerm, map_div₀, map_mul, map_pow, map_neg, map_one, map_add,
      map_natCast]
  change HasSum (fun n => e (negativeLogTerm x n)) (e (negativeLogSeries x)) at hm
  rw [hterm] at hm
  have hsum := negativeLogSeries_hasSum (p := p) (e x) (hnorm.trans_lt hx)
  unfold log1p
  rw [map_neg, hm.unique hsum]

end LeanFormal.IUT.LocalFieldLogarithm
