/-
# IUT IV §2 落点：卡清单（纯陈述 + 具名卡）+ 已证小额项（Prop 2.1 (i)）

论文出处（行号均为 `papers\motizuki_corpus\text\Inter-universal Teichmuller Theory IV.txt` 的行）：
§2 范围 L2329–3663（L2330–2332：§2 目标 = 由 Thm 1.10 + [GenEll] 理论给出 ABC 猜想
（等价地 Vojta 猜想）的证明，见 Cor 2.3）。

## §2 卡清单（逐条）

1. Prop 2.1（L2334）：Well-known Estimates。
   (i)（L2335）Linearization of Logarithms：log(x) ≤ x（∀ x ≥ 1）。
       [proved] `iutIVProp21i_log_le_self`（本文件；论文证明："entirely elementary"，L2356）。
   (ii)（L2336–2355）The Prime Number Theorem：存在实数 ξprm ≥ 5，使 ∀x ≥ ξprm，
        (2/3)·x ≤ θ(x) ≤ (4/3)·x，其中 θ(x) := Σ_{p≤x} log(p)（对素数求和）；
        且对有限素集 A（θ_A := Σ_{p∈A} log p，空集取 0）存在素数 p ∉ A，p ≤ 2(θ_A + ξprm)。
       [machine-gap] 需要 θ（Chebyshev 函数）与显式 Chebyshev 界；Mathlib 现有 PNT 渐近
       不足以给出此显式常数形式。数值版本见 Explicit estimates Prop 2.2（该文 L1078：
       ηprm = 5·10^20、ξprm = 10^15、π(x) ≤ 1.022x/log x、|θ(x)−x| ≤ 0.00071x）。
       缩减显式标注：本仓库未形式化任何显式 PNT 界；(ii) 属大机器卡。
2. Cor 2.2（L2380–2530）：Construction of Suitable Initial Θ-Data。设定（L2380–2400）：
   X = P^1_Q（λ-线）、D = {0,1,∞}、K_V ⊆ U_X(Q) 紧有界（支撑含非阿基米德素 2）、
   条件 (*j-inv)。断言：
   (i)（L~2410–2478；证明 L2506–2529）BD 类等式链：(1/6)·log(q∤2) ≈ (1/6)·log(q∀)
       ≈ (1/6)·ht∞ ≈ ht_{ωX(D)} on K_V。
   (ii)（L2469–2530）由"EF/Fmod 取自初始 Θ-数据"（L2473–2474）得：
       (C1)（L2475）(log q∀)^{1/2} ≤ l ≤ 10δ·(log q∀)^{1/2}·log(2δ·log q∀)；
       (C2)（L2476–2486）(1/6)log(q) ≤ (1/6)log(q∤2) ≤ (1/6)log(q∀)
            ≤ (1+ε_E)·(log-diff_X(x_E)+log-cond_D(x_E)) + C_K，
            其中 ε_E := (60δ)^2·log(2δ·(log q∀))/(log q∀)^{1/2}（L2483–2486；依赖 d 与 E_F）；
            并注意 log-diff_X(x_E) = log(d_{F_tpd})，log(f_{F_tpd}) ≤ log-cond_D(x_E)
            ≤ log(f_{F_tpd}) + log(2l)（L2491–2493）。
       存在 H_unif（与 K_V 无关）、C_K、H_K（仅依赖 K_V）（L2494–2495 语境）。
   (iii)（L2494–2505）例外集版本：∃ Exc_{ε,d} ⊆ U_X(Q)^{≤d}（仅依赖 K_V、ε、d、ε_d），
        log(q∀(−)) ≤ H_unif·ε^{−3}·ε_d^{−3}·d^{4+ε_d} + H_K on Exc_{ε,d}；
        且 x_E ∉ Exc_{ε,d} ⇒ ε_E ≤ ε。
   [machine-gap] 依赖 Thm 1.10（log-volume 层）、[GenEll] 的 log-diff/log-cond/ht 高度函数层、
   椭圆曲线 Legendre 形与 (2θ) 挠点层（Prop 1.8）。缩减显式标注：本仓库未形式化
   [GenEll] 记号与 BD 类；本卡只登记陈述与行号。
3. Cor 2.3（L3117–3128）：Diophantine Inequalities（§2 主定理）。设定：X/k 数域上光滑
   完备几何连通曲线、D 既约、U_X := X∖D、d ≥ 1、ε > 0、ω_X 典范层；U_X 双曲
   （deg ω_X(D) > 0）。结论：BD 类不等式 ht_{ωX(D)} ≲ (1+ε)(log-diff_X + log-cond_D)
   on U_X(Q)^{≤d}，即 (1+ε)(log-diff_X+log-cond_D) − ht_{ωX(D)} 在 U_X(Q)^{≤d} 上有下界
   （[GenEll] Def 1.2 (ii) 意义下）。证明（L3129–3155）归约到 [GenEll] Thm 2.1
   （X = P^1_Q、D = {0,1,∞}、K_V 情形），用 Cor 2.2 (i) 的 BD 等式 + (ii)(C2) + (iii)。
   [machine-gap] 依赖 Cor 2.2 全量 + [GenEll] Thm 2.1 等价归约。
4. Remarks 2.2.1–2.2.4（L2806/2922/2982/2996）、2.3.1–2.3.5（L3156/3213/3243/3526/3539）：
   说明与勘误（Remark 2.3.1 含 [GenEll] 订正），不单列机器。

## 缩减显式标注（总）
- 本文件不含任何未证断言；仅 (i) 为已证定理，其余为登记卡。
- ε_E、C_K、H_K、H_unif 等的存在性从属于 Thm 1.10 / Cor 3.12 的显式化（Step XI 墙），
  与 Cor 2.2 的"构造"语义一致（消费者：cor312-to-ABC 归约）。

## 更新（2026-10-17，Tao）：卡1(ii) 下界半边 + "In particular" 无条件落地
- 已证 `iutIVProp21ii_theta_ge_two_thirds_eventually`：∃ ξ ≥ 5，∀ x ≥ ξ，(2/3)·x ≤ θ(x)。
  这是论文 (ii) 双侧不等式（L2336–2345）的下界半边，常数 2/3 与原文一致；证明经 Mathlib
  `Chebyshev.theta_ge'`（θ(x) ≥ (x−1)log 2 − log(x+2) − 2√x·log x）与 log =o(x)、log =o(√x)，
  用 log 2 > 2/3（Real.log_two_gt_d9）的斜率余量。原文注记：断言来自 PNT（L2356–2358）。
- 已证 `iutIVProp21ii_prime_notMem_of_theta_lower`（参数化）与
  `iutIVProp21ii_exists_prime_notMem_le_two_mul`（∃ ξ 形态）：对有限素集 A，
  ∃ 素数 p ∉ A，p ≤ 2(θ_A + ξ)。对应 L2347–2355 的 "In particular"。
  注解：该推论的反证只需下界半边（反设全部 ≤ 2(θ_A+ξ) 之素数 ∈ A ⇒ θ(2(θ_A+ξ)) ≤ θ_A，
  与 (2/3)·2(θ_A+ξ) ≤ θ(2(θ_A+ξ)) 及 θ_A ≥ 0、ξ ≥ 5 矛盾）。
- PARK 卡（卡1(ii) 上界半边）：θ(x) ≤ (4/3)·x for x ≥ ξ。阻塞：Mathlib v4.32.2 无 PNT
  （无 θ ~ x / IsEquivalent 形态），现有最强 `Chebyshev.theta_le_log4_mul_x` 为
  θ ≤ log 4·x ≈ 1.3863x（距 4/3 差约 0.053x），`psi_le` 主项同为 log 4；比值 2 窗递推
  （ψ(2m)−ψ(m) ≤ 2m·log 2 沿二进位尺度求和）的主常数恰为 log 4（每窗修正仅 O(log)，
  总和 O(log²)），改进需多比值二项式 LP（Diamond–Erdős 型常数 ~1.10555）或 PNT，
  二者均未形式化。接口请求（任一）：`Tendsto (fun x ↦ Chebyshev.theta x / x) atTop (𝓝 1)`
  或 `∀ᶠ x in atTop, Chebyshev.theta x ≤ (4/3)·x`。

## 更新（2026-10-17，root 单 agent）：卡1(ii) 上界半边 PARK 解除
- 上文 PARK 判断"改进需 PNT 或多比值 LP"不成立：上界只需 θ ≤ c·x（c < 4/3），初等即可。
- 已证 `theta_sixfold_window_le`：θ(6n) ≤ θ(n) + 9n·log 2。证明：N := C(6n,3n)·C(3n,n)
  = (6n)!/((3n)!(2n)!n!)；Legendre 公式 + 逐项 ⌊t/2⌋+⌊t/3⌋+⌊t/6⌋ ≤ t（1≤t≤5 严格）⇒ (n,6n] 中
  每个素数整除 N；N ≤ 2^{6n}·2^{3n}。
- 已证 `theta_le_thirteen_tenths_mul_add`：∀ x ≥ 0，θ(x) ≤ (13/10)x + 300（递推；9 log 2/5 ≈ 1.2477 < 1.3）。
- 已证 `iutIVProp21ii_theta_le_four_thirds_eventually`（ξ = 9000）与双侧
  `iutIVProp21ii_theta_two_sided_eventually`：∃ ξ ≥ 5，∀ x ≥ ξ，(2/3)x ≤ θ(x) ≤ (4/3)x（论文常数忠实）。
- 边界：只给 ξ 存在，不给论文以外的显式 PNT 数值；Explicit estimates Prop 2.2 的数值版未涉及。

## 更新（2026-10-17，root 单 agent）：IUT IV §1 Prop 1.6 亦已证（落于本文件）
- `iutIVProp16_primeCounting_le_four_thirds_eventually`：∃ ηprm > 0，∀ η ≥ ηprm，π(η) ≤ 4η/(3 log η)。
- `iutIVProp16_index_le_four_thirds_nthPrime`：∃ n₀，∀ n ≥ n₀，(n+1) ≤ 4p/(3 log p)，p = nth Prime n。
- 依赖：θ(x) ≤ 1.3x + 300（上节）＋ Mathlib Abel 求和（`primeCounting_eq_theta_div_log_add_integral`、
  `integral_theta_div_log_sq_isLittleO`）。放在本文件是因为 θ 界在此；Section1 卡6 的文字保留。

-/

import LeanFormal.IUT.Audit.Status
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Bounds

namespace LeanFormal.IUT.Audit

def iutIVSection2 : Obligation :=
  { id := "IUT-IV.section-2"
    source := "IUT IV, Section 2"
    status := VerificationStatus.pending
    note := "The explicit estimates remain downstream of Corollary 3.12." }

end LeanFormal.IUT.Audit

namespace LeanFormal.IUT.IUTIV.Estimates

/-- Prop 2.1 (i)（L2335）：x ≥ 1 ⇒ log x ≤ x。论文："well-known and entirely elementary"。 -/
theorem iutIVProp21i_log_le_self (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ x := by
  have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hx)
  linarith


open Filter
open Real


/-- Prop 2.1 (ii) 下界半边（L2336–2345）：∃ ξ ≥ 5，∀ x ≥ ξ，(2/3)·x ≤ θ(x)，其中
θ = Chebyshev.theta（θ(x) = Σ_{p≤x} log p，与 Mathlib `Chebyshev.theta_eq_sum_primesLE` 一致）。
论文原文为双侧 (2/3)·x ≤ θ(x) ≤ (4/3)·x；本定理是无条件落地的下界一半（常数忠实），
上界半边 PARK（见文件头更新块）。证明：`Chebyshev.theta_ge'`（L504–507）加两个初等渐近。 -/
theorem iutIVProp21ii_theta_ge_two_thirds_eventually :
    ∃ ξ : ℝ, 5 ≤ ξ ∧ ∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x := by
  set c : ℝ := Real.log 2 - 2 / 3 with hc
  have hc_pos : 0 < c := by
    rw [hc]
    linarith [Real.log_two_gt_d9]
  have hEa : ∀ᶠ x : ℝ in atTop, Real.log x ≤ c / 4 * x := by
    filter_upwards [Real.isLittleO_log_id_atTop.bound (show 0 < c / 4 by linarith),
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [show id x = x from rfl] at hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hx
    exact hx
  have hEb : ∀ᶠ x : ℝ in atTop, 2 * Real.log 2 ≤ c / 4 * x := by
    filter_upwards [Filter.eventually_ge_atTop (8 * Real.log 2 / c)] with x hx
    have hconst : c / 4 * (8 * Real.log 2 / c) = 2 * Real.log 2 := by
      field_simp [hc_pos.ne']
      ring
    rw [← hconst]
    exact mul_le_mul_of_nonneg_left hx (by linarith)
  have hEc : ∀ᶠ x : ℝ in atTop, Real.log x ≤ c / 4 * Real.sqrt x := by
    have hlog_sqrt : Real.log =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num)
    filter_upwards [hlog_sqrt.bound (show 0 < c / 4 by linarith),
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)] at hx
    rwa [Real.sqrt_eq_rpow]
  have hev : ∀ᶠ x : ℝ in atTop, 2 / 3 * x ≤ Chebyshev.theta x := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hEa, hEb, hEc]
      with x hx2 hlogx hlog2 hlogsqrt
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hsq : Real.sqrt x * Real.sqrt x = x := by
      rw [← pow_two, Real.sq_sqrt hx0]
    have hterm2 : 2 * Real.sqrt x * Real.log x ≤ c / 2 * x := by
      have h2sx : (0 : ℝ) ≤ 2 * Real.sqrt x := by positivity
      calc 2 * Real.sqrt x * Real.log x ≤ 2 * Real.sqrt x * (c / 4 * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hlogsqrt h2sx
        _ = c / 2 * (Real.sqrt x * Real.sqrt x) := by ring
        _ = c / 2 * x := by rw [hsq]
    have hterm1 : Real.log (x + 2) + Real.log 2 ≤ c / 2 * x := by
      have h2x : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
        have hle : Real.log (x + 2) ≤ Real.log (2 * x) :=
          Real.log_le_log (by linarith) (by linarith)
        rwa [Real.log_mul (by norm_num) (by linarith : x ≠ 0)] at hle
      linarith
    have key : Real.log 2 + (Real.log (x + 2) + 2 * Real.sqrt x * Real.log x) ≤ c * x := by
      linarith
    have hident :
        (x - 1) * Real.log 2 - Real.log (x + 2) - 2 * Real.sqrt x * Real.log x - 2 / 3 * x
          = c * x - (Real.log 2 + (Real.log (x + 2) + 2 * Real.sqrt x * Real.log x)) := by
      rw [hc]
      ring
    have hfinal :
        2 / 3 * x ≤ (x - 1) * Real.log 2 - Real.log (x + 2) - 2 * Real.sqrt x * Real.log x := by
      linarith
    exact hfinal.trans (Chebyshev.theta_ge' hx1)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max a 5, le_max_right a 5, fun x hx => ha x (le_trans (le_max_left a 5) hx)⟩

/-- Prop 2.1 (ii) "In particular"（L2347–2355）参数化形态：给定下界半边假设
（∃ 常数 ξ ≥ 5 使 ∀ x ≥ ξ，(2/3)·x ≤ θ(x)），对任意有限素集 A 存在素数 p ∉ A
满足 p ≤ 2(θ_A + ξ)，θ_A := Σ_{q∈A} log q（空集为 0）。反证只用下界半边：
若全部 ≤ 2(θ_A+ξ) 之素数 ∈ A 则 θ(2(θ_A+ξ)) ≤ θ_A，与 (2/3)·2(θ_A+ξ) ≤ θ(2(θ_A+ξ))
及 θ_A ≥ 0、ξ ≥ 5 矛盾。 -/
theorem iutIVProp21ii_prime_notMem_of_theta_lower
    (ξ : ℝ) (hξ : 5 ≤ ξ)
    (hθ : ∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x)
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    ∃ p : ℕ, p.Prime ∧ p ∉ A ∧ (p : ℝ) ≤ 2 * ((∑ q ∈ A, Real.log q) + ξ) := by
  by_contra hcon
  push Not at hcon
  have hlog_nonneg : ∀ q ∈ A, (0 : ℝ) ≤ Real.log q := fun q hq =>
    Real.log_nonneg (by
      have h2 := (hA q hq).two_le
      exact_mod_cast (show 1 ≤ q by omega))
  have hsum_nonneg : (0 : ℝ) ≤ ∑ q ∈ A, Real.log q := Finset.sum_nonneg hlog_nonneg
  have hB_ge : ξ ≤ 2 * ((∑ q ∈ A, Real.log q) + ξ) := by linarith
  have hθB_le : Chebyshev.theta (2 * ((∑ q ∈ A, Real.log q) + ξ)) ≤ ∑ q ∈ A, Real.log q := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Nat.mem_primesLE] at hp
      by_contra hpA
      have hlt : 2 * ((∑ q ∈ A, Real.log q) + ξ) < (p : ℝ) := hcon p hp.2 hpA
      have hp_le : (p : ℝ) ≤ 2 * ((∑ q ∈ A, Real.log q) + ξ) := by
        have h1 : (p : ℝ) ≤ (⌊2 * ((∑ q ∈ A, Real.log q) + ξ)⌋₊ : ℝ) := by
          exact_mod_cast hp.1
        have h2 : (⌊2 * ((∑ q ∈ A, Real.log q) + ξ)⌋₊ : ℝ) ≤
            2 * ((∑ q ∈ A, Real.log q) + ξ) := Nat.floor_le (by linarith)
        linarith
      linarith
    · intro q hq _
      exact hlog_nonneg q hq
  have hθB_ge : 2 / 3 * (2 * ((∑ q ∈ A, Real.log q) + ξ)) ≤
      Chebyshev.theta (2 * ((∑ q ∈ A, Real.log q) + ξ)) := hθ _ hB_ge
  linarith

/-- Prop 2.1 (ii) "In particular"（L2347–2355）存在形态：∃ ξ ≥ 5，使对每个有限素集 A
存在素数 p ∉ A 满足 p ≤ 2(θ_A + ξ)。由下界半边定理与参数化形态组合。 -/
theorem iutIVProp21ii_exists_prime_notMem_le_two_mul :
    ∃ ξ : ℝ, 5 ≤ ξ ∧ ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∃ p : ℕ, p.Prime ∧ p ∉ A ∧ (p : ℝ) ≤ 2 * ((∑ q ∈ A, Real.log q) + ξ) := by
  obtain ⟨ξ, hξ, hθ⟩ := iutIVProp21ii_theta_ge_two_thirds_eventually
  exact ⟨ξ, hξ, fun A hA => iutIVProp21ii_prime_notMem_of_theta_lower ξ hξ hθ A hA⟩

open Finset
open scoped Nat

/-- Chebyshev six-fold floor inequality: `⌊t/2⌋+⌊t/3⌋+⌊t/6⌋ ≤ t`. -/
lemma sixfold_floor_sum_le (t : ℕ) : t / 2 + t / 3 + t / 6 ≤ t := by omega

/-- Strict form for `1 ≤ t ≤ 5`. -/
lemma sixfold_floor_sum_lt {t : ℕ} (h1 : 1 ≤ t) (h5 : t ≤ 5) :
    t / 2 + t / 3 + t / 6 < t := by omega

/-- Nested-quotient identities `3n/q = ⌊6n/q⌋/2`, `2n/q = ⌊6n/q⌋/3`, `n/q = ⌊6n/q⌋/6`. -/
lemma sixfold_div_eqs (n q : ℕ) :
    3 * n / q = 6 * n / q / 2 ∧ 2 * n / q = 6 * n / q / 3 ∧ n / q = 6 * n / q / 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Nat.div_div_eq_div_mul]
  · rw [show 6 * n = 2 * (3 * n) by ring, mul_comm q 2,
      Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
  · rw [show 6 * n = 3 * (2 * n) by ring, mul_comm q 3,
      Nat.mul_div_mul_left _ _ (by norm_num : 0 < 3)]
  · rw [mul_comm q 6, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 6)]

/-- The integer `C(6n,3n)·C(3n,n) = (6n)!/((3n)!(2n)!n!)`. -/
def sixfoldBinomialProduct (n : ℕ) : ℕ := (6 * n).choose (3 * n) * (3 * n).choose n

lemma sixfoldBinomialProduct_mul_factorials (n : ℕ) :
    sixfoldBinomialProduct n * ((3 * n)! * (2 * n)! * n !) = (6 * n)! := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show 3 * n ≤ 6 * n by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
  rw [show 6 * n - 3 * n = 3 * n by omega] at h1
  rw [show 3 * n - n = 2 * n by omega] at h2
  unfold sixfoldBinomialProduct
  calc _ = (6 * n).choose (3 * n) * ((3 * n).choose n * n ! * (2 * n)!) * (3 * n)! := by ring
    _ = _ := by rw [h2, h1]

lemma sixfoldBinomialProduct_ne_zero (n : ℕ) : sixfoldBinomialProduct n ≠ 0 := by
  unfold sixfoldBinomialProduct
  exact Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'

lemma sixfoldBinomialProduct_le (n : ℕ) : sixfoldBinomialProduct n ≤ 2 ^ (9 * n) := by
  unfold sixfoldBinomialProduct
  calc _ ≤ 2 ^ (6 * n) * 2 ^ (3 * n) :=
        Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ = 2 ^ (9 * n) := by rw [← pow_add]; ring_nf

/-- Every prime `p` with `n < p ≤ 6n` divides `C(6n,3n)·C(3n,n)` (Legendre's formula plus
the six-fold floor inequality). -/
lemma prime_dvd_sixfoldBinomialProduct {n p : ℕ} (hp : p.Prime) (hnp : n < p)
    (hp6 : p ≤ 6 * n) : p ∣ sixfoldBinomialProduct n := by
  set N := sixfoldBinomialProduct n with hNdef
  have hN : N ≠ 0 := sixfoldBinomialProduct_ne_zero n
  have hfac : (6 * n)!.factorization p =
      N.factorization p + ((3 * n)!.factorization p + (2 * n)!.factorization p +
        (n)!.factorization p) := by
    rw [← sixfoldBinomialProduct_mul_factorials n,
      Nat.factorization_mul hN (by positivity), Nat.factorization_mul (by positivity)
        (by positivity), Nat.factorization_mul (by positivity) (by positivity)]
    simp only [Finsupp.coe_add, Pi.add_apply]
  set b := Nat.log p (6 * n) + 1 with hbdef
  have hb6 : Nat.log p (6 * n) < b := Nat.lt_succ_self _
  have hb3 : Nat.log p (3 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6
  have hb2 : Nat.log p (2 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6
  have hb1 : Nat.log p n < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6
  rw [Nat.factorization_factorial hp hb6, Nat.factorization_factorial hp hb3,
    Nat.factorization_factorial hp hb2, Nat.factorization_factorial hp hb1] at hfac
  have hterm : ∀ i ∈ Ico 1 b,
      3 * n / p ^ i + 2 * n / p ^ i + n / p ^ i ≤ 6 * n / p ^ i := by
    intro i _
    obtain ⟨e3, e2, e1⟩ := sixfold_div_eqs n (p ^ i)
    rw [e3, e2, e1]
    exact sixfold_floor_sum_le _
  have hstrict : 3 * n / p ^ 1 + 2 * n / p ^ 1 + n / p ^ 1 < 6 * n / p ^ 1 := by
    obtain ⟨e3, e2, e1⟩ := sixfold_div_eqs n (p ^ 1)
    rw [e3, e2, e1, pow_one]
    apply sixfold_floor_sum_lt
    · exact Nat.div_pos hp6 hp.pos
    · have : 6 * n / p < 6 := (Nat.div_lt_iff_lt_mul hp.pos).2 (by nlinarith)
      omega
  have h1b : 1 ∈ Ico 1 b := by
    rw [mem_Ico]
    exact ⟨le_rfl, by have := Nat.log_pos hp.one_lt hp6; omega⟩
  have hsum := Finset.sum_lt_sum hterm ⟨1, h1b, hstrict⟩
  rw [sum_add_distrib, sum_add_distrib] at hsum
  have hpos : 1 ≤ N.factorization p := by omega
  exact (hp.dvd_iff_one_le_factorization hN).2 hpos

/-- The product of the primes in `(n, 6n]` divides `C(6n,3n)·C(3n,n)`. -/
lemma prod_primes_Ioc_dvd_sixfoldBinomialProduct (n : ℕ) :
    ∏ p ∈ (Ioc n (6 * n)).filter Nat.Prime, p ∣ sixfoldBinomialProduct n := by
  refine Finset.prod_primes_dvd _ (fun p hp => (mem_filter.1 hp).2.prime) ?_
  intro p hp
  obtain ⟨h1, h2⟩ := mem_filter.1 hp
  rw [mem_Ioc] at h1
  exact prime_dvd_sixfoldBinomialProduct h2 h1.1 h1.2

/-- Six-fold Chebyshev window: `θ(6n) ≤ θ(n) + 9n·log 2`. -/
theorem theta_sixfold_window_le (n : ℕ) :
    Chebyshev.theta ((6 * n : ℕ) : ℝ) ≤ Chebyshev.theta (n : ℝ) + 9 * n * Real.log 2 := by
  set S := (Ioc n (6 * n)).filter Nat.Prime with hS
  have hsplit : Chebyshev.theta ((6 * n : ℕ) : ℝ) =
      Chebyshev.theta (n : ℝ) + ∑ p ∈ S, Real.log p := by
    simp only [Chebyshev.theta, Nat.floor_natCast, hS, sum_filter]
    rw [sum_Ioc_consecutive _ (Nat.zero_le n) (by omega : n ≤ 6 * n)]
  have hprod_pos : (0 : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (mem_filter.1 hp).2.pos)
    exact_mod_cast this
  have hlogsum : ∑ p ∈ S, Real.log p = Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (mem_filter.1 hp).2.ne_zero
  have hle : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (9 * n)) := by
    have h1 : ∏ p ∈ S, p ≤ sixfoldBinomialProduct n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (sixfoldBinomialProduct_ne_zero n))
        (prod_primes_Ioc_dvd_sixfoldBinomialProduct n)
    have h2 := (h1.trans (sixfoldBinomialProduct_le n))
    exact_mod_cast h2
  have hlog : Real.log ((∏ p ∈ S, p : ℕ) : ℝ) ≤ 9 * n * Real.log 2 := by
    calc _ ≤ Real.log ((2 : ℝ) ^ (9 * n)) := Real.log_le_log hprod_pos hle
      _ = 9 * n * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  rw [hsplit, hlogsum]
  linarith

/-- Global affine Chebyshev bound `θ(x) ≤ (13/10)·x + 300` for all `x ≥ 0`
(recursion on the six-fold window; `9·log 2 / 5 < 13/10`). -/
theorem theta_le_thirteen_tenths_mul_add (x : ℝ) (hx : 0 ≤ x) :
    Chebyshev.theta x ≤ 13 / 10 * x + 300 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  suffices H : ∀ m : ℕ, ∀ y : ℝ, 0 ≤ y → y < m → Chebyshev.theta y ≤ 13 / 10 * y + 300 by
    exact H (⌈x⌉₊ + 1) x hx (by push_cast; linarith [Nat.le_ceil x])
  intro m
  induction m with
  | zero => intro y hy hym; norm_num at hym; linarith
  | succ m ih =>
    intro y hy hym
    by_cases hsmall : y < 200
    · have h4 := Chebyshev.theta_le_log4_mul_x hy
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      have : Real.log 4 * y ≤ 3 / 2 * y :=
        mul_le_mul_of_nonneg_right (by rw [hlog4]; linarith) hy
      linarith
    · push Not at hsmall
      set n := ⌈y / 6⌉₊ with hn
      have hn1 : y / 6 ≤ n := Nat.le_ceil _
      have hn2 : (n : ℝ) < y / 6 + 1 := Nat.ceil_lt_add_one (by linarith)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hθ1 : Chebyshev.theta y ≤ Chebyshev.theta ((6 * n : ℕ) : ℝ) :=
        Chebyshev.theta_mono (by push_cast; linarith)
      have hθ2 := theta_sixfold_window_le n
      have hθ3 : Chebyshev.theta (n : ℝ) ≤ 13 / 10 * n + 300 :=
        ih n hn0 (by push_cast at hym ⊢; linarith)
      have hprod : Real.log 2 * n ≤ 0.6931471808 * n :=
        mul_le_mul_of_nonneg_right hl2.le hn0
      nlinarith

/-- IUT IV Prop 2.1 (ii) upper half: `∃ ξ ≥ 5, ∀ x ≥ ξ, θ(x) ≤ (4/3)·x`. -/
theorem iutIVProp21ii_theta_le_four_thirds_eventually :
    ∃ ξ : ℝ, 5 ≤ ξ ∧ ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ 4 / 3 * x := by
  refine ⟨9000, by norm_num, fun x hx => ?_⟩
  have := theta_le_thirteen_tenths_mul_add x (by linarith)
  linarith

/-- IUT IV Prop 2.1 (ii)（L2336–2345）双侧形态：∃ ξ ≥ 5，∀ x ≥ ξ，(2/3)·x ≤ θ(x) ≤ (4/3)·x。 -/
theorem iutIVProp21ii_theta_two_sided_eventually :
    ∃ ξ : ℝ, 5 ≤ ξ ∧ ∀ x : ℝ, ξ ≤ x →
      2 / 3 * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ 4 / 3 * x := by
  obtain ⟨ξ₁, hξ₁, hlow⟩ := iutIVProp21ii_theta_ge_two_thirds_eventually
  obtain ⟨ξ₂, _, hup⟩ := iutIVProp21ii_theta_le_four_thirds_eventually
  exact ⟨max ξ₁ ξ₂, le_trans hξ₁ (le_max_left _ _), fun x hx =>
    ⟨hlow x (le_trans (le_max_left _ _) hx), hup x (le_trans (le_max_right _ _) hx)⟩⟩

/-- π(p) = n + 1 for the `n`-th prime `p = nth Prime n` (0-indexed). -/
theorem primeCounting_nth_prime_eq (n : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, ← Nat.primeCounting',
    Nat.primeCounting'_nth_eq, if_pos (Nat.prime_nth_prime n)]

/-- IUT IV Prop 1.6（L901–926），素数计数形：∃ ηprm > 0，∀ η ≥ ηprm，
π(η) ≤ 4η/(3·log η)。证明：Mathlib 的 Abel 求和 π = θ/log + ∫θ/(t log²t)（积分项 = o(x/log x)）
加上本文件的 θ(x) ≤ 1.3x + 300；1.3 + 1/60 + 1/60 = 4/3。 -/
theorem iutIVProp16_primeCounting_le_four_thirds_eventually :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η₀ ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η) := by
  have hI := Chebyshev.integral_theta_div_log_sq_isLittleO.bound (show (0 : ℝ) < 1 / 60 by norm_num)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 4 * x / (3 * Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop (18000 : ℝ), hI] with x hx hIx
    have hL : 0 < Real.log x := Real.log_pos (by linarith)
    rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral (by linarith)]
    rw [Real.norm_of_nonneg (div_nonneg (by linarith) hL.le)] at hIx
    have hIle := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hIx)
    have hθ := theta_le_thirteen_tenths_mul_add x (by linarith)
    have h1 : Chebyshev.theta x / Real.log x ≤ (13 / 10 * x + 300) / Real.log x :=
      div_le_div_of_nonneg_right hθ hL.le
    have h2 : (13 / 10 * x + 300) / Real.log x + 1 / 60 * (x / Real.log x) =
        (13 / 10 * x + 300 + x / 60) / Real.log x := by
      field_simp
    have h3 : (13 / 10 * x + 300 + x / 60) / Real.log x ≤ (4 * x / 3) / Real.log x :=
      div_le_div_of_nonneg_right (by linarith) hL.le
    have h4 : (4 * x / 3) / Real.log x = 4 * x / (3 * Real.log x) := by
      field_simp
    linarith
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max a 1, by positivity, fun η hη => ha η (le_trans (le_max_left _ _) hη)⟩

/-- IUT IV Prop 1.6（L901）第 n 个素数形：∃ n₀，∀ n ≥ n₀，n ≤ 4p_n/(3·log p_n)，其中 p_n 为
第 n 个素数（1 起算）；此处以 0 起算的 `Nat.nth Nat.Prime n` 表为 p_{n+1}，故左侧为 n + 1。 -/
theorem iutIVProp16_index_le_four_thirds_nthPrime :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ((n + 1 : ℕ) : ℝ) ≤
        4 * (Nat.nth Nat.Prime n : ℝ) / (3 * Real.log (Nat.nth Nat.Prime n : ℝ)) := by
  obtain ⟨η₀, _, hη⟩ := iutIVProp16_primeCounting_le_four_thirds_eventually
  refine ⟨⌈η₀⌉₊, fun n hn => ?_⟩
  have hle : η₀ ≤ (Nat.nth Nat.Prime n : ℝ) := by
    have h1 : η₀ ≤ (⌈η₀⌉₊ : ℝ) := Nat.le_ceil η₀
    have h2 : ⌈η₀⌉₊ ≤ Nat.nth Nat.Prime n := by
      have := Nat.add_two_le_nth_prime n
      omega
    exact h1.trans (by exact_mod_cast h2)
  have := hη _ hle
  rwa [Nat.floor_natCast, primeCounting_nth_prime_eq] at this

end LeanFormal.IUT.IUTIV.Estimates
