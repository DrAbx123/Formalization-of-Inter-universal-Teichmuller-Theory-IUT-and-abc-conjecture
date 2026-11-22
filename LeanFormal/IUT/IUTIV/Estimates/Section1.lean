/-
# IUT IV §1 落点：卡清单（纯陈述 + 具名卡）+ 已证小额项（Prop 1.7）

论文出处（行号均为 `papers\motizuki_corpus\text\Inter-universal Teichmuller Theory IV.txt` 的行）：
§1 范围 L391–2328。本文件按 root 2026-10-16 任务包①落两份材料：
(1) §1 逐条卡清单（纯陈述；缺机器者只登记，不承诺证明）；(2) 已证小额项：
Prop 1.7 加权平均恒等式（L927–942 陈述、L966–997 证明步骤），全证明在本文件。

## §1 卡清单（逐条）

1. Prop 1.1（L400）：p 进张量环 R^{pM} 的归一化包含（多重张量与 different 幂）。
   [machine-gap] 缺：p 进张量环 ≅ 归一化子环（different 幂）的结构定理。消费者：Prop 1.4 的 log-volume。
2. Prop 1.2（L451）：differents 与对数：a_i、b_i 定义；log_p(R^×_I) 的估计。
   [machine-gap] 依赖 1；log_p 为局部域归一化对数（论文自定）。消费者：Prop 1.4。
3. Prop 1.3（L568）：differents 估计。(i)（L579–583）d_i ≥ d_0 + (e_{i/0}−1)/e_i
   （等号当 k_i/k_0 驯分歧）；(ii)（L584–585）k_i/k_1 有限 Galois、k_1/k_0 驯分歧 ⇒
   d_i ≤ d_0 + n_i + 1/e_0。 [machine-gap] 依赖 1、2；需要不同理想的 ord 与分歧指数记账。
4. Prop 1.4（L656）：非阿基米德归一化 log-volume 估计；关键 (ii)：
   μlog(log_p(R^×_i)) = −(1/e_i + m_i/(e_i f_i))·log(p)。
   [machine-gap] 需要 [Mzk1] 风格的 log-volume / Hodge 剧场层（本仓库未见）。消费者：Thm 1.10。
5. Prop 1.5（L822）：阿基米德度量估计：(i) C⊗_R C ≅ C⊕C（因子 2）；
   (iii) 2^{|I|−1}·|V|^{|I|}；(iv) ⊗m_i ∈ λ^{|I|}·B_I。 [machine-gap] 需复张量范数/体积机器。
6. Prop 1.6（L901）：显式 PNT 形式：∃n0，∀n≥n0，n ≤ 4p_n/(3·log p_n)（p_n = 第 n 个素数）；
   存在 ηprm>0 使 ∀η≥ηprm，Σ_{p≤η} 1 ≤ 4η/(3·log η)。（证明 L913–926 经 PNT
   lim n·log(p_n)/p_n = 1 化归。）
   [machine-gap] 需要素数枚举与显式上界（Mathlib 有 PNT 渐近，无此显式常数形式）。
7. Prop 1.7（L927–942）：加权平均恒等式——[proved] 见本文件 `iutIVProp17` 及其引理。
8. Prop 1.8（L1066）：椭圆曲线挠点：(i) Serre 判据；(ii) 定义域与截面；(vi) Legendre 形与半稳定；
   (vii) good/mult 的惰性/驯分支。 [machine-gap] 依赖 Serre 开像/挠点表示层（大机器）。
9. Def 1.9（L1204）：R-算术除子 ADiv_R(F)、deg_F（v ↦ log q_v；阿基米德 v ↦ 1）、
   deg := (1/[F:Q])·deg_F、拉回 a|K 的归一化度不变、deg_E（E-度，L~1236）。
    [proved·部分；2026-10-16 更新，旧结论保留] 落点 `ArithmeticDivisorDegree.lean`：degLinearMap/deg/ndeg/deg_part/eDegree；
    `deg_pullback`/`ndeg_pullback`（拉回不变）。原缩减标注（“Def 1.9 (ii) 的 deg_E 拉回不变仍为卡 C1、
    依赖纤维记账卡 C2”）已被后续工作取代：C2 落地为 `sum_localDegree_finiteFiberOf` /
    `sum_localDegree_infiniteFiberOf` / `sum_localDegree_biUnion`（逐纤维 Σ_{w|v} ld = [K:F]·ld(v)）；
    C1 的精确不变式落地为 `eDegreeUnnormalized_pullback`（未归一化分子读数），
    字面读数满足 `eDegree_pullback_factor`（精确到 [K:F]⁻¹ 因子）。ADD SHA `D75F30C6F98DEA4EF7B51CB82A935B17D9FD361B19DCE823B75DE47A6C96DCAD`（3363 jobs EXIT=0，2026-10-16）。
10. Thm 1.10（L1255）：Θ-pilot log-volume 估计。设定：初始 Θ-数据（[IUTchI] Def 3.1）+
    Cor 3.12 情境 + 好归约假设（L1256–1259）；d_mod := [F_mod:Q]（L1259–1261）、
    (1≤)e_mod≤d_mod（L1262）、d*_mod := 2^12·3^3·5·d_mod、e*_mod := 2^12·3^3·5·e_mod（L1264–1271）、
    F_tpd（L1273–1277）。结论（L~1346–1350）：
    (1/6)log(q) ≤ (1+20·d_mod/l)·(log d_{F_tpd}+log f_{F_tpd}) + 20·(e*_mod·l+ηprm)
    ≤ (1+20·d_mod/l)·(log d_F+log f_F) + 20·(e*_mod·l+ηprm)。
    [machine-gap] 依赖 log-volume 层（本文件 4）与 Cor 3.12 的显式常数 C_Θ（L1363–1370）。
    缩减显式标注：本卡只登记陈述与常数取法，不含证明承诺；"初等估计落点"指 §1 的
    1–8 与 (E1)–(E6)，Thm 1.10 本身属于 log-volume 层结论。
11. (E1)–(E6)（L1388–1408，Thm 1.10 证明内有限核算）：(E1) 1/(…)^2 ≤ 1 型不等式；
    (E3) |GL2(F_p)| = p(p+1)(p−1)^2；(E4) p=2,3,5 的数值化；(E6) 0≤log2≤1,
    1≤log3≤logπ≤log5≤2 等对数常数区间。 [machine-gap·可做] (E1)/(E3)/(E4)/(E6) 为
    有限组合/初等数值引理（Mathlib 可形式化）；(E2)/(E5) 涉及额外常数核算。
12. Remarks 1.10.1–1.10.7（L1961/1990/2019/2038/2096/2193/2292）：说明性备注，不单列机器。
    Remark 1.10.1（L1990）的 ndeg 语义与 Explicit estimates Remark 1.10.1（L884）一致，
    决定登记见 `ArithmeticDivisorDegree.lean` 文件头"决定登记（rec3）"。

## 缩减显式标注（总）
- §1 中 1–8 为纯算术/局部域/分析估计，不含 IUT の Step XI 依赖；与 Cor 3.12 相接的只有
  Thm 1.10 的 log-volume 结论（属卡）。
- 本文件不引入 V(F) 高度层；该层已落于 `ArithmeticDivisorDegree.lean` 的
  `section HeightBoxLayer`（2026-10-16 晚：absValAt、支撑有限集、h_non/h_arc/h^tor、Lemma 1.3 (i)/(iv)）。
  hweightvol/hpoint 的算术侧按 Def 1.9 + Explicit estimates
  Remark 1.10.1 论文化（rec3 决定），源侧保留几何卡。
- Lean 记法：论文中的坐标元组（组合向量箭头记号）在本文件中写作 et（该组合字符不能作 Lean 标识符）。
- Prop 1.7 的 Lean 陈述忠实 L927–942：E 非空有限（[Fintype E] [Nonempty E]），
  n = k+1（结构性正数），λ_e > 0（hlam），β_e ∈ ℝ；三式同值。论文的 E^n 计数
  用函数空间 `Fin n → E` 表示（基数相同）。

## 更新（2026-10-17，root 单 agent）：卡6（Prop 1.6）已证
- 证明落在 `Section2.lean`（与 θ ≤ 1.3x + 300 同文件）：`iutIVProp16_primeCounting_le_four_thirds_eventually`
  与 `iutIVProp16_index_le_four_thirds_nthPrime`。上文卡6的 [machine-gap] 标注作废（旧行保留）。

## 更新（2026-10-17 05:08，root 单 agent）：卡3 Prop 1.3 (i) 不等式部分已证
- `DifferentTowerEstimate.lean`：`iutIVProp13i_normalizedDifferent_ge`
  （一般 Dedekind 塔 A⊆B⊆C、素理想链 p⊆Q⊆P：
  ord_Q𝔇_{B/A}/e(Q|p) + (e(P|Q)−1)/e(P|p) ≤ ord_P𝔇_{C/A}/e(P|p)；ℤ_p⊆𝒪_{k_0}⊆𝒪_{k_i} 为特例）。
- 未证：(i) 的等号⇔驯分歧；(ii)。

## 更新（2026-10-17 05:32，root 单 agent）：卡3 Prop 1.3 (i) 驯分歧等号方向已证
- `DifferentTameEquality.lean`：`count_differentIdeal_eq_of_tame`（驯分歧 ⇒ ord_P𝔇 = e − 1）与
  `iutIVProp13i_normalizedDifferent_eq_of_tame`（塔中 d_C = d_B + (e(P|Q)−1)/e(P|p)）。
- 论文 (i) 仅断言 tame ⇒ 等号（L577–579），故 (i) 已完整；未证：(ii)。
-/

import LeanFormal.IUT.Audit.Status
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace LeanFormal.IUT.Audit

def iutIVSection1 : Obligation :=
  { id := "IUT-IV.section-1"
    source := "IUT IV, Section 1"
    status := VerificationStatus.pending
    note := "Import elementary estimates only after the Corollary 3.12 dependency is explicit." }

end LeanFormal.IUT.Audit

namespace LeanFormal.IUT.IUTIV.Estimates

/-! ## Prop 1.7（Weighted Averages，L927–942）：已证

论文记号（L945–965）：λ_E := Σ_{e∈E} λ_e；β_E := Σ_{e∈E} β_e·λ_e；β_avg := β_E/λ_E；
对 et = (e_1,…,e_n) ∈ E^n：β_{et} := Σ_{j=1}^n β_{e_j}，λ_Π(et) := ∏_{j=1}^n λ_{e_j}。
结论（任意 i = 1,…,n）：[Σ β_{et}·λ_Π]/[Σ λ_Π] = [Σ n·β_{e_i}·λ_Π]/[Σ λ_Π] = n·β_avg。
以下 Lean 化取 n = k+1（正数由结构保证）、E^n ↦ `Fin (k+1) → E`。 -/

section WeightedAverages

variable {E : Type*} [Fintype E]

/-- Prop 1.7 定义的 β_avg = β_E/λ_E（L945–950）。 -/
noncomputable def iutIVProp17_betaAvg (lam bet : E → ℝ) : ℝ :=
  (∑ e, bet e * lam e) / (∑ e, lam e)

/-- Prop 1.7 证明第一步（L967–971）：λ_E^n = Σ_{et∈E^n} λ_Π(et)。 -/
theorem iutIVProp17_lambdaE_pow (lam : E → ℝ) (n : ℕ) :
    (∑ e, lam e) ^ n = ∑ et : Fin n → E, ∏ j, lam (et j) := by
  rw [Finset.sum_pow', Fintype.piFinset_univ]

/-- Prop 1.7 证明第二步（L971–975）：β_E·λ_E^{n−1} = Σ_{et} β_{e_i}·λ_Π(et)（任意坐标 i；
取 n = k+1，此时 λ_E^{n−1} = λ_E^k）。 -/
theorem iutIVProp17_weightedTupleSum (lam bet : E → ℝ) (k : ℕ) (i : Fin (k + 1)) :
    ∑ et : Fin (k + 1) → E, bet (et i) * ∏ j, lam (et j) =
      (∑ e, bet e * lam e) * (∑ e, lam e) ^ k := by
  calc ∑ et : Fin (k + 1) → E, bet (et i) * ∏ j, lam (et j)
      = ∑ x : E × (Fin k → E),
          bet ((Fin.insertNthEquiv (fun _ => E) i) x i) *
            ∏ j, lam ((Fin.insertNthEquiv (fun _ => E) i) x j) := by
        rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ => E) i)
          (fun et : Fin (k + 1) → E => bet (et i) * ∏ j, lam (et j))]
    _ = ∑ x : E × (Fin k → E), (bet x.1 * lam x.1) * ∏ j : Fin k, lam (x.2 j) := by
        apply Finset.sum_congr rfl
        rintro ⟨a, u⟩ _
        change bet (Fin.insertNth (α := fun _ => E) i a u i) *
            ∏ j, lam (Fin.insertNth (α := fun _ => E) i a u j) =
          (bet a * lam a) * ∏ j : Fin k, lam (u j)
        rw [Fin.insertNth_apply_same, Fin.prod_univ_succAbove,
          Fin.insertNth_apply_same, mul_assoc]
        congr 1
        congr 1
        apply Finset.prod_congr rfl
        intro j _
        exact congrArg lam (Fin.insertNth_apply_succAbove (α := fun _ => E) i a u j)
    _ = ∑ a, ∑ u : Fin k → E, (bet a * lam a) * ∏ j, lam (u j) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ a, (bet a * lam a) * (∑ e, lam e) ^ k := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum, ← iutIVProp17_lambdaE_pow lam k]
    _ = (∑ e, bet e * lam e) * (∑ e, lam e) ^ k := by
        rw [Finset.sum_mul]

/-- Prop 1.7 证明第三步（L977–986）：对 i 求和：n·β_E·λ_E^{n−1} = Σ_{et} β_{et}·λ_Π(et)。 -/
theorem iutIVProp17_betaTupleSum (lam bet : E → ℝ) (k : ℕ) :
    ∑ et : Fin (k + 1) → E, (∑ j, bet (et j)) * ∏ j, lam (et j) =
      ((k + 1 : ℕ) : ℝ) * ((∑ e, bet e * lam e) * (∑ e, lam e) ^ k) := by
  have h1 : ∑ et : Fin (k + 1) → E, (∑ j, bet (et j)) * ∏ j, lam (et j) =
      ∑ j : Fin (k + 1), ∑ et : Fin (k + 1) → E, bet (et j) * ∏ j', lam (et j') := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [h1]
  trans ∑ _j : Fin (k + 1), (∑ e, bet e * lam e) * (∑ e, lam e) ^ k
  · apply Finset.sum_congr rfl
    intro j _
    rw [iutIVProp17_weightedTupleSum lam bet k j]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Prop 1.7 第一个等号（L929–942）：两个分子同值（= n·β_E·λ_E^{n−1}），分母同值（= λ_E^n）。 -/
theorem iutIVProp17_middle (lam bet : E → ℝ) (k : ℕ) (i : Fin (k + 1)) :
    (∑ et : Fin (k + 1) → E, (∑ j, bet (et j)) * ∏ j, lam (et j)) /
        (∑ et : Fin (k + 1) → E, ∏ j, lam (et j)) =
      (∑ et : Fin (k + 1) → E,
          ((k + 1 : ℕ) : ℝ) * (bet (et i) * ∏ j, lam (et j))) /
        (∑ et : Fin (k + 1) → E, ∏ j, lam (et j)) := by
  have hnum := iutIVProp17_betaTupleSum lam bet k
  have hnum_i : ∑ et : Fin (k + 1) → E,
        ((k + 1 : ℕ) : ℝ) * (bet (et i) * ∏ j, lam (et j)) =
      ((k + 1 : ℕ) : ℝ) * ((∑ e, bet e * lam e) * (∑ e, lam e) ^ k) := by
    rw [← Finset.mul_sum, iutIVProp17_weightedTupleSum lam bet k i]
  rw [hnum, hnum_i]

/-- Prop 1.7 第二个等号（L942, L986–997）：公共比值 = n·β_avg。 -/
theorem iutIVProp17_value [Nonempty E] (lam bet : E → ℝ) (hlam : ∀ e, 0 < lam e) (k : ℕ) :
    (∑ et : Fin (k + 1) → E, (∑ j, bet (et j)) * ∏ j, lam (et j)) /
        (∑ et : Fin (k + 1) → E, ∏ j, lam (et j)) =
      ((k + 1 : ℕ) : ℝ) * iutIVProp17_betaAvg lam bet := by
  rw [iutIVProp17_betaAvg]
  have hE : (0 : ℝ) < ∑ e, lam e :=
    Finset.sum_pos (fun e _ => hlam e) Finset.univ_nonempty
  have hEne : (∑ e, lam e) ≠ 0 := hE.ne'
  have hEk : (∑ e, lam e) ^ k ≠ 0 := pow_ne_zero k hEne
  rw [iutIVProp17_betaTupleSum lam bet k, ← iutIVProp17_lambdaE_pow lam (k + 1), pow_succ]
  field_simp [hEne, hEk]

/-- Prop 1.7 全文（L927–942）：两个等号合取（n = k+1）。 -/
theorem iutIVProp17 [Nonempty E] (lam bet : E → ℝ) (hlam : ∀ e, 0 < lam e) (k : ℕ)
    (i : Fin (k + 1)) :
    (∑ et : Fin (k + 1) → E, (∑ j, bet (et j)) * ∏ j, lam (et j)) /
        (∑ et : Fin (k + 1) → E, ∏ j, lam (et j)) =
      (∑ et : Fin (k + 1) → E,
          ((k + 1 : ℕ) : ℝ) * (bet (et i) * ∏ j, lam (et j))) /
        (∑ et : Fin (k + 1) → E, ∏ j, lam (et j)) ∧
    (∑ et : Fin (k + 1) → E, (∑ j, bet (et j)) * ∏ j, lam (et j)) /
        (∑ et : Fin (k + 1) → E, ∏ j, lam (et j)) =
      ((k + 1 : ℕ) : ℝ) * iutIVProp17_betaAvg lam bet :=
  ⟨iutIVProp17_middle lam bet k i, iutIVProp17_value lam bet hlam k⟩

end WeightedAverages

end LeanFormal.IUT.IUTIV.Estimates