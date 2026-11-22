# O6 / M2 解析 h 计划（m2AnalyticTarget_of_branch）

日期：2026-11-17；owner：henry（落码）+ sophie（corpus 核对/缺口清单）；Lead 立项。
目标（route §4.3）：`m2AnalyticTarget_of_branch` ⇒ `M2AnalyticTarget (Branch ψFixed)`。

## 1. 已有 donor（直接 import，不重 port）
- `tmp.external.ported.belyi_poly.TauCeti.FieldTheory.Minpoly.BelyiReduction`（olean 已存在）：
  - **`TauCeti.exists_polynomial_aeval_mem_range [PerfectField F] {K} [Field K] [Algebra F K]`**：
    `∃ q : F[X], derivative q ≠ 0 ∧ (∀ s ∈ S, aeval s q ∈ range (algebraMap F K)) ∧
     ∀ (L) [Field L] [Algebra F L] (x : L), aeval x (derivative q) = 0 → aeval x q ∈ range (algebraMap F L)`；
  - `TauCeti.exists_forall_dvd_sub_C [PerfectField F]`（模每个 p∈P 与 q′ 不可约因子为常数）；
  - `TauCeti.exists_irreducible_finset_dvd_comp`（lex 测度 (max degree, count) 的度数下降步）。
- `tmp.external.ported.belyi_poly.TauCeti.Algebra.Polynomial.CriticalValues`：`Polynomial.criticalValues`、
  `mem_criticalValues_self_iff`、**`criticalValues_comp_subset`**。
- `tmp.external.ported.belyi_poly.TauCeti.Algebra.Polynomial.Belyi`：`TauCeti.belyiPolynomial`、
  **`criticalValues_belyiPolynomial_subset : criticalValues ⊆ {0,1}`**、`rootSet_derivative_belyiPolynomial_subset`。
- 旧 Lemma 2.4 corpus（owner: sophie 核 exact 名/三公理）：
  - `Mzk1Rational24TargetBottomActual`：`Mzk1Lemma24Target_finite_beta_bottom`、`rational24TargetFiniteBeta_proved`、
    `mzk1Lemma24Target_of_betaAvoidingBelyiBaseCorrected`、**`oldBaseProviderPremise_refuted`（旧 pin 形状不可用）**、
    `restatedBaseStatementFinite_bottom`、`restatedInductionConclusionFinite_bottom`；
  - `Mzk1BetaAvoidingBelyiRationalActual`：`critIn01_iff_criticalValues {q} (hq : 0 < q.natDegree)`；
  - `Mzk1Lemma22FullShapeHelpersActual`：**`critValues_comp_subset (p q : ℚ[X])`**、`critValues_comp_subset_union`、
    `baseGood_natDegree`、`baseGood_derivative`。
- 我 lane 装配接口：`Mzk1G1PsiM2AnalyticAssemblyActual`：`m2AnalyticTarget_of_witness`、
  `m2AnalyticTarget_branch_mem`、`branchFixedFinite_finite`、`branchFixedFinite_mem_iff`。

## 2. 缺步（pin 到 {0,1}）
ported BelyiReduction 的结论是「值入 ℚ + 临界值入 ℚ」，而 `M2AnalyticTarget` 要求：
1. `∀ z ∈ Branch, aeval z q ∈ {0,1}`；
2. `∀ z, aeval z (derivative q) = 0 → aeval z q ∈ {0,1}`；
3. `aeval 0 q ∉ {0,1}`；4. `0 < q.natDegree`。
缺的装配：把有限有理值集 pin 到 {0,1}（同时保持临界值 ⊆{0,1}）——
候选：`critValues_comp_subset`（复合临界值包含）+ `TauCeti.belyiPolynomial`（{0,1} 内部保持）+
`critIn01_iff_criticalValues`；`q(0)∉{0,1}` 用 beta-avoiding 步（`Mzk1BetaAvoidingBelyiRationalActual`）。
**禁止**用 `oldBaseProviderPremise_refuted` 的旧 pin 形状（sophie 已提醒）。

## 3. 分工
- henry：主件 `m2AnalyticTarget_of_branch`（lex 归纳下降 + donor 使用时序；import ported 包或经 sophie 的树内 adapter）；与 GK δ1/δ2 交替，δ 优先。
- sophie：corpus 编完后发 exact 名 + 三公理 + 适用条件；按 `m2AnalyticTarget_of_branch` 四字段逐条列「已证/缺」；提供树内 adapter（若不直接 import `tmp.external`）。

## 4. 状态
- `Mzk1G1GKDeltaActual` DONE 12:43:38（chordal + 泛函 padic 距离连续/正性，三公理）；
- `Mzk1G1GKDeltaAssemblyActual`（δ2）在编；
- O6 主件待 sophie corpus exact 名清单（当前 corpus 文件 NO-EVENT/重排中）。
