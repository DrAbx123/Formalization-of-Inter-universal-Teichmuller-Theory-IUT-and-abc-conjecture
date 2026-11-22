# TauCetiPort L_p 基建：漂移审计与止损记录

日期：2026-11-16（Asia/Shanghai）。责任人：andrew（stage4 lane）。裁决：Lead 批准确认放弃全链 build。

## 0. 结论（先行）

- **TauCetiPort 的 local field 理论链与当前仓库 Mathlib 版本不兼容，放弃 build；不做 port-repair。**
- 依据：只 build 到拓扑第 0 层（31 文件）就出现 **8 个红**，其中 3 个是「port 引用的 Mathlib 模块在当前版本不存在」的结构性漂移，5–6 个是符号/实例 API 改名漂移。L1–L9 尚有 39 文件、未知漂移，收益（只有 unramified 级 + different 基建，**不含** §7.2 硬核 bounded-degree 有限性）远低于成本。
- L_p（§7.2）改走 **Mathlib-only 路线**：`Mathlib.Analysis.Normed.Field.Krasner`（IsKrasner.of_completeSpace）+ Eisenstein 系数有限类 + compositum；硬核三步由 kurt lane 主攻（Lead 裁决 2026-11-16 12:46Z）。

## 1. 版本与环境

- 仓库根：`D:\lean`。
- Mathlib pin（lake-manifest.json rev）：`e12c1910fe855cbfc38803cd4e55543906d5fa62`；batteries `88679d088c9720c27ebdf2ba4dafe17341747f94`。
- Port 根：`tmp/sheaf/xif/paper/TauCetiPort/TauCeti/`（port 文件用 `module` + `public import` 语法；grep 闭包时必须匹配 `^(public\s+)?import`）。
- 目标文件：`tmp/sheaf/xif/paper/TauCetiPort/TauCeti/NumberTheory/LocalField/Unramified/Existence.lean`（unramified 存在唯一性 `existsUnique_isUnramified_finrank_eq` 等）。
- 编译方式：仅 watchdog（`node tools/wd_add.mjs` + `node tools/wd_status.mjs`），未使用 `lake env lean` 手工编译。

## 2. 依赖闭包（正确版）

- transitive import 闭包：**65 文件**（目标 + 64 依赖）；其中 16 文件在本次前已有 olean、49 需新编；Mathlib import 138 个。
- 拓扑分层（9 层 + L0）：
  - L0 = 31（无项目依赖的叶子）
  - L1 = 10，L2 = 6，L3 = 4，L4 = 3，L5 = 3，L6 = 3，L7 = 2，L8 = 2，L9 = 1（= Unramified/Existence）
- 说明：先前一次闭包统计漏算，是因为把 port 的 `public import` 当成非 import；修正后闭包从 62 → 65，且 L0 叶子集合变化。

## 3. L0 批次结果（31 文件，16 需编，15 已有 olean）

- **8 DONE**（oleans 保留，可用作可选 donor）：`LinearAlgebra/Trace/Prod`、`RingTheory/DedekindDomain/Ideal/QuotientPow`、`RingTheory/LocalRing/Pointwise`、`RingTheory/PowerBasis`、`RingTheory/RootsOfUnity/Finite`、`RingTheory/RootsOfUnity/IntegrallyClosed`、`Algebra/Group/Subgroup/FiniteFiltration`、`RingTheory/DiscreteValuationRing/Basic`（旧 olean）。
- **8 FAIL**（详见 §4）：`Algebra/Ring/Action/End`、`FieldTheory/IntermediateField/Adjoin/EqTop`、`RingTheory/DedekindDomain/PrimesAbove`、`RingTheory/Ideal/Inertia`、`RingTheory/RootsOfUnity/Basic`、`RingTheory/Valuation/ValuativeRel/Extension`、`Algebra/Order/Floor/Div`、`RingTheory/Subring/Torsion`。

## 4. 漂移点清单（文件:行 / 缺失符号 / 类别 / 修复量级估计）

### 4.1 结构性漂移：import 的 Mathlib 模块在当前 Mathlib 不存在（不可用改名修复）

1. `Algebra/Order/Floor/Div.lean:7` — `Mathlib.Data.ENat.Monoid` 不存在（当前 Mathlib `Data/ENat/` 只有 Basic/BigOperators/Defs/Lattice/Pow）。
2. `RingTheory/Subring/Torsion.lean:7` — `Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic` 不存在（当前只有 `HasFiniteQuotients.lean`、无 `Basic` 子目录）。
   估计：需重写 import 并适配 API 迁移，1 文件 3–10 行，但暴露 port 面向的 Mathlib 版本比 pin 新/不同，后续层有同类风险。

### 4.2 符号/实例漂移（旧 Mathlib 名 → 当前名）

3. `Algebra/Ring/Action/End.lean:65` — `Set.forall_mem_singleton` 在当前 Mathlib 不存在（只有 `List.forall_mem_singleton`）。修复 ~1 行（`simp`/`Set.mem_singleton_iff`/`forall_eq`）。
4. `FieldTheory/IntermediateField/Adjoin/EqTop.lean:141` — `IntermediateField.adjoin_adjoin_right` 不存在；当前有 `adjoin_adjoin_left`（`Adjoin/Defs.lean:376`）与 `adjoin_adjoin_comm`（:399）。修复 ~1–2 行。
5. `RingTheory/Ideal/Inertia.lean:49,89` — `Ideal.mem_inertia` 不存在；当前有 `Ideal.inertia`（`Ideal/Defs.lean:154`）、`Ideal.coe_mem_inertia`（:157）。修复 ~2–4 行。
6. `RingTheory/RootsOfUnity/Basic.lean:187,196` — `HasEnoughRootsOfUnity.exists_isPrimitiveRoot` 不存在；当前对应 `IsCyclotomicExtension.exists_isPrimitiveRoot`（`RootsOfUnity/AlgebraicallyClosed.lean:33` 用法）。修复 ~2 行。
7. `RingTheory/DedekindDomain/PrimesAbove.lean:100,195` — rw pattern 不匹配 + instance synth fail；疑 `Ideal.primesOver`/`PrimesOver` API 改名。修复 2–5 行，可能需补 instance。
8. `RingTheory/Valuation/ValuativeRel/Extension.lean:83,101` — `IsLocalHom (algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L])`、`IsScalarTower (𝒪ᵥ[K]) (𝒪ᵥ[L]) L` 综合失败；当前 Mathlib 有 `RingTheory/Valuation/Extension.lean:157–196`（`IsLocalHom (algebraMap vR.integer vS.integer)`、`instIsLocalHomValuationInteger`）。修复 2–6 行（可能要补 port 局部 instance，属"不改语义"的范围）。

合计：8 文件、约 15–30 行补丁，纯 API 对齐；但 §4.1 表明 port 面向的 Mathlib 版本与 pin 不一致，L1–L9 同类漂移概率高。


## 6. 限时试用补丁记录（Lead 授权 (a) 修订版：≤20 行、纯 API 对齐、L1 为时间盒终点）

目标：只让 L1 的 10 个文件变绿。经依赖分析，L1 需要的红 L0 文件只有 3 个（其余 5 个 L0 红文件不在 L1 直接依赖中，保留红状态不动）：
`Algebra/Ring/Action/End`（→ RamificationGroup）、`RingTheory/RootsOfUnity/Basic`（→ RootsOfUnity/LocalRing）、`RingTheory/DedekindDomain/PrimesAbove`（→ Ideal/PrimesOver）。

| # | 文件:行 | 旧符号/写法 | 新写法 | 等价性理由 | 结果 |
|---|---|---|---|---|---|
| P1 | `Algebra/Ring/Action/End.lean:65` | `Set.forall_mem_singleton.2 h` | `fun a ha => by rw [Set.mem_singleton_iff] at ha; subst ha; exact h` | 旧引理语义即 `(∀ a ∈ {ξ}, σ • a = a) ↔ σ • ξ = ξ`；当前 Mathlib 无 Set 版，仅 List 版，直接展开集合成员 | DONE 12:52:29 |
| P2 | `RingTheory/RootsOfUnity/Basic.lean:187,196` | `HasEnoughRootsOfUnity.exists_isPrimitiveRoot M n` | `HasEnoughRootsOfUnity.exists_primitiveRoot M n` | 当前 Mathlib `EnoughRootsOfUnity.lean:33` 的 lemma 名改为 `exists_primitiveRoot`（同声明类型） | DONE 12:52:34 |
| P3a | `RingTheory/DedekindDomain/PrimesAbove.lean:100` | `rw [h, Ideal.under_bot]` | `rw [h]; exact Ideal.under_bot R B` | `Ideal.under` 现为 `abbrev` = `Ideal.comap (algebraMap ..)`（Over.lean:96），rw 不在 comap 形上匹配；`Ideal.under_bot`(:263) 结论 defeq 目标 | DONE 12:52:38 |
| P3b | `RingTheory/DedekindDomain/PrimesAbove.lean:193` | `instance finite_liesOver [IsDedekindDomain B] ...` | 加 `[IsDomain R]` 到 instance binder | 当前 Mathlib `IsDedekindDomain` 不再蕴含 `IsDomain`（本实例用到 `v.ne_bot` 的 domain 性），与旧版语义一致：旧版由 `IsDomain R` 在 section 提供 | DONE 12:52:38 |

- 补丁均为局部、无缝改数学语义；未新增公理/sorry。补丁后 3 文件 `#print axioms` 标准三公理（见 watchdog 日志）。
- 其余 5 个 L0 红文件（`FieldTheory/IntermediateField/Adjoin/EqTop`、`RingTheory/Ideal/Inertia`、`RingTheory/Valuation/ValuativeRel/Extension`、`Algebra/Order/Floor/Div`、`RingTheory/Subring/Torsion`）**不在 L1 依赖中**，保持未改（未触碰）。

## 7. 保留资产与后续建议（数值不变）

见 §5 原文（上方保留于本文件历史版本）；可选 donor 列表与后续修复建议不变。

## 8. L1 限时试用结果（2026-11-16 21:00，触发止损线，未开 L2）

L0 三个补丁后，L1（10 文件）实测：**7 DONE**（Trace/Exact、Henselian、RootsOfUnity/Adjoin、RootsOfUnity/LocalRing、Unramified/LocalRing、ValuativeRel/Basic、OrderOfElement/Basic 旧 olean），**3 红 = L1 新增漂移 3 文件 > Lead 判据 ≤2**：

1. `RingTheory/Ideal/PrimesOver.lean:42`：当前 Mathlib `Ideal.ne_bot_of_liesOver_of_ne_bot` 要求 `[IsDomain A] [Module.IsTorsionFree A B]`；port 上下文（任意 CommRing B）两者都没有，即使加 `[IsDomain R]` 也无法从 `FaithfulSMul` 推出 `IsTorsionFree R B`（B 有零因子时反例）。需在文件内补 ~4 行 inline 证明（`Ideal.comap_bot_of_injective` 路线）→ 可修但非纯改名。
2. `RingTheory/Ideal/RamificationGroup.lean:73,107`：当前 Mathlib 无 `Ideal.mem_inertia`、`Ideal.inertia_smul`、ideal 版 `smul_pow'`；`AddSubgroup.mem_inertia` 可替代前者，但共轭等式需自证 ~25 行 → 超出「别名/局部 instance」补丁预算。
3. `NumberTheory/LocalField/NormalizedValuation.lean:442`：`valueGroup` 未知（当前 Mathlib 与整个 port 闭包均无此定义）→ 同类结构漂移。

**结构性结论**：这些不是「旧名→新名」的后向漂移，而是 port 面向的 Mathlib **比 pin `e12c1910fe855cbfc38803cd4e55543906d5fa62` 更新**（引用了当前 Mathlib 中不存在的 lemma/API）。因此 L2–L9 同型缺失 lemma 概率极高，修复成本无界。按 Lead「L1 新增漂移 ≤2 才继续」判据：**3 > 2，停链，未开 L2**。最终建议维持放弃全链 build；已 DONE 的 port 文件 olean 保留为可选 donor（使用前需 gate 三公理）。
