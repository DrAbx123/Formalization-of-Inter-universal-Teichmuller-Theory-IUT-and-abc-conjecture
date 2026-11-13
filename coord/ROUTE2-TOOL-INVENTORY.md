# ROUTE2-TOOL-INVENTORY — 路线二 (B1)–(B5)/(B8)–(B9) 盘点与 B-DualVolume 首块

日期：2026-11-13；R29/task-75；状态：**TOOL/PARTIAL**。未改目标、未新增假设、无 sorry/PUnit/True/空类型。

## 0. 结论先行

- 已有 green 覆盖：B1 定义/成员判定、B2 的 basis-dual 形式、B6/B7 的 different/tensor 部分、B9 的乘法伴随片段；oleans 均在 `.lake/build/lib/lean/...` 存在（见 §1）。
- 新文件 `tmp/sheaf/xif/paper/Mzk1TraceDualVolumeActual.lean` 已编译：**B3**（basis lattice 双对偶）、**scalar p-power 的 B4/B5 actual-Haar 块**；4 条主定理 axioms probe = trio。
- **不是完整 B4**：目前只证 `L = p^k • O` 的 scalar dilation；一般格 `L`、B2 的显式矩阵 `S^{-1}B^{-T}`、B8 仍未证。详见 §3。
- 按 lead 更新：本工具供 **P3 B-Estimate/B-DualVolume 与精确求值**使用；**不宣称本身给目标增益**。qVFam 块上 `paperRootThetaImageNZ = F(c_root)·O_hol` 是公共标量族，相对 index 不随 m 增长；增益只能来自 Ind2/gap 源结构；B4/B5 不改变这一点。

## 1. 已有覆盖（逐条 B1–B9）

| 条目 | 已有声明/文件:line | olean | 覆盖判定 |
|---|---|---|---|
| **B1** 迹配对/对偶格 | `LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualLattice.lean:50` (`integralTraceDualLattice`), `:56`/`:63` (membership), `:112` (`padic` version) | EXISTS 712,000B | **完整工具**（定义+成员） |
| **B2** 矩阵公式 | `IntegralTraceDualLattice.lean:94`/`:118` (`integralTraceDualLattice_span_basis`/`padic..._span_basis`)；`B.dualBasis` 给 dual basis | EXISTS | **部分**：basis-dual 形式可用；**没有**显式 `S^{-1}B^{-T}Z_p^d` 矩阵定理 |
| **B3** 双对偶 | 新 `Mzk1TraceDualVolumeActual.lean:35` `doubleDual_basisIntegralLattice`；Mathlib `Submodule.traceDual_traceDual` 仅 basis 情形 | EXISTS 429,376B new | **basis lattice 完整**；任意满格 `L` 的 `(L#)#=L` 未证（需 full lattice/reflexive） |
| **B4** 相对 Haar 体积 | 新 `:157` `relativeHaarVolume_scalar_traceDual`；actual `Measure.addHaar` + 真实 bilinear trace `B` | new olean | **scalar p-power 块完整**；一般 `L` 的 B4 是 GAP |
| **B5** log 形式 | 新 `:185` `relativeHaarLog_scalar_traceDual`；带 positivity/finiteness 假设 | new olean | **scalar 块完整**；一般 `L` 的 B5 是 GAP |
| **B6** different/整闭包修正 | `DifferentTraceProduct.lean:81` (`dualSubmodule_pi`), `:151` (`traceDualLattice_pi`), `:192` (`traceMultiplierIdeal_eq_differentIdeal`); `IntegralTraceDualTensorInclusion.lean:209` | EXISTS 677,576B / 1,728,800B | **部分工具**：product/different 有；`R⊆O_E ⇒ O_E#⊆R#` 的完整 B6 未单列 |
| **B7** 指数等式 | `IntegralTraceDualLattice.lean:226` (`natCard_quotient_eq_pow_valuation_det_equiv`), `:300` (`natCard_traceDual_quotient_eq_pow_valuation_gram_det`) | EXISTS 712,000B | **部分**：商指数/Smith 公式有；`#O_E/R = #R#/O_E#` 的完美配对形式未证 |
| **B8** 和的对偶 | 未找到 | N/A | **GAP**：无 `(Σ L_a)# = ⋂ L_a#` 声明 |
| **B9** O_E-生成的对偶 | `IntegralTraceDualLattice.lean:411` (`mul_le_traceDual_one_of_le_traceDual`) 仅乘法伴随片段 | EXISTS | **部分**：无 `(O_E L)# = ⋂_{a∈O_E} {x | ax∈L#}` 完整形式 |

已有 green 资产列表（均 olean EXISTS）：`IntegralTraceDualLattice`、`IntegralTraceDualTensorInclusion`、`PadicLatticeIndexFormula`、`DifferentTraceProduct`、`IntegralLogShellHaarIndex`、`FinitePadicHaarScaling`、`CompactOpenAddSubgroupIndex`、`ProductIntegerLattice`、`FinitePlaceIntegralTensorCovolume`。

## 2. 新文件与 build 证据

文件：`tmp/sheaf/xif/paper/Mzk1TraceDualVolumeActual.lean`（10,056B，src mtime 2026-11-13 04:18:12 local）；olean：`.lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1TraceDualVolumeActual.olean`（429,384B，mtime 04:20:41 local，fresh）。**按 Lead 统一编译约定，不采用自己跑的 lake/lean 结果；以下只引 watchdog 日志。**

watchdog 证据（`dag/watchdog/watchdog.log`）：

| event | log line |
|---|---|
| START | `2026-11-12T20:19:54.907Z START tmp/sheaf/xif/paper/Mzk1TraceDualVolumeActual.lean` |
| DONE EXIT=0 | `2026-11-12T20:20:42.132Z DONE EXIT=0 ... (47s)` |
| olean | `.lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1TraceDualVolumeActual.olean` 429,384B @04:20:41 local，fresh |

逐文件日志：`dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1TraceDualVolumeActual.lean.log`。


| 定理 | file:line | 作用 | axioms probe |
|---|---|---|---|
| `doubleDual_basisIntegralLattice` | `Mzk1TraceDualVolumeActual.lean:35` | basis lattice 的 (B3) | UNKNOWN (watchdog probe pending) |
| `traceDual_smulSubmodule` | `:75` | scalar dilation 的对偶 = 逆伸缩对偶 | UNKNOWN |
| `measure_pow_smul_finiteDimensional` | `:105` | actual Haar p^k 缩放 | （构建在现有 `measure_prime_smul_finiteDimensional` 上） |
| `measure_inv_pow_smul_finiteDimensional` | `:123` | actual Haar p^{-k} 缩放 | 同上 |
| `relativeHaarVolume_scalar_traceDual` | `:157` | scalar B4 乘积式 | UNKNOWN |
| `relativeHaarLog_scalar_traceDual` | `:185` | scalar B5 log 式 | UNKNOWN |

`#print axioms`：按新约定，watchdog 尚无该文件的 axiom probe 记录；**trio 记为 UNKNOWN/pending**（不在本盘点中宣称 trio）。

### B4/B5 的精确范围

- B4 定理陈述：对任意 `B : BilinForm ℚ_[p] M`、任意 `ℤ_[p]`-子模 `O`、任意 `k : ℕ`，
  `μ((p^k)•O) * μ((p^k • O)#) = μ(O) * μ(O#)`。
- 证明实际使用：`Measure.addHaar`（actual Haar）、真实 bilinear `B`、`measure_prime_smul_finiteDimensional`、`traceDual_smulSubmodule`。
- 未覆盖：任意 `L = B Z_p^d` 的矩阵 B4、任意满格双对偶、B2 显式矩阵、B8。

## 3. 剩余 GAP（按 B 编号）

1. **B2 显式矩阵**：需 `traceDual_basis_eq_inverse_transpose`（`S^{-1}B^{-T}`）；当前只有 `B.dualBasis`/span 公式，不能把 basis-dual 当矩阵公式。
2. **B3 一般满格**：`(L#)#=L` 目前仅 basis lattice；需 full lattice/reflexive 条件或 Smith 标准形。
3. **B4/B5 一般 L**：当前 scalar `p^k•O`；一般 `L` 需把 B4 化到 Smith 标准形（或一般 determinant-Haar 缩放），这是本任务未完成的主缺口。
4. **B8**：`(Σ L_a)# = ⋂ L_a#` 无现有声明；有限族版本也需补。
5. **B9**：需完整 `(O_E L)#` 交错/有限生成形式；现有只有 `mul_le_traceDual_one_of_le_traceDual`。
6. **B6/B7**：product/different 工具有，但 B6 的 inclusion 与 B7 的完美配对指数等式未单列。

## 4. 定位与停止条件

- 本文件是 **P3 B-DualVolume 工具块**，供 B-Estimate/精确求值消费；不构成目标 `M≥0` 的增益，也不改变 hull 对象表。
- 按 HANDOFF §5.5/§5.13 停止条件：若后续只能得到 B4 的等价改写而没有新估计，或把 scalar 块冒充一般 B4，应停止并记为工具闭合/源实例未闭合。
- 未构造 (B12) 的实例矩阵，也未把 B4 接到 hull 的 `X_G`；这些是 P3 后继任务，不在本文件宣称完成。

## 5. 指针

- HANDOFF：`D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md` §5.2–§5.6、§5.11–§5.13（更新后 1623 行版）。
- 现有：`LeanFormal/IUT/Foundations/LocalFields/{IntegralTraceDualLattice,IntegralTraceDualTensorInclusion,DifferentTraceProduct,PadicLatticeIndexFormula,IntegralLogShellHaarIndex,FinitePadicHaarScaling}.lean`。
- 新：`tmp/sheaf/xif/paper/Mzk1TraceDualVolumeActual.lean`。


---

## 联动更新（23:45Z，A 线完成）

- SNF 工具 green：`Mzk1SNFToolActual`（Mathlib `Submodule.smithNormalForm`）、`BasisDetUnit`、`SNFDiag`、`SNFDiagEquiv`、`GLAct`；
- φ 链 green：`Mzk1DiagEquivProvedActual`（e'/map）、`Mzk1DiagQuotCardActual`（商/cardinal）、`Mzk1DiagVolumeProvedActual`（体积比）；
- 路线二对偶侧：`Mzk1DualTransposeActual`（X_G 列配对/comap）green；一般 X_G GL_d(Z_p)-等价比与 Ind1 桥反向仍 GAP。
- 详见 `coord/XG-DIAGONAL-SOURCE-GAP.md §8–10`。