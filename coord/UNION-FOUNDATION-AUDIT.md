# UNION-FOUNDATION-AUDIT — 联合地基复用/重复审计（A505）

generated: 2026-11-11 06:00 (lattice，只读审计 + 队列操作)

## 0) 目的

A505 用户指示：不手写基础，先合并所有外部基础（Mathlib 4.32.2、`tmp/local-cft-port`、脚本移植的 TauCeti/Fermat/Belyi、Takkun、自有 LeanFormal/Iut/xif），只造真正缺的对象。本审计检查最近新增文件是否**重复已有基础**（浪费）。

## 1) 方法/统计

- 样本: `tmp/sheaf/xif/paper` 最近 100 分钟新增/修改 **120** 个文件。
- 联合地基索引: Mathlib 4.32.2 + local-cft-port + ported（TauCeti/Fermat/Belyi）+ Takkun + LeanFormal/Iut/根 Iut；建立 3,912 文件 / 69,099 声明 / 42,796 唯一名索引。
- 直接 import 统计（最近 120 文件）: `tmp.local-cft-port` **0/120**、`tmp.external.ported` **0/120**、`tmp.sheaf.takkun` **5/120**、`LeanFormal` **59/120**、根 `Iut` **0/120**。
- import 闭包分析: 最近含数学关键词的文件中，只有 **7** 个闭包不含任何联合地基模块；其中 3 个是 LANA 参考文件（已归档）、4 个为候选（见 §2）。

## 2) 重复/浪费判定

| # | file:decl | 判定 | 证据/建议 |
|---|---|---|---|
| 1 | `Mzk1LogVolumeRealActual.lean`（`logVolume_mul/pow/inv/one`） | **重复基础（Mathlib）** | 四个定理分别直接等于 `Real.log_mul/Real.log_pow/Real.log_inv/Real.log_one`，纯 re-export wrapper；建议删除，调用方直接用 Mathlib。 |
| 2 | `Mzk1IUTIVStage5NumericalCoreActual.lean`（`exists_delta_sq_le_one_add`, `additiveHeightWeightBound_of_literalEstimates`, `additiveHeightWeightBound_of_literalEstimates_nondilatedMain`） | **重复自研基础（应合并）** | 与既有 `Mzk1IUTIVStage5ABCFormActual.lean` 的 `exists_delta_sq_le_one_add`（同一证明）、`abcFormAdditiveHeightBound_of_literalEstimates`（同一吸收论证）重复；只是换成 `AdditiveHeightWeightBound` 抽象名。建议：删掉 core，或让 ABCForm 的证明改为引用 core（单一来源）。 |
| 3 | `A502HcompToRealAdapterActual.lean:toReal_le_of_le_ofReal` | **重复基础（LeanFormal）** | 与 `LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean` 的同名引理完全重复；应 import 后者而非重写。 |
| 4 | `Mzk1ThetaPilotObjectActual.lean` 的 `ind1Act`/`ind2Act` | **概念/命名重复** | LeanFormal `IUTIII/Theorem311/ConcreteFiniteModel.lean:121/124` 已有同名 `ind1Act/ind2Act`（语义不同：有限模型 vs 函数空间作用）；新文件在 `Mzk1ThetaPilotObjectActual` 自建同名定义。建议重命名（如 `thetaInd1Act`）或复用 foundation 的作用类型；避免同名混淆。 |
| 5 | `Mzk1MultiradialRepresentationActual.lean`（`MultiradialRepresentation`, `multiradialRepresentationOf`, `mrr_*_constructed`） | **重复包装（identity wrapper 风险）** | 字段 `lattice/logChain/shell/qTheta/nativePlace/hullState` 全部是参数；`_constructed` 为 `:= rfl` 投影；没有构造新的 lattice/shell/qTheta 实例。虽非基础重复，但属于“把已有对象打包”，不应算新对象/进度；真正缺的是 lattice/shell 的实例。 |
| 6 | `A499QPilotObjectActual.lean`（`qPilotValue/qPilotLog/QPilotObject`） | **可接受的局部新对象** | 只用 Mathlib p-adic（规范基础），未重复外部项目；但只是单素数局部 q-pilot，不是 global q-pilot。 |
| 7 | `Mzk1NormalizedComparisonRegionActual.lean` | **正确复用** | 使用 `S2723GlobalIQHullActual` + LeanFormal `Cor312ToABCBridgeInterface`，并证明与 core `normalizedComparisonRegion` 相等；无重复基础。 |
| 8 | `Mzk1ThetaPilotIndependentReadoutActual/ThetaPilotIndependentReadout` | **正确复用** | 用 S3137 C3 Haar 实际读法 + 独立 q 读法；比较 `ThetaHullComparison` 明示 named gap。 |
| 9 | `Mzk1PadicLogVolumeBridgeActual` | **正确复用（Takkun）** | 用 Takkun `IUT.Padic.logVol/logVol_*` 具体引理填充对象，不再手写 p-adic 体积律。 |

## 3) 关键风险：外部基础“移植了但没人用”

- 最近 120 文件中 **0 个** import `tmp.local-cft-port`、**0 个** import `tmp.external.ported`（TauCeti/Fermat/Belyi 全部已有移植）。这意味着大量新文件仍在手写外部基础本可覆盖的内容（p 进分析/曲线/高度/模形式）。
- 已开始的补救：A506 从 ported flt 选 10 个模块（different/留数/Weil differential、椭圆曲线 Frobenius/GaloisRep/Frey、Hecke、Riemann–Roch）用 `tools/extras_add_closure.mjs` 入队（closure 84、added 79；详见 `coord/PORTED-FLT-ASSETS.md`）。
- 建议规则：新增文件先 grep `tmp.external.ported`、`tmp.local-cft-port`、`tmp.sheaf.takkun`、`LeanFormal`；若基础已有，直接 import；缺 olean 时用 `extras_add_closure` 入队闭包，而不是手写。

## 4) Takkun/ported 编译与 OOM 状态（A504/A506 相关）

- Takkun: 43 DONE、3 FAIL、42 oleans；FAIL = `Padic/LogShellRadius.lean`（OOM）、`EllipticCurve/FieldOfModuli.lean`（OOM，已收窄 import）、`Padic/PadicExp.lean`（4.32.2 API 差异：`Finset.HasAntidiagonal.antidiagonal n` → 已修为 `Finset.antidiagonal n`，待重编）。
- ported: 1093 oleans 已存在；本轮新增 flt 条目 177；plan 旧（05:47:03），等 reload 后编译。
- OOM 主因判断：并发 12 个 Lean 进程 + 重型 `Mathlib` import；收窄 import 对 `FieldOfModuli` 已做；`LogShellRadius` 仍 import `Mathlib.Tactic`（可进一步收窄到 Linarith/NormNum/Positivity，但 `omega` 的 module 需先确认，避免破坏编译）。

## 5) 建议行动

1. **删除/合并重复**: `Mzk1LogVolumeRealActual`、`Mzk1IUTIVStage5NumericalCoreActual`（或反向统一到 core）、`A502HcompToRealAdapter.toReal_le_of_le_ofReal`；`Mzk1ThetaPilotObjectActual.ind1Act/ind2Act` 重命名避免与 LeanFormal 同名。
2. **禁止重复包装**: `Mzk1MultiradialRepresentationActual` 的字段/`_constructed := rfl` 不得计入对象 gate；若要成为 O3 对象，需实例化 lattice/shell（否则只是 `UnifiedSkeleton` 同类包装）。
3. **优先移植基础**: 后续 p 进/曲线/高度/椭圆曲线任务先查 `tmp/external/ported/flt*`、TauCeti、local-cft；用 `extras_add_closure` 入队闭包。
4. **维持空壳拦截**（A503）: 新增 `def X (p:Prop):=p`、`:= True`、identity wrapper 继续登记 DAG-BLOCKED。
