# Watchdog 队列与索引状态

快照时间：2026-11-15 09:44 CST（依据 state.json / watchdog.log mtime）
范围：只读审计；未运行 Lean 编译，未修改任何 Lean 源或索引文件。

## 1. 数据源与计数

| 数据源 | 当前计数/说明 |
|---|---|
| `dag/watchdog/extra-targets.txt` | 1363 个唯一路径；0 个不存在路径 |
| `tmp/xif_guarded_results.log` | 13924 条历史结果：DONE=9694，FAIL=4226 |
| `dag/watchdog/state.json` | 175 个 failed 记录；其中 122 仍在 whitelist，53 已不在 whitelist |
| `dag/watchdog/watchdog.log` 最近 400 行 | 10 个当前/最近 START 未终结 |
| whitelist 无任何结果 | 43 个（pending/unrun/路径格式问题） |

注意：results 是累计历史，不是本轮 batch 结果；DONE/FAIL 数不代表当前队列状态。

## 2. 当前运行时（最近 log START 未终结）

- `tmp/sheaf/xif/paper/Mzk1GaloisCompletionActual.lean`
- `tmp/sheaf/xif/paper/Mzk1IVThm110TensorUnitBallActual.lean`
- `tmp/sheaf/xif/paper/Mzk1P2DetHaarConsumerActual.lean`
- `tmp/sheaf/xif/paper/Mzk1P2NoDetRankOneActual.lean`
- `tmp/sheaf/xif/paper/Mzk1P2DetCoefficientFinalActual.lean`
- `tmp/sheaf/xif/paper/Mzk1NativeHaarNormalizationActual.lean`
- `tmp/sheaf/xif/paper/Mzk1UnitMassNormalizationBridgeActual.lean`
- `tmp/sheaf/xif/paper/Mzk1Ob33B5GeneratorCandidateActual.lean`
- `tmp/sheaf/xif/paper/Mzk1Ob33B5CountUnconditionalAttemptActual.lean`
- `tmp/sheaf/xif/paper/Mzk1IVThm110SlackReductionActual.lean`

## 3. Failed / pending 分类

### 3.1 state failed
- 总 failed 记录：**175**
- 仍在 whitelist：**122**
- 已不在 whitelist（清理候选）：**53**
- 最近源码被 retouch、但 state 仍是 failed：**4**
  - `tmp/sheaf/xif/paper/Mzk1P1LocalizedFractionalIdealMapActual.lean`
  - `tmp/sheaf/xif/paper/Mzk1IVThm110UnitRegionScalingActual.lean`
  - `LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean`
  - `tmp/sheaf/xif/paper/Mzk1P2Log1pHalfActual.lean`

### 3.2 stale olean 假错
按 per-file log 最后一条 error 是否包含
`object file ... does not exist` / `failed to read file` 分类：

- whitelist 内 stale dependency 假错：**45**
- 全 state 内 stale dependency：**81**
- 其余 94 条需按真实证明错误处理。

stale 样例：
- `tmp/sheaf/xif/paper/Mzk1P2Route2SummaryActual.lean`
- `tmp/sheaf/xif/paper/Mzk1P1CountLocalGeneratorActual.lean`
- `tmp/sheaf/xif/paper/Mzk1P1LocalValuationGeneratorActual.lean`
- `tmp/sheaf/xif/paper/Mzk1P1CountFromGeneratorAttemptActual.lean`
- `tmp/sheaf/xif/paper/Mzk1B5FiniteIndexExpansionIffActual.lean`
- `tmp/sheaf/xif/paper/Mzk1C17ResNormDegreeGapOfResidueOneActual.lean`
- `tmp/sheaf/xif/paper/Mzk1C17ResidueOneBothSidesActual.lean`

处理原则：**不要改证明**；等依赖 DONE 后 retouch 本文件。watchdog 的 RETRY TRANSIENT 会处理一部分。

### 3.3 pending / 无结果
whitelist 中 43 个无历史结果，显著分组：
- 活跃 root 文件（约 19）：
  - `GlobalThetaPilotPossibleImagesActual`
  - `GlobalThetaPilotPossibleImageGeometryActual`
  - `GlobalThetaPilotProcessionActual`
  - `GlobalThetaPilotPlaceComparisonActual`
  - `S778PaperQPilotHalfRegionActual`
  - `OrigXiFPaperQPilotObjectActual`
  - `Mzk1P1LocalizedSpanProofActual`
  - `Mzk1IVThm110UnitLogNormHalfActual`
  - `BasePlaceQCandidateActual`
  - `BaseQContractionUnconditional`
  - `BaseQDescentAssembly`
  - `NormalizedNormValuationResidueActual`
  - `NormalizedCompletionUnitLogActual`
  - `NormalizedCompletionPadicBridgeActual`
  - `Mzk1ResidueGaloisWProbeActual`
  - `Mzk1PadicFieldValuedBridgeActual`
  - `RelativeNormFieldNormActual`
  - `Mzk1ThetaFullLatticeBoundActual`
  - `S3171IUTIVSection1DisplayActual`
- external FLT port 路径（13 条），例如
  `tmp/external/ported/flt/FLT/.../AdicValuation.lean`；
- TauCetiPort 绝对 Windows 路径（11 条），例如
  `D:\lean\tmp\sheaf\xif\paper\TauCetiPort\...`。

## 4. 活跃类别 whitelist 覆盖

| 类别 | 目录内总数 | whitelist 内 | 未进 whitelist |
|---|---:|---:|---:|
| principal | 38 | 29 | 9 |
| card（窄） | 83 | 17 | 66 |
| unitLog | 13 | 8 | 5 |
| norm valuation | 19 | 12 | 7 |
| stage4 | 105 | 0 | 105 |
| hq / hθ | 48 | 13 | 35 |
| tensor | 210 | 29 | 181 |
| P1 | 184 | 108 | 76 |
| Ob33 | 18 | 18 | 0 |
| B5 | 41 | 41 | 0 |
| IV | 29 | 29 | 0 |
| P2 | 68 | 66 | 2 |
| P3 | 119 | 119 | 0 |

说明：
- 宽泛 `Card|Principal|UnitLog|Norm` 模式会命中大量 adapted/probe/archive 文件，不能全加入队列；上表 card/principal 等只是找“可能活跃”候选。
- **stage4 全部 105 个都不在 whitelist**。若 Stage4 仍是活跃线，这是最大覆盖缺口；若已归档，应在索引中明确标注。
- hq/hθ 只进了 `Mzk1HqHthetaStructuralObstructionActual`，acceptance/gate 文件均未入 whitelist。
- P2 仅缺两个：
  - `tmp/sheaf/xif/paper/Mzk1P2DeficitActual.lean`
  - `tmp/sheaf/xif/paper/Mzk1P2FaithfulLogMuShaActual.lean`

## 5. 队列卫生问题

1. **路径格式不一致**
   whitelist 含绝对 Windows 路径（`D:/lean/...` 与 `D:\lean\...`），而 watchdog 正常使用相对路径（`tmp/...`）。这些会被当作不同条目/no-result；建议统一为相对路径并去重。

2. **external/TauCeti 非项目根**
   whitelist 含 `tmp/external/ported/flt/...` 的 Mathlib 副本与 `TauCetiPort` 绝对路径；它们不是当前项目 lean_lib，建议从活跃 whitelist 移出，另设 donor 列表。

3. **state 外失败记录 53 条**
   这些已不在 whitelist，仍占 state.json；建议只读清理/归档，不要在 state 中保留为活动失败。

4. **历史 results 与当前状态混淆**
   `tmp/xif_guarded_results.log` 是累计 13924 条；不能用 DONE/FAIL 总数判断当前 gate，必须看每文件最新结果 + state + 当前 batch log。

## 6. 索引覆盖审计（上次报告摘要）

实际 Lean 根但无 `_INDEX/README.md`：
- `external/`（462 个 .lean）
- `Heights/`（64）
- `OrbicurveCores/`（134）
- `Genl/`（9）

活跃根缺本地 `_INDEX`：
- `LeanFormal/IUT/`
- `LeanFormal/Archive/`
- `Iut/Foundations/`

这些目录都不在 `lakefile.toml` 的 `lean_lib`（`LeanFormal`、`Iut`、`PadicField` 等）中，故建议索引标注为 “archive/port，未入 lakefile”，不要当作活跃构建根。

非 Lean 根/生成目录，不建议建 `_INDEX`：
`coord`、`logs`、`metadata-probes`、`scripts`、`verification`、`iut-audit-20261113`、`vendor`、`Mathlib`。

已核对存在且路径正确的索引/ donor：
- `tmp/local-cft-port/PadicField/FieldNorm.lean`
- `tmp/local-cft-port/_INDEX/README.md`
- `tmp/external/ported/_INDEX/README.md`
- `tmp/sheaf/_INDEX/README.md`
- `tmp/sheaf/xif/paper/_INDEX/README.md`
- `LeanFormal/_INDEX/README.md`
- `Iut/_INDEX/README.md`
- `LocalClassFieldTheory/_INDEX/README.md`

## 7. 禁止 direct lean 下的下一步队列

1. **P0 路径卫生**：统一 whitelist 为相对路径；去重绝对路径；把 external FLT/TauCetiPort 移出活跃 whitelist（另设 donor 列表）。
2. **P0 stale 重建**：对 45 个 whitelist stale-dependency 文件，等依赖 DONE 后 retouch；不修改证明。
3. **P0 dirty 4 文件**：自然 retouch 后由 watchdog 重编，优先核 `IntegralUnitLogarithm.lean` 这种核心定义。
4. **P1 活跃缺口补齐**（经 owner 确认）：
   - P2 两个缺失：`Mzk1P2DeficitActual`、`Mzk1P2FaithfulLogMuShaActual`；
   - Hq/hθ acceptance/gate 文件按当前主线筛选后加入；
   - Stage4 若仍活跃，整组 105 个需要单独批次，不要零散加。
5. **P1 pending 分类**：43 个 no-result 中，先处理 19 个活跃 root 文件；external/TauCeti 绝对路径不应作为 pending。
6. **P2 索引修复**：补 `LeanFormal/IUT/_INDEX` 或明确代管；给缺失根加 archive/port 行；更新 `coord/LEAN-INDEX.md` §1 规则“每个 lean_lib/活动根”。

## 8. 状态结论

- 当前 watchdog 有 **10 个近期 running**；
- whitelist **1363 条**，其中 **43 条无结果**；
- state 记录 **175 failed**：**122 在 whitelist**，**81 全库 stale 假错**，**45 在 whitelist**；
- **stage4/hq/tensor 是 whitelist 覆盖缺口最大三类**；
- 索引缺根：`external`、`Heights`、`OrbicurveCores`、`Genl`，以及活跃子根 `LeanFormal/IUT` 的本地索引。

未直接编译；所有验证以 watchdog 的 DONE/FAIL 为准。
