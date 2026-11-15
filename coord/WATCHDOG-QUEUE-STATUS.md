# Watchdog 队列与索引状态

快照时间：2026-11-15 09:58 CST（watchdog.log 最新 DONE 01:58:32Z）
范围：只读审计；未运行 Lean 编译，未修改任何 Lean 源或索引文件。

## 1. 当前 whitelist

| 项 | 数值 |
|---|---:|
| 非空行 | 75 |
| 唯一路径 | 74 |
| 重复条目 | 1：`Mzk1IVThm110Actual.lean` 出现 2 次 |
| 不存在路径 | 0 |
| 绝对/反斜杠路径 | 0（已统一为相对路径） |

结论：当前 whitelist 是 74 个唯一相对路径，不是 75 个唯一文件；75 是含重复行的行数。

## 2. 当前状态（基于最近 log + results/state）

| 状态 | 数量 |
|---|---:|
| DONE | 60 |
| RUNNING（最近 START 未终结） | 6 |
| FAIL（最近失败） | 5 |
| PENDING（无结果） | 3 |

### 2.1 当前 RUNNING
- `tmp/sheaf/xif/paper/Mzk1ActualRamifiedDataActual.lean`
- `tmp/sheaf/xif/paper/Mzk1GaloisCompletionActual.lean`
- `tmp/sheaf/xif/paper/Mzk1IVThm110Actual.lean`
- `tmp/sheaf/xif/paper/Mzk1ThetaFullLatticeBoundActual.lean`
- `tmp/sheaf/xif/paper/Mzk1Cor312ToABCConsumerActual.lean`
- `tmp/sheaf/xif/paper/Mzk1RamifiedPlaceDataActual.lean`

### 2.2 当前 DONE（本轮里程碑）
- `S3171IUTIVSection1DisplayActual` @01:52:21Z
- `Mzk1PadicFieldValuedBridgeActual` @01:49:56Z
- `Mzk1TaskECompletionFieldEquivActual` @01:54:33Z
- `QPilotGlobalLogVolumeFromQActual` @01:54:53Z
- `S3133RealifiedQPilotDivisorActual` @01:55:48Z
- `S3133QPilotReadoutActual` @01:55:52Z
- `S3133RealifiedQPilotLogVolumeActual` @01:56:41Z
- `S3133QPilotLogVolumeAgreementActual` @01:57:36Z
- `Cor312ToABCBridgeInterface` @01:58:32Z
另有 51 个 whitelist 文件在更早批次 DONE。

### 2.3 当前 FAIL（5）
1. `LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean`
2. `tmp/sheaf/xif/paper/Mzk1GaloisCompletionCurrentProbeActual.lean`
3. `tmp/sheaf/xif/paper/Mzk1IVThm110UnitRegionScalingActual.lean`
4. `tmp/sheaf/xif/paper/Mzk1P2Log1pHalfActual.lean`
5. `tmp/sheaf/xif/paper/Mzk1TaskEProbeActual.lean`

其中 stale olean/依赖假错：**2**
- `Mzk1IVThm110UnitRegionScalingActual`
- `Mzk1TaskEProbeActual`

其他 3 条需按 per-file 首错处理；IntegralUnitLogarithm 是 fail 后 retouch 的 dirty 核心文件之一。

### 2.4 当前 PENDING（3）
- `tmp/sheaf/xif/paper/Mzk1IVThm110UnitLogNormHalfActual.lean`
- `tmp/sheaf/xif/paper/NormalizedCompletionPadicBridgeActual.lean`
- `tmp/sheaf/xif/paper/NormalizedCompletionUnitLogActual.lean`

## 3. 活跃文件是否全部入队

### 3.1 已完整入队
- **IV 主线**：29/29 全部在 whitelist。
- **S3133 / qPilot global log / Cor312 接口**：相关主入口在 whitelist，且多数已 DONE。
- **Normalized completion / unitLog / norm valuation 的代表入口**：部分已入队（详见 3.2）。

### 3.2 未整体入队（按目录扫描）
| 类别 | 目录内总数 | whitelist | 缺口 |
|---|---:|---:|---:|
| P1 | 184 | 0 | 184 |
| Ob33 | 18 | 0 | 18 |
| B5 | 41 | 0 | 41 |
| P2 | 68 | 1 | 67 |
| P3 | 119 | 0 | 119 |
| stage4 | 105 | 0 | 105 |
| hq / hθ | 48 | 1 | 47 |
| tensor | 210 | 1 | 209 |

解释：
- 当前 whitelist 是**精选当前主线 74 文件**，不是全目录队列；
- 因此“所有活跃文件都已排队”只在“当前 74 文件 active set”意义上成立；
- 若 P1/Ob33/B5/P3/stage4/hq/tensor 仍算活跃线，则**没有全部入队**，尤其 stage4 整组 0/105、tensor 1/210。

## 4. 队列卫生与 stale 状态

- whitelist 已无绝对 Windows 路径，已统一相对路径。
- 唯一重复：`Mzk1IVThm110Actual.lean` 出现 2 次，可去重。
- state.json 仍有历史 failed 记录：175 条（其中 122 在 whitelist、53 已不在 whitelist）；全库 stale olean 假错 81 条。
- fail 后已 retouch、等待重编的 dirty 文件 4 个：
  - `Mzk1P1LocalizedFractionalIdealMapActual`
  - `Mzk1IVThm110UnitRegionScalingActual`
  - `IntegralUnitLogarithm`
  - `Mzk1P2Log1pHalfActual`

处理原则：stale 假错只在依赖 DONE 后 retouch，不改证明；真实 fail 按 per-file 首错修。

## 5. 索引覆盖审计（未改索引）

缺少 `_INDEX/README.md` 的实际 Lean 根：
- `external/`（462 个 .lean）
- `Heights/`（64）
- `OrbicurveCores/`（134）
- `Genl/`（9）

活跃子根缺本地 `_INDEX`：
- `LeanFormal/IUT/`
- `LeanFormal/Archive/`
- `Iut/Foundations/`

这些目录都不在 `lakefile.toml` 的 `lean_lib`（LeanFormal/Iut/PadicField 等）中，建议索引标为 archive/port，不当作活跃构建根。

非 Lean 根/生成目录，不建议建 `_INDEX`：
`coord`、`logs`、`metadata-probes`、`scripts`、`verification`、`iut-audit-20261113`、`vendor`、`Mathlib`。

已核对存在且路径正确的索引/donor：
- `tmp/local-cft-port/PadicField/FieldNorm.lean`
- `tmp/local-cft-port/_INDEX/README.md`
- `tmp/external/ported/_INDEX/README.md`
- `tmp/sheaf/_INDEX/README.md`
- `tmp/sheaf/xif/paper/_INDEX/README.md`
- `LeanFormal/_INDEX/README.md`
- `Iut/_INDEX/README.md`
- `LocalClassFieldTheory/_INDEX/README.md`

## 6. 禁止 direct lean 下的下一步队列

1. **等当前 6 RUNNING 收尾**；不要在此期间改这些文件。
2. **清理 whitelist**：删 `Mzk1IVThm110Actual.lean` 重复行；保持 74 个唯一相对路径。
3. **2 个 stale FAIL**：`Mzk1IVThm110UnitRegionScalingActual`、`Mzk1TaskEProbeActual` 等依赖 DONE 后 retouch。
4. **3 个 PENDING** 由 watchdog 自然抽取；若长时间不跑，再确认是否在 whitelist 中（当前在）。
5. **P1/Ob33/B5/P3/stage4/hq/tensor**：按 owner 确认后分组补入 whitelist；不要零散全加 700+ 文件。
6. **索引修复**：补 `LeanFormal/IUT/_INDEX` 或明确代管；给缺失根加 archive/port 行；更新 `coord/LEAN-INDEX.md` 规则为“每个 lean_lib/活动根”。

## 7. 状态结论

- whitelist：**75 行 / 74 唯一 / 0 缺失路径**；
- 状态：**DONE 60 / RUNNING 6 / FAIL 5 / PENDING 3**；
- 活跃 IV 主线 29/29 已入队；
- 但 P1/Ob33/B5/P3/stage4/hq/tensor 没有整组入队；当前是 74 文件精选队列；
- stale 假错 2 条在 whitelist 内，dirty 4 条等待重编；
- 索引缺根已列于 §5。

未直接编译；所有验证以 watchdog 的 DONE/FAIL 为准。
