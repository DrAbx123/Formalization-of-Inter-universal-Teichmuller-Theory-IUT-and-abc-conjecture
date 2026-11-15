# Watchdog 队列与索引状态

快照时间：2026-11-15 10:03 CST（watchdog.log 最新 02:02:12Z）
范围：只读审计；未运行 Lean 编译，未修改任何 Lean 源或索引文件。

## 1. 当前 whitelist

| 项 | 数值 |
|---|---:|
| 非空行 | 75 |
| 唯一路径 | 74 |
| 重复条目 | 1：`Mzk1IVThm110Actual.lean` 出现 2 次 |
| 不存在路径 | 0 |
| 绝对/反斜杠路径 | 0（已统一相对路径） |

## 2. 当前状态

| 状态 | 数量 |
|---|---:|
| DONE | 64 |
| RUNNING | 2 |
| FAIL | 6 |
| PENDING | 4 |

### 2.1 RUNNING（2）
- `tmp/sheaf/xif/paper/Mzk1GaloisCompletionActual.lean`（retry）
- `tmp/sheaf/xif/paper/Mzk1TaskECompletionFieldEquivActual.lean`（结构断裂，重试中）

### 2.2 新 cycle DONE
- `Mzk1TaskEProbeActual` @02:01:32Z
- `Mzk1PadicFieldValuedQpActual` @02:01:55Z
- `Mzk1RamifiedPlaceDataActual` @01:59:07Z
- `Mzk1IVThm110Actual` @01:59:08Z
- `Mzk1Cor312ToABCConsumerActual` @01:59:35Z
- `Cor312ToABCBridgeInterface` @01:58:32Z
- 另有 S3133 四件、S3171、QPilotGlobalLog、TaskGDonor 等在前一 cycle DONE。

### 2.3 新 cycle FAIL（6）
1. `LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean`（无最近 log 事件；state fail/dirty）
2. `Mzk1ActualRamifiedDataActual` @01:59:08Z
3. `Mzk1GaloisCompletionCurrentProbeActual` @01:52:23Z
4. `Mzk1IVThm110UnitRegionScalingActual`（stale dependency 假错）
5. `Mzk1P2Log1pHalfActual`（dirty/最近无事件）
6. `Mzk1ThetaFullLatticeBoundActual` @01:59:10Z

### 2.4 精确首错备注
- **TaskECompletionFieldEquivActual**：结构断裂
  - 未知常量 `CompletionFieldQFiveEquivRequired`；
  - `(kernel) unknown constant ...CompletionFieldQFiveEquivRequired`；
  - 不是 stale 假错，需要恢复该定义/接口。
- **ThetaFullLatticeBoundActual**：cast / logmono
  - 目标是 `(1:ℝ) ≤ (actualC3LogShellTensorHaar ...).toReal`，
    但给出的是 `(1:ℝ≥0∞) ≤ actualC3LogShellTensorHaar ...`；
  - 需 `ENNReal.toReal` 转换/单调性，随后 `linarith failed`；
  - 不是 stale 假错。
- **ActualRamifiedDataActual**：结构字段断裂
  - `mult is not a field of structure RamifiedPlaceData`（两处）；
  - 需对齐 `RamifiedPlaceData` 结构与消费者字段。
- stale dependency 假错：`Mzk1IVThm110UnitRegionScalingActual`、`Mzk1TaskEProbeActual`（后者本 cycle 已 DONE，state 仍历史 fail）。

### 2.5 PENDING（4）
- `Mzk1IVThm110UnitLogNormHalfActual`
- `NormalizedCompletionPadicBridgeActual`
- `NormalizedCompletionUnitLogActual`
- `Mzk1CheckSharpDonorProbe`

## 3. 活跃文件覆盖

- **IV 主线：29/29 已入 whitelist**。
- S3133 / qPilot global log / Cor312 主入口已入队，且多数 DONE。
- 当前 whitelist 是 74 文件精选 active set，不是全目录队列。

未整组入队（按目录扫描）：
| 类别 | 总数 | whitelist | 缺口 |
|---|---:|---:|---:|
| P1 | 184 | 0 | 184 |
| Ob33 | 18 | 0 | 18 |
| B5 | 41 | 0 | 41 |
| P2 | 68 | 1 | 67 |
| P3 | 119 | 0 | 119 |
| stage4 | 105 | 0 | 105 |
| hq/hθ | 48 | 1 | 47 |
| tensor | 210 | 1 | 209 |

结论：
- “当前 74 精选 active set 已全部排队”成立；
- “所有活跃线全排队”不成立，尤其 stage4 0/105、tensor 1/210；
- 若 P1/Ob33/B5/P3/stage4/hq/tensor 仍是活跃线，需 owner 分组补队列。

## 4. 队列卫生

- whitelist 已统一相对路径；无绝对 Windows 路径。
- 唯一重复：`Mzk1IVThm110Actual.lean` 出现 2 次，建议去重。
- state.json 仍有历史 failed 175 条；其中 122 在 whitelist、53 已移出。
- 全库 stale olean 假错 81 条（whitelist 内约 45 条历史）；当前 cycle 具体 stale fail 2 条。
- fail 后 retouch/dirty 4 个：
  - `Mzk1P1LocalizedFractionalIdealMapActual`
  - `Mzk1IVThm110UnitRegionScalingActual`
  - `IntegralUnitLogarithm`
  - `Mzk1P2Log1pHalfActual`

处理：stale 只在依赖 DONE 后 retouch，不改证明；真实结构错误按上面 per-file 首错修。

## 5. 索引覆盖审计（未改索引）

缺 `_INDEX/README.md` 的实际 Lean 根：
- `external/`（462 个 .lean）
- `Heights/`（64）
- `OrbicurveCores/`（134）
- `Genl/`（9）

活跃子根缺本地 `_INDEX`：
- `LeanFormal/IUT/`
- `LeanFormal/Archive/`
- `Iut/Foundations/`

这些目录均不在 `lakefile.toml` 的 `lean_lib`，建议标 archive/port，不当作活跃构建根。

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

## 6. 下一步队列（禁止 direct lean）

1. 等 2 个 RUNNING：GaloisCompletion 重试、TaskECompletion 结构恢复后重编。
2. 修结构错误：
   - TaskECompletion：恢复 `CompletionFieldQFiveEquivRequired` 定义/接口；
   - ThetaFullLattice：`ENNReal.toReal` + logmono/linarith；
   - ActualRamifiedData：对齐 `RamifiedPlaceData` 的 `mult` 字段。
3. stale retouch：`IVThm110UnitRegionScaling` 等依赖 DONE 后再 retouch。
4. 4 PENDING 等 watchdog 自然抽取。
5. 去重 `Mzk1IVThm110Actual.lean`。
6. 其他主线按 owner 分组补入，尤其 stage4/tensor/P1/Ob33/B5。

## 7. 结论

- whitelist：75 行 / 74 唯一 / 0 缺失；
- 状态：DONE 64 / RUNNING 2 / FAIL 6 / PENDING 4；
- 新 cycle：TaskEProbe DONE、PadicFieldValuedQp DONE；TaskECompletion 结构断裂；ThetaFullLattice cast/logmono；ActualRamifiedData 结构字段断裂；
- 当前 74 精选 active set 已排；全目录活跃线未全排；
- 索引缺根见 §5。

未直接编译；所有验证以 watchdog 的 DONE/FAIL 为准。
