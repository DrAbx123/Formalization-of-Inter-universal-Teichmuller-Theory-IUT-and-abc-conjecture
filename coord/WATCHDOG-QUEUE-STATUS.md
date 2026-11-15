# Watchdog 队列与索引状态

快照时间：2026-11-15 10:21 CST（watchdog.log 最新 02:20:37Z）
范围：只读审计；未运行 Lean 编译，未修改任何 Lean 源或索引文件。

## 1. 当前 whitelist

| 项 | 数值 |
|---|---:|
| 非空行 | 83 |
| 唯一路径 | 81 |
| 重复条目 | 2：`Mzk1ActualRamifiedDataActual.lean`、`Mzk1IVThm110Actual.lean` 各 2 次 |
| 不存在路径 | 0 |
| 绝对/反斜杠路径 | 0 |

## 2. 当前状态

| 状态 | 数量 |
|---|---:|
| DONE | 67 |
| RUNNING | 4 |
| FAIL | 7 |
| PENDING | 3 |

### 2.1 当前 RUNNING（4）
- `tmp/sheaf/xif/paper/Mzk1GaloisCompletionActual.lean`
- `tmp/sheaf/xif/paper/Mzk1ThetaUnitLatticeBoundActual.lean`
- `tmp/sheaf/xif/paper/Mzk1PadicValuedOnlyProbeActual.lean`
- `tmp/sheaf/xif/paper/Mzk1GaloisValOnlyProbeActual.lean`

### 2.2 当前 FAIL（7）
1. `LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean`
2. `tmp/sheaf/xif/paper/Mzk1GaloisCompletionCurrentProbeActual.lean`（stale probe）
3. `tmp/sheaf/xif/paper/Mzk1IVThm110UnitRegionScalingActual.lean`（stale dependency）
4. `tmp/sheaf/xif/paper/Mzk1P2Log1pHalfActual.lean`（stale/dirty）
5. `tmp/sheaf/xif/paper/Mzk1TaskECompletionFieldEquivActual.lean` @02:20:37Z
6. `tmp/sheaf/xif/paper/Mzk1QVMultiplicityBridgeActual.lean` @02:19:38Z
7. `tmp/sheaf/xif/paper/Mzk1PadicGaloisProbeActual.lean` @02:15:37Z（stale probe）

说明：TaskECompletion 在 02:19:54 START、02:20:37 FAIL；Lead 消息中的 “TaskE running” 是 START 时刻，当前已是 FAIL。

### 2.3 精确首错
- **QVMultiplicityBridgeActual**：unknown identifier
  - `qVFamily`
  - `qVEffectiveMultiplicity_eq_order_mul_localResidueDegree`
  - `qVFactor_logVolume_with_mult`
  - 判断：缺 S3133 相关 import/open，或 donor 文件未加载；不是 stale olean。
- **TaskECompletionFieldEquivActual**：结构断裂
  - 首错转为 `synthInstanceFailed: Field GaussianField`；
  - 之前 `CompletionFieldQFiveEquivRequired` unknown constant 仍是结构问题；
  - 非 stale。
- **ThetaUnitLatticeBoundActual**：measure 实例
  - `IsFiniteMeasureOnCompacts μ` synth 失败；
  - `Measure.measure_pos_of_mem_nhds` 处 `L ∈ nhds ?m` 失败。
- **GaloisCompletionActual**：rewrite 目标不匹配
  - `Valued.v ((withValMovedSigma ?T ?σ ?v) ?x)` pattern 不在目标；
  - 真实证明错误，不是 stale。
- stale probe：`GaloisCompletionCurrentProbe`、`Mzk1PadicGaloisProbe`、`IVThm110UnitRegionScaling`、`P2Log1pHalf`。

### 2.4 PENDING（3）
- `Mzk1IVThm110UnitLogNormHalfActual`
- `NormalizedCompletionPadicBridgeActual`
- `NormalizedCompletionUnitLogActual`

## 3. 活跃文件覆盖

- **IV 主线：29/29 已入 whitelist**。
- 当前 whitelist 是 81 个唯一路径精选 active set，不是全目录队列。

未整组入队：
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

## 4. 队列卫生

- whitelist 已相对路径；无绝对路径。
- 重复：`Mzk1ActualRamifiedDataActual`、`Mzk1IVThm110Actual`。
- state.json 历史 failed 175 条（122 在 whitelist、53 移出）；全库 stale olean 假错 81 条。
- dirty/fail 后 retouch 4 个：
  - `Mzk1P1LocalizedFractionalIdealMapActual`
  - `Mzk1IVThm110UnitRegionScalingActual`
  - `IntegralUnitLogarithm`
  - `Mzk1P2Log1pHalfActual`

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

这些目录均不在 `lakefile.toml` 的 `lean_lib`，建议标 archive/port。

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

1. 等 4 RUNNING：GaloisCompletion、ThetaUnit、PadicValuedOnlyProbe、GaloisValOnlyProbe。
2. 修真实错误：
   - QVMultiplicityBridge：补 S3133 donor import/open（`qVFamily` 等）；
   - TaskECompletion：恢复 `CompletionFieldQFiveEquivRequired` + 修 `Field GaussianField`；
   - ThetaUnit：补 `IsFiniteMeasureOnCompacts μ` 实例/邻域；
   - GaloisCompletion：按 `withValMovedSigma` 目标重写。
3. stale probe 等依赖 DONE 后 retouch。
4. 3 PENDING 等 watchdog。
5. 去重两个 whitelist 条目。

## 7. 结论

- whitelist：83 行 / 81 唯一 / 0 缺失；
- 状态：DONE 67 / RUNNING 4 / FAIL 7 / PENDING 3；
- QVMultiplicityBridge FAIL 02:19:38（缺 qV donor 标识符）；TaskECompletion 02:20:37 FAIL（结构断裂）；ThetaUnit/GaloisCompletion 仍在跑（另有 FAIL 记录，需下一 cycle 判定）；
- 索引缺根见 §5。

未直接编译；所有验证以 watchdog 的 DONE/FAIL 为准。
