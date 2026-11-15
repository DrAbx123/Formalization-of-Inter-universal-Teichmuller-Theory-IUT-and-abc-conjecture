# Watchdog 队列与索引状态

快照时间：2026-11-15 10:31 CST（watchdog.log 最新 02:31:00Z）
范围：只读审计；未运行 Lean 编译，未修改任何 Lean 源或索引文件。

## 1. 当前 whitelist

| 项 | 数值 |
|---|---:|
| 非空行 | 86 |
| 唯一路径 | 84 |
| 重复条目 | 2：`Mzk1ActualRamifiedDataActual.lean`、`Mzk1IVThm110Actual.lean` 各 2 次 |
| 不存在路径 | 0 |
| 绝对路径 | 0 |

## 2. 当前状态

| 状态 | 数量 |
|---|---:|
| DONE | 71 |
| RUNNING | 2 |
| FAIL | 8 |
| PENDING | 3 |

### 2.1 当前 RUNNING（2）
- `tmp/sheaf/xif/paper/Mzk1GaloisCompletionActual.lean`（retry）
- `tmp/sheaf/xif/paper/Mzk1TaskECompletionFieldEquivActual.lean`（retry）

### 2.2 本 cycle DONE（新增）
- `Mzk1PadicValuedOnlyProbeActual` @02:21:00Z
- `Mzk1ThetaUnitLatticeBoundActual` @02:21:03Z
- `Mzk1GaloisValOnlyProbeActual` @02:21:06Z
- `Mzk1GaloisCompletionActual` @02:21:06Z（随后 02:31 retry，当前 RUNNING）
- `Mzk1QVMultiplicityBridgeActual` @02:27:50Z

### 2.3 当前 FAIL（8）
1. `LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean`
2. `tmp/sheaf/xif/paper/Mzk1ContextGoalCheckActual.lean` @02:24:05Z
3. `tmp/sheaf/xif/paper/Mzk1GaloisCompletionCurrentProbeActual.lean` @02:26:42Z（stale probe）
4. `tmp/sheaf/xif/paper/Mzk1IVThm110UnitRegionScalingActual.lean`（stale dependency）
5. `tmp/sheaf/xif/paper/Mzk1P2Log1pHalfActual.lean`（stale/dirty）
6. `tmp/sheaf/xif/paper/Mzk1PadicGaloisProbeActual.lean` @02:26:42Z（stale probe）
7. `tmp/sheaf/xif/paper/RelativeNormFieldNormActual.lean` @02:30:44Z
8. `tmp/sheaf/xif/paper/Mzk1QVIndexMapActual.lean` @02:30:35Z

### 2.4 精确首错
- **RelativeNormFieldNormActual**
  - `synthInstanceFailed: IsScalarTower ℚ_[pBase X] (NativeBaseCompletionRaw X) (NativeFCompletion X)`;
  - `PadicField.v` / valuation 类型不匹配；
  - 真实 tower/归一化错误，不是 stale。
- **QVIndexMapActual**
  - unknown identifiers：`Bad`、`qVEffectiveMultiplicity`、`badPlaceIndex`；
  - 缺 S3133/Vbad donor 的 import/open，不是 stale olean。
- **ContextGoalCheckActual**
  - unknown identifier `Mzk1GaloisCompletionActual.valueGroup_comap_eq`；
  - 依赖 GaloisCompletion 中已改名/缺失的定理；结构漂移。
- stale probe：`GaloisCompletionCurrentProbe`、`PadicGaloisProbe`、`IVThm110UnitRegionScaling`、`P2Log1pHalf`。

### 2.5 PENDING（3）
- `Mzk1IVThm110UnitLogNormHalfActual`
- `NormalizedCompletionPadicBridgeActual`
- `NormalizedCompletionUnitLogActual`

## 3. 活跃文件覆盖

- **IV 主线：29/29 已入 whitelist**。
- 当前 whitelist 是 84 个唯一路径精选 active set，不是全目录队列。

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

- whitelist 已相对路径，无绝对路径。
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

1. 等 2 RUNNING：GaloisCompletion retry、TaskECompletion retry。
2. 修真实错误：
   - RelativeNormFieldNorm：补 `IsScalarTower ℚ_[pBase X] NativeBaseCompletionRaw NativeFCompletion` 与 valuation 归一化；
   - QVIndexMap：补 S3133/Vbad import/open（`Bad`、`qVEffectiveMultiplicity`、`badPlaceIndex`）；
   - ContextGoalCheck：对齐 `valueGroup_comap_eq` 的定义/名称；
   - IntegralUnitLogarithm：核心 dirty 重编。
3. stale probe 等依赖 DONE 后 retouch。
4. 3 PENDING 等 watchdog。
5. 去重两个 whitelist 条目。

## 7. 结论

- whitelist：86 行 / 84 唯一 / 0 缺失；
- 状态：DONE 71 / RUNNING 2 / FAIL 8 / PENDING 3；
- 本 cycle：ThetaUnit/GaloisValOnly/PadicValuedOnly/QVMultiplicityBridge DONE；RelativeNormFieldNorm、QVIndexMap、ContextGoalCheck FAIL；GaloisCompletion/TaskECompletion 重试中；
- 索引缺根见 §5。

未直接编译；所有验证以 watchdog 的 DONE/FAIL 为准。
