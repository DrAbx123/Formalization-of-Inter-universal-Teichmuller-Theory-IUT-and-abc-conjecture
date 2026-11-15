# Watchdog 队列与索引状态

快照时间：2026-11-15 10:42 CST（watchdog.log 最新 02:41:36Z）
范围：只读审计；未运行 Lean 编译，未修改 Lean 源或索引。

## 0. Revision 16 非空闲策略
- Goal revision 16，phase active，rounds 14/256。
- 不允许 lane 空转：watchdog 有 runnable 项时必须推进。
- 无 runnable Lean 时产出精确 gap/审计/队列更新，不得 direct lake env lean。
- 所有编译只走 watchdog，只信 DONE/FAIL。

## 1. 当前 whitelist
| 项 | 数值 |
|---|---:|
| 非空行 | 90 |
| 唯一路径 | 88 |
| 重复条目 | 2：Mzk1ActualRamifiedDataActual、Mzk1IVThm110Actual |
| 不存在路径 | 0 |
| 绝对路径 | 0 |

## 2. 当前状态
| 状态 | 数量 |
|---|---:|
| DONE | 77 |
| RUNNING | 0 |
| FAIL | 8 |
| PENDING | 3 |

### 2.1 本 cycle DONE
- Mzk1QVIndexMapActual @02:39:01Z
- Mzk1TaskEWQuotientFiveActual @02:38:34Z
- Mzk1TaskEIntegersRingEquivActual @02:40:03Z（02:38:36 FAIL 后修绿）
- Mzk1ThetaUnitLatticeBoundActual @02:40:26Z
- Mzk1TaskEUnitsTorsionActual @02:41:13Z
- RelativeNormFieldNormActual @02:41:36Z（02:39:09 FAIL 后修绿）

### 2.2 FAIL（8）
1. LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean
2. Mzk1GaloisCompletionActual @02:40:28Z
3. Mzk1GaloisCompletionCurrentProbeActual（stale probe）
4. Mzk1IVThm110UnitRegionScalingActual（stale dependency）
5. Mzk1P2Log1pHalfActual（stale/dirty）
6. Mzk1PadicGaloisProbeActual（stale probe）
7. Mzk1TaskECompletionFieldEquivActual @02:31:38Z
8. Mzk1Ind1WQuotientFiveIsoActual @02:39:59Z

### 2.3 精确首错
- GaloisCompletionActual：rewrite 失败；目标是 u ∈ Valued.v.valueGroup，pattern 是 valueMonoid；:95 不是 stale。
- Ind1WQuotientFiveIsoActual：unknown normedIntegerEquivValuative；且 padicIntegersEquivZp 历史依赖 sorryAx，必须清除；不是可接受 GREEN。
- TaskECompletionFieldEquivActual：synthInstanceFailed Field GaussianField；结构/实例问题。
- stale probe：GaloisCompletionCurrentProbe、PadicGaloisProbe、IVThm110UnitRegionScaling、P2Log1pHalf。
- 注：QVIndexMap、TaskEIntegers、ThetaUnit、TaskEUnitsTorsion、RelativeNorm 均已转 DONE。

### 2.4 PENDING（3）
- Mzk1IVThm110UnitLogNormHalfActual
- NormalizedCompletionPadicBridgeActual
- NormalizedCompletionUnitLogActual

## 3. Rev15/16 优先项对照
| 优先项 | 当前状态 |
|---|---|
| qV family / 全局 q | QVMultiplicityBridge DONE 02:27:50；QVIndexMap DONE 02:39:01 |
| stage4 | TaskEIntegers/ThetaUnit DONE 02:40；GaloisCompletion FAIL 02:40:28；TaskECompletion FAIL |
| θ-hull | ThetaUnitLatticeBound DONE 02:40:26；ThetaFullLattice 旧 hsub 方向作废 |
| RelativeNorm | DONE 02:41:36（scalar tower/v_norm 修绿） |
| A2 / WQuotient | TaskEWQuotientFive DONE；Ind1WQuotientFiveIso FAIL + sorryAx 历史 |

## 4. 活跃覆盖（按目录扫描）
- IV 主线：29/29 已入 whitelist。
- 当前 whitelist 是 88 唯一精选 active set，不是全目录队列。

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

## 5. 队列卫生
- whitelist 相对路径，无绝对路径。
- 重复：Mzk1ActualRamifiedDataActual、Mzk1IVThm110Actual。
- state.json 历史 failed 175 条（122 在 whitelist、53 移出）；全库 stale olean 假错 81 条。
- dirty/retouch 4 个：Mzk1P1LocalizedFractionalIdealMapActual、Mzk1IVThm110UnitRegionScalingActual、IntegralUnitLogarithm、Mzk1P2Log1pHalfActual。

## 6. 索引覆盖审计（未改索引）
缺 _INDEX/README.md 的实际 Lean 根：
- external/（462 个 .lean）
- Heights/（64）
- OrbicurveCores/（134）
- Genl/（9）

活跃子根缺本地 _INDEX：LeanFormal/IUT/、LeanFormal/Archive/、Iut/Foundations/。
均不在 lakefile.toml 的 lean_lib；建议标 archive/port。

非 Lean 根/生成目录不建 _INDEX：coord、logs、metadata-probes、scripts、verification、iut-audit-20261113、vendor、Mathlib。

已核对存在且路径正确：tmp/local-cft-port/PadicField/FieldNorm.lean、tmp/local-cft-port/_INDEX、tmp/external/ported/_INDEX、tmp/sheaf/_INDEX、tmp/sheaf/xif/paper/_INDEX、LeanFormal/_INDEX、Iut/_INDEX、LocalClassFieldTheory/_INDEX。

## 7. 下一步队列（禁止 direct lean）
1. 无 RUNNING；先修 WQuotient：unknown normedIntegerEquivValuative + 清除 padicIntegersEquivZp 的 sorryAx。
2. 修 GaloisCompletion valueMonoid/valueGroup rewrite；TaskECompletion Field GaussianField。
3. stale probe 等依赖 DONE 后 retouch；3 PENDING 等 watchdog。
4. 补 runnable active targets：A2、stage4 其余、P1/Ob33/B5/P3/tensor 按 owner 分组。
5. 去重两个 whitelist 条目。

## 8. 结论
- whitelist：90 行 / 88 唯一 / 0 缺失。
- 状态：DONE 77 / RUNNING 0 / FAIL 8 / PENDING 3。
- 本 cycle：QVIndexMap、TaskEIntegers、ThetaUnit、TaskEUnitsTorsion、RelativeNorm DONE；GaloisCompletion/Ind1WQuotientFiveIso FAIL；TaskEUnitsTorsion 已 02:41:13 DONE。
- Quality: Ind1WQuotientFiveIso 的 sorryAx 必须清除，不能算 GREEN。
- Rev16 非空闲：当前无 running，下一动作应修 WQuotient/Galois/TaskE 或补 runnable 队列。

未直接编译；所有验证以 watchdog 的 DONE/FAIL 为准。