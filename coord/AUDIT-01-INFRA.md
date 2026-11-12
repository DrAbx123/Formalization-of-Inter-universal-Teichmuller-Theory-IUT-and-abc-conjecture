# AUDIT-01-INFRA — D:/lean 全仓基础设施审计（只读）

- **审计任务**：审计01-基础设施（lead 指令）
- **快照目标时间**：2026-11-13 02:30 Asia/Shanghai
- **实际采集时间**：2026-11-13 02:19:42 +08:00（2026-11-13，Asia/Shanghai）
- **方式**：只读（PowerShell/Get-ChildItem/Get-Content），未编译、未修改仓内文件（本报告除外）
- **不确定性标记**：凡未能直接验证者写 **UNKNOWN**；不做臆断。

---

## 1. 顶层目录清单与用途

| # | 目录/文件 | 用途（证据/推断） | 备注 |
|---|---|---|---|
| 1 | `.lake/` | Lean 构建产物（olean）与依赖包 | 15.31 GB，lean 10,107 |
| 2 | `vendor/` | 第三方 vendor 依赖 | 8.35 GB，lean 9,640 |
| 3 | `Mathlib/` | Mathlib 源码副本（顶层，非 .lake 内） | lean 计数见 .lake/vendor 区分 UNKNOWN |
| 4 | `Iut/` | lana IUT 主树（Cor312/WallEquiv/Concrete/Tripod/...） | lean 950，olean **374/950** |
| 5 | `LeanFormal/` | 本项目 Lean 形式化层（IUT/ABCBridge/...） | lean 1,189，olean 采样见 §3 |
| 6 | `TemperedFundamentalGroups/` | TG（Tempered Fundamental Groups）树 | lean 744 |
| 7 | `Oka/` `FormalSchemes/` `CurvesJacobian/` `EllipticCurves/` `Pi1/` `Belyi/` `Heights/` `WeilCurves/` `Genl/` `OrbicurveCores/` `LocalClassFieldTheory/` `ContinuousKummerTheory/` `TateCurvesTheta/` `PadicLogVolume/` | 各数学主题子库（lana/本项目模块树） | 计数见 §2 |
| 8 | `coord/` | 协调/审计/计划文档（1,175 md） | 冻结 pin、gate、port 计划均在此 |
| 9 | `dag/` | DAG watchdog 状态（plan/extra/order/state/heartbeat/logs） | 见 §5 |
| 10 | `tools/` | 自动化工具（watchdog、port、closure_analyze、feeder、retouch） | ps1=369/mjs=2,003 全仓 |
| 11 | `tmp/` | 工作目录：ported 树、paper 节点、外部仓库副本 | lean 167,699（5.44 GB） |
| 12 | `papers/` `Plans/` `docs/` `data/` `logs/` `scripts/` `checks/` `verification/` `external/` `metadata-probes/` | 论文/计划/文档/数据/日志/脚本/校验/外部参考/探针 | 详见 §2 计数 |
| 13 | `_s1912priv/` | **UNKNOWN**（私有构建目录，未打开） | 2026-11-01 |
| 14 | `.claude/` `.codex/` | agent 配置/缓存目录 | 非项目内容 |
| 15 | `.dsh-office-*`（10 个）`.dsh-tex-check-*` | DSH office/tex 运行期目录 | **UNKNOWN** 具体内容 |
| 16 | `.lean-shadow/` `.tmpbuild/` `.scratch/` | 影子/临时构建/草稿 | **UNKNOWN** 是否可清理 |
| 17 | `%SystemDrive%/` | 字面名为 `%SystemDrive%` 的目录 | **UNKNOWN** 来源 |
| 18 | `.github/` | CI 配置 | — |
| 19 | 根级文件 353 个 `.lean` + 大量 `_a3*.log/_s19*.log` | 根级探针/日志残留 | 未逐一登记（见 UNKNOWN-U1） |

## 2. 文件计数（全仓；只读扫描）

| 指标 | 值 |
|---|---|
| `.lean` 总数 | **195,603** |
| `S*.lean` | **8,116** |
| `Mzk1*.lean` | **2,965** |
| `.md` | **5,361** |
| `.json` | **34,329** |
| `.ps1` | **369** |
| `.mjs` | **2,003** |
| 根级 `.lean`（`D:/lean/*.lean`） | 353 |

按顶层树的 lean 计数（前 25）：tmp 167,699；.lake 10,107；vendor 9,640；LeanFormal 1,189；Iut 950；Oka 828；TemperedFundamentalGroups 744；FormalSchemes 647；CurvesJacobian 590；logs 573；.claude 506；EllipticCurves 480；external 462；Belyi 156；OrbicurveCores 134；LocalClassFieldTheory 121；Pi1 114；TateCurvesTheta 78；Heights 64；WeilCurves 49；ContinuousKummerTheory 38；metadata-probes 23；coord 21；Genl 9；.scratch 7。

## 3. `.lake/build/lib/lean` olean

| 指标 | 值 |
|---|---|
| olean 总数 | **13,889** |
| 最新 olean | `D:/lean/.lake/build/lib/lean/tmp/external/ported/lana_core/Iut/Concrete/LocalConstruct/Arithmetic.olean`，mtime **2026-11-13 01:53:28** |
| `Iut` 树 olean | **374 / 950** |
| `tmp/sheaf/xif/paper` lean | **16,739**，olean **8,550** |
| `lana_core`（28 源文件） | olean **8/29**（含手工加入的 RationalPlace） |
| `lana_a`（Cor312 7 文件） | olean **7/7** |
| `lana_tgfree`（334 文件） | olean **61/334** |

代表性文件（路径 | 大小 | olean | 首 2 行）：
- `Iut/Cor312/LogVolume.lean` | 12,148 B | **Yes** | `/-` / `Copyright (c) 2026 LANA Project...`
- `Iut/WallEquiv/Gap.lean` | 52,650 B | **No** | `/-` / `Copyright (c) 2026 LANA Project...`
- `Iut/Concrete/LocalTheory.lean` | 3,485 B | **No** | `/-` / `Copyright (c) 2026 LANA Project...`
- `TemperedFundamentalGroups/SemistableReduction/NilpotentFlatness.lean` | 25,247 B | **No** | `/-` / `Copyright (c) 2026 LANA Project...`
- `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullInterface.lean` | 12,381 B | **Yes** | `import ...FinitePlaceArithmeticTupleCanonicalHull` / `import ...SourceHullCompactnessReduction`
- `tmp/sheaf/xif/paper/Mzk1S3137LChainActual.lean` | 4,939 B | **Yes** | `/- Copyright (c) 2026 LeanFormal contributors.` / `import ...Mzk1RealifiedValueMonoidActual`
- `tmp/sheaf/xif/paper/Mzk1GateProbeA1043Actual.lean` | 3,256 B | **Yes** | `/- Copyright ...` / `import ...Mzk1S3137LChainActual`
- `tmp/sheaf/xif/paper/Mzk1ScalingNormalizationActual.lean` | 4,617 B | **Yes** | `/- Copyright ...` / `import ...Mzk1ProcessionAverageActual`
- `tmp/external/ported/lana_core/Iut/Concrete/LocalTheory.lean` | 3,822 B | **Yes** | `import ...lana_core.Iut.Cor312.ThetaData.Places` / (空行)
- `tmp/external/ported/lana_tgfree/Iut/Wall/BPS.lean` | 17,500 B | **Yes** | `/- Ported from Iut/Wall/BPS.lean ...` / `/-`
- `tmp/external/ported/lana_a/Iut/Cor312/LogVolume.lean` | 12,642 B | **Yes** | `import ...lana_a.Iut.Cor312.Container` / (空行)

## 4. Gate pins（coord 文档）

| 来源 | 原文（精确） |
|---|---|
| `coord/CURRENT-HARD-POINTS.md:8` | “Main paper files live in `tmp/sheaf/xif/paper/*.lean`; registry pins are FROZEN at **14041 / gate 23066 / record 18800**.” |
| `coord/CANONICAL-GATE-DRAFT-V2.md:5` | “**Pins:** registry **14041** / gate **in flux** / record **18800**; L8 frozen; no registry edits.” |
| `coord/COMBINED-REOPEN-CHECKLIST.md:122` | “Status: NOT OPEN. Pins locked at gate **23066** / registry **13129** / record **15501**; 2 reopens” |
| `coord/AUDIT-07-LEANFORMAL-IUT.md:1622/356` | 14041/18800 作为文件 id/字节数出现，非 pin 定义 |

**结论/UNKNOWN**：现行 frozen pin 以 `CURRENT-HARD-POINTS.md` 的 **registry 14041 / gate 23066 / record 18800** 为准（与 `CANONICAL-GATE-DRAFT-V2` 一致）；`COMBINED-REOPEN-CHECKLIST` 的 13129/15501 为**历史阶段值**，需 lead 确认是否作废 —— 标记 **UNKNOWN-U2**。

## 5. dag/watchdog 冻结时状态（快照 18:14–18:15 UTC）

| 文件 | 事实 |
|---|---|
| `dag/watchdog/plan.json` | generated_at=11/12/2026 18:14:39；targets=**111**；extra_targets=**111**；closure=**398**；dirty=**27** |
| `dag/watchdog/extra-targets.txt` | **111** 行（完整清单见附录 A） |
| `dag/watchdog/order.json` | 顶层属性 **2** 个（非完整拓扑序；具体内容 UNKNOWN 用途） |
| `dag/watchdog/heartbeat.json` | at=`2026-11-12T18:14:34Z`，running=0，pending=**7** |
| `dag/watchdog/state.json` | 条目 **31** |
| watchdog 进程 | **procs=0**（已停止/退出；最后日志 18:15:15） |
| 最近日志 | 18:14:51 START S1487QPilotTarget/S1487SourceRootIdentity；18:14:57 二者 FAIL；18:14:57 `lana_tgfree/.../Admissible.lean` FAIL；18:15:15 `Mzk1CompletionMapIdActual` FAIL |
| 当前在编 | **无**（进程退出） |
| 当前排队（plan.dirty 27） | 见附录 B |

**关键结论**：快照时 watchdog **已停**（heartbeat 停在 18:14:34，最后日志 18:15:15）；队列仍有 27 dirty、111 extra；team 的 feeder/retouch 循环（powershell/node）与 watchdog 进程无关联，UNKNOWN 是否仍在跑（见 §7）。

## 6. 当前在编/排队文件清单（快照）

- 在编：**空**（watchdog 进程 0）。
- 排队 = plan.dirty 的 27 文件（附录 B 全列）。
- 被 state 冷却/失败记录排除者：31 条 state 条目（附录 C 略；路径以 `dag/watchdog/state.json` 为准）。

## 7. 其他基础设施事实

| 项 | 值 |
|---|---|
| DAG_MAX | `tools/run_dag_watchdog.cmd` 中 **16**（A1099 修改，备份 `.bak-a1099`） |
| watchdog 计划任务 | `DshDagWatchdog`（已改 AllowStart/DontStop + ExecutionTimeLimit=0，A1086） |
| retouch 循环 | `tools/retouch_ready.mjs`（`tmp/retouch.log` 最后 “touched 8”；循环进程 UNKNOWN 当前是否存活，采集时见 2 个 node retouch 进程） |
| feeder | `tools/lana_core_feeder.ps1`（每 15s 放行 lana_core 就绪文件；进程数采集时 1） |
| gate probe | `Mzk1GateProbeA1043Actual.lean`（olean Yes；证据 `tmp/gate_trio_A1057.md` 24 条 axiom 输出：23 trio + Concrete status 无公理） |
| port 工具 | `tools/xif_external_port.ps1`（备份 `.bak-a1010`/`.bak-a1010c`）；`tools/port_lana_tgfree.mjs`；`tools/lana_tgfree_feeder.mjs` |
| 外部 lana 源 | `tmp/online/lana-agents__iut/iut-main`（710 lean，lean v4.32.0，无 .lake）；`tmp/dsh-oct6-.../repos/lana/iut/iut-main`（322 lean） |
| 版本 pins | lean-toolchain `leanprover/lean4:v4.32.2`；mathlib rev `905b95818eb32af7874a58b427f50c1711a5e96c`（外部 lana 源 v4.32.0 / mathlib 81a5d257c8e4…） |

## 8. UNKNOWN 清单（不臆断）

- **UNKNOWN-U1**：根级 353 个 `.lean` 及大量 `_a3*.log/_s19*.log` 逐文件用途未登记（数量多、疑似历史探针/日志残留；未逐一打开）。
- **UNKNOWN-U2**：gate pin 历史值（COMBINED-REOPEN-CHECKLIST 的 13129/15501）是否作废、以哪个文档为权威 —— 待 lead 确认。
- **UNKNOWN-U3**：`_s1912priv/`、`.dsh-office-*/`、`.lean-shadow/`、`.tmpbuild/`、`%SystemDrive%/` 内容/用途未打开核对。
- **UNKNOWN-U4**：`Mathlib/` 顶层目录与 `.lake/packages/mathlib` 的对应关系（是否同源副本）未验证。
- **UNKNOWN-U5**：watchdog 停止时刻的准确原因（进程 0；最后日志 18:15:15 FAIL；是否有异常退出无 dump 可查）。
- **UNKNOWN-U6**：`lana_tgfree` 334 文件闭包的完整依赖图/剩余 273 文件 ETA 未在本审计重算。

---

## 附录 A：extra-targets.txt（111 行，完整）

```
tmp/sheaf/xif/paper/Mzk1GateProbeA1043Actual.lean
tmp/sheaf/xif/paper/Mzk1CThetaRetargetActual.lean
tmp/sheaf/xif/paper/Mzk1QPilotHaarBridgeActual.lean
tmp/sheaf/xif/paper/Mzk1QRegionConstructActual.lean
tmp/sheaf/xif/paper/Mzk1ContainAttemptActual.lean
tmp/sheaf/xif/paper/RefLANAMultiradialSpecActual.lean
tmp/sheaf/xif/paper/Mzk1RouteBBridgeActual.lean
tmp/sheaf/xif/paper/Mzk1QPilotVolumeScalarActual.lean
tmp/sheaf/xif/paper/Mzk1RouteBBridgeDegreeOneActual.lean
tmp/sheaf/xif/paper/BadToC3TensorMapActual.lean
tmp/sheaf/xif/paper/Mzk1SourceRootIdentityActual.lean
tmp/sheaf/xif/paper/Mzk1CompletionMapSelfActual.lean
tmp/sheaf/xif/paper/Mzk1S1487SourceRootIdentityActual.lean
tmp/sheaf/xif/paper/Mzk1PlaceEqSpecializationActual.lean
tmp/sheaf/xif/paper/Mzk1S1487QPilotTargetActual.lean
tmp/sheaf/xif/paper/Mzk1CompletionMapIdActual.lean
tmp/sheaf/xif/paper/Mzk1PerPlaceReductionActual.lean
tmp/external/ported/lana_tgfree/Iut/Abc/Classical.lean
tmp/external/ported/lana_tgfree/Iut/Abc/Target.lean
tmp/external/ported/lana_tgfree/Iut/Anabelian/Linear.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/Basic.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/Disc/Basic.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/Elliptic/RLinear.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/Elliptic/Torus.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/EntireAut.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Haar.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/LocalLogShell.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/PacketPresentation.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/Procession.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/RationalPlace.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/ThetaData/Places.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/ThetaData/PointMap.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/ThetaData/UltrametricSqrt.lean
tmp/external/ported/lana_tgfree/Iut/EtaleTheta/Heisenberg.lean
tmp/external/ported/lana_tgfree/Iut/EtaleTheta/MonoTheta.lean
tmp/external/ported/lana_tgfree/Iut/EtaleTheta/Theta.lean
tmp/external/ported/lana_tgfree/Iut/Frobenioid/Angular/Circle.lean
tmp/external/ported/lana_tgfree/Iut/Frobenioid/Basic.lean
tmp/external/ported/lana_tgfree/Iut/HodgeTheater/Labels.lean
tmp/external/ported/lana_tgfree/Iut/Implication/PrimeSelection.lean
tmp/external/ported/lana_tgfree/Iut/NumberTheory/SixExponentials/ExpPolyZeros.lean
tmp/external/ported/lana_tgfree/Iut/NumberTheory/SixExponentials/InterpolationDeterminant.lean
tmp/external/ported/lana_tgfree/Iut/Reconstruction/Cusp/GaloisConj.lean
tmp/external/ported/lana_tgfree/Iut/Torsion/Identities.lean
tmp/external/ported/lana_tgfree/Iut/Tower/IntegralModel.lean
tmp/external/ported/lana_tgfree/Iut/Tower/QuotientBasis.lean
tmp/external/ported/lana_tgfree/Iut/Tower/ReductionKernel.lean
tmp/external/ported/lana_tgfree/Iut/Tripod/Legendre.lean
tmp/external/ported/lana_tgfree/Iut/Tripod/SL2Generation.lean
tmp/external/ported/lana_tgfree/Iut/Wall/BPS.lean
tmp/external/ported/lana_tgfree/Iut/Tripod/CyclicArch.lean
tmp/external/ported/lana_tgfree/Iut/Tripod/CyclicPoints.lean
tmp/external/ported/lana_tgfree/Iut/Torsion/EDS.lean
tmp/external/ported/lana_tgfree/Iut/Frobenioid/Defs.lean
tmp/external/ported/lana_tgfree/Iut/Frobenioid/Invariance.lean
tmp/external/ported/lana_tgfree/Iut/Frobenioid/TemperedBase.lean
tmp/external/ported/lana_tgfree/Iut/Tower/SerreCore.lean
tmp/external/ported/lana_tgfree/Iut/NumberTheory/SixExponentials/Basic.lean
tmp/sheaf/xif/paper/Mzk1StructuralTargetActual.lean
tmp/sheaf/xif/paper/Mzk1StructuralLineBundleActual.lean
tmp/external/ported/lana_tgfree/Iut/Anabelian/Genuine/Basic.lean
tmp/external/ported/lana_tgfree/Iut/Anabelian/Model.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/ThetaData/TateStructure.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/ThetaData/VariableChangePoint.lean
tmp/external/ported/lana_tgfree/Iut/EtaleTheta/CyclotomicEnvelope.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/Elliptic/Lie.lean
tmp/external/ported/lana_tgfree/Iut/EtaleTheta/ThetaValues.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/Disc/Formulas.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/OfCover.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/Plane.lean
tmp/external/ported/lana_tgfree/Iut/AutHolomorphic/Reconstruct.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/LogLattice.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/Container.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/HolomorphicHull.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/ThetaData/GlobalField.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/ThetaData/PlacesOver.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/ThetaData/TateIsomorphism.lean
tmp/external/ported/lana_tgfree/Iut/HodgeTheater/Procession.lean
tmp/external/ported/lana_tgfree/Iut/Tripod/Basic.lean
tmp/sheaf/xif/paper/Mzk1ThetaSectionActual.lean
tmp/sheaf/xif/paper/Mzk1LogMeasureSubmodularActual.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Admissible.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Arithmetic.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/ThetaAdmissible.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Volume.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/ScaleVolume.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Packet.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/IndAut.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/ThetaLocalConstruct/Data.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/Statement.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/LogVolume.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/ThetaRegion.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/Forms.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/Gap.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/VcI.lean
tmp/sheaf/xif/paper/Mzk1ConditionalMainActual.lean
tmp/sheaf/xif/paper/Mzk1QPilotPrincipalActual.lean
tmp/sheaf/xif/paper/Mzk1GapBookkeepingActual.lean
tmp/sheaf/xif/paper/Mzk1EnlargementActual.lean
tmp/sheaf/xif/paper/Mzk1FaithfulEnlargementActual.lean
tmp/external/ported/lana_core/Iut/Cor312/ThetaData/Places.lean
tmp/external/ported/lana_core/Iut/Concrete/LocalConstruct/LogLattice.lean
tmp/external/ported/lana_core/Iut/Concrete/LocalTheory.lean
tmp/external/ported/lana_core/Iut/Concrete/ThetaLocalConstruct/Ordp.lean
tmp/external/ported/lana_core/Iut/Concrete/LocalConstruct/Packet.lean
tmp/external/ported/lana_core/Iut/Cor312/RationalPlace.lean
tmp/external/ported/lana_core/Iut/Concrete/LocalConstruct/Arithmetic.lean
tmp/sheaf/xif/paper/Mzk1OurAccurateTargetActual.lean
tmp/sheaf/xif/paper/Mzk1GreenChainAssemblyActual.lean
tmp/sheaf/xif/paper/Mzk1TensorRegionNormalizationActual.lean
tmp/sheaf/xif/paper/Mzk1ActualFinalLDataActual.lean
```

## 附录 B：plan.dirty（27 文件，完整）

```
tmp/sheaf/xif/paper/Mzk1ActualFinalLDataActual.lean
tmp/sheaf/xif/paper/Mzk1TensorRegionNormalizationActual.lean
tmp/sheaf/xif/paper/Mzk1GreenChainAssemblyActual.lean
tmp/sheaf/xif/paper/Mzk1PlaceEqSpecializationActual.lean
tmp/sheaf/xif/paper/Mzk1FaithfulEnlargementActual.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/VcI.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/Gap.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/Forms.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/ThetaRegion.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/Statement.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/ThetaLocalConstruct/Data.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/IndAut.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Packet.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/ScaleVolume.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Volume.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/ThetaAdmissible.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Arithmetic.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Admissible.lean
tmp/sheaf/xif/paper/Mzk1CompletionMapIdActual.lean
tmp/sheaf/xif/paper/Mzk1S1487QPilotTargetActual.lean
tmp/sheaf/xif/paper/Mzk1S1487SourceRootIdentityActual.lean
tmp/sheaf/xif/paper/GlobalThetaPilotProcessionActual.lean
tmp/sheaf/xif/paper/GlobalThetaPilotPossibleImageGeometryActual.lean
tmp/sheaf/xif/paper/GlobalThetaPilotPossibleImagesActual.lean
tmp/sheaf/xif/paper/GlobalThetaPilotPlaceComparisonActual.lean
tmp/sheaf/xif/paper/GlobalThetaPilotPlaceMapActual.lean
tmp/sheaf/xif/paper/BadToC3TensorMapActual.lean
```

## 附录 C：state.json 条目（31 条，路径表）

```
TemperedFundamentalGroups/SemistableReduction/AdmissibleEtaleLift.lean
tmp/sheaf/xif/paper/Mzk1SignedLogVolumeActual.lean
tmp/sheaf/xif/paper/Mzk1FaithfulXiEContainmentActual.lean
tmp/sheaf/xif/paper/Mzk1S1487SourceRootIdentityActual.lean
tmp/sheaf/xif/paper/Mzk1S1487QPilotTargetActual.lean
tmp/sheaf/xif/paper/Mzk1SourceRootIdentityActual.lean
tmp/sheaf/xif/paper/Mzk1RouteBBridgeActual.lean
tmp/sheaf/xif/paper/Mzk1RouteBBridgeDegreeOneActual.lean
tmp/sheaf/xif/paper/Mzk1PlaceEqSpecializationActual.lean
tmp/sheaf/xif/paper/Mzk1CompletionMapIdActual.lean
tmp/sheaf/xif/paper/Mzk1StructuralLineBundleActual.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/VcI.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/Forms.lean
tmp/external/ported/lana_tgfree/Iut/Cor312/Statement.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/ThetaRegion.lean
tmp/external/ported/lana_tgfree/Iut/WallEquiv/Gap.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Volume.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Packet.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/ThetaLocalConstruct/Data.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/IndAut.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/ScaleVolume.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/ThetaAdmissible.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Admissible.lean
tmp/external/ported/lana_tgfree/Iut/Concrete/LocalConstruct/Arithmetic.lean
tmp/sheaf/xif/paper/Mzk1QPilotPrincipalActual.lean
tmp/sheaf/xif/paper/Mzk1FaithfulEnlargementActual.lean
tmp/sheaf/xif/paper/Mzk1OurAccurateTargetActual.lean
tmp/sheaf/xif/paper/Mzk1GreenChainAssemblyActual.lean
tmp/sheaf/xif/paper/Mzk1TensorRegionNormalizationActual.lean
tmp/sheaf/xif/paper/Mzk1ActualFinalLDataActual.lean
tmp/external/ported/lana_core/Iut/Concrete/LocalConstruct/Packet.lean
```
