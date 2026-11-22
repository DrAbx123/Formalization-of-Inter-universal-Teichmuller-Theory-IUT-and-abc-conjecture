# AUDIT-ROUTE-20261116 — 独立审计 gate 表（lane = audit）

- 本批（batch 22）快照：**2026-11-16 17:57 UTC = 2026-11-17 01:57 CST**（覆盖 **17:44:18–17:57**；旧行全保留）。**关键翻转**：PsiGlobal **17:47:13 DONE**——wToPullback/wToPullback_fst/wToPullback_snd 首次进 olean（8 条打印全三公理、二进制无 sorryAx）→ **解除 batch21 的“wToPullback 禁引”**；PsiCover **17:49:07 DONE**（Y_n 的真开覆盖 U0∪D(q)，cover_point 由两图表覆盖+素理想避开 q/r 真证，8 条三公理）；JHeightUniform **17:52:16 DONE**（9 条三公理，仍 coeffAbsSum infra）；ULStepVIIIInstances **17:56:13 DONE**（hVh 条件式）；PlaceData **17:53:31 DONE**（H-T 8.2 place data，delta NO INHABITANT）；PsiOverlapIso **17:57:02 DONE**（仅 IsIso w 的 step (a)）。**新红/回归**：ChartKbar 17:49:06/17:52:14/17:55:42 三红（ambientEquiv 带 sorryAx，基变换方向/类型错）；**ULStepVIII 17:56:20 FAIL**（hiii_of_stepII_and_sQ 在 182 行先用、定义却在 547 行）→ 17:39:42 olean 被 src 17:54:24 顶成 **stale**，C4 只能引 17:39:42；PsiGlueCompat 17:55:51 **真错**（psi/glueMorphisms_compat 带 sorryAx，已改用 wToPullback）；HT84 17:44:35 olean 被 src 17:56:35 顶成 stale；URThetaHullNonzero 8329B/8051B/8004B **已无 sorry 文本但未绿**（心跳超时 / 悬空 #print）。新增 §2u、§3t（Probe 22，6/6 三公理）、§4.172–§4.182、§5r、§6v。**§6w 补记 17:57–18:05：ChartKbar ambient、URThetaHullNonzero、HT84、ULStepVIII 先后翻绿（各有附加条件），Probe 22b/22c 共 9/9 三公理**。**未运行** lake env lean、未自起 watchdog、未 spawn_teammate、未写 sorry/axiom。

- 本批（batch 21）快照：**2026-11-16 17:44 UTC = 2026-11-17 01:44 CST**（最后已审事件 Probe 21 DONE 17:44:09；**17:44:18 之后未审计**）。接续 §2s/§3r/§4.153+/§5p 与 §6s 补记，覆盖 **17:34:40–17:44:18**。**关键翻转：G-A smooth 出口 CLOSED（SmoothFinal 17:40:31，P21 三公理）**，与 proper（PiProper 17:19:18）并列为 G-A 双出口；**(h) 仍只有 cover（17:31:53），scheme 层整性/连通无陈述 → OPEN**。ULStepVIII 17:39:42 DONE（8 条三公理，新增 hiii_of_stepII_and_sQ）；ConductorDifferentCancellationAssembly 由 17:34:38 parse error 翻为 **17:40:33 DONE**（f2_of_witness 条件式）；URThetaHullTensor 17:37:57、JHeightUniform 17:40:32、RelativeDifferentNorm 17:42:54、ULStepVIIIInstances 17:43:21 新 DONE；PsiGlobal 17:39:09 olean 含 hcomp（17:42:52 log 三公理）但当前源 wToPullback 因缺 open CategoryTheory.Limits 红，PsiGlueCompat 17:42:58 红 → **全局 ψ 仍未组装**；URThetaHullNonzero 新文件红；HT84F4F5 17:44:35 翻绿（仍接口，F4/F5 NO INHABITANT）。新增 §2t、§3s（Probe 21）、§4.162–§4.171、§5q、§6t。**未运行** lake env lean、未自起 watchdog、未 spawn_teammate、未写 sorry/axiom。

- 本批（batch 19）快照：**2026-11-16 16:58 UTC = 2026-11-17 00:58 CST**（最后事件 PiFiniteChart FAIL 16:57:36 / ConductorCore FAIL 16:57:38；Probe 19 DONE 16:52:56，8 条全部三公理）。接续 §2q/#340–341；覆盖 **16:46:18–16:57:38** 的新 DONE/FAIL，并复核 Lead 指定 10 项（PiPreimageClose 16:44:16、Close2、CurveSmooth2 16:42:12、OmegaRamificationInfinity、URSmallPrime、URBadWeightSum、ULHviTableFinal、ULStepVIII、ChartPreimage、16:46 后其它文件）。新增 §2r/#342–356、§2r-3（audit18 评估口径收录）、§3q（Probe 19）、§4.144–§4.152、§5o、§6q。**关键翻转：Close2 t 侧 16:50:10 DONE 且 log 三公理，16:46:18 的 sorryAx 已被修掉；ULStepVIII 16:54:16 三公理版含 `hstepVIII_of_collectionLayer`；PiFiniteChart 16:50:10 的 3 引理 olean 与 00:56:45 新源（finite restriction）不同，新源 16:57:36 红。**16:59:41 之后未审计（16:58:22–16:59:41 见 §6r）。**

- 本批（batch 13）快照：**2026-11-16 14:46 UTC = 22:46 CST**（最后事件 14:46:10；Probe 13 DONE 14:41:30、13b 14:44:20、13c 14:45:44）；新增 §2l（#242–#256，覆盖 14:35–14:46 全部 DONE/FAIL 并复核 Lead 指定 6 项）、§3j/§3k（Probe 13/13b/13c，12 条全部三公理）、§4.96–§4.101、§5i、§6j。**14:46 UTC 之后未审计**（watchdog 仍在跑：P1Valuative src 22:46:09 待重试、P6P5ThetaHullControl2 与 URThetaPacketCarrier 红）。

- 本批（batch 15）快照：**2026-11-16 15:31 UTC = 23:31 CST**（主表截至 15:29:22；15:29:22–15:31:30 的补记见 §2n-3；Probe 15 DONE 15:29:22，8 条全部三公理）。接续 §2m/#257–272；**§2m 已覆盖 14:46–15:02，因此 14:48Z 之后到 15:29 的全部 DONE/FAIL 由 §2m + §2n 合起来覆盖，无遗漏**。新增 §2n（#273–285，覆盖 15:02–15:29 全部 DONE/FAIL）、§3m（Probe 15）、§4.108–§4.115、§5k、§6l。**15:29 UTC 之后未审计**（watchdog 仍在跑）。

- 审计者：audit lane（独立于各 lane，不修改被审计文件）。
- 快照时间（本批 batch 4）：**2026-11-16 07:50 CST = 2026-11-15 23:50 UTC**（本表事件时间截至 23:49:18；watchdog 仍在跑，状态可能继续变化；表中时间均为 watchdog.log 的 UTC 时间）。
- 历史快照：23:25 UTC（§2 原文保留）、23:33:35 UTC（§2b 原文保留）、23:50 UTC（§2c，batch 4）。
- 本批（batch 5）快照：**2026-11-16 00:16 UTC = 08:16 CST**；新增 §2d（#70–#104，含旧行翻转）、Probe 5、§4.29–§4.35、§6 更新。00:16 UTC 之后的变化本表未审计（watchdog 仍在跑）。
- 本批（batch 6）快照：**2026-11-16 00:55 UTC = 08:55 CST**；新增 §2e（#105–#129，含 00:16–00:37 补审、旧行翻转/STALE）、Probe 6、§4.36–§4.43、§5b、§6c。00:55 UTC 之后的变化本表未审计（本批快照时 watchdog pending=3，正在重试 FermatOverlapRing / URRootExtension / URThetaHull）。
- 本批（batch 7）快照：**2026-11-16 12:55 UTC = 20:55 CST**；新增 §2f（#130–#149，12:35–12:53 UTC 的 DONE/FAIL，含同文件 DONE→FAIL 翻转与 STALE）、Probe 7（8 条，全部三公理）、§4.45–§4.52、§6d。**12:53 UTC 之后的变化本表未审计**（watchdog 仍在跑，快照时仍在改 `HullFermatGluing` / `RadicalSupportFinal3` / `OmegaFree` / `URThetaPacketInstance` / `OmegaPresentation`）。
- 本批（batch 8）快照：**2026-11-16 13:06 UTC = 21:06 CST**（表内最后事件 13:05:51 UTC；Probe 8 DONE 13:05:31）；新增 §2g（#150–#168，含 **4 个 RETIRED 文件** + **TauCetiPort closed-port** + consumer 检查）、Probe 8（8 条，全部三公理）、§4.53–§4.59、§5d、§6e。**13:06 UTC 之后的变化本表未审计**（watchdog 仍在跑；快照时 `SmoothLocalize` / `URThetaPacketInstance` / `RadicalSupportFinal3` 已于 13:05:46 重新 START）。
- 本批（batch 9）快照：**2026-11-16 13:18 UTC = 21:18 CST**（表内最后事件 13:18:17；Probe 9 DONE 13:16:37）；新增 §2h（#169–#183，覆盖 13:06 之后**全部** DONE/FAIL + STALE/RETIRED 复核）、Probe 9（7 条，全部三公理）、§4.60–§4.66（含 cocycle/xi/Y_n 模型/TauCetiPort 四条引用纪律）、§5e、§6f。**13:18 UTC 之后的变化本表未审计**（watchdog 仍在跑；快照时 `RadicalSupportFinal3` 于 13:17:37 START，`SmoothLocalize`/`FermatPi`/`QHeight` 刚被改写）。
- 本批（batch 11）快照：**2026-11-16 14:13 UTC = 22:13 CST**（主表 14:09；§2j-3/§2j-4 补记 14:09–14:13，最后事件 14:13:21；Probe 11 DONE 13:56:36、11b DONE 14:05:22、11c DONE 14:09:01）；新增 §2j（#200–#220，覆盖 13:33–14:08 的全部 DONE/FAIL/START + STALE/RETIRED）、Probe 11/11b/11c（16 条，全部三公理）、§4.76–§4.86、§5g、§6h。**14:13 UTC 之后的变化本表未审计**（watchdog 仍在跑；快照时 `PiPreimageChart`/`URQNormalization` 红，`P1Proper` 只到 locally-finite-type + quasi-compact，`IsFinite π`/`IsProper P¹_glued` 仍无定理）。
- 本批（batch 12）快照：**2026-11-16 14:33 UTC = 22:33 CST**（最后事件 14:34:53；Probe 12 扩展版 DONE 14:26:19，8 条全部三公理；Probe 12b DONE 14:32:45，3 条全部三公理）；新增 §2k（#221–#241，覆盖 14:13–14:34 全部 DONE/FAIL 并逐个复核 Lead 指定 6 项）、§3h（Probe 12/12b）、§4.87–§4.95、§5h、§6i。**14:35 UTC 之后的变化本表未审计**（watchdog 仍在跑；快照时 `URQNormalization` 14:30:29 DONE（C2 q 侧 M=Q/(2l) 三公理）、`RadicalSupportActual` 14:26:18 DONE、`P1Proper` 14:28:59 DONE 仍无 `p1GluedToBase_isProper`、`P1Valuative` 14:33:26 DONE（仅 5 条预备引理，无 valuative criterion）、`PiPreimageChart`/`OmegaTransitionGlobal`/`URThetaMonotone` 红、`P1ProperAssembly` 无 olean、`UCHpkt` 14:29:25 DONE（C4 条件式装配）、`ChartSwap` 14:31:12 DONE）。**未运行** `lake env lean`、未自起 watchdog、未 spawn_teammate、未写 sorry/axiom。
- 本批写入范围：本表 + **新建** `tmp/sheaf/xif/paper/_ProbeBatch9Actual.lean` + `coord/ROUTE-COMPLIANCE-20261116.md` 末尾纪律条目；未改其它 Lean 文件；未 spawn_teammate、未 `lake env lean`、未自起 watchdog。
- 本批写入范围：本表 + **新建** `tmp/sheaf/xif/paper/_ProbeBatch8Actual.lean`；未改其它 Lean 文件；未 spawn_teammate、未 `lake env lean`、未自起 watchdog。
- 编译方式：只用 `node tools/wd_add.mjs` / `node tools/wd_status.mjs`；单文件日志 `dag/watchdog/logs/<路径 / 换 _>.log`。**未使用** `lake env lean`，未自起 watchdog，未写 sorry/axiom。
- 写入范围：本表 + `tmp/sheaf/xif/paper/_Probe*Actual.lean`；batch 4 只新建/更新 `_ProbeGeom4Actual.lean`；batch 6 新建 `_ProbeBatch6Actual.lean`；batch 7 新建 `_ProbeBatch7Actual.lean`（未改其它 Lean 文件；未 spawn_teammate、未 `lake env lean`、未自起 watchdog）。


- 本批（batch 16）快照：**2026-11-16 15:45 UTC = 23:45 CST**（最后完成事件 15:44:42；15:44:56 起的 5 文件波在飞，未审计）。接续 §2n/#273–285；本批覆盖 **15:31:30–15:44:42** 的全部 DONE/FAIL（含 15:31:30 ULStepVIII、15:32:13 PiPreimage、15:32:15 CurveSmooth、15:32:16 URThetaHullUpper、15:33:46/15:35:13/15:36:57/15:44:42 HullUpper、15:35:14 Bridge、15:37:44 Uniqueness、15:37:48/15:39:41 Probe16/16b、15:43:58 D1D3、15:43:05 UCHCor312 等）。新增 §2o（#286–296）、§3n（Probe 16/16b，8 条全部三公理）、§4.116–§4.122、§5l、§6m。**15:44:56 之后未审计**（watchdog 在跑：G1PsiCover 新文件、PointSep、ULStepVIII、Uniqueness、PiPreimage）。

- 本批（batch 17）快照：**2026-11-16 16:29 UTC = 2026-11-17 00:29 CST**（Probe 17 DONE 16:29:30；16:24:24 起的文件波中 ULStepVIII 16:25:37、OmegaRamificationLocal 16:25:02 已 DONE，其余在飞）。接续 §2o/#286–304；覆盖 **15:54:29–16:25:04** 全部 DONE/FAIL，并复核 Lead 指定 10 项（CurveSmooth 15:55:41 终版含 `chartSpec_smoothOfRelativeDimension`、P1ProperFinal producer、OmegaLineBundle/Data、D2、UCHthetaWiring、HviTableLetters、CollectionLayer、DisplayIdentity、JHeightUniform 占位、ULStepVIII 16:11、CurveSmooth2）。新增 §2p（#305–327）、§3o（Probe 17，8 条全部三公理）、§4.123–§4.133、§5m、§6n。**16:25:04 之后未审计**（URBadWeightSum / ULHviTableFinal / URSmallPrime / ProjectiveLineChartPreimage 在飞）。

## 0. 判定方法与证据等级

每个文件四层检查，缺一层即不能判 accepted：

1. **禁止项 grep**：`sorry|admit\b|^\s*axiom |PUnit|True\b|toy|surrogate`（人工排除注释/命名中的词）。
2. **watchdog DONE/FAIL + olean 新鲜度**：DONE 必须晚于源码 mtime，且 `.lake/build/lib/lean/tmp/sheaf/xif/paper/<file>.olean` 存在并晚于源码；源码比 olean 新的旧 DONE **不算数**。
3. **语义阅读**：命题里的对象是否就是路线要求的对象；引理是否只是把假设原样搬进结构体/是否定义自反；是否有 `varpi = 1`、`exceptional = univ`、`PUnit.unit`、`True` 字段、空 card 等 surrogate。
4. **`#print axioms`**：由审计 probe 独立 import 后复算；同时对照各文件自带 `#print axioms` 的日志输出。

证据等级：**A** = 三公理 + 真实对象；**B** = 三公理但只值层/局部，不能当路线出口；**C** = toy / 空 card / 定义自反；**R** = red（FAIL、sorryAx、换题或禁用 surrogate）。

> 本轮最重要的结论：**grep 干净 + 三公理 ≠ accepted**。本轮多数 toy（TwoChartGluing、StepXIChartMap4、ULPhiRealization、URJ2、UCHpkt、D1Producer、DisjointFamily）都 grep 干净且 kernel 三公理，但都不是路线要求的数学对象。

> **batch 3 新增判读纪律（重要）**：watchdog 的单文件日志是**跨多次尝试追加**的，同一个 log 里会残留旧尝试的 `sorryAx` 块。判 axiom 只认日志**末段**（最新一次尝试）或本审计 probe 的独立复算；判 FAIL 只认 watchdog.log 里该文件**最后一次** FAIL 时间。本批已因此纠正两处误判（BelyiCVComposition、TwoSectionData 的旧 sorryAx 块）。

### 0.5 本批新增判读纪律（batch 4，必须与 §0 四层一起用）

1. **只取当前 attempt**：单文件日志跨 attempt 追加；判 axiom / 首错只取**该文件源码 mtime 之后**那一次 watchdog 尝试。本批 `Mzk1G1FermatSmoothChartActual` 就出现「旧段是缺 olean 的首错、末段才是真错（sorryAx）」的情形。
2. **先排除级联假红**：FAIL 首错若是 `object file … does not exist`（缺依赖 olean），先 `Test-Path` 该 olean；若该 dep 已 DONE（olean 存在），则这次 FAIL **不能**记数学缺口。本批 5 例（SmoothChart / Support / SmoothAttempt / B1B3 / 旧 FiniteDisjointBelyi 首段）。
3. **假红转真红 ≠ 退步**：依赖补齐后重编，同一文件可能从「缺 olean」变成真正的 tactic 错误。判定只看该文件**当前源码**的最后一次尝试。

## 1. 最近 DONE 清单（**上一批**：本 round 新增，watchdog.log，UTC）

本 round 简报时间 07:04 CST = 23:04 UTC；23:04 UTC 之后的 route DONE：

| 时间 (UTC) | 文件 | 节点 | 备注 |
|---|---|---|---|
| 23:08:12 | Mzk1UCC1UpperActual | U-C | 三公理；但 C1 只在 `Hpkt = 0` 下等价（见 §4） |
| 23:08:25 | Mzk1ULPacketVActual | U-L | 该版本三公理；23:14 源码被改，23:16 FAIL（依赖 olean 缺失） |
| 23:08:25 | Mzk1ULPhiRealizationActual | U-L | 23:16 FAIL（unknown namespace），23:20 修复后 DONE |
| 23:09:00 | Mzk1G1TwoSectionDataActual | G-C | 真代数但 `s1 = 1` 退化 |
| 23:09:15 | Mzk1UCHpktActual | U-C | 三公理；纯代数（per-packet 界是假设） |
| 23:09:44 | Mzk1G1B1B3ComponentActual | G-C | 三公理；组件为定义性组包 |
| 23:09:45 | Mzk1G1NoncriticalPsiActual | G-C | 三公理；affine 多项式层，非 scheme morphism |
| 23:10:01 | Mzk1G1FermatTwoChartGluingActual | G-A | **空壳/换题**（见 §4.1） |
| 23:11:07 | Mzk1P6P5ControlJ1Actual | U-C | 未逐一审计（不在本表 14 文件内） |
| 23:17:48 | Mzk1ULFieldProductActual | U-L | 真字段积（包装 tensorCoreWitness） |
| 23:18:19 | Mzk1ULPacketFamilyActual | U-L | 真 hull 包含性；`PUnit.unit`/q-as-varpi 待澄清 |
| 23:20:21 | Mzk1ULPhiRealizationActual | U-L | 三公理；但 cover 是定义自反（见 §4.6） |

本 round **没有**任何 G-A glue、G-B、G-K、L-H actual D1、H-T、P8-P 的新 DONE。
（前一小时 22:41–22:57 UTC 的 route DONE 已在上轮 gate，本表只复核其中 8 个 route 关键文件。）

明确 FAIL（上一批）：`Mzk1G1FermatFiniteDegree2Actual`(23:17:42)、`Mzk1G1FermatCurveClosed2Actual`(23:17:42)、`Mzk1ULPacketVActual`(23:16:26)、`Mzk1HullFermatGluingActual`(23:19:49)、`Mzk1URRootExtensionActual`(23:19:52)、`Mzk1URRootMassActual`(23:19:47)、`Mzk1URThetaHullActual`(23:09:14)、`Mzk1G1FermatSmoothAttemptActual`(23:21:03)、`Mzk1G1FermatSupportActual`(23:21:30)、`Mzk1URPacketActual`(22:45:00)。

## 1b. 本批 batch 3 新增 DONE / FAIL（23:22–23:33 UTC，watchdog.log 实测）

**新增 DONE（本批 ★4 + 随后 3 个）**

| 时间 (UTC) | 文件 | 节点 | 备注 |
|---|---|---|---|
| 23:23:49 | Mzk1G1FiniteDisjointBelyiActual | G-K | ★；只有陈述，无族 inhabitant（§4.16） |
| 23:23:49 | Mzk1G1QHeightActual | L-H 高度 | ★；D3 未出现，interface 无 inhabitant（§4.14） |
| 23:24:31 | Mzk1G1TwoSectionPsiLocalActual | G-C | ★；affine Spec→A¹，非 P¹（§4.15） |
| 23:24:33 | Mzk1G1TwoSectionDataActual | G-C | ★；覆盖 23:21:39 的 FAIL；`s1=1` 仍退化（§4.13） |
| 23:30:24 | Mzk1G1BelyiCVCompositionActual | G-C h∘ψ | 23:24:32 曾 FAIL，修复后 DONE；多项式值层（§4.17） |
| 23:30:28 | Mzk1UCC1UpperActual | U-C C1/C3 | 23:24:35 曾 FAIL（import olean 缺），修复后 DONE；条件式（§4.18） |
| 23:30:51 | Mzk1ULPacketVActual | U-L | 23:16:26 曾 FAIL；**源码 23:33:06 又被改，当前 stale，未审计** |
| 23:31:19 | Mzk1ULPacketHull2Actual | U-L | 本批未语义审计（U-L 组） |

**新增 FAIL**：★ `Mzk1G1KvCompactActual`、`Mzk1G1D1ProducerActual`、`Mzk1G1DisjointFamilyActual`、`Mzk1G1LocalHeightCriterionActual`、`Mzk1HullFermatGluingActual`、`Mzk1G1FermatOmegaTransitionActual`；★ 中随后修好的 `Mzk1G1BelyiCVCompositionActual` / `Mzk1UCC1UpperActual`；相关 `Mzk1G1OmegaActual`、`Mzk1G1PsiChartMapsActual`、`Mzk1G1PsiTwoChartCocycleActual`、`Mzk1ULPacketHullActual`、`Mzk1ULWeightedHullActual`；以及**原 DONE 现 FAIL** 的 `Mzk1G1FermatTwoChartGluingActual`(23:31:02)、`Mzk1UCHpktActual`(23:30:21)。详见 §2b。

## 2. DONE/FAIL gate 表（**上一批快照 23:25 UTC，原文保留；batch 3 翻转见 §2b，batch 4 见 §2c**）

"grep" 列为禁止项扫描结果（全部无字面命中；语义 surrogate 另列"判定"）。"axioms" 列：(P) = 审计 probe 独立复算；(L) = 仅文件自带 `#print axioms` 日志；"—" = 无 `#print`。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 1 | Mzk1G1FermatTwoChartGluingActual | G-A 粘合 | DONE | 23:10:01 | fresh | clean | propext, choice, Quot.sound (P) | **C 空壳/换题** |
| 2 | Mzk1G1FermatOverlapActual | G-A overlap | DONE | 22:30:54 | fresh | clean | — | **C placeholder**（无定理） |
| 3 | Mzk1G1FermatTwoCharts2Actual | G-A charts | DONE | 22:42:04 | fresh | clean | 三公理 (P) | **A-局部**（Spec AdjoinRoot + finite） |
| 4 | Mzk1G1FermatProjClosedSubscheme4Actual | G-A proper | DONE | 22:52:58 | fresh | clean | 三公理 (P) | **A-局部**（closed immersion/proper 真） |
| 5 | Mzk1G1FermatFiniteDegree2Actual | G-A finite/degree | **FAIL** | 23:17:42 | none | clean | — | **R**（import 在 `open` 后；rank 语义错，见 §4.3） |
| 6 | Mzk1G1FermatCurveClosed2Actual | G-A closed | **FAIL** | 23:17:42 | none | clean | 日志示例：`fermatCurve_proper` = propext, **sorryAx**, choice, Quot | **R** |
| 7 | Mzk1G1StepXIChartMap4Actual | G-A π | DONE | 22:42:37 | fresh | clean | 三公理 (P) | **C 值层 surrogate** |
| 8 | Mzk1G1NoncriticalPsiActual | G-C B1/B2 | DONE | 23:09:45 | fresh | clean | 三公理 (P) | **B**（多项式层，非 scheme morphism） |
| 9 | Mzk1G1B1B3ComponentActual | G-C B1–B3 | DONE | 23:09:44 | fresh | clean | 三公理 (P) | **B**（组件=定义性组包） |
| 10 | Mzk1ULPacketVActual | U-L C1 | **FAIL** | 23:16:26 | stale | clean | 23:08 版本：三公理 (P) | **R 当前版**（仅缺依赖 olean，易修） |
| 11 | Mzk1ULHpktActual | U-L Hpkt | DONE | 22:43:55 | fresh | clean | 三公理 (P) | **C toy-代数** |
| 12 | Mzk1ULActualRootActual | U-L root | DONE | 22:54:28 | fresh | clean | 三公理 (P) | **A-局部**（真 root pow） |
| 13 | Mzk1URJ2Actual | U-R J2 | DONE | 22:41:13 | fresh | clean | 三公理 (P) | **C toy-代数** |
| 14 | Mzk1UCC1UpperActual | U-C C1 | DONE | 23:08:12 | fresh | clean | 三公理 (P) | **C/B 条件空洞**（需 `Hpkt = 0`） |
| 15 | Mzk1UCHpktActual | U-C Hpkt | DONE | 23:09:15 | fresh | clean | 三公理 (P) | **C toy-代数** |
| 16 | Mzk1G1D1ProducerActual | L-H D1 | DONE | 22:43:55 | fresh | clean | 三公理 (P) | **C toy**（singleton `KV={1/2}`, disc=cond=0） |
| 17 | Mzk1G1DisjointFamilyActual | G-K | DONE | 22:43:26 | fresh | clean | 三公理 (P) | **C toy**（const map 0, empty boundary） |
| 18 | Mzk1HullFermatGluingActual | G-A glue | **FAIL** | 23:19:49 | none | clean | `fermatGluingResidualMissing` = **sorryAx** | **R 空 card** |
| 19 | Mzk1URPacketActual | U-R packet | **FAIL** | 22:45:00 | none | clean | `ur_c1_feed` = propext, **sorryAx**, choice, Quot | **R + 禁用 surrogate** |
| 20 | Mzk1ULPhiRealizationActual | U-L Φ | DONE | 23:20:21 | fresh | clean | 三公理 (P) | **C 定义自反** |
| 21 | Mzk1ULPacketFamilyActual | U-L packet family | DONE | 23:18:19 | fresh | clean | 三公理 (P) | **A-局部**（hull 包含性真；q-as-varpi 待澄清） |
| 22 | Mzk1G1TwoSectionDataActual | G-C section | DONE | 23:09:00 | fresh | clean | 三公理 (P) | **B**（`s1=1` 退化） |

## 2b. 本批 batch 3 gate 表（快照 23:33:35 UTC；**21 行，覆盖 #1/#10/#14/#15/#16/#17/#22 的旧状态；batch 4 的状态翻转见 §2c**）

grep 列 = 大小写敏感扫描 `sorry|admit|^axiom |PUnit|^True|maxHeartbeats`（注意：`PUnit` 的大小写不敏感扫描会在 `overlapUnit0`/`overlapRing` 上假命中子串 `pUnit`，已人工排除）。axioms 列：(P) = 审计 probe 独立复算；(L) = 文件自带 `#print` 的**日志末段**；"—" = 无。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 23 | Mzk1G1TwoSectionDataActual（覆盖 #22） | G-C 截面 | DONE | 23:24:33 | fresh | clean | 三公理 (P+L) | **B**（s1=1 仍退化；s0 侧真实，§4.13） |
| 24 | Mzk1G1QHeightActual | L-H 高度 D3 | DONE | 23:23:49 | fresh | clean | 三公理 (P)；文件无 #print | **TOY/换题**（D3 未出现；interface 无 inhabitant，§4.14） |
| 25 | Mzk1G1TwoSectionPsiLocalActual | G-C ψ | DONE | 23:24:31 | fresh | clean | 三公理 (P+L) | **B**（affine Spec→A¹，非 P¹；cocycle 群恒等，§4.15） |
| 26 | Mzk1G1FiniteDisjointBelyiActual | G-K 有限族 | DONE | 23:23:49 | fresh | clean | 三公理 (P，只 probe `boundarySet_isClosed`） | **C/换题**（只有陈述+假设，无族 inhabitant，§4.16） |
| 27 | Mzk1G1BelyiCVCompositionActual | G-C h∘ψ | DONE | 23:30:24（23:24:32 曾 FAIL） | fresh | clean | 三公理 (L 末段) | **B**（多项式值层 composition law，§4.17） |
| 28 | Mzk1UCC1UpperActual（覆盖 #14） | U-C C1/C3 | DONE | 23:30:28（23:24:35 曾 FAIL） | fresh | clean | 三公理 (L) | **B 条件式**（C1 是定义、Hpkt≤B 是假设；C4 端接真 P5，§4.18） |
| 29 | Mzk1ULPacketVActual（覆盖 #10） | U-L C1 | DONE | 23:30:51 | **stale**（源码 23:33:06 又改） | clean | 旧 23:08 版三公理 (P) | **未审计当前版**（U-L 组） |
| 30 | Mzk1ULPacketHull2Actual | U-L hull | DONE | 23:31:19 | fresh | — | — | **未审计**（U-L 组） |
| 31 | Mzk1G1KvCompactActual | G-K K_V | **FAIL** | 23:23:50（23:29:35 重试仍 FAIL） | none | clean | — | **R**（首错 `15:2 unsolved goals ⊢ False`；`FinitePlace`/`InfinitePlace`/`Finset.not_mem_empty` 未知；136–139 norm_num/linarith 关不掉 `0<δ<1/2`） |
| 32 | Mzk1G1LocalHeightCriterionActual | L-H criterion | **FAIL** | 23:24:32（23:30:24 仍 FAIL） | none | clean | — | **R**（首错 `12:5 unexpected token 'λ'`；仍 `InKv`/`KvData` 未知、`ActualD1 ↔ ∀d∀D∀η…` 类型不符） |
| 33 | Mzk1G1D1ProducerActual（覆盖 #16） | L-H D1 | **FAIL** | 23:24:33（23:30:26 仍 FAIL） | none | clean | — | **R**（首错 `8:5 unknown namespace G1KvCompactActual` → 级联 `truncConductor/InKv/discOver/D1AnalyticInput` 未定义；最新尝试错在 150:54） |
| 34 | Mzk1G1DisjointFamilyActual（覆盖 #17） | G-K | **FAIL** | 23:24:32（23:30:24 仍 FAIL） | none | clean | — | **R**（首错 `15:5 unknown namespace …FermatProjClosedSubscheme4Actual`；`KvData`/`InKv`/`boundaryPreimage` 未知；96:0 universe metavariable） |
| 35 | Mzk1G1FermatOmegaTransitionActual | G-B ω 过渡 | **FAIL** | 23:21:40 | none | clean | 日志 sorryAx（elab 失败回退；源码无 sorry） | **R**（首错 `9:61 ring 未关`；目标 `−y^(n−1) = −(x²(y/x)^(n−1)x^(n−3))`） |
| 36 | Mzk1UCHpktActual（覆盖 #15） | U-C Hpkt | **FAIL** | 23:23:43（23:30:21 仍 FAIL） | stale | clean | 23:09 版三公理 (P) | **R**（最新尝试首错 `51:5 unknown identifier uc_c3`；更早 `49:70 hw`） |
| 37 | Mzk1HullFermatGluingActual | G-A glue | **FAIL** | 23:24:35（23:31:14 仍 FAIL） | none | clean | — | **R**（首错 `24:7 typeclass instance problem is stuck`；`FermatGluingResidual` 未知；§4.2 空 card 仍在文件） |
| 38 | Mzk1G1FermatTwoChartGluingActual（覆盖 #1） | G-A 粘合 | **FAIL** | 23:31:02 | none | clean | 日志 sorryAx（elab 失败回退） | **R 当前**（`17:8 Type mismatch`；原 23:10 空壳 DONE 作废） |
| 39 | Mzk1G1PsiChartMapsActual | G-C 图 | **FAIL** | 23:29:32 | none | — | — | **R**（首错 `33:57 rewrite 未找到模式`） |
| 40 | Mzk1G1PsiTwoChartCocycleActual | G-C cocycle | **FAIL** | 23:29:29 | none | — | — | **R**（首错 `39:6 rewrite 未找到模式`） |
| 41 | Mzk1G1OmegaActual | G-B Ω | **FAIL** | 23:24:06（23:29:51 仍 FAIL） | none | clean | — | **R**（首错 `24:2 Type mismatch after simp`） |
| 42 | Mzk1ULPacketHullActual | U-L hull | **FAIL** | 23:28:13（23:32:47 仍 FAIL） | none | — | — | **R**（最新尝试 `37:29 Function expected` / `97:2 Type mismatch`；早前有 import olean 缺） |
| 43 | Mzk1ULWeightedHullActual | U-L weighted | **FAIL** | 23:29:36 | none | — | — | **R**（首错 `3:0 import Mathlib.LinearAlgebra.Finrank olean 缺失`；`74:6 rewrite`） |

## 2c. 本批 batch 4 gate 表（快照 23:50 UTC；**覆盖 #5/#6/#10/#15/#17/#24/#29/#36/#39 的旧状态，并新增 #44–#69**）

grep 列 = 大小写敏感扫描 `sorry|admit|^axiom |PUnit|^True|maxHeartbeats`（注释/命名里出现该词的已人工排除）；本批被审文件 grep 全部 clean（唯一 `maxHeartbeats` 命中见 #55/§4.26）。axioms 列：(P) = 本批 `_ProbeGeom4Actual.lean` 独立复算；(L) = 文件自带 `#print` 的**日志末段**；— = 无。olean 列 fresh = olean mtime > 源码 mtime。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 44 | Mzk1G1PsiTwoChartCocycleActual | G-C cocycle | DONE | 23:34:24 | fresh | clean | 三公理 (P) | **B**：真环恒等式 `chartProdInv r T = r^|T| * chartProd x T`（由 `r*x=1` 逐因子证），及 ψ 两图坐标互逆；但 `r*x=1`、`qinv*chartProdInv=1` 是**假设**，未在 `Localization.Away` 上构造，也没有 scheme morphism |
| 45 | Mzk1UCHpktActual（覆盖 #15/#36） | U-C C3/C4 | DONE | 23:34:24 | **stale**（源码 23:40:20 > olean 23:34:23） | clean | 三公理 (P，对 23:34 olean) | **B 条件式**：`uc_sandwich` 只是 `−M ≤ θ`、`θ ≤ H_pkt`、`H_pkt ≤ κ(A−cL Q)−M` 三条假设的传递；`uc_c3` 的 `hullVol i ≤ paper i` 与 `hpaper` 均为假设。**docstring 声称用 ULPacketV/ULWeightedHull 的实际对象，但定理对任意 `w hullVol paper` 量化且未 import 这两个文件（§4.22）**；当前源码已改，需重审 |
| 46 | Mzk1ULWeightedHullActual（覆盖 #43） | U-L 权 | DONE | 23:34:30 | fresh | clean | 三公理 (P) | **A-局部**：`ulDivisorWeight = finrank_{ℚ_p} F_v`（真 local degree）、归一权总和 1、加权 hull 单调；但与 U-C 用的 `UCC3Producer.ucWeightedHpkt` 是**两套**未连接的加权 hull（§4.22） |
| 47 | Mzk1G1FermatOmegaTransitionActual（覆盖 #35） | G-B (A3) | DONE | 23:35:11 | fresh | clean | 三公理 (P) | **B**：标量恒等式 `(1/s^(n−1))*(−1/x²) = −x^(n−3)*(1/y^(n−1))`，任意域、不需要 Fermat 关系；无 Ω-模/局部化层，`ω∞ = x^(n−3)ω₀` 仍在其上待证 |
| 48 | Mzk1HullFermatGluingActual（覆盖 #18/#37） | G-A glue | DONE | 23:35:19 | fresh | clean | 三公理 (P，`twoChartGlueData` def 级) | **B（关键推进，不再是空 card）**：真 `Scheme.GlueData`（J=Bool、V 对角=chart、非对角=W、t=id、`t_fac`/`cocycle`/`f_open` 均真证）。但**完全 generic**（任意 U0,U1,W + open immersion），未实例化 Fermat 两图，无 `glued` 命名、无 π — 仍不是 G-A 出口（§4.23） |
| 49 | Mzk1ULPacketVActual（覆盖 #10/#29） | U-L C1 | DONE | 23:35:21 | fresh | clean | 三公理 (P) | **B+/A-局部**：`packetExceptional` 变成**定义**（filter `p−2 < shellExp`），`packetExceptional_small_outside` 由定义推出；`varpi` 是实际 completion 元素 + `hvarpi ≠ 0` 假设，**`varpi := 1` 已不存在**。仍缺 producer 提供 ϖ（kurt carrier） |
| 50 | Mzk1G1FermatProperFinal2Actual | G-A proper | DONE | 23:35:37 | fresh | clean | 三公理 (P) | **B**：18 行纯 re-export accepted donor（`ProjClosedSubscheme4`）的 proper/closed；无新数学，但给出 G-A proper 的稳定出口名 |
| 51 | Mzk1G1PsiChartMapsActual（覆盖 #39） | G-C ψ 图 | DONE | 23:39:30 | fresh | clean | 三公理 (L 末段；未单独 probe) | **B**：真实 quotient-ring chart 方程（`x^n+y^n=1`、`1+s^n=r^n`）、`psiChart0Coord_mem_iff`（素理想含乘积 ⟺ 含某线性因子，归纳真证）、`psiChart0Map : Spec A₀ ⟶ Spec ℚ[u]`、`psiChartInfCoord` 在 `Localization.Away q` 中。仍到 A¹ 不到 P¹，无 glue、无 `ψ*O(1)` |
| 52 | Mzk1G1FermatCurveClosed2Actual（覆盖 #6） | G-A closed/cover | DONE | 23:39:31 | fresh | clean | 三公理 (P) | **A-局部**：closed/proper 转述 accepted donor；新增 `fermatPolynomial_relation`、**`fermat_X1_pow_mem_span`（`X₁^n ∈ (F,X₀,X₂)`）**、`fermat_X1_mem_of_prime` 都是真代数。注意：**scheme 层「两张标准图覆盖 Y_n」仍未写出**，只有理想层结论 |
| 53 | Mzk1G1FermatFiniteDegree2Actual（覆盖 #5） | G-A rank | DONE | 23:39:32 | fresh | clean | 三公理 (P) | **A-局部（修正 §4.3 的 rank 错位）**：A₀ = ℚ[λ][x]/(x^n−λ)[y]/(y^n−(1−λ))，`Module.Basis (Fin n × Fin n) (ℚ[λ])`（两个 monic power basis 的 `smulTower`），`fermatA0Ring_finrank = n*n`，`A∞` 同。这正是 §2.3 要的 k[λ]-秩 n² |
| 54 | Mzk1G1QHeightActual（覆盖 #24） | L-H 高度 D3 | DONE | 23:39:32 | fresh（源码 23:37:22 重写） | clean | —（本批该文件无日志可查；23:23 版曾三公理 (P)） | **TOY/换题（D3 仍缺）**，但 **§4.14 的假命题 `legendreJ_zero`/`legendreJ_one` 已删除**（该风险条目作废）；现存只有 nonneg 两条 + `HeightDictionaryInterface`（无 inhabitant）。`legendreJ` 定义可复用 |
| 55 | Mzk1ULPacketHullActual（覆盖 #42） | U-L qVFamily packet | DONE | 23:42:48 | fresh | clean（含 `maxHeartbeats 4e6`，§4.26） | 三公理 (L) | **B**：把 `packetV/packetB` 实例化到实际 `qVFamTensorBlock`（`ulPacketTensorWitness`）；`ulQVFamPacketExceptional` 是定义、`small_outside` 由定义推出；仍需外部提供非零 ϖ（同 #49） |
| 56 | Mzk1G1FermatSupportActual | G-A support | DONE | **23:49:04**（23:45:47 前一次；源码 23:46:34 重编） | fresh | clean | 三公理 (P) | **A-局部**：`fermatChart0Map : Spec A₀ → Spec ℚ[λ]`、`fermatChartInfMap` 的 `IsFinite`（由 `Module.Finite` + `IsFinite.SpecMap_iff`）与 `IsProper`（finite ⇒ proper）；曲线 proper/closed 转述。这是 G-A「两图 finite/proper」骨架 |
| 57 | Mzk1G1FermatSmoothChartActual | G-A chart iso | **FAIL** | 23:49:18（同源码 23:46:33；上一次 23:45:16） | none | clean | 末段 **sorryAx**（`fermatA0EquivCurve`、`chart0RingEquiv`、两条 comp 恒等、`fermatU0_root_pow`、`fermatA0_x_pow`） | **R 当前尝试（不是旧 attempt）**：首错 `48:43`/`48:51 Ambiguous term`（`C` 在 `open Polynomial MvPolynomial` 下歧义）、`50:4`/`47:92 whnf 心跳 200000 超时`（`exact dvd_rfl` 展开 `fermatU0Poly`）、`71:17`/`99:30`/`106:66`/`112:23 rewrite 未找到模式`、`83:4 Unknown constant AdjoinRoot.liftAlgHom_toRingHom`（正确名 `toRingHom_liftAlgHom`/`coe_liftAlgHom`）、`80:73 unsolved goals`。**禁止引用 `fermatA0EquivCurve`** |
| 58 | Mzk1G1FiniteDisjointBelyiActual（覆盖 #26） | G-K | **FAIL** | 23:39:31（23:36:47 亦 FAIL；23:23:49 曾 DONE） | stale（源码 23:40:50） | clean | 23:23 版三公理 | **R（可秒修）**：`59:14 Unknown constant boundarySet_isClosed` — 文件末尾多了一行 `#print axioms boundarySet_isClosed` 写在 `end`/namespace **之外**；删掉该行即可。内容仍是 §4.16 的「无族」骨架（E1 是结构字段） |
| 59 | Mzk1G1B1B3ComponentActual（覆盖 #9） | G-C B1–B3 | **FAIL** | 23:36:33（23:09:44 曾 DONE） | stale（源码 23:35:34 > olean 23:09:43） | — | — | **未审计当前版**。FAIL 时其 import `PsiChartMapsActual` 正 FAIL → 级联；后者 23:39:30 已 DONE，应重编后再判 |
| 60 | Mzk1G1KvCompactActual（覆盖 #31） | L-H Kv | **FAIL** | 23:39:33（源码 23:40:50 又改） | none | clean | `localValueSet_isCompact` 三公理；**`kv_nonempty_emptyV` = sorryAx** | **R（stage4 根因未解）**：`Nat.Prime.mem_primeFactors` 参数类型错（`a*b*c ≠ 0` vs `n ≠ 0`）；`Finset.not_mem_empty` 不存在；`0<δ<1/2` 的 norm_num/linarith 仍关不掉 |
| 61 | Mzk1G1LocalHeightCriterionActual（覆盖 #32） | L-H criterion | **FAIL** | 23:45:47 | none | — | — | **R**（同 §2b#32：`12:5 unexpected token λ` 等；本轮仍红） |
| 62 | Mzk1G1DisjointFamilyActual（覆盖 #34） | G-K | **FAIL** | 23:45:47 | none | — | — | **R**（级联 KvCompact 的 `open …G1KvCompactActual`；未逐行重读） |
| 63 | Mzk1G1D1ProducerActual（覆盖 #33） | L-H D1 | **FAIL** | 23:45:49（源码 23:40:53 又改） | none | — | — | **R**（级联 KvCompact；当前源码未编译） |
| 64 | Mzk1G1OmegaActual（覆盖 #41） | G-B Ω | **FAIL** | 23:39:34（源码 23:40:44 又改） | none | clean | — | **R**：`61:2`/`68:2` 化简后是 `coordX * coordX^(n−1)` vs `coordX^n`（`pow_succ`/`pow_succ'` 方向问题），不是深层数学 |
| 65 | Mzk1G1FermatTransitionActual | G-B 过渡 | **FAIL** | 23:39:36（源码 23:40:32 又改） | none | clean | `affineX_pow_add_affineY_pow_sub_one`、`one_add_overlapS_pow_sub_overlapR_pow` = **sorryAx** | **R**：残留 goal `⊢ 1 * overlapY^n = overlapY^n`（`simp`/`ring` 即可）；两条定理在 sorryAx 清掉前不得引用 |
| 66 | Mzk1G1FermatOverlapActual（覆盖 #2） | G-A overlap | **FAIL** | 23:39:38（源码 23:42:18 又改） | stale（olean 23:30:53） | — | 末段 `overlapToChart0_isOpenImmersion`/`overlapToChartInf_isOpenImmersion` = **sorryAx** | **R 当前尝试**（正在重写成真 overlap；22:30 DONE 的 placeholder 判 C 作废，但 red 期间不得引用） |
| 67 | Mzk1G1FermatRadicalSupportActual | H-T radical | **FAIL** | 23:45:48（23:40:03、23:42:35 亦 FAIL） | none | clean | — | **R**：`Nat.Prime.mem_primeFactors` 类型错（同 #60）；`165:2` `log_natAbs_discr_eq_sum_factorization` 方向反（需 `.symm`） |
| 68 | Mzk1G1FermatCurveClosedActual（新文件） | G-A closed（重复） | **FAIL** | 23:35:37 | none | clean | `fermatCurveClosedImmersion_isClosed/_isProper` = **sorryAx** | **R − 冗余文件**：与 accepted `ProjClosedSubscheme4Actual` 逐字同义；病根：`24:2`/`28:2` `SynthInstanceFailed IsClosedImmersion (fermatIdealSheaf n).subschemeι`（`def` 不可归约，instances 透明下匹配不到 `IdealSheafData.subschemeι` 实例），`31:3 Unknown constant …iff_isProper_and_mono.mp`（缺 `(f := …)`）。donor 用 `abbrev` + `(f := …)` 已 DONE → **建议删，不要修** |
| 69 | Mzk1HullFermatClosedSubschemeActual（新文件） | G-A closed（重复） | **FAIL** | 23:35:44 | none | clean | 同上 = **sorryAx** | **R − 冗余文件**（同 #68；`24:2` synth 失败、`27:9` unknown constant）→ 删除或改 `abbrev` + `(f := …)` |

**状态翻转一览（本批）**：`FiniteDegree2Actual` FAIL→DONE（23:39:32）、`CurveClosed2Actual` FAIL→DONE（23:39:31）、`SupportActual` FAIL→DONE（23:45:47）、`SmoothChartActual` FAIL→**新尝试真 FAIL**（23:45:16）、`HullFermatGluingActual` FAIL→DONE（空 card → 真 `GlueData`）、`OmegaTransitionActual` FAIL→DONE、`UCHpktActual` FAIL→DONE（现又 stale）、`ULWeightedHullActual` FAIL→DONE、`PsiTwoChartCocycleActual` FAIL→DONE、`PsiChartMapsActual` FAIL→DONE、`FiniteDisjointBelyiActual` DONE→FAIL（尾部 `#print`）、`QHeightActual` DONE→FAIL→DONE（重写）、`B1B3ComponentActual` DONE→FAIL（级联，stale）。

## 2d. 本批 batch 5 gate 表（快照 **00:16 UTC**；**覆盖 #1/#19/#20/#31/#33/#38/#45/#54/#57/#58/#60/#61/#62/#63/#66/#67/#68/#69 的旧状态，并新增 #70–#104**）

grep 列 = 大小写敏感扫描 `sorry|admit\b|^axiom |PUnit|^True|maxHeartbeats`（注释/命令名里的词已人工排除；`ULift.up true/false`、`if_true`、`Polynomial.C` 等为假命中）。axioms 列：(P) = 本批 `_ProbeBatch5Actual.lean` 独立复算；(L) = 文件自带 `#print` 的**当前 attempt 日志末段**；— = 该文件无 `#print`（不表示无公理）。olean 列 fresh = olean mtime > 源码 mtime。

**纪律**：本批所有状态都取自 `watchdog.log` 中该文件**最后一次** START/DONE/FAIL，并把该时间与源码 mtime 对照；源码 mtime 晚于最后一次尝试的表内记 "stale / 未运行"。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 70 | Mzk1G1OmegaActual（覆盖 #41/#64） | G-B Ω | DONE | 23:54:09 | fresh | clean | 三公理 (P) | **B+**：真 `KaehlerDifferential ℚ (R n)`、单关系 `n x^(n−1)dx + n y^(n−1)dy = 0`、Euler 形式 `ω = y dx − x dy`、`presMap_relation`；仅 A₀ 一张图，无 ω∞ 与两图比较（§4.33） |
| 71 | Mzk1G1FermatOverlapActual（覆盖 #2/#66） | G-A overlap | DONE | 23:54:18 | fresh | clean | 三公理 (P) | **A-局部**：`alpha : Away x0 → Away r1`、`beta` 互逆（`alpha_beta`/`beta_alpha`），`overlapSchemeIso` 真 scheme 同构，两条 open immersion（§4.29） |
| 72 | Mzk1URPacketActual（覆盖 #19） | U-R packet | DONE | 23:54:41 | fresh | clean | 三公理 (L) | **B**：`varpi = 1`/`exceptional = univ` 已消失；`urPhi_preserves` 是定义展开、`ur_qReading_formula` 是 donor `rootParameterWeight_eq_ord_varpi` 转述；仍无 q = −M、无 θ_P5 ≤ H_pkt |
| 73 | Mzk1G1ProjectiveLineChartsActual | G-C P¹ 图 | DONE | 23:55:36 | fresh | clean | 三公理 (L) | **B+**：`chart0/chart1 = Proj.awayι`、两条 `IsOpenImmersion`、`overlapOpen_eq_inf`、`overlapIso`（`Proj.basicOpenIsoSpec`）；真 P¹ 图表基础设施 |
| 74 | Mzk1G1LocalHeightCriterionActual（覆盖 #61） | L-H D1 | DONE | 23:56:59 | fresh | clean | 三公理 (L) | **B−/陈述层**：`LocalHeightCriterion d D η = ∃ C, ∀ K, finrank ≤ d → ∀ lam, InKv D lam → h ≤ (1+η)(D+trunc) + C`（量词与路线一致），`ActualD1 := ∀ d D η, 0<η → …`，但 **`actualD1_iff = Iff.rfl` 是定义自反**，D1 本身无 inhabitant（§4.31） |
| 75 | Mzk1P8EpsilonSelectionActual | P8-P | DONE | 23:58:10 | fresh | clean | —（无 `#print`） | **A-局部**：δ = min 1 (ε/3) ⇒ (1+δ)² ≤ 1+ε、∃ n ≥ 4 使 n/(n−3) ≤ 1+δ，均为真实数不等式证明 |
| 76 | Mzk1G1PsiChartInfCoverActual | G-C 覆盖输入 | DONE | 23:59:36 | fresh | clean | 三公理 (P) | **B+**：`psiChartInfDenom ≡ 1 mod (r)`（归纳真证）、`span{q, r} = ⊤`、无素理想同时含 q 与 r；仍只是环层覆盖输入，不是 scheme 覆盖 |
| 77 | Mzk1P8FreyAssemblyActual | P8-P | DONE | 23:59:39 | fresh | clean | —（无 `#print`） | **B**：`ABCLogConjecture → ABCFreyJProductHeightCriterion → ABCConjecture` 真归约（条件式），donor `abcJInvariant_logHeight_le` 已 olean 存在 |
| 78 | Mzk1G1FermatRadicalSupportActual（覆盖 #67） | H-T radical | DONE | 00:00:04 | fresh | clean | —（无 `#print`） | **B（未逐行读）**：182 行；`radical_eq_prod_primeFactors_f7`、`f7_sum_bound`、`log_natAbs_discr_eq_sum_factorization` 等；此前首错 `.symm` 已修 |
| 79 | Mzk1ULPhiRealizationActual（覆盖 #20） | U-L Φ | DONE | 00:01:31 | fresh | clean | 三公理 (L) | **B−**：新增真标量作用 `c • x`（`ulScalarActionEquiv`）并**真的**证明其保 `arithmeticTupleUnitLogLattice`（ℤ_p-模结构）；但 `ulPhiRealization_cover` 仍是逐元素自反（§4.6 只部分作废） |
| 80 | Mzk1G1FermatTwoChartGluingActual（覆盖 #1/#38） | G-A 粘合 | DONE | 00:04:36 | fresh | clean | 三公理 (P) | **A-局部（本批最大 G-A 推进）**：`Chart0Ring = R n`、`ChartInfRing = R2 n`、`Overlap0 = Away x0`，`fermatTwoChartGlueData := twoChartGlueData …`，`fermatCurveScheme := glued`，两条 chart open immersion；仍缺 overlap 相容等式（文件自标 TODO）、π、smooth/整性（§4.29） |
| 81 | Mzk1F7TameOrderActual | H-T F7 tame | DONE | 00:06:50 | fresh | clean | 三公理 (P；本文件无 `#print`) | **B+**：`d = e−1 ⇒ d/e ≤ 1`（`div_le_iff₀` + `nlinarith`）与 `(d/e)·log p ≤ log p`；tame 假设作为参数，未 import `count_differentIdeal_eq_of_tame` 自行生产 |
| 82 | Mzk1G1FermatCurveActual | G-A 出口名 | DONE | 00:07:41 | fresh | clean | 三公理 (P) | **B**：薄 re-export（`fermatCurveScheme := TwoChartGluing.fermatCurveScheme`、`_eq_glued` = rfl、两条 open immersion、`fermatCurveOpenCover := GlueData.openCover`）；无新数学，但给出 G-A 的稳定名 |
| 83 | Mzk1G1DisjointFamilyActual（覆盖 #34/#62） | G-K | DONE | 00:08:42 | **stale**（源码 00:14:41 > olean 00:08:42） | clean | —（无 `#print`） | **B−（当前源码未编译）**：`exists_boundary_avoiding`/`uniform_positive_away` 是真组合/拓扑引理；`GKData` 的 `family : ActualDisjointBelyiFamily n` 是字段（无 inhabitant） |
| 84 | Mzk1URRootMassActual | U-R mass | DONE | 00:08:43 | fresh | clean | —（无 `#print`） | **未深审**：296 行测度论（`distribHaarChar_*`、`normalizedLogMass_kummer_root`）；DONE + grep clean，语义未逐行读 |
| 85 | Mzk1G1D1ProducerActual（覆盖 #33/#63） | L-H D1 | DONE | 00:08:51 | fresh | clean | —（无 `#print`） | **B**：`d1_of_analyticInput : D1AnalyticInput D → 0<η → LocalHeightCriterion d D η`，吸收论证（`ratio_le`、`sqrt_mul_log_sublinear`）是真证；D3/D4 仍是结构字段，无 producer |
| 86 | Mzk1G1ProjectiveLineChartMapsActual | G-C P¹ 映射 | DONE | 00:12:00 | fresh | clean | 三公理 (L) | **B+**：`chart0OfPolynomial/chart1OfPolynomial` 与 `_preimage_chart0/1`；多项式图→P¹ 的可复用层 |
| 87 | Mzk1G1PsiChartToP1Actual | G-C ψ→P¹ | DONE | 00:12:00 | fresh | clean | **三公理 (L + Probe 5 (P))** | **B+/A-局部**：`psiChart0ToP1 := Proj.fromOfGlobalSections (X0 ↦ u, X1 ↦ 1)` 是真 scheme 态射到 `Proj Q[X0,X1]`，`psiChart0ToP1_preimage_basicOpen` 给出 `D_+(X0)` 原像 = `D(u)`（= D_T 的补）；仍只有第一图、未粘成 Y_n → P¹（§4.30） |
| 88 | Mzk1G1QHeightActual（覆盖 #54） | L-H D3 | DONE | 00:12:00 | fresh | clean | 三公理 (L，仅两条 nonneg) | **TOY/换题（D3 仍缺）**：只有 `lambdaHeight_nonneg`/`jHeight_nonneg`；`legendreJ` 定义可复用，D3 与 `HeightDictionaryInterface` 无 inhabitant |
| 89 | Mzk1G1KvCompactActual（覆盖 #31/#60） | L-H K_V | DONE | 00:12:01 | fresh | clean | 三公理 (L：`localValueSet_isCompact` + `kv_nonempty_emptyV`) | **B+**：`LocalValueSet δ = [δ, δ⁻¹]` 真 compact、`InKv.arch_mem/arch_bound/arch_apply_ne_zero`；**此前的 `sorryAx` 已清**，L-H 级联根因解除 |
| 90 | Mzk1UCHpktActual（覆盖 #45） | U-C C3/C4 | DONE | 23:51:30 | fresh（src 23:49:21） | clean | —（未重读当前版） | **未重读**：§2c#45 的判定针对 23:34 olean；23:49:21 源码版已 DONE，语义待下批 |
| 91 | Mzk1G1FermatSmoothChartActual（覆盖 #57） | G-A chart | DONE | 00:13:40 | fresh | clean | 三公理 (L，4 条) | **B−（降级）**：当前版只到 `fermatU0ToCurve : U₀ → D`（`λ ↦ x^n`、`x ↦ x`）+ `fermatCurve_relation`；上一版的 `fermatA0ToCurve`/`chart0RingHom`（A₀ → D）**已从该版删除**，A₀≃D 识别仍未完成 |
| 92 | Mzk1G1FiniteDisjointBelyiActual（覆盖 #58） | G-K | DONE | 00:13:41 | fresh | clean | 三公理 (L) | **C/换题（但已诚实标注）**：尾部 `#print` 已移入 namespace（§2c#58 的秒修已完成）；`B1AvoidingMaps`/`ActualDisjointBelyiFamily` 均标 "INTERFACE, NO INHABITANT"；仍无族 inhabitant |
| 93 | Mzk1G1FermatSmoothIntegralActual | G-A 整性 | **FAIL** | 00:13:39 | none | clean | 前次末段 sorryAx（error-recovery） | **R（最接近修好的一个）**：当前源码（00:12:45）只剩 **2 条 `unsolved goals`**（138:66、146:71，都在 `fermatMvEquivPoly_fermatCurvePoly` 的 `simp only` 段）；Eisenstein 路线（`fermatTwoVarPoly_isEisenstein` → `Irreducible` → `IsDomain`）本身方向正确 |
| 94 | Mzk1G1FermatSmoothAttemptActual（覆盖 #57 邻） | G-A smooth | **FAIL** | 00:04:36（当前源码 00:03:01，log 仅含该 attempt） | none | clean | 前次 sorryAx（error-recovery） | **R（API 名错，非数学错）**：首错 `58:4/59:2 Unknown identifier PreSubmersivePresentation`（Mathlib 里在 `namespace Algebra` 下）、`jacobiMatrix_naive` 不存在（应为 `jacobiMatrix_apply`）；Jacobian = `(n x^{n−1})²` 的推导本身已写好 |
| 95 | Mzk1G1FermatPiActual | G-A π | **FAIL** | 00:13:44 | none | — | — | **R**：首错 `32:41 Type mismatch`；构造（`Proj.fromOfGlobalSections`，`X0 ↦ x^n, X1 ↦ 1` / `X0 ↦ 1, X1 ↦ r^n`）方向正确，两图 glue 尚未写 |
| 96 | Mzk1G1FermatOverlapRingActual | G-A overlap ring | **FAIL** | 00:05:48 | none | — | — | **R（未读源码）** |
| 97 | Mzk1G1OmegaPresentationActual | G-B | **FAIL** | 00:12:03 | none | — | — | **R（未读源码）** |
| 98 | Mzk1G1OmegaBasisActual | G-B | **FAIL** | 00:13:42 | none | — | — | **R（未读源码）** |
| 99 | Mzk1UCC3ProducerActual | U-C 权 | **FAIL** | 00:13:41 | none | — | — | **R（未读源码；注意 §4.22 的三套加权 hull 之一在此文件）** |
| 100 | Mzk1URThetaHullActual | U-R | **FAIL** | 00:13:59 | none | — | — | **R（未读源码）** |
| 101 | Mzk1URRootExtensionActual | U-R | **FAIL** | 00:14:15 | none | — | — | **R（未读源码）** |
| 102 | Mzk1G1FermatRadicalSupportFinal3Actual（新文件） | H-T | **FAIL** | 00:14:17 | none | — | — | **R（新文件，未读）**；与 #78 的命名关系需 H-T lane 说明（避免重复文件） |
| 103 | Mzk1G1FermatCurveClosedActual（覆盖 #68） | G-A closed（重复） | **FAIL** | 00:10:00 | none | clean | — | **R − 冗余文件**（§4.25 结论不变：建议删） |
| 104 | Mzk1HullFermatClosedSubschemeActual（覆盖 #69） | G-A closed（重复） | **FAIL** | 00:10:00 | none | clean | — | **R − 冗余文件**（同上） |

**状态翻转一览（batch 5，对比 §2c/§2b）**：
- FAIL→DONE：`OmegaActual`(23:54:09)、`FermatOverlapActual`(23:54:18)、`URPacketActual`(23:54:41)、`LocalHeightCriterionActual`(23:56:59)、`PsiChartInfCoverActual`(23:59:36)、`RadicalSupportActual`(00:00:04)、`ULPhiRealizationActual`(00:01:31)、`FermatTwoChartGluingActual`(00:04:36)、`D1ProducerActual`(00:08:51)、`DisjointFamilyActual`(00:08:42)、`SmoothChartActual`(00:13:40)、`FiniteDisjointBelyiActual`(00:13:41)、`KvCompactActual`(00:12:01)、`PsiChartToP1Actual`（00:10:24 源码版 00:12:00 DONE）。
- DONE→FAIL/stale：`DisjointFamilyActual`（00:14:41 又改，olean stale）。
- 新 DONE（本批首次）：`ProjectiveLineChartsActual`、`P8EpsilonSelectionActual`、`P8FreyAssemblyActual`、`F7TameOrderActual`、`FermatCurveActual`、`ProjectiveLineChartMapsActual`、`URRootMassActual`。
- 新 FAIL：`FermatPiActual`、`FermatOverlapRingActual`、`OmegaPresentationActual`、`OmegaBasisActual`、`UCC3ProducerActual`、`URThetaHullActual`、`URRootExtensionActual`、`RadicalSupportFinal3Actual`。

> **快照（00:16 UTC）之后的变化（未审计，仅记录）**：`Mzk1G1FermatTwoChartGluingActual` 于 **00:19:37 FAIL**（源码被再次改写，00:04:35 的 olean 变 stale；本表 #80 与 Probe 5 对应的是 00:04:36 那一版）；新文件 `Mzk1G1ProjectiveLineGluedActual` 00:19:39 FAIL。

## 2e. 本批 batch 6 gate 表（快照 **00:55 UTC = 08:55 CST**；**覆盖 #48/#80/#92/#93/#94/#95/#96/#97/#98/#99/#100/#101/#102/#103/#104 的旧状态，并新增 #105–#129**）

grep 列 = 大小写敏感扫描 `sorry|admit|^axiom |PUnit|^True|toy|surrogate|maxHeartbeats`（注释里的"不含 sorry/admit/axiom/PUnit/True/toy"字样已人工排除；本批唯一命中是三个 geom 文件的 `set_option maxHeartbeats 800000`，单列）。axioms 列：(P) = 本批 `_ProbeBatch6Actual.lean` 独立复算；(L) = 文件自带 `#print` 的**当前 attempt 日志末段**；(L*) = Lead 自建 `_ProbeP8LeadActual` 的日志（**不是 audit 独立 probe**）；— = 无 `#print` 或未单独 probe。olean 列 fresh = olean mtime > 源码 mtime。

**纪律**：本批所有状态都取自 `watchdog.log` 中该文件**最后一次** START/DONE/FAIL，并把该时间与源码 mtime 对照；源码 mtime 晚于最后一次尝试的表内记 "stale / 未运行"。#105–#108 是 00:16–00:37 之间的 DONE（batch 5 快照 00:16 之后、本批 Lead 清单 00:37 之前），单独放在 §2e-0 补审。

### 2e-0 补审：00:16–00:37 UTC（batch 5 快照后、Lead 清单前）

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 105 | Mzk1UCC3ProducerActual（覆盖 #99） | U-C 加权 | DONE | 00:28:25 | fresh | clean | 三公理 (L) | **B**：`uc_c3_from_weighted` 仍是 `hHpkt`+`hpaper` 两条假设的传递（§4.22 三套加权 hull 未统一）；真增量是 `primeCounting_mul_log_le_four_thirds` / `exists_primeCounting_mul_log_le_four_thirds`（Section2 donor `iutIVProp16_primeCounting_le_four_thirds_eventually` + 两分支论证）。 |
| 106 | Mzk1G1DisjointFamilyActual（覆盖 #34/#62/#83 的 stale） | G-K | DONE | 00:26:57 | fresh | clean | 三公理 (L) | **B−**：`exists_boundary_avoiding`（r+1 个两两不交边界漏掉 ≤r 个点）、`exists_pos_min_of_compact`、`uniform_positive_away` 是真组合/拓扑；但 `GKData.family` 仍是字段、`UniversalLocalFieldExists` 明标 "interface, no inhabitant"。 |
| 107 | Mzk1G1ProjectiveLineGluedActual | G-C P¹ 粘合 | DONE | 00:31:10 | fresh | clean | 三公理 (L：5 条) | **A-局部**：真两图 `Scheme.GlueData`（chart0=chartInf=Spec ℚ[λ]、overlap=ℚ[λ,λ⁻¹]、`invAuto` 对合）、`localChart_overlap_condition = glue_condition`、两图 `jointly_surjective`；是 P¹ 的可用 glued 模型（FermatPi / ProjectiveLineTransition 的底座）。 |
| 108 | Mzk1G1FiniteDisjointBelyiActual（覆盖 #92 的 stale） | G-K | DONE | 00:32:40（00:25:30 亦重编） | fresh（src 00:31:54） | clean | 三公理 (L：`boundarySet_isClosed`） | **C/换题（仍无族）**：新增 `gluedBoundary`（用真 `localChart0/localChart1` 的像）与 `GluedBelyiFamily`，但 `B1AvoidingMaps` / `GluedBelyiFamily` 明标 NO INHABITANT；`disjoint_edges` 仍是字段。 |

### 2e-1 00:37–00:55 UTC（Lead 清单逐项核对 + 其他 DONE/FAIL）

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 109 | Mzk1G1FermatSmoothIntegralActual（覆盖 #93） | G-A 整性 | DONE | 00:37:00 | fresh | clean（`maxHeartbeats 800000`） | 三公理 (P；`fermatCurveRing_isDomain`) | **A-局部（#93 的 R 翻转）**：Eisenstein 于 (Y−1) ⇒ `Irreducible F` ⇒ `(F)` 素 ⇒ `R n` 整环，真证；仅 `n>0`，无 scheme 层/几何整性（任意 K 的 copy 见 #128，仍 FAIL）。 |
| 110 | Mzk1G1FermatSmoothAttemptActual（覆盖 #94） | G-A smooth | DONE | 00:37:00 | fresh | clean（`maxHeartbeats 800000`） | 三公理 (P；`fermatModel_isStandardSmooth`) | **A-局部（#94 翻转）**：真 `Algebra.SubmersivePresentation`（Fin 3/Fin 2）、`fermatModel_det = (n x^(n−1))²`、关系使偏导可逆、`IsStandardSmoothOfRelativeDimension 1`；但只在局部化模型 ℚ[x,y,z]/(F,(n x^(n−1))z−1) 上，未证它与 `(R n)[1/x]` 同构、也无 scheme 层 smooth。 |
| 111 | Mzk1G1FermatTwoChartGluingActual（覆盖 #80；**STALE**） | G-A 粘合 | DONE | 00:39:10（00:37:00 FAIL 后） | fresh | clean | 三公理 (P：chart open immersion；日志末段) | **A-局部**：`fermatTwoChartGlueData` 是真实例（chart ring 取 Overlap 文件），两条 chart open immersion 真；**用户级 cocycle 等式仍是 TODO 注释**（instances transparency），未证 `Y_n ≅ Proj(F)`、无 π。**#80/Probe5 对 00:04 版的判定 STALE**。 |
| 112 | Mzk1HullFermatGluingActual（覆盖 #48/#37/#18；**STALE**） | G-A generic glue | DONE | 00:39:11 | fresh | clean | 当前 `twoChartGlueData` **未单独 probe**（无 #print）；Probe 6 经 #111 import 成功 + chart imm 三公理 | **A-局部（generic 模板）**：真 `Scheme.GlueData`（t=id、t_fac/cocycle/f_open 全真证）；仍 generic，无 Fermat 实例化、无 π。**#48/Probe4 对 23:35 版判定 STALE**。 |
| 113 | Mzk1G1FermatPiActual（覆盖 #95） | G-A π | DONE | 00:41:49 | fresh | clean | 三公理 (P：`piChart0` 定义 + 两条 chart X 恒等) | **B−**：定义了 `piChart0/piChartInf : Spec A0/A1 → projectiveLineGlued`（λ↦x^n、t↦r^n），但**没有** `glueMorphisms`/相容定理/`pi : Y_n → P¹`/原像/degree；docstring 声称的 glue 未写（#95 的 R 翻转成"半成品"）。 |
| 114 | Mzk1G1ProjectiveLineTransitionActual | G-C P¹ 过渡 | DONE | 00:43:15 | fresh | clean | 三公理 (P) | **A-局部**：任意 ℚ-代数基上 `chartMorphism0 u = chartMorphismInf u⁻¹`（u 单位），用 `IsLocalization.Away.lift` + overlap 条件；是 π 粘合的可复用输入，但本身不产生 π。 |
| 115 | Mzk1F7DiscProductActual（Lead） | F7 product | DONE | 00:43:17 | fresh | clean | 三公理 (L* Lead probe；日志含旧 attempt 错误，末段仅 linter warning) | **A-局部/B+**：`factorization_multiset_prod_absNorm` 真 multiset 归纳（`Nat.factorization_mul` + `Multiset.induction`）；对象/量词正确。日志中 24:6/49:23 是旧源码 attempt，勿判红（§4.40）。 |
| 116 | Mzk1F7DiscSumActual（Lead） | F7 主公式 | DONE | 00:44:40 | fresh | clean | 三公理 (P：`disc_factorization_eq_multiset_sum`；L* 同) | **A-局部/B+**：真 `v_p(|disc K|)=Σ_P v_P(𝔇)·[under=p]·f_P`（multiset 计数 + 规范化因子 + `factorization_absNorm_eq_ite`）；仍未接 tame 上界（#129 仍 FAIL）。 |
| 117 | Mzk1G1FermatRadicalSupportFinal3Actual（覆盖 #102） | H-T tame 桥 | DONE | 00:45:07 | fresh | clean | 三公理 (P：`tame_localDifferentPaperOrder_le_one_of_tame`；文件 #print) | **B+（#102 的 FAIL 翻转）**：`tame_count_differentIdeal_eq` 是 donor `count_differentIdeal_eq_of_tame` 在 ℤ_p/𝒪_L 的实例化（`hsepFrac`/`hsep`/`he` 为诚实假设）；桥到 `localDifferentPaperOrder ≤ 1` 真。全局 `v_p(disc)≤finrank` 未完成（#129）。 |
| 118 | Mzk1ULThetaPacketActual | U-L per-b | DONE | 00:45:07 | fresh | clean | 三公理 (P：`ulNormalizedLogMass_smul`；文件 #print) | **B**：实际 per-b 对象都定义（`rootNormedExtension`、`rootExtensionHaar`、`ulFinrankF`、`θ_j • unit ball`、`ulThetaPacketV`），`ulNormalizedLogMass_smul` 是真质量恒等式；`V_a = −ord_p θ_j log p` 与 C1 界按 docstring 明确留待下一步，无 `θ_P5 ≤ H_pkt`。 |
| 119 | Mzk1G1OmegaBasisActual（覆盖 #98） | G-B | **FAIL** | 00:52:52（00:41:51 亦 FAIL） | none | clean | `y_pow_smul_omegaForm` / `n_y_pow_smul_omega0` / `n_x_pow_smul_omega0` = sorryAx (L 末段) | **R**：104:22/133:22/149:8/161:8/176:8 `rewrite` 找不到模式（Ω 基 scalar 公式），非 toy。 |
| 120 | Mzk1G1FermatOverlapRingActual（覆盖 #96） | G-A overlap ring | **FAIL** | 00:54:35（00:43:21 亦 FAIL） | none | clean | `beta_alpha` / `overlapEquiv` / `overlapSchemeIso` = sorryAx (L) | **R**：86:4/87:42 `linarith`、183:50 Application type mismatch；注意 `Mzk1G1FermatOverlapActual.overlapSchemeIso` 已是 A-局部 accepted，本文件是重复/竞争实现，引用时勿混淆。 |
| 121 | Mzk1URThetaHullActual（覆盖 #100） | U-R | **FAIL** | 00:54:45（00:43:33 亦 FAIL） | none | clean | — | **R（级联）**：首错 `object file Mzk1URRootExtensionActual.olean does not exist`；根因是 #122，不是自身数学（§0.5 纪律）。 |
| 122 | Mzk1URRootExtensionActual（覆盖 #101） | U-R | **FAIL** | 00:43:47；00:54:00 重试中（快照时未出结果） | none | — | `urRootMass_kummer` = sorryAx (L)；`urRootTheta_order`/`urRootTheta_order_base` 三公理 | **R**：189:2 Type mismatch（`normalizedLogMass_kummer_root` 应用链）。 |
| 123 | Mzk1G1ProjectiveLineBoundaryActual | G-C P¹ boundary | **FAIL** | 00:47:54 | none | — | — | **R**：51:31 Application type mismatch（`isPrime_span_X_sub_C`/子类型）；新文件。 |
| 124 | Mzk1G1ProjectiveLinePiOverlapActual | G-C π overlap | **FAIL** | 00:53:40（00:52:03、00:47:58 亦 FAIL） | none | — | `fermatPiOverlap_condition` = sorryAx (L) | **R**：106:6 `rewrite` 找不到 `↑(overlapUnit ?n)⁻¹`；早前 21:2 `simp` nested、32:28/34:28 `rewrite`。π 的 overlap 相容仍未写出。 |
| 125 | Mzk1G1OmegaPresentationActual（覆盖 #97） | G-B | **FAIL** | 00:47:59 | none | — | — | **R**：24:2 Type mismatch（`omBasis.baseChange ... \|>.equivFun`）、71:18 rewrite、79:97 Application type mismatch；Ω 展示层仍红。 |
| 126 | Mzk1G1FermatCurveClosedActual（覆盖 #103） | G-A 重复 | **FAIL** | 00:47:56 | none | clean | `fermatCurveClosedImmersion_isClosed/_isProper` = sorryAx | **R − 冗余**：28:2 synthInstanceFailed、31:3 unknown constant；结论同 §4.25：删，不修。 |
| 127 | Mzk1HullFermatClosedSubschemeActual（覆盖 #104） | G-A 重复 | **FAIL** | 00:47:56 | none | clean | `fermatCurveImmersion_isClosedImmersion/_isProper` = sorryAx | **R − 冗余**：24:2 synthInstanceFailed、27:9 unknown constant；删。 |
| 128 | Mzk1G1FermatSmoothGeomIntegralActual（新文件） | G-A 几何整性 (K) | **FAIL** | 00:52:49（00:48:46 亦 FAIL） | none | clean（`maxHeartbeats 800000`） | — | **R**：38:23 Application type mismatch、46:61/53:52/58:35 typeclass stuck、192/195–198 unknown constant；**命名空间关闭写错**（开 `...GeomIntegralActual`，关 `...SmoothIntegralActual`，200:0），是 SmoothIntegral 的 198 行 copy，勿引用。 |
| 129 | Mzk1F7DiscTameBoundActual（新文件） | F7 tame 主界 | **FAIL** | 00:48:49 | none | clean | — | **R**：46:8/49:8 rewrite、54:2 Type mismatch（`Finset.sum_le_sum_of_subset_of_nonneg` 用法）；主界 `v_p(disc) ≤ finrank` 未落地。 |

**状态翻转一览（batch 6，对比 §2d/§2c）**：
- FAIL→DONE：`SmoothIntegralActual`(00:37:00，#93)、`SmoothAttemptActual`(00:37:00，#94)、`FermatPiActual`(00:41:49，#95，但只到 chart maps)、`UCC3ProducerActual`(00:28:25，#99)、`RadicalSupportFinal3Actual`(00:45:07，#102)、`TwoChartGluingActual`/`HullFermatGluingActual`（00:39 恢复）。
- 新 DONE（本批首次）：`ProjectiveLineGluedActual`(00:31:10)、`ProjectiveLineTransitionActual`(00:43:15)、`F7DiscProductActual`(00:43:17)、`F7DiscSumActual`(00:44:40)、`ULThetaPacketActual`(00:45:07)；另有 00:25–00:35 的 Lead 线 `P6HConst`、`F7DiscLocalGlobal`、`F7DiscPrimeFactor`（§4.39）。
- DONE→FAIL/STALE：**没有"旧 DONE 被新 FAIL 覆盖且未恢复"的路线文件**；但 `TwoChartGluingActual` 的 00:04:36 DONE 与 `HullFermatGluingActual` 的 23:35:19 DONE 都被 00:19–00:37 的 FAIL 覆盖后重编，旧 #80/#48 与 Probe 4/5 的对应结果 **STALE**（当前版本已重审，见 #111/#112）。
- 新增 FAIL（本批首次）：`ProjectiveLineBoundaryActual`、`ProjectiveLinePiOverlapActual`、`SmoothGeomIntegralActual`、`F7DiscTameBoundActual`。
- 仍未翻转：`OmegaPresentationActual`、`OmegaBasisActual`、`FermatOverlapRingActual`、`URThetaHullActual`、`URRootExtensionActual`、两个 closed-immersion 冗余文件。

## 2f. 本批 batch 7 gate 表（快照 **12:55 UTC = 20:55 CST**；新增 #130–#149，覆盖 #111/#112/#117/#119/#122/#124/#129 等旧行）

grep 列 = 大小写敏感扫描 `sorry|admit\b|^axiom |PUnit|^True|surrogate|toy|maxHeartbeats`（对 #130–#149 共 18 个文件；命中只有注释与 `maxHeartbeats`，已人工排除）。axioms 列：(P) = 本批 `_ProbeBatch7Actual.lean` 独立复算；(L) = 文件自带 `#print` 的**当前 attempt 日志末段**；— = 无 `#print` 或未 probe。olean 列 fresh = olean mtime > 源码 mtime；**stale = 源码在最后一次 DONE 后被改，该 DONE 不算数**。

**纪律（本批实测补充，见 §4.46）**：watchdog 在每次 START 时清空 per-file log，所以 FAIL 的首错必须**在 FAIL 之后、下次 START 之前**读；本批 `OmegaFree`(12:51:30) 与 `URThetaHull`(12:42:26) 的 log 已被后续 START 清掉，首错只能记“未取”。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 130 | Mzk1URRootExtensionActual（覆盖 #122） | U-R root carrier | **DONE** | 12:41:43（12:37:42 曾 FAIL） | fresh | clean | 三公理 (P：`urRootTheta_order_base`；L：6 条) | **A-局部/B+**：carrier 是 donor `rootNormedExtension`（real finite extension in normed alg closure），root 元素/Kummer 幂关系 `α^(2l)=q_b` 复用 donor；`urRootTheta_order_base`=真实 log/阶计算（θ=α^g、α^(2l)=q ⇒ ord θ=(g/2l)·ord q）。**docstring 声称的 `urRootMass_kummer` 在本文件不存在**（§4.48）；无 q=−M、无 θ≤H_pkt。 |
| 131 | Mzk1G1OmegaBasisActual（覆盖 #119） | G-B Ω 局部基 | **DONE** | 12:41:16（12:38:29/12:40:00 曾 FAIL） | fresh | clean | 三公理 (P：`n_y_pow_smul_omega0`、`n_x_pow_smul_omega0`；L：4 条) | **A-局部**：`ω₀=(y dx−x dy)/n`，(n y^(n−1))ω₀=dx（D(y)）、(n x^(n−1))ω₀=−dy（D(x)）全部真算（Derivation 关系 + n 为 ℚ-单位 + 单位单射消去）。仍是**环境 Ω_{B n} 上的恒等式**：未写 `Away x` 局部化版、无 scheme 层 Ω 层、无 ω∞ 与两图比较。 |
| 132 | Mzk1ULHpktActual（david 新文件） | U-L hpaper | **DONE** | 12:40:23 | fresh | clean | 三公理 (P：`ul_hpaper_assembled_paperConstants`；L：7 条) | **B**：`Hpkt w V := Σ w_a V_a`（def，形式正确）；`ul_hpaper_of_stepVIII` 是真分析归约（`lstar_logs ≤ (4/3)E_ar` + `2log l+56 ≤ (4/9)E_ar` ⇒ `(28/3)E_ar ≤ 10E_ar`，κ>0 传递）。**但 `w V B` 任意**，未接 `packetVActual`/`ulDivisorWeight`（同 §4.22），`hstepVIII` 是假设。 |
| 133 | Mzk1F7DiscTameBoundActual（覆盖 #129） | F7 tame 主界 | **DONE** | 12:43:18（12:36:11/12:38:29/12:41:17 三次 FAIL） | fresh | clean | 三公理 (P：`disc_factorization_le_finrank_of_tame`) | **A-局部/B+**：真装配 `v_p(|disc K|) ≤ finrank ℚ K`——donor `disc_factorization_eq_multiset_sum` + `Ideal.sum_ramification_inertia`，count=e_P−1 ⇒ `Σ(e−1)f ≤ Σ e f = d`；`TameCount` 是诚实假设，且**恰为 RadicalSupport `f7_normalizedLogDisc_le` 的 htame 前提**（`differentContribution = v_p(disc)·log p / [K:ℚ]`）。 |
| 134 | Mzk1G1FermatSmoothLocalizeActual（grace 新文件） | G-A 局部化识别 | **DONE**（12:41:14 与 12:50:16 曾 FAIL） | 12:51:31 | fresh | clean（`maxHeartbeats 800000`） | 三公理 (P：`localizeToModel`) | **A-局部/B（单向，grace 声明属实）**：`localizeToModel : (R n)[1/(n x^(n−1))] →+* fermatModelRing n` 真（`IsLocalization.Away.lift` + `chartToModel_chartR_isUnit`）；**反向所需输入** `modelEval_rel_zero/_one`（两条关系在局部化中为 0，用 `IsLocalization.Away.mul_invSelf` + `rw [hmul, sub_self]`）已在，但**反向映射 `Model → (R n)[1/r]` 与两条互逆恒等仍未写**。 |
| 135 | Mzk1G1FermatTwoChartGluingActual（覆盖 #111） | G-A 粘合 | **DONE**（12:43:15 DONE → 12:45:45 FAIL → 12:48:27 DONE） | 12:48:27 | fresh | clean | 三公理 (P：`fermatChart0ToCurve_isOpenImmersion`；L：2 条) | **A-局部，但用户级 cocycle 仍缺**：12:43:15 之后加的 `fermatOverlap_glue_condition` 在 12:45:45 **真 FAIL**（`60:6`：`𝟙 (V(i,j)) ≫ f` 因 `V(i,j)=V(j,i)` 只 definitional 相等而不成合成），**该定理已在 12:47:02 版删除**、改为 TECHNICAL NOTE（三条修法）。Probe 7 用 unknown constant 独立证实：**旧 olean 不含该常量**，即它从未编译成功。 |
| 136 | Mzk1HullFermatGluingActual（覆盖 #112） | G-A generic glue | **FAIL 当前**（12:37:01 曾 DONE，旧版） | 12:50:16 | **stale**（olean 12:37:01 < src 12:51:35） | clean | 旧版 `twoChartGlueData` def 级三公理（Probe 4，对 23:35 版）| **R（当前源码）/A-局部（旧版）**：旧版 generic `GlueData`（t=id）无新数学；当前源码新增 `twoChartGlueDataOfIso`（W0≅W1 两 overlap 版 = cocycle 修法 b），但 FAIL：`75:7` Type mismatch、`150:12` rewrite 未找到模式、`144:20/145:22` Type mismatch。 |
| 137 | Mzk1G1DisjointFamilyActual（覆盖 #106） | G-K | **DONE** | 12:43:18（12:38:30 曾 FAIL） | fresh | clean | L：5 条（未单独 probe） | **B+**：真递归 `exists_goodChain`（Fin 归纳 + `Fin.snoc`，避点 ⇒ 边界两两不交）与 `hasGluedBelyiFamily_of_b1`（构造 `HasGluedBelyiFamily n d V`，r=d·|V|+1）；**唯一缺口是 `B1StepProducer n`（文件自标 INTERFACE, NO INHABITANT）**。 |
| 138 | Mzk1G1FermatRadicalSupportFinal3Actual（覆盖 #117） | H-T tame 桥 | **FAIL 当前**（12:41:47 曾 DONE，旧版） | 12:49:10 | **stale**（olean 12:41:46 < src 12:51:31） | clean | 12:41:47 版三公理 (L；Probe 6 已验 `…le_one_of_tame`) | **R（当前）/B+（旧版）**：旧版 `tame_count_differentIdeal_eq`（donor 实例化）+ `…le_one_of_tame` 真；当前新增 `separable_fractionRing/_residue`、`…_glued` 落红——`164:6` `Module.Finite.of_surjective` 的参数没 pin 到同一个 `Submodule.mkQ`（机械错，非数学，§4.47）。 |
| 139 | Mzk1UCHpktActual（覆盖 #45/#90） | U-C C3/C4 | **DONE** | 12:43:44 | fresh | clean | 三公理 (P：`uc_c3_of_primeCounting`；L：1 条) | **B+/A-局部**：`ucActualV/ucActualB`（真 per-packet 值 + 真 exceptional）与 `ucActualV_le_ucActualB`（donor `ulPacketVOfWitness_le_paperBound`）落地；`ucWeightedHpkt_eq_ulHpkt = rfl` 把两套加权 hull 接上（§4.22 部分作废）；`uc_c3_of_primeCounting` 把 prime-count 与常数两项都消掉，**唯一残差 hstepVIII**。 |
| 140 | Mzk1G1ProjectiveLinePiOverlapActual（覆盖 #124） | G-C/G-A π overlap | **DONE** | 12:44:51（00:47–12:36 长期 FAIL） | fresh | clean | 三公理 (P：`fermatPiOverlap_condition`) | **A-局部（本批最实推进）**：`overlapToChart0 ≫ chartMorphism0(x0^n) = overlapToChartInf ≫ chartMorphismInf(r1^n)` 真证——环层 `overlapToChart0_spec`/`overlapToChartInf_spec` + 真单位 `overlapUnit (u0^n, iu0^n)` + `chartMorphism_transition`。这是 `(fermatTwoChartGlueData n).openCover.glueMorphisms` 的**唯一输入**。 |
| 141 | Mzk1G1OmegaFreeActual（新文件） | G-B Ω≅O 局部平凡 | **FAIL 当前**（12:47:03 曾 DONE） | 12:51:30 | **stale**（olean 12:47:03 < src 12:51:02） | clean | 12:47:03 版 L：5 条（`omegaForm_is_basis` 等） | **R（当前）/A-局部（12:47 版）**：真 `D0`（`MvPolynomial.mkDerivation` + 杀理想 + `Derivation.liftOfSurjective`）、`Psi(ω₀)=n`、`Phi` 单/满 ⇒ `omegaEquivO : Ω n ≃ₗ[B n] B n`、`omegaForm_is_basis`（路线 §3.1 (A4) 局部平凡）。当前版红，**首错未取**（log 已被下一次 START 清空）。 |
| 142 | Mzk1URThetaPacketInstanceActual（kurt 新文件） | U-L V_a 值公式 | **DONE**（12:46:12、12:49:07 曾 FAIL） | 12:54:48 | fresh（src 12:53:05） | clean（`maxHeartbeats 4000000`，§4.48） | 三公理 (L：4 条，当前 attempt) | **B+/A-局部**：`ulThetaPacketV_eq_log_norm`（= `ulNormalizedLogMass_smul` 在真 θ 上的实例）、`_eq_neg_order`、`_eq_neg_shift`（`V_a = −(g/(2l))·ord_p(q_b)·log p`，路线 §5.2.2 的 C1 负项）全真；`ulThetaPacketV_le_paperC1` 条件式（hdiff/hexc 为非负和）。**12:53:05 版 import 了 `Mzk1URRootExtInstancesActual`，把 `37:12` 的 `FiniteDimensional ℚ_p` synth 失败修掉**；`maxHeartbeats 4e6` 仍在（§4.48）。 |
| 143 | Mzk1URRootExtInstancesActual（kurt 新文件） | U-R 全局实例 | **DONE** | 12:50:42（12:47:31 曾 FAIL） | fresh | clean | —（无 `#print`） | **未语义审计**（92 行）：补 `Algebra ℚ_p`/`FiniteDimensional ℚ_p` 全局实例（钉在同一 Module 上避免 diamond）+ 两条 per-b mass 恒等式；只确认编译与单文件 log 无 error。 |
| 144 | Mzk1URThetaHullActual（覆盖 #121） | U-R theta hull | **FAIL** | 12:42:26 | none | clean | 4 条 target 全是 donor re-export（`p6_neg_M_le_HTheta2`/`actualPerB_inequality`/`actualTargetMagnitude_actual`/`urRootTheta_log_norm_eq_neg_shift`） | **R（级联，待重编；且本身只是 wrapper）**：START 12:41:30 早于 `URRootExtension.olean`（12:41:43），之后**未再重试**（源码 mtime 12:39:57 早于 FAIL）。即使转绿也无新数学。 |
| 145 | Mzk1G1ProjectiveLineBoundaryActual（覆盖 #123） | G-C boundary | **DONE** | 12:50:12（12:36:07/12:47:02 曾 FAIL 且 `p1Zero_nonempty` sorryAx） | fresh | clean | —（文件有 5 条 `#print`，未单独 probe） | **A-局部（点集层）**：`chartPoint r`、`isPrime_span_X_sub_C`、三条非空、`boundarySetGlued`、`boundaryPreimageGlued` 真；**但 0/∞ 命名与注释反了**（`p1Zero` 取 t-图 t=0 = λ 图的无穷远点 [1:0]，`p1Infinity` 取 λ=0 = [0:1]，见 §4.51）。 |
| 146 | Mzk1G1OmegaPresentationActual（覆盖 #125） | G-B 展示 | **FAIL** | 12:44:54 | none | clean | — | **R**：`188:43` synthInstanceFailed `AddCommMonoid (Pres n)`；`190:5/190:30` Unknown `presToOmega_injective/_surjective`；183–185 “this tactic is never executed”（源码在编到一半就断）。 |
| 147 | Mzk1G1FermatOverlapRingActual（覆盖 #120） | G-A overlap ring（重复实现） | **FAIL** | 12:44:56 | none | clean | `beta_alpha`/`overlapEquiv`/`overlapSchemeIso` = sorryAx | **R**：同一个实例透明性/defeq 问题；**accepted 的 `Mzk1G1FermatOverlapActual` 已有 A-局部版**（§4.29）。两个同名 `overlapSchemeIso` 并存 → **建议删本文件**，避免引用混淆。 |
| 148 | Mzk1G1FermatCurveClosedActual（覆盖 #126） | G-A closed（冗余） | **FAIL** | 12:44:50 | none | clean | 两定理 sorryAx | **R − 冗余**（§4.25 不变）：`28:2` synthInstanceFailed、`31:3` Unknown `…iff_isProper_and_mono.mp`。删。 |
| 149 | Mzk1HullFermatClosedSubschemeActual（覆盖 #127） | G-A closed（冗余） | **FAIL** | 12:44:50 | none | clean | 两定理 sorryAx | **R − 冗余**（同上，`24:2`/`27:9`）。删。 |

**状态翻转一览（batch 7，对比 §2e）**：
- FAIL→DONE：`URRootExtensionActual`(12:41:43)、`OmegaBasisActual`(12:41:16)、`F7DiscTameBoundActual`(12:43:18)、`ProjectiveLinePiOverlapActual`(12:44:51)、`ProjectiveLineBoundaryActual`(12:50:12)、`OmegaFreeActual`(12:47:03)、`URRootExtInstancesActual`(12:50:42，新)。
- 新 DONE（本批首次）：`ULHpktActual`(12:40:23)、`FermatSmoothLocalizeActual`(12:43:16，后 12:51:31 重编)、`OmegaFreeActual`、`URRootExtInstancesActual`。
- **DONE→FAIL（同文件被改后覆盖，旧 DONE 标 STALE）**：`HullFermatGluingActual`(12:37:01→12:50:16)、`RadicalSupportFinal3Actual`(12:41:47→12:49:10)、`OmegaFreeActual`(12:47:03→12:51:30)、`TwoChartGluingActual`(12:43:15→12:45:45→12:48:27 恢复)、`SmoothLocalizeActual`(12:43:16→12:47:06/12:50:16→12:51:31 恢复)。
- 仍红（无翻转）：`OmegaPresentationActual`、`FermatOverlapRingActual`、两个 closed 冗余文件、`URThetaHullActual`。
**12:53–12:55 追加变化（快照时仍在动；行号仍按上表）**：
- #136 `Mzk1HullFermatGluingActual` **12:52:54 DONE**（src 12:51:35，olean fresh）：`twoChartGlueDataOfIso`（W0≅W1 两 overlap 版）编译通过，但**仍无用户级 cocycle 定理**（文件只有两组 GlueData 数据 + 原 TECHNICAL NOTE）→ §4.45 结论不变；#136 当前判定改为 **A-局部（generic 两变体），用户级等式仍缺**（不再记 R）。
- #138 `Mzk1G1FermatRadicalSupportFinal3Actual` **12:53:12 DONE**（src 12:51:31）：`separable_residue` 已被删除，`tame_localDifferentPaperOrder_le_one_glued` 改为**以 hsep 为显式假设**（分母可分离性由 `separable_fractionRing` 真证）→ 诚实的部分装配（B+）；随后 12:54:21 又改（新增 `quotient_span_natCast_ne_zero_iff`、`ramificationIdx_invertible_of_dvd`，为 `he` 补算术输入），当前**未编译**。
- #134 `Mzk1G1FermatSmoothLocalizeActual` 12:54:19 再次 FAIL（src 12:53:11）→ 本批第 6 次翻转；最新**可引用**版本仍是 olean 12:51:31（单向 + 反向输入）。
- #142 `Mzk1URThetaPacketInstanceActual` **12:54:48 DONE**（src 12:53:05，olean fresh）：import `Mzk1URRootExtInstancesActual` 后 `37:12` 的实例失败解除，4 条全三公理（L，当前 attempt）→ 判定升为 **B+/A-局部**，V_a 值公式（§5.2.2 C1 负项）落地。


## 3. 独立 `#print axioms` probe

### Probe 1（上一批）：`tmp/sheaf/xif/paper/_ProbeRoute20261116Actual.lean`
- watchdog：**DONE 2026-11-15T23:15:41.653Z**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeRoute20261116Actual.lean.log`。
- 10 个定理全部只依赖 **[propext, Classical.choice, Quot.sound]**，无 sorryAx、无自定义 axiom：
  - `Mzk1G1FermatTwoChartGluingActual.fermatTwoChartData_U0`
  - `Mzk1G1FermatTwoCharts2Actual.fermatChart0_module_finite`
  - `Mzk1G1FermatProjClosedSubscheme4Actual.fermatCurveImmersion_isProper`
  - `Mzk1G1NoncriticalPsiActual.noncriticalPsiActual`
  - `Mzk1G1B1B3ComponentActual.noncriticalB1B3Component`
  - `Mzk1ULPacketVActual.packetV_le_packetB`（23:08 版本）
  - `Mzk1ULActualRootActual.uL_actual_root_pow`
  - `Mzk1URJ2Actual.detCovolume_basis_change`
  - `Mzk1UCC1UpperActual.uc_c3_of_uc1`
  - `Mzk1UCHpktActual.ucHpkt_weighted_bound`

### Probe 2（上一批）：`tmp/sheaf/xif/paper/_ProbeRoute20261116bActual.lean`
- watchdog：**DONE 2026-11-15T23:22:24.857Z**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeRoute20261116bActual.lean.log`。
- 7 个定理全部只依赖 **[propext, Classical.choice, Quot.sound]**：
  - `G1D1ProducerActual.d1ProducerSingleton`（toy，但 kernel 干净）
  - `G1DisjointFamilyActual.singletonBelyiFamily`（toy，但 kernel 干净）
  - `Mzk1ULPhiRealizationActual.ulPhiRealization_cover`（定义自反，kernel 干净）
  - `Mzk1ULPhiRealizationActual.ulSourceArrowRealization_mem_p6Phi`（同上）
  - `Mzk1ULPacketFamilyActual.ulPossibleImages_subset_packetHull`
  - `Mzk1G1StepXIChartMap4Actual.chartPolynomial_eval`
  - `Mzk1G1TwoSectionDataActual.protectedToZeroTwoSection`

### Probe 3（本批 batch 3）：`tmp/sheaf/xif/paper/_ProbeBatch3Actual.lean`
- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch3Actual.lean` → `{"added":1,"total":50}`。
- watchdog：**START 23:30:33.290Z → DONE 2026-11-15T23:31:22.547Z (49s)**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch3Actual.lean.log`（25 行，无 error、无 sorryAx）。
- 11 个定理的独立复算结果（原样抄录）：

| 定理 | axioms |
|---|---|
| `Mzk1G1TwoSectionDataActual.eval_protectedToZero_eq_zero_iff` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1TwoSectionDataActual.rootMultiplicity_protectedToZero_of_mem` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1TwoSectionDataActual.protectedToZeroTwoSection` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1TwoSectionDataActual.not_both_mem_of_span_top` | [propext, Quot.sound]（未用 choice） |
| `Mzk1G1TwoSectionPsiLocalActual.psi_no_common_zero` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1TwoSectionPsiLocalActual.overlapCoord_mul_cocycle` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1TwoSectionPsiLocalActual.twoSectionPsiData` | [propext, Classical.choice, Quot.sound] |
| `G1QHeightActual.lambdaHeight_nonneg` | [propext, Classical.choice, Quot.sound] |
| `G1QHeightActual.legendreJ_zero` | [propext, Quot.sound] |
| `G1QHeightActual.legendreJ_of_rat` | [propext, Classical.choice, Quot.sound] |
| `G1FiniteDisjointBelyiActual.boundarySet_isClosed` | [propext, Classical.choice, Quot.sound] |

> 注（batch 4）：上表 `G1QHeightActual.legendreJ_zero`、`legendreJ_of_rat` 已在 23:37:22 的重写中删除（假命题清理，见 §2c#54 / §4.24）；此行保留 batch 3 原始记录。

### Batch 3 结论（原文保留，已由 batch 4 更新）
kernel 层面 batch 3 的 DONE 文件**没有伪证**（FAIL 文件日志里的 sorryAx 都是 Lean 对失败 tactic 的 error-recovery 回退；这些源码 grep 均无 `sorry`）。风险全部在**语义层**：空 card、值层 surrogate、定义自反、条件空洞、只有陈述没有 inhabitant。这些用 `#print axioms` 查不出来。

### Probe 4（本批 batch 4）：`tmp/sheaf/xif/paper/_ProbeGeom4Actual.lean`
- 两次排队（同一文件，第二次加 Support）：
  - stage 1：`node tools/wd_add.mjs …` → added 1 / total 56；START 23:40:26 → **DONE 23:41:15**；30 条 `#print axioms`。
  - stage 2（加 `Mzk1G1FermatSupportActual` 6 条）：added 0 / total 58（已在 extra-targets，靠源码 mtime 触发重编）→ **DONE 23:47:15**；36 条。
- 日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeGeom4Actual.lean.log`：**无 sorryAx**（0 次命中），每条 depends on axioms 均为 [propext, Classical.choice, Quot.sound]。
- 与任务清单的对应：`fermatA0Ring_finrank`（#53）、`fermat_X1_pow_mem_span`（#52）、`fermatCurve_proper`（#50/#52）已复算；**`fermatA0EquivCurve` 未复算**（SmoothChart 当前 FAIL，无法 import，见 #57）。

| 定理（namespace 见文件） | axioms |
|---|---|
| `Mzk1G1FermatFiniteDegree2Actual.fermatA0Poly_monic` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1FermatFiniteDegree2Actual.fermatA0Ring_finite_over_U0` | 同上 |
| `Mzk1G1FermatFiniteDegree2Actual.fermatA0Ring_finrank` | 同上 |
| `Mzk1G1FermatFiniteDegree2Actual.fermatA0Ring_finite` | 同上 |
| `Mzk1G1FermatFiniteDegree2Actual.fermatA0_root_pow` | 同上 |
| `Mzk1G1FermatFiniteDegree2Actual.fermatAInfRing_finrank` | 同上 |
| `Mzk1G1FermatFiniteDegree2Actual.fermatAInf_root_pow` | 同上 |
| `Mzk1G1FermatCurveClosed2Actual.fermatCurve_closedImmersion` | 同上 |
| `Mzk1G1FermatCurveClosed2Actual.fermatCurve_proper` | 同上 |
| `Mzk1G1FermatCurveClosed2Actual.fermatPolynomial_relation` | 同上 |
| `Mzk1G1FermatCurveClosed2Actual.fermat_X1_pow_mem_span` | 同上 |
| `Mzk1G1FermatCurveClosed2Actual.fermat_X1_mem_of_prime` | 同上 |
| `Mzk1G1FermatProperFinal2Actual.fermatCurve_proper` / `…_closedImmersion` | 同上 |
| `Mzk1G1FermatSupportActual.fermatChart0Map_isFinite` / `_isProper` | 同上 |
| `Mzk1G1FermatSupportActual.fermatChartInfMap_isFinite` / `_isProper` | 同上 |
| `Mzk1G1FermatSupportActual.fermatCurve_proper_support` / `_closed_support` | 同上 |
| `Mzk1G1FermatOmegaTransitionActual.fermatOmegaTransition` | 同上 |
| `Mzk1HullFermatGluingActual.twoChartGlueData`（def 级） | 同上 |
| `Mzk1UCHpktActual.uc_sandwich` / `uc_c3` / `uc_c4_from_weighted` | 同上 |
| `Mzk1ULWeightedHullActual.ulDivisorWeight_nonneg` / `ulNormalizedWeight_sum` / `ulWeightedPacketHull_eq_average` / `ulWeightedPacketHull_le` / `ulWeightedSum_le` | 同上 |
| `Mzk1ULPacketVActual.packetV_le_packetB` / `packetExceptional_small_outside` | 同上 |
| `Mzk1G1PsiTwoChartCocycleActual.chartProdInv_eq_pow_mul_chartProd` / `psi_chart_coords_mul_eq_one` / `chartProd_eq_mul_erase` | 同上 |

> 结论（本批）：**kernel 层仍然没有伪证**；本批所有 FAIL 的 sorryAx 都来自失败 tactic 的 error-recovery，且这些文件源码 grep 均无 `sorry`。真正的风险仍是语义层（§4.21–§4.28）。

### Probe 5（本批 batch 5）：`tmp/sheaf/xif/paper/_ProbeBatch5Actual.lean`
- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch5Actual.lean` → `{"added":1,"total":72}`。
- watchdog：**START 00:19:37.817Z → DONE 2026-11-16T00:20:18.358Z (41s)**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch5Actual.lean.log`（1110 B / 24 行，**无 error、0 次 sorryAx**）。
- 8 条定理的独立复算（原样抄录，全部 **[propext, Classical.choice, Quot.sound]**）：

| 定理 | axioms |
|---|---|
| `Mzk1G1FermatTwoChartGluingActual.fermatChart0ToCurve_isOpenImmersion` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1FermatOverlapActual.overlapSchemeIso` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1FermatCurveActual.fermatCurveScheme_eq_glued` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1PsiChartToP1Actual.psiChart0ToP1` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1PsiChartToP1Actual.psiChart0ToP1_preimage_basicOpen` | [propext, Classical.choice, Quot.sound] |
| `Mzk1F7TameOrderActual.tame_localDifferent_contribution_le_log` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1PsiChartInfCoverActual.span_denom_chartR_eq_top` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1OmegaActual.derivation_relation` | [propext, Classical.choice, Quot.sound] |

- 覆盖的 gate 行：#70（Ω 关系式）、#71（overlap 同构）、#76（q,r 生成单位理想）、#80（chart open immersion）、#81（F7 tame 界）、#82（`Y_n = glued`）、#87（ψ 第一图 → P¹ 及其原像）。
- **未覆盖**（本批未 probe，只用了文件自带 `#print` 或完全未复算）：`ProjectiveLineChartsActual`、`ProjectiveLineChartMapsActual`、`KvCompactActual`、`SmoothChartActual`、`Mzk1P8FreyAssemblyActual`、`Mzk1P8EpsilonSelectionActual`、`Mzk1G1D1ProducerActual`、`Mzk1G1LocalHeightCriterionActual`、`Mzk1G1QHeightActual`、`Mzk1ULPhiRealizationActual`、`Mzk1URPacketActual`、`Mzk1G1DisjointFamilyActual`、`Mzk1G1FiniteDisjointBelyiActual`（均为#2d 表内 (L) 或 "—"）。

> 注：`_ProbeBatch5Actual` 编译时 `Mzk1G1FermatTwoChartGluingActual` 的源码（00:19:3x 起又被改）正处 FAIL，但 probe 用的是 **00:04:35 的 olean**；因此上表 `fermatChart0ToCurve_isOpenImmersion` / `fermatCurveScheme_eq_glued` 对应的是 **00:04:36 那一版**，不是正在改的新版。

### Probe 6（本批 batch 6）：`tmp/sheaf/xif/paper/_ProbeBatch6Actual.lean`
- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch6Actual.lean` → `{"added":1,"total":84}`。
- watchdog：**START 2026-11-16T00:50:17.045Z → DONE 2026-11-16T00:51:17.108Z (60s)**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch6Actual.lean.log`（8 条 `#print axioms`；本 attempt 无 `error`、0 次 `sorryAx`）。
- 8 条定理的独立复算结果（原样抄录，全部 **[propext, Classical.choice, Quot.sound]**）：

| 定理 | axioms |
|---|---|
| `Mzk1G1FermatSmoothIntegralActual.fermatCurveRing_isDomain` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1FermatSmoothAttemptActual.fermatModel_isStandardSmooth` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1FermatTwoChartGluingActual.fermatChart0ToCurve_isOpenImmersion` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1FermatPiActual.piChart0`（def 级） | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1ProjectiveLineTransitionActual.chartMorphism_transition` | [propext, Classical.choice, Quot.sound] |
| `Mzk1F7DiscSumActual.disc_factorization_eq_multiset_sum` | [propext, Classical.choice, Quot.sound] |
| `Mzk1G1FermatRadicalSupportFinal3Actual.tame_localDifferentPaperOrder_le_one_of_tame` | [propext, Classical.choice, Quot.sound] |
| `Mzk1ULThetaPacketActual.ulNormalizedLogMass_smul` | [propext, Classical.choice, Quot.sound] |

- 覆盖的 gate 行：#109（整性）、#110（smooth）、#111（当前 00:39 版 chart open immersion，**不是 Probe 5 的 00:04 版**）、#113（π 的 chart map def）、#114（P¹ 过渡）、#116（F7 主公式）、#117（H-T tame 桥）、#118（U-L per-b mass）。
- **未覆盖（明确未运行）**：#112 当前 `twoChartGlueData` 的 def 级 axioms（文件无 `#print`，Probe 6 只经 import 使用其 chart immersion）；#105/#106/#107/#108 仅有文件自带 `#print` (L)；Lead 8 文件中的另外 7 条见 §4.39（Lead probe L*，非 audit 独立）。
- 结论：kernel 层本批新 DONE **没有伪证**；残差全在语义层（#112/#113 的 π 与 cocycle、#110 的局部化识别、#118 的 V_a 值公式）。

### Probe 7（本批 batch 7）：`tmp/sheaf/xif/paper/_ProbeBatch7Actual.lean`
- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch7Actual.lean` → `{"added":1,"total":92}`（两次改写只改 mtime，`added 0`）。
- **三次 attempt**（都是本 audit 自己的 probe 文件的真实失败，如实记录）：
  1. START 12:46:30 → **FAIL 12:47:29**：`21:14 Unknown constant …Mzk1G1FermatTwoChartGluingActual.fermatOverlap_glue_condition`；
  2. START 12:49:34 → **FAIL 12:50:40**：`22:14 Unknown constant …Mzk1G1FermatSmoothLocalizeActual.modelEval_rel_zero`；
  3. START 12:50:56 → **DONE 12:51:54（58s）**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch7Actual.lean.log`（3553 B，本 attempt 无 `error`、**0 次 sorryAx**）。
- 两次 unknown-constant 失败本身是**证据**：`fermatOverlap_glue_condition`（12:43:15 olean）与 `modelEval_rel_zero`（12:43:16 olean）**都不在对应 olean 里**，即这两个定理在被 probe 的时刻从未编译成功（前者 12:45:45 真 FAIL，后者 12:47:06/12:50:16 FAIL）。
- 8 条独立复算（原样抄录，**全部 [propext, Classical.choice, Quot.sound]**）：

| 定理（namespace 见文件） | axioms | 覆盖行 |
|---|---|---|
| `Mzk1URRootExtensionActual.urRootTheta_order_base` | [propext, Classical.choice, Quot.sound] | #130 |
| `Mzk1G1OmegaBasisActual.n_y_pow_smul_omega0` | [propext, Classical.choice, Quot.sound] | #131 |
| `Mzk1G1OmegaBasisActual.n_x_pow_smul_omega0` | [propext, Classical.choice, Quot.sound] | #131 |
| `Mzk1ULHpktActual.ul_hpaper_assembled_paperConstants` | [propext, Classical.choice, Quot.sound] | #132 |
| `Mzk1F7DiscTameBoundActual.disc_factorization_le_finrank_of_tame` | [propext, Classical.choice, Quot.sound] | #133 |
| `Mzk1G1FermatSmoothLocalizeActual.localizeToModel`（def 级） | [propext, Classical.choice, Quot.sound] | #134 |
| `Mzk1G1ProjectiveLinePiOverlapActual.fermatPiOverlap_condition` | [propext, Classical.choice, Quot.sound] | #140 |
| `Mzk1UCHpktActual.uc_c3_of_primeCounting` | [propext, Classical.choice, Quot.sound] | #139 |

- **未覆盖（明确未运行）**：`localizeToModel` 的复算对应 **olean 12:43:15**，而当前 `SmoothLocalize` 源码（12:50:54）12:51:31 才 DONE，`modelEval_rel_zero/_one` 仍未 probe；`URRootExtInstancesActual`（#143）、`DisjointFamilyActual`（#137）、`ProjectiveLineBoundaryActual`（#145）只有文件自带 `#print` 或完全未 probe；`HullFermatGluingActual` 当前版（#136）与 `RadicalSupportFinal3Actual` 当前版（#138）**无法 probe（源码红、olean stale）**。
- 结论：**kernel 层本批 8 条关键 DONE 没有伪证**；风险全在语义层与“DONE 只覆盖旧 olean”（§4.46）。

### 结论（batch 3 + batch 4 合并）
batch 4 的 36 条 `#print axioms` 全部是三公理、probe 日志 0 次 sorryAx；本批 DONE 文件的语义判定见 §2c（A-局部：#49/#52/#53/#56；B：#44–#48/#50/#51/#55；TOY/换题：#54；R：#57–#69）。新增的语义风险类型是「文档声明用了 actual 对象，但定理对任意量词」（§4.22）与「accepted donor 的坏副本」（§4.25）。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险

### 4.1 【高】G-A 的"两图粘合"是空壳 —— `Mzk1G1FermatTwoChartGluingActual`（23:10 DONE 时判 C；**23:31:02 已 FAIL**）
文件 25 行，全部内容是：
```lean
structure FermatTwoChartData where n; hn; U0; U1; U0_eq : U0 = fermatChart0 n; U1_eq : U1 = fermatChartInf n
def fermatTwoChartData ... := { U0 := fermatChart0 n, ..., U0_eq := rfl, U1_eq := rfl }
theorem fermatTwoChartData_U0 : (fermatTwoChartData n hn).U0 = fermatChart0 n := rfl
```
没有 `Scheme.GlueData`、没有 `glued`、没有 overlap ring iso（`x⁻¹, s=y/x` 的互逆）、没有 `π : Y_n ⟶ P¹`、没有 `π⁻¹(A¹_λ)=U₀`。路线 §2.1/§2.2 的四项出口全部缺失。
**batch 3 更新**：该文件 23:31:02 变 FAIL（首错 `17:8 Type mismatch`），说明 hull lane 正在把它重写成真粘合；在重新 DONE 并语义复核前 **G-A 不得引用它**，23:10 的旧 DONE 作废。

**batch 5 更新**：§4.1 的「空壳」结论已作废。00:04:36 该文件 DONE，`fermatTwoChartGlueData` 是**真实例化**（`Spec A0`、`Spec A1`、`Spec Overlap0` + 两条 open immersion），见 §2d#80 / §4.29。注意它 00:19:37 又被改并 FAIL（源码改动中），引用时须重新核对 olean 版本。

### 4.2 【高】`Mzk1HullFermatGluingActual` 是"空 card"，23:24:35 / 23:31:14 仍 FAIL（red）
```lean
structure FermatGluingResidual (n) where
  Y : Scheme
  pi : Y ⟶ Scheme           -- 目标不是 P¹ 而是裸 Scheme（且触发 Quiver stuck 错误）
  isFinite : Prop           -- 字段是自由 Prop
  isProper : Prop
  smooth : Prop
  degree : Nat
  degree_eq : degree = n ^ 2 -- rfl 字段
def fermatGluingResidualMissing (n) : Prop := Nonempty (FermatGluingResidual n)
```
这正是简报禁止的"空 card"：`Nonempty` 一个字段全是自由 Prop 的结构，等于把路线出口列成愿望清单；`#print axioms fermatGluingResidualMissing` 输出 **[sorryAx]**。必须整文件作废重写，不能作为 G-A 的残余接口。本批两次重试仍 FAIL（首错 `24:7 typeclass instance problem is stuck`，且 `FermatGluingResidual` 已变 unknown identifier —— 文件正在被重写）。

### 4.3 【高】G-A 的 `π` 与 degree 语义错位
- `Mzk1G1StepXIChartMap4Actual`（DONE，判 C）：`def fermatChartMap (n) (x _) := x ^ n` —— 在 `ℚ × ℚ` 上丢弃第二坐标；`chartPolynomial` 是无关的 `∏ (X - t i)`；`chartPolynomial_eval` 平凡。路线要的是 scheme morphism `π : Y_n → P¹`，`[X:Y:Z] ↦ [X^n:Z^n]`，以及两图上的原像等式。这里是**值层 surrogate**。
- `Mzk1G1FermatFiniteDegree2Actual`（FAIL 23:17:42，23:31:18 仍 FAIL）：`fermatChartRank n := n`，证明 `finrank (ℚ[X]) (fermatU0Ring n) = n`。这是 `A₀` 作为 `ℚ[x]`-模的秩；路线 §2.3 要的是作为 `k[λ]`（`λ = x^n`）-模的秩 **n²**。命名会被误读成"degree 已经 n²"。当前 FAIL 首因是 `import` 写在 `open` 之后（`line 5: invalid 'import' command`）。
- `Mzk1G1FermatCurveClosed2Actual`（FAIL，23:31:17 仍 FAIL）：`fermatCurve_proper` 的实例证明依赖 `IsFinite (fermatCurveι n)`（不存在），日志直接给出 **sorryAx**；red，禁止引用。

### 4.4 【中】`Mzk1G1FermatProjClosedSubscheme4Actual` 是局部真结果，但不是路线出口
closed immersion + proper 是真实定理（probe 三公理），对象是 `vanishingIdeal` 于 `zeroLocus {X₀^n+X₁^n−X₂^n}` 的 closed set 上。但：没有证明得到的 ideal sheaf 由 `F` 生成；没有与 `Proj(k[X,Y,Z]/(F))` 或两图 glue 的同一性；没有 smooth / 几何整性 / degree。判 **A-局部**：可作为 proper 的候选组件，不能当 G-A 出口。

### 4.5 【高】U-R 用了明令禁止的 surrogate，且未触及 q=−M —— `Mzk1URPacketActual`（FAIL，red）
- `def urVarpi : CommonPrimeCompletion ... := 1` —— 简报 lane 表明确"禁用 varpi=1"；
- `ur_c1_feed` 用 `exceptional := Finset.univ`，`small_outside := fun i hi => absurd (Finset.mem_univ i) hi`（空真）——禁用项"exceptional=univ"；
- `set_option maxHeartbeats 16000000`（1600 万）—— 简报禁止"为绕过错误加 maxHeartbeats"；
- 日志：`ur_c1_feed` 依赖 **sorryAx**；`ur_qReading_formula` 只是 donor `rootParameterWeight_eq_ord_varpi` 的转述，**没有 q_P5 = −M**，也没有 `θ_P5 ≤ H_pkt` 的 actual region 证明；`urQRootLattice` 与真实 q-root 主格无绑定。

### 4.6 【高】U-L 的 Φ "coverage" 是定义自反 —— `Mzk1ULPhiRealizationActual`（DONE 23:20，判 C）
`p6Phi places tuple := { phi | ∀ u ∈ unitLogLattice, phi u ∈ unitLogLattice }`（= 保格集合）。于是 `ULSourceArrowRealization.unit_layer_exchange` 的字段类型与 `p6Phi` 的成员条件**逐字相同**；`ulSourceArrowRealization_mem_p6Phi` = `R.unit_layer_exchange`（rfl）；`ulPhiRealization_cover` 的证明是 `⟨{ phi := phi, unit_layer_exchange := hphi }, rfl⟩` —— "每个 Φ 元素都由 source arrow realization 实现（取它自己的保格证明）"。这**不是**路线 §9.3 第 3 条要求的"任意合法 source arrow 的坐标作用进入 Φ 并保格"。

### 4.7 【高】U-L 的 Hpkt / U-C 的 Hpkt 是纯代数，C1 只是条件等价
- `Mzk1ULHpktActual`：`Hpkt w V := ∑ a, w a * V a`；`Hpkt_le_weighted_bound` 是 `Finset.sum_le_sum`；`Hpkt_stepV_upper` 转述 donor。三公理，但 `V` 是任意 `A → Real`，**没有**与 actual packet 读数连接。
- `Mzk1UCHpktActual`（**23:30:21 已 FAIL**）：`ucHpkt_weighted_bound` 的前提 `h : ∀ i, ucHull ... ≤ paper i` 把每个 packet 的界当假设；结论只是加权求和。当前版本 `uc_c3` 变成 unknown identifier（`51:5`），文件已不可用。
- `Mzk1UCC1UpperActual`：旧版 `uc_c3_iff_uc1 (Hpkt := 0)` 需假设 `Hpkt = 0`；**新版（23:30:28 DONE）改为 `Hpkt ≤ B` 假设 + 定义式 `UC1UpperActual`（见 §4.18）**。C1/C3 仍未闭合。

### 4.8 【中】U-L packet family 的 slot/varpi 需澄清 —— `Mzk1ULPacketFamilyActual`（DONE 23:18）
`ulActualPacketHull` 里 `arithmeticTupleStepVPossibleImages ... PUnit.unit (qVFamily T b).q ...`：distinguished slot 固定为 `PUnit.unit`（one-slot 索引，尚可），但把 **q 作为 varpi 实参**传入。需要 U-L owner 说明 `(qVFamily T b).q` 就是该 slot 的合法非零 completion 元素（否则是另一种 surrogate）。其 `ulPossibleImages_subset_packetHull` 是真实的 holomorphic hull 包含性。

### 4.9 【中】G-C 只是 affine 多项式层，不是 scheme morphism（batch 3 有推进，见 §4.13/§4.15）
`Mzk1G1NoncriticalPsiActual` / `Mzk1G1B1B3ComponentActual` 的 B1/B2 是 `protectedToZeroPolynomial T` 在点上的取值/导数非零；B3 只是 `FiniteBetaCorrectedBase` 与 `TwoSectionData` 的组包。`TwoSectionData` 里 `s1 := 1` 使 `span_top` 平凡。这些是 G-C 的代数组件（可复用），但**没有** `φ : Y → P¹` 的 scheme morphism、非临界性、0/1/∞ 三分歧值。判 B，不能记为 G-C。

### 4.10 【中】L-H / G-K 的 toy 已被 batch 3 新版本覆盖（现状见 §2b#31–34）
- `Mzk1G1D1ProducerActual` 旧版：`d1ProducerSingleton` 取 `discriminant := fun _ => 0`、`conductor := fun _ => 0`、`KV := Kv`（`Kv = {1/2}`），`LocalHeightCriterion` 在单点上用 `norm_num` 关闭；不是路线 §6 的 `∀d∀K_V∀η∃C∀λ` 量词。**batch 3：singleton 版已被删掉重写，当前 FAIL（首错 unknown namespace G1KvCompactActual）**。
- `Mzk1G1DisjointFamilyActual` 旧版：`singletonBelyiFamily` 是 `map := fun _ _ => some 0`（常映射）、`boundary := ∅`；常映射不是 Belyi 覆盖，空边界使不相交性平凡。**batch 3：已改为 import `G1FiniteDisjointBelyiActual` 的真实族接口，当前 FAIL**。

### 4.11 【低】`Mzk1G1FermatOverlapActual` 无内容（DONE 22:30）
只有两个 `Localization.Away` 定义和 `algebraMap`，两行 `#check`；没有互逆同构、没有 cocycle、没有 `IsLocalization` 识别。DONE 仅表示"能编译"。判 C placeholder。

### 4.12 【低】其它 FAIL 文件的当下状态（不计入 gate，仅记录）
- `Mzk1URThetaHullActual`(23:33:12)、`Mzk1URRootExtensionActual`(23:30:56)、`Mzk1URRootMassActual`(23:30:30)、`Mzk1URPacketActual`(23:30:53)：U-R 仍在修。
- `Mzk1G1FermatSmoothAttemptActual`(23:21:03)、`Mzk1G1FermatSupportActual`(23:30:33)、`Mzk1G1FermatRadicalSupportActual`(23:30:29)：G-A 后段 / H-T 相关，FAIL。
- `Mzk1G1FermatTransitionActual`(23:31:18) FAIL：G-B 过渡仍未落地。

### 4.13 【本批·中】`Mzk1G1TwoSectionDataActual`：s0 侧变真了，但 **s1 仍是 1**（判 B）
- `structure TwoSectionData A`：`s0 s1 : A`、`span_top : Ideal.span {s0,s1} = ⊤`、`s0_ne_zero`、`s1_ne_zero`。
- `protectedToZeroTwoSection T := { s0 := protectedToZeroPolynomial T, s1 := 1, ... }` —— **`s1 := 1` 逐字仍在（第 85 行）**。因此 `span_top` 由 `1 ∈ {s0,1}` 平凡关闭（`Ideal.subset_span`），`s1_ne_zero := one_ne_zero`，`protectedToZero_s1_avoids` 只是 `simp`。"两个 actual 截面"里只有 s0 是实际的，s1 是单位常数。
- 真实增量：`eval_protectedToZero_eq_zero_iff`（`eval a (∏(X−t)) = 0 ↔ a ∈ T`，归纳真证）、`protectedToZeroPolynomial_monic/ne_zero`、**`rootMultiplicity_protectedToZero_of_mem = 1`（零点全为单零点 = 路线 (B2) 在 A¹ 上的除子层版本）**。
- 与路线 §4.1 的差：路线要 `L = O_Y(D_T)`、`s0` 为该线丛的 canonical section、`deg D_T ≥ deg K_Y + 3`、`s1` 在 `D_T` 上非零且给出 `ψ*O(1) ≃ L`。这里没有 Y、没有线丛、没有 degree 条件。**s1=1 使 ψ=[s0:1] 永远打不到 ∞，构造不出 0/1/∞ 三分歧值。**
- 判定 **B**；probe 三公理（`not_both_mem_of_span_top` 只用 propext+Quot.sound）。

### 4.14 【本批·高】`Mzk1G1QHeightActual`：定义是真的，**定理几乎全平凡/语义错**，D3 完全没出现（判 TOY/换题）
- 真实部分：`legendreJ lam = 256 * (1 - lam + lam^2)^3 / (lam^2 * (1 - lam)^2)` 逐字就是路线 §6.3 的有理函数；`lambdaHeight = jHeight = Height.logHeight₁`。**这是本项目第一次把 j(λ) 的实际有理函数与 `logHeight₁` 接上**，定义可复用。
- 问题：
  1. **没有 D3**：没有 `h(j) = 6 h(λ) + O(1)`、没有 degree 6 morphism、没有 `O_{K_V}(1)` 的实际见证。全文件只有 `lambdaHeight_nonneg`/`jHeight_nonneg`（`zero_le_logHeight₁` 的直接转述）与 `legendreJ_of_rat`（`rfl`）。
  2. **`legendreJ_zero` / `legendreJ_one` 数学上是假命题**：`j(0)=0`、`j(1)=0` 只在"域里除以 0 得 0"的模型下成立；真实 j 在 0、1、∞ 处有极点。注释诚实写了 "in the field model division by zero is zero"，但定理名与结论会被下游误当 **j 在 0/1 处取 0** 使用。**禁止任何 consumer 引用这两条**。
  3. **`HeightDictionaryInterface qHeight B` 是无 inhabitant 的 interface Prop**（`∀ lam, |lambdaHeight lam − qHeight lam / 6| ≤ B`）；文件自己写 "interface with no inhabitant yet"。引用时必须标 "interface, no inhabitant"。
  4. 命名空间 `LeanFormal.IUT.XiFPaper.G1QHeightActual`（**无 Mzk1 前缀**），与多数文件不一致；consumer `Mzk1G1LambdaThetaActual` 按无前缀 `open`，跨 lane 引用易踩空。
- 判定 **TOY/换题**（不到 B：没有任何路线要求的定量结论）。probe：三公理（`legendreJ_zero` 只 propext+Quot.sound）。

### 4.15 【本批·中】`Mzk1G1TwoSectionPsiLocalActual`：**ψ 已是 scheme morphism，但只到 A¹，且只在任意 ℚ-代数上**（判 B）
- 真增量（比上一批的纯多项式层明确前进）：
  - `psiChart0 D : Spec (Away D.s0) ⟶ Spec ℚ[t]` = `Spec.map (eval₂RingHom (algebraMap ℚ _) (ratio0 D))`，`ratio0 = s1/s0` 由 `IsLocalization.mk'` 构造；`psiChart1` 对称。**这是真的 `Spec` 态射**（scheme 层，不是"多项式在点上的取值"）。
  - `psi_no_common_zero`：任何素理想不同时含 s0、s1（由 `span_top` 推出）→ 两张 chart 覆盖源，真实。
  - overlap 环 `A[(s0 s1)^{-1}]` 上 `s0`、`s1` 是 unit（`IsLocalization.Away.algebraMap_isUnit_iff` + `dvd_mul_right/left`），真实。
- 问题：
  1. **目标是 `Spec ℚ[t] = A¹`，不是 `P¹`**：没有 `Proj`、没有齐次化、没有 glue 到 P¹。
  2. **量词不是 actual 的**：`variable {A : Type} [CommRing A] [Algebra ℚ A]`，即"任意带 ℚ-代数的交换环 + 任意 TwoSectionData"；**没有 Y_n、没有 Fermat 曲线、没有 D_T 的 degree 条件**。
  3. `overlapCoord_mul_cocycle` 是**群恒等式**：`overlapCoord0 = u1*u0⁻¹`、`overlapCoord1 = u0*u1⁻¹`，证明体是 `by group`。它确实证明两坐标互逆，但**没有 `Scheme.GlueData`、没有 glued 态射、没有 `ψ*O(1) ≃ L`、没有 `ψ⁻¹(0) = D_T`**；`TwoSectionPsiData` 的 7 个字段全由这几条定理填入（`twoSectionPsiData` 是定义性组包）。
- 判定 **B**：affine 图表层真实，离路线 §4.1 的 `ψ : Y → P¹` 还差 P¹ 粘合、线丛、除子原像与 0-纤维无分歧。

### 4.16 【本批·高】`Mzk1G1FiniteDisjointBelyiActual`：不再是 empty family，但**一个族都没有**（判 C/换题）
- 真增量：`projectiveLine := Proj (homogeneousSubmodule (Fin 2) ℚ)`；`boundarySet := zeroLocus {X 0, X 1, X 0 - X 1}`（即 `[1:0],[1:1],[0:1]`，真）；`boundarySet_isClosed` 真；`boundaryPreimage n phi := phi ⁻¹' boundarySet` 用了 **accepted 的 `fermatCurveScheme n`**。旧版 `boundary := ∅` 的常映射 toy 已删除。
- 但：
  1. `structure ActualDisjointBelyiFamily` 的 `disjoint_edges : Pairwise (Disjoint ∘ boundaryPreimage)` 是**假设字段**——没有证明任何真实 φ_i 满足 (E1)。
  2. `HasActualDisjointBelyiFamily n d V := ∃ F, F.r = d * V.card` 是**无 inhabitant 的 Prop**：文件里没有任何 `φ_i : Y_n → P¹` 被构造，全文件只有一个定理（`boundarySet_isClosed`）。
  3. 路线 §7.1 要递归构造 `φ₁,…,φ_{r+1}` 并**证明** E1；现在把 E1 写进结构字段，等于把结论当假设。
- 结论：**"是否仍只有 empty family"→ 不再是空族恒真，而是"无族"陈述**；同样不能记 G-K 进度。判定 **C/换题**（陈述层有效，可作 G-K 接口骨架，须标 "no inhabitant"）。
- **batch 5 更新**：文件 00:13:41 重新 DONE（§2d#92）。`#print axioms boundarySet_isClosed` 已移回 namespace 内（§2c#58 的秒修完成）；`B1AvoidingMaps`、`ActualDisjointBelyiFamily` 现在明确写 "INTERFACE, NO INHABITANT"，且 `boundaryPreimage` 用 **`fermatCurveScheme n`（真 `GlueData.glued`）** 与 `projectiveLine`。**判定不变（C/换题），仍无族 inhabitant**；`GKData`（§4/DisjointFamily）把 `family` 当字段，所以 G-K 出口仍未闭合。

### 4.17 【本批·中】`Mzk1G1BelyiCVCompositionActual`（23:30:24 DONE）：多项式值层的 composition law（判 B）
- 7 条定理：`criticalValuesOverC_comp_subset`、`cvCompositionLaw_proved`、`specialSetPreservation_proved`、`zero_not_critical_value`、`comp_T_avoids_specialSet`、`comp_criticalValues_subset`、`comp_preserves_values`；当前 run 的日志末段为 **[propext, Classical.choice, Quot.sound]**（前段的 sorryAx 块属于 23:24:32 那次失败尝试）。
- 但对象是 **`Polynomial ℚ` 与其 critical values 有限集**（值层），没有 `Spec`/scheme morphism、没有 `φ = h∘ψ` 的实际复合、没有 `φ*O(1)` 与 branch divisor。路线 §4.3/§4.4 要"每步实际有理函数 + 其 scheme morphism + branch composition 公式"。判 **B**（可作 §4.3 下降的代数供体）。

### 4.18 【本批·中】`Mzk1UCC1UpperActual` 新版（23:30:28 DONE）：仍是条件式，但 C4 端接真 P5（判 B）
- `def UC1UpperActual l A Q M B : Prop := B = kappa l * (A - cL l * Q) - M` —— **定义式**，不是"加权 paper 界"的构造；`uc_c3_of_weighted_paper` 就是 `unfold` + `rw`，前提 `hHpkt : Hpkt ≤ B` 把加权的实际界**当假设**。
- 真实进步：`uc_c4_of_p6_data` 用 accepted 的 `P6HThetaNormalization2Actual.p6_neg_M_le_HTheta2` 给出实际下界 `−M ≤ actualThetaHullLogRoot`（`M = actualQPilotMagnitudeClassical`），再用 `uc_c3_to_c4`（UCC3 algebra）夹出 `cL l * Q ≤ A`。下界端是真的。
- 仍缺：`θ_P5 ≤ H_pkt`（U-R reading bound）与 `H_pkt ≤ B`（加权 paper 界）两个 actual producer。判 **B 条件式**，不能记 U-C C1/C3 accepted。

### 4.19 【本批·高·项目级】多处 FAIL 首错是"import olean 不存在"，但 olean 实际存在 → 假 FAIL / 并发窗口
- `Mzk1UCC1UpperActual`(23:24:35)：`object file … Mzk1P6P5ControlJ1Actual.olean … does not exist`，但该 olean **存在**（mtime 23:11:06，DONE 23:11:07）；23:30:28 重编即 DONE。
- `Mzk1ULPacketHullActual` / `ULPacketHull2Actual`(23:23:57)：首错 `Mzk1ULFieldProductActual.olean` / `Mzk1ULFieldProduct2Actual.olean` 缺失，但两个 olean **都存在**（23:17:48 / 22:52:58）；`ULPacketHull2Actual` 23:31:19 已 DONE。
- `Mzk1ULWeightedHullActual`(23:29:36)：首错是 **`Mathlib.LinearAlgebra.Finrank.olean` 缺失**——这是共享 build 树里的 Mathlib olean，不是本仓库文件；`.lake/build` 与 `.lake/packages/mathlib/.lake/build` 两处路径均不存在该 olean，但 `Mathlib.Tactic` 等能 import（说明存在另一套解析路径/缓存）。**需要 Lead/维护者查共享 build 树是否被并发 `lake` 调用或清理破坏**；否则会出现大面积假 FAIL 与假"依赖缺失"。
- 纪律结论：**见到 `object file … does not exist` 的 FAIL，先 `Test-Path` 该 olean，再判 red**；不要把假 FAIL 当数学缺口写进交接。

### 4.20 【本批·中·纪律】日志跨尝试追加，判 axiom/首错只能取末段
- `Mzk1G1TwoSectionDataActual` 的 log 同时含 `eval_protectedToZero_eq_zero_iff` 的 **sorryAx 块**（来自 23:21:39 的失败尝试）与末段的**三公理块**（23:24:33 DONE）。
- `Mzk1G1BelyiCVCompositionActual` 同理（23:24:32 失败的 sorryAx 块 + 23:30:24 成功的三公理块）。
- 因此本表 axioms 列：(P) 一律以 `_ProbeBatch3Actual.lean` 独立复算为准；(L) 只取日志末段并注明。

### 4.21 【高·G-A】本轮 geom 修复的真实增量与仍然缺口
- **已 DONE 且是真数学**：
  - `Mzk1G1FermatFiniteDegree2Actual`（23:39:32）：A₀/A∞ 的实际环呈现 + `Module.Basis (Fin n × Fin n) (ℚ[λ])` + `finrank = n*n`。**这修掉了 §4.3 的 rank 语义错位**（旧版是 n over ℚ[x]）。
  - `Mzk1G1FermatCurveClosed2Actual`（23:39:31）：closed/proper 转述 donor，外加 `fermat_X1_pow_mem_span`、`fermat_X1_mem_of_prime`（F = X₀^n+X₁^n−X₂^n，X₁^n ∈ (F,X₀,X₂)）。
  - `Mzk1G1FermatSupportActual`（23:45:47）：两图结构态射 `Spec A₀ → Spec ℚ[λ]`、`Spec A∞ → Spec ℚ[t]` 的 `IsFinite` 与 `IsProper`。
- **未 DONE**：`Mzk1G1FermatSmoothChartActual`（23:45:16 FAIL，首错是 `C` 歧义 / `AdjoinRoot.liftAlgHom_toRingHom` 不存在 / 两条互逆恒等未关）。它的计划（`A₀ ≃ₐ ℚ[X,Y]/(X^n+Y^n−1)`）正是 §2.1 的识别步骤，方向正确但**当前 `fermatA0EquivCurve` 依赖 sorryAx**。
- **仍然缺的 G-A 出口**：(a) `π : Y_n → P¹`（[X:Y:Z] ↦ [X^n:Z^n]）与两图原像等式；(b) 粘合实例化（§4.23）；(c) scheme 层的「D(X₀)∪D(X₂) 覆盖 Y_n」；(d) smooth / 几何整性 / degree（n² 的 rank 已有，但「Y_n → P¹ 的 degree = n²」仍缺）。

### 4.22 【高·U-C/U-L】三套加权 hull 与「实际对象」文档声明不一致
- 本批三处并存、互不引用：
  1. `Mzk1ULWeightedHullActual.ulWeightedPacketHull = Σ (finrank_{ℚ_p}F_v / Σ finrank) * W_i`（真 local-degree 权、归一化、总权 1）；
  2. `Mzk1UCC3ProducerActual.ucWeightedHpkt w hullVol = Σ w_i * hullVol_i`（**任意** w，无归一化）；
  3. `Mzk1UCHpktActual` 的 `uc_c3/uc_c4_from_weighted` 只用 (2)，且**没有 import** `ULPacketVActual` / `ULWeightedHullActual`。
- 因此 `Mzk1UCHpktActual` 注释里「the weights are the actual local-degree weights …」「the per-packet volumes V a are the actual packet volumes …」**与定理陈述不符**：定理对任意 `w hullVol paper : ι → ℝ` 量化，actual 对象没有被引用。
- 纪律：引用 `uc_c3` / `uc_c4_from_weighted` 时必须写明「conditional: 任意权 + 任意 per-packet 界 + 加权 paper 恒等式均为假设」，**不能**记 U-C C1/C3/C4 accepted。真正缺的是 (i) `θ_P5 ≤ H_pkt` 的 actual producer（U-R 侧），(ii) `Σ w_a B_a = κ(A−cL Q)−M` 的 actual 恒等式，(iii) 把 (1)(2) 统一成一个定义。

### 4.23 【中·G-A】`Mzk1HullFermatGluingActual` 是真 `GlueData`，但仍是 generic 模板
- 23:35:19 DONE 的 `twoChartGlueData U0 U1 W g0 g1 hg0 hg1 : Scheme.GlueData` 是**真构造**（J = ULift Bool；V (false,true) = V (true,false) = W；t = 𝟙；`f_mono/f_hasPullback/f_id/t_id/t_fac/cocycle/f_open` 全部真证），注释说模式取自已编译的 `S2801E37ProjectiveClosure`。
- 但它**没有**：U0/U1 是 Fermat 两图（`Spec A₀`、`Spec A∞`）的实例化；W 是 overlap 环 `A[(s0 s1)^{-1}]` 的 `Spec`；两张 open immersion 的像确实是两图的 standard open；`glued` 与 `Y_n` 的同一性；`π`。
- 判定 **B**（可复用的正确组件）；G-A 的下一步是写一个 Fermat 实例（约 20 行）：`twoChartGlueData (Spec A₀) (Spec A∞) (Spec (Localization.Away …)) …` + `IsOpenImmersion` 实例 + 命名 `fermatGluing`。

### 4.24 【中·L-H】`Mzk1G1QHeightActual` 的假命题已删；D3 仍然没有
- 23:37:22 重写后：`legendreJ_zero` / `legendreJ_one` **已删除**（§4.14 第 2 条作废；这两个命题在 0/1 处数学为假），现只剩 `lambdaHeight_nonneg`、`jHeight_nonneg`（`zero_le_logHeight₁` 转述）+ `HeightDictionaryInterface`（**无 inhabitant**）。
- D3（h(j) = 6 h(λ) + O(1)）仍未出现；`legendreJ`（256(1−λ+λ²)³/(λ²(1−λ)²)）与 `lambdaHeight = Height.logHeight₁` 的定义可复用。
- 判定仍 **TOY/换题**（不到 B：没有任何路线要求的定量结论）；引用 `HeightDictionaryInterface` 必须标 interface, no inhabitant。

### 4.25 【中·G-A】两个新的 closed-immersion 文件是 accepted donor 的坏副本（#68/#69）
- `Mzk1G1FermatCurveClosedActual` / `Mzk1HullFermatClosedSubschemeActual` 与 accepted 的 `Mzk1G1FermatProjClosedSubscheme4Actual`（22:52:58 DONE，§2#4 判 A-局部）**逐个定义相同**（fermatCloseds、fermatIdealSheaf = vanishingIdeal、fermatCurveScheme = subscheme、fermatCurveImmersion = subschemeι）。
- 但 donor 用 `abbrev` + `(IsClosedImmersion.iff_isProper_and_mono (f := …)).mp`，两个新文件用 `def` + 省略 `(f := …)`，于是：`24:2`/`28:2` SynthInstanceFailed、`31:3`/`27:9` Unknown constant，两个定理都落成 sorryAx。
- **动作：删除这两个文件**（不是修）：G-A 的 proper/closed 已有 `ProjClosedSubscheme4Actual`（A-局部）与 `FermatProperFinal2Actual`（B，稳定出口名）。

### 4.26 【低·纪律】`maxHeartbeats` 在全仓普遍存在；本批 `ULPacketHullActual` 用 4e6
- `grep maxHeartbeats tmp/sheaf/xif/paper` 命中大量文件（1e6–2e7 级）；本批被审文件中唯一命中是 `Mzk1ULPacketHullActual:16 set_option maxHeartbeats 4000000`（DONE 23:42:48）。
- 这不算本批新增的「为绕过错误调高」证据（该文件确实实例化到 `qVFamTensorBlock` 并复用 `packetV_le_packetB`），但**记录**：高 heartbeats 文件编译脆弱、且拖慢 batch（该文件 143s，本批最慢）。

### 4.27 【高·纪律】olean 级联假 FAIL 的实例（本批实际发生）
- `Mzk1G1FermatSmoothChartActual`(23:36:13)：`Mzk1G1FermatFiniteDegree2Actual.olean does not exist`；该 olean 于 23:39:31 生成后重编，23:45:16 变成真错误（C 歧义等）。
- `Mzk1G1FermatSupportActual`(23:30:33)：`Mzk1G1FermatProperFinal2Actual.olean does not exist`；ProperFinal2 于 23:35:37 DONE，Support 于 23:45:47 DONE。
- `Mzk1G1FermatSmoothAttemptActual`(23:35:18)：`Mzk1G1FermatSupportActual.olean` 缺失。
- `Mzk1G1B1B3ComponentActual`(23:36:33)：其 import `PsiChartMapsActual` 当时 FAIL；后者 23:39:30 DONE（属级联，非自身数学）。
- `Mzk1G1FiniteDisjointBelyiActual`(23:36:47 / 23:39:31)：由自身 `#print` 写在 namespace 外导致，**不是**级联（§2c#58）。
- 规则：判 red 前先 `Test-Path` 依赖 olean + 看首错；假红不进交接，也不作为「数学缺口」写。

### 4.28 【中】本批 FAIL 的可执行修复映射（首错 → 修法）
| 文件 | 首错（当前源码） | 修法 |
|---|---|---|
| `Mzk1G1FermatSmoothChartActual` | `48:43 Ambiguous term`；`50:4 whnf 心跳超时`；`82:42 Unknown constant AdjoinRoot.liftAlgHom_toRingHom`；`128/133/141/146/150 unsolved goals` | `C` → `Polynomial.C`；`dvd_rfl` 前先 `rw [fermatU0Poly]`；`liftAlgHom_toRingHom` → `AdjoinRoot.toRingHom_liftAlgHom`（或 `coe_liftAlgHom`）；两条互逆恒等按 `algHom_ext'` 分层 simp |
| `Mzk1G1KvCompactActual` / `…RadicalSupportActual` | `Nat.Prime.mem_primeFactors` 第三参数类型 `a*b*c ≠ 0` vs `n ≠ 0`；`Finset.not_mem_empty`；`0<δ<1/2` 的 norm_num | 先用 `habc` 反推 `n ≠ 0` 再传；`Finset.not_mem_empty` 改 `Finset.notMem_empty`；δ 界用 `nlinarith`/`field_simp` |
| `Mzk1G1FermatRadicalSupportActual` | `165:2` 等式方向反 | `log_natAbs_discr_eq_sum_factorization … |>.symm` |
| `Mzk1G1OmegaActual` | `61:2/68:2` `coordX*coordX^(n−1)` vs `coordX^n` | `rw [show coordX^n = coordX*coordX^(n−1) from …]`（`pow_succ'`）或 `ring_nf` |
| `Mzk1G1FermatTransitionActual` | `⊢ 1 * overlapY^n = overlapY^n` | `simp` / `ring`，再重跑 `#print axioms` |
| `Mzk1G1FiniteDisjointBelyiActual` | `59:14 Unknown constant boundarySet_isClosed` | 删掉 namespace/section 之外的第 59 行 `#print axioms` |
| `Mzk1G1FermatCurveClosedActual` / `Mzk1HullFermatClosedSubschemeActual` | SynthInstanceFailed + Unknown constant `…iff_isProper_and_mono.mp` | 删文件（用 donor `ProjClosedSubscheme4Actual` / `ProperFinal2Actual`） |

### 4.29 【高·G-A】Y_n 的两图粘合这次是真实例化 —— 但仍缺 π / 覆盖等式 / 与 Proj 模型的同一性（#71/#80/#82）
- **真增量**（比 §4.23 的 generic 模板前进了一大步）：
  - `Mzk1G1FermatOverlapActual`：`Chart0Ring := R n = ℚ[x,y]/(x^n+y^n−1)`、`ChartInfRing := R2 n = ℚ[s,r]/(1+s^n−r^n)`、`Overlap0 := Away x0`、`OverlapInf := Away r1`；`psi : A0 → Away r1`（r ↦ x⁻¹, s ↦ y x⁻¹）与 `phi : A1 → Away x0` 由 `Ideal.Quotient.lift` + `IsLocalization.Away.lift` 构造；`alpha_beta`/`beta_alpha` 证明 `alpha : Away x0 → Away r1` 与 `beta` **互逆**，`overlapSchemeIso` 是 scheme 同构。这是路线 §2.1 的 overlap 识别（此前 §4.11 判 C placeholder、§2c#66 判 R）。
  - `Mzk1G1FermatTwoChartGluingActual`：`fermatTwoChartGlueData := twoChartGlueData (Spec A0) (Spec A1) (Spec Overlap0) overlapToChart0 overlapToChartInf …`，`fermatCurveScheme := glued`，两条 `IsOpenImmersion`（走 `GlueData.ι_isOpenImmersion`）。`fermatChart0ToCurve` 是**定义**（不是假设），所以 `fermatCurveScheme_eq_glued` 是 rfl。
  - `Mzk1G1FermatCurveActual`：把上述包成 G-A 的稳定出口名 + `fermatCurveOpenCover := (fermatTwoChartGlueData n).openCover`。
- **仍缺**（不能记 G-A accepted）：
  1. `overlapToChart0 ≫ ι0 = overlapToChartInf ≫ ι1` 的相容等式**仍是文件里的 TODO 注释**（第 48–51 行），没写成定理；`GlueData` 的 `cocycle` 只保证模板自洽。
  2. `π : Y_n → P¹`：`Mzk1G1FermatPiActual`（124 行）正在写两图的 `Proj.fromOfGlobalSections`（`X0 ↦ x^n, X1 ↦ 1` / `X0 ↦ 1, X1 ↦ r^n`），当前 **FAIL**（首错 32:41 Type mismatch），且两图 glue 尚缺（§2d#95）。
  3. 「`Y_n`（`GlueData.glued`）≅ `Proj(k[X,Y,Z]/(F))`（accepted 的 `ProjClosedSubscheme4Actual.fermatCurveScheme`）」**未证**；`FermatCurveActual` 的 docstring 自认 "not yet proved"。因此 proper/closed/smooth 现在挂在**另一套模型**上，两边只有名字相同。
  4. scheme 层的两图覆盖 `D(X₀) ∪ D(X₂) = Y_n` 仍未写成 `⊤` 的开覆盖等式（有 `OpenCover` 对象，但没有与坐标对应的两条 basic open 的相等）。
- 结论：G-A 从「只有 proper/closed 转述」推进到「有真粘合 + 真 overlap 识别」，但**出口（π + degree n² + smooth + 两模型同一）未到**。

### 4.30 【高·G-C】ψ 到 P¹ 的第一图是真 scheme 态射（#87），但只到第一图（#76 只补了环层覆盖）
- `psiChart0Global : Q[X0,X1] → Γ(Spec R n, ⊤)`，`X0 ↦ u = ∏(x − t)`、`X1 ↦ 1`；`psiChart0Irrelevant` 证明 irrelevant ideal 的像 = ⊤（用 `X1 ↦ 1` 含于 irrelevant），于是 `Proj.fromOfGlobalSections` 可用；`psiChart0ToP1_preimage_basicOpen` = `Proj.fromOfGlobalSections_preimage_basicOpen`，给出 **`(ψ₀)⁻¹D_+(X0) = D(u)`**，即路线 §4.1 里 `ψ⁻¹(A¹) = Y ∖ D_T` 的 chart 层形式。
- 缺口：(a) 第二图 `psiChart1 : Spec A1 → P¹` 与两图粘合（`PsiChartInfCoverActual` 只给了 `span{q, r} = ⊤` 这个环层输入，没有 scheme 态射）；(b) `ψ*O(1) ≃ L = O(D_T)`；(c) `ψ⁻¹(0) = D_T` 的除子等式（现在只有 basic open 原像）；(d) `s1 = 1` 退化（§4.13）仍然存在，所以 `u = ∏(x−t)` 的 0-纤维就是 D_T 但 §4.1 要的 0/1/∞ 三分歧值还缺 `∞`。
- 判定：**B+/A-局部**。这是本批 G-C 最实在的推进。

### 4.31 【高·L-H】D1 被归约到 (D3)+(D4)；D3 仍无 inhabitant；KvCompact 根因已清
- `Mzk1G1KvCompactActual`（00:12:01 DONE）：`LocalValueSet δ = [δ, δ⁻¹]`（`localValueSet_eq_Icc`）⇒ `IsCompact`，`InKv.arch_mem/arch_bound/arch_apply_ne_zero` 都由 `KvData` 字段推出；**此前 `kv_nonempty_emptyV` 的 sorryAx 块已消失，两定理均三公理**。这解除了 §2c 里 D1Producer / LocalHeightCriterion / DisjointFamily / RadicalSupport 的级联根因。
- `Mzk1G1D1ProducerActual`（00:08:51 DONE）：`d1_of_analyticInput (A : D1AnalyticInput D) (hη : 0 < η) : LocalHeightCriterion d D η`。吸收论证是真的（`ratio_le`：`(1+μ/6)/(1−μ/4) ≤ 1+μ`；`sqrt_mul_log_sublinear`；μ = min η 1；C = ((μ/4)B + CK + B)/(1−μ/4)）。**但 `D1AnalyticInput` 的 `height_dictionary`（D3）与 `upper_estimate`（D4）是结构字段**，没有 producer。
- `Mzk1G1QHeightActual`（00:12:00 DONE）：仍只有两条 nonneg；**D3（h(j) = 6h(λ) + O(1)）没有出现**，`HeightDictionaryInterface` 无 inhabitant。
- `Mzk1G1LocalHeightCriterionActual`（23:56:59 DONE）：D1 的量词**这次是对的**（`∀d ∀K_V ∀η>0 ∃C ∀K ∀lam`），但 `actualD1_iff = Iff.rfl` 是定义自反；它只是陈述层落地，**不是 D1 已证**。
- 纪律：引用 `LocalHeightCriterion` / `D1AnalyticInput` 时必须写「D1 ⇐ D3 + D4，均无 producer」。

### 4.32 【中·纪律】"新文件 NO-OLEAN / 一次 FAIL" 不能直接判 red —— 本批 PsiChartToP1 是活例（#87）
- 00:10:00 时 `Mzk1G1PsiChartToP1Actual` 的 FAIL 看起来像 "新文件 NO-OLEAN"：olean 确实 **MISSING**，per-file log 只有 888 字节。但三条依赖 olean **全部存在且 DONE**（`PsiChartMapsActual` 23:39:30、`ProjectiveLineChartsActual` 23:55:36、`FermatTwoChartGluingActual` 00:04:35），首错是真实的 elaboration 错误（`41:4` `HomogeneousIdeal.mem_irrelevant_of_mem` 参数不全 + `41:53 unsolved goals ⊢ ℕ → ?m.74`），**不是缺依赖的假红**。
- 00:10:24 源码重写后，00:12:00 **DONE**（53s），自带 `#print` 三条均三公理。所以正确判定是：**当时真红（数学/API 错），但不是假红、也不是 toy**；判 red 必须同时有「首错 + 依赖 olean 存在性 + 源码 mtime 对比」三件套，且必须在报告里写清是不是当前源码。
- 本条同时纠 §2d 表头：本表所有 "stale/未运行" 都是这样得到的。

### 4.33 【中·G-B】Ω 的微分模落地了，但两图过渡仍红
- `Mzk1G1OmegaActual`（23:54:09 DONE）：真 `KaehlerDifferential ℚ (R n)`、`dX/dY`、单关系式、`ω = y dx − x dy`、`presMap` 的单关系；判定 **B+**（此前 §2c#47 只是标量恒等式）。
- `OmegaPresentationActual`(00:12:03)、`OmegaBasisActual`(00:13:42)、`FermatOverlapRingActual`(00:05:48) 仍 FAIL；`ω∞ = x^{n−3} ω₀` 的两图比较、`Ω_{Y_n/ℚ}` 的整体层、以及 (A3)/(A4) 需要的 `H¹` 类都**没有**。

### 4.34 【中·G-A 后段】三个 geom 文件的当前真实状态（"grace 组"）
| 文件 | 当前状态 (00:16Z) | 首错 / 结论 | 字面 sorry | 语义判定 |
|---|---|---|---|---|
| `Mzk1G1FermatSmoothChartActual` | **DONE 00:13:40**（src 00:12:45, olean fresh） | 无错；自带 4 条 `#print` 三公理 | 无（grep clean） | **B−**：只到 `fermatU0ToCurve : U₀ = ℚ[λ][x]/(x^n−λ) → D = ℚ[x,y]/(x^n+y^n−1)`；上一版的 `fermatA0ToCurve`/`chart0RingHom`（A₀ → D）被删，A₀ ≃ D 仍缺 |
| `Mzk1G1FermatSmoothIntegralActual` | **FAIL 00:13:39**（src 00:12:45, 该 attempt） | **仅 2 条 `unsolved goals`：138:66、146:71**，均在 `fermatMvEquivPoly_fermatCurvePoly` 的 `simp only [...]`（`h1/h2/hX/hC` 重写后 `ring` 那一步） | 无（grep clean；历史 sorryAx 全是 error-recovery） | **R（准绿）**：Eisenstein 于 (Y−1) ⇒ `Irreducible (X^n+Y^n−1)` ⇒ `IsDomain (R n)` 的路线正确且已写全，卡在 simp 归一 |
| `Mzk1G1FermatSmoothAttemptActual` | **FAIL 00:04:36**（src 00:03:01，log 只含该 attempt） | 首错 **`58:4` 与 `59:2 Unknown identifier PreSubmersivePresentation`**；连带 `82/92/99 jacobiMatrix_naive` 不存在、`131:4 typeclass stuck`、`139:4 SubmersivePresentation` 未定义、`156:14 fermatModel_jacobian_isUnit` unknown | 无（grep clean） | **R（API 名错）**：Mathlib 中在 `namespace Algebra` 下；`jacobiMatrix_naive` 应为 `jacobiMatrix_apply`（`P.jacobiMatrix i j = pderiv (P.map i) (P.relation j)`），`jacobian_eq_jacobiMatrix_det` 存在。Jacobian = `(n x^{n−1})²` 与"由关系 `(n x^{n−1})z = 1` 成为单位"的推理已写好，只差改名 |
- 这三个文件在 00:10–00:13 之间被反复重写（per-file log 每次被清空，源码 mtime 追着 FAIL 走），**任何"上一分钟的首错"都可能已经过时**；本表已按最后一次 attempt 记录，并标明源码 mtime。

### 4.35 【低·纪律】文档与 `set_option` 不一致（#71）
- `Mzk1G1FermatOverlapActual` 第 29 行 `set_option maxHeartbeats 2000000`，但该文件上一版注释/交接里写的是 "no heartbeat override"。数学内容不受影响（探针三公理），但**不要把它当"未调心跳"的证据引用**；如需低风险引用，用 `overlapSchemeIso` 与 `alpha_beta/beta_alpha` 这几条定理，而不是整文件。

### 4.36 【高·G-A】SmoothIntegral / SmoothAttempt 双翻绿：都是真数学，但只到局部化/环层
- `Mzk1G1FermatSmoothIntegralActual`（00:37:00 DONE）：Eisenstein 路线完整落地——`fermatTwoVarPoly = X^n − (1−Y^n)` 于素理想 (Y−1) 是 Eisenstein（常数项 `Y^n−1` 恰被 Y−1 整除一次，用 `X_sub_C_pow_dvd_iff` + `coeff 1 = n ≠ 0`），故 `Irreducible`；UFD 中不可约 ⇒ 素 ⇒ `(F)` 素 ⇒ `fermatCurveRing_isDomain`。**这是 §2.4 整性目标的真实证明**（此前 #93 判 R 是因 2 条 `unsolved goals`，现已修）。
- `Mzk1G1FermatSmoothAttemptActual`（00:37:00 DONE）：真 `Algebra.PreSubmersivePresentation`（vars Fin 3, rels Fin 2）、`jacobiMatrix` 逐项计算、`fermatModel_det = ((n)*x^(n−1))²`、由关系 `(n x^(n−1)) z = 1` 得 `IsUnit`、从而 `Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (fermatModelRing n)`。**Jacobian 判据这次是真证**（此前 #94 判 R 是 API 名错）。
- 但两条都**不能**记 G-A smooth accepted：(i) SmoothAttempt 的 `fermatModelRing` 只是 `ℚ[x,y,z]/(F,(n x^{n−1})z−1)`，没有证明它等于 `(R n)[1/x]`（局部化识别），也没有 scheme 层 `Smooth (π)`；(ii) SmoothIntegral 只给 `R n` 整性（`n>0`），几何整性（基域 k̄）的 copy #128 仍 FAIL 且有命名空间关闭 bug。判定 **A-局部**（可作为 §2.4 的环层组件）。
- 两个文件都有 `set_option maxHeartbeats 800000`（grep 唯一命中）；不算"为绕错调大"（8e5 属常规），但记录。

### 4.37 【高·G-A】`Mzk1G1FermatPiActual` 00:41:49 DONE 只是 π 的 chart maps，不是 π
- 文件 44 行，只有：`piChart0RingHom : ℚ[λ] → A0`（λ↦x^n）、`piChartInfRingHom`（t↦r^n）、`piChart0 = Spec.map ... ≫ localChart0`、`piChartInf`，以及两条 `simp` 恒等 `..._X`。#print/probe 三公理（`piChart0` def 级）。
- **缺失**：docstring 说的 "compatibility is the input to `(fermatTwoChartGlueData n).openCover.glueMorphisms`" 并未出现；没有 `glueMorphisms`/相容定理、没有 `pi : fermatCurveScheme n ⟶ projectiveLineGlued`、没有 `π⁻¹(D_+(X0)) = D(x^n)`、没有 degree = n²。
- 判定 **B−**：对象是 actual scheme morphism（不是值层 surrogate），但只是 π 的两块局部输入；#95 从 R 翻成"半成品"，不能当 G-A 出口。下一步可直接用 #114 的 `chartMorphism_transition` 在 overlap 上拼 `glueMorphisms`。

### 4.38 【中·G-A】TwoChartGluing / HullFermatGluing 00:39 恢复：旧 Probe 4/5 结果 STALE
- `Mzk1HullFermatGluingActual`（00:39:11，src 00:37:59）与 `Mzk1G1FermatTwoChartGluingActual`（00:39:10，src 00:38:06）都从 00:35/00:37 的 FAIL 恢复；`fermatTwoChartGlueData` 现在是 `twoChartGlueData (Spec A0) (Spec A1) (Spec Overlap0) overlapToChart0 overlapToChartInf ...` 的真实例，两条 chart open immersion 真。
- **但用户级 cocycle 等式仍是文件里的 TODO 注释**（`overlapToChart0 ≫ ι0 = overlapToChartInf ≫ ι1`）；作者诚实说明卡在 `GlueData` 的 `J = ULift Bool` 的 instances transparency。`GlueData.cocycle` 只保证模板自洽，不等于该等式已被下游拿到。
- 仍缺：`Y_n ≅ Proj(k[X,Y,Z]/(F))`、π、scheme 层两图覆盖等式 `D(X0)∪D(X2)=Y_n`。判定 **A-局部**（真粘合组件）。
- **STALE 标注**：#80 的 00:04:36 DONE 与 #48 的 23:35:19 DONE 对应的源码都已变；Probe 5 的 `fermatChart0ToCurve_isOpenImmersion` / `fermatCurveScheme_eq_glued` 与 Probe 4 的 `twoChartGlueData` def 级结果均**只对旧版有效**。Probe 6 已对当前版重测 chart open immersion（三公理）。

### 4.39 【中·Lead 线】Lead 8 文件语义复核（H-T / P8-P）：真实但多为薄 wrapper / 条件式
对象列区分 **actual**（真实数学对象且量词对齐）、**wrapper**（只转述 donor）、**conditional**（结论以路线输入为假设）。公理列：L* = Lead 自建 `_ProbeP8LeadActual` DONE 00:46:53，8 条全部 [propext, Classical.choice, Quot.sound]（**非 audit 独立 probe**；本批 Probe 6 独立复算其中 `F7DiscSum` 一条，同结果）。

| 文件 | 对象 | 量词/假设 | 判定 | 理由（1–2 行） |
|---|---|---|---|---|
| `Mzk1P8EpsilonSelectionActual` | actual 实数 δ、n | 任意 ε>0；结论 ∃δ,n | **A-局部** | δ=min 1 (ε/3) ⇒ (1+δ)²≤1+ε、∃n≥4 使 n/(n−3)≤1+δ，都是真不等式；只是 §8.6 的选择步，不含 F9/ABC。 |
| `Mzk1P8FreyAssemblyActual` | conditional 归约 | 以 `ABCLogConjecture`（F9）为假设 | **B（条件式）** | 真归约 `ABCLogConjecture → ABCFreyJProductHeightCriterion → ABCConjecture`，用 donor `abcJInvariant_logHeight_le`；ABC 本身没有被证明（也不能由该文件证）。 |
| `Mzk1F7TameOrderActual` | actual 局部域量 | 假设 `d = e−1`；任意 tame 局部域 | **B+** | `d/e ≤ 1` 与 `(d/e)·log p ≤ log p` 真证（`Nat.sub_le` + `div_le_iff₀`）；未生产 `d=e−1`（留给 donor/实例化）。 |
| `Mzk1P6HConstActual` | actual 论文常数 | 假设 `552960·l ≤ E`、`l≥5` | **A-局部** | 纯数值 `2 log l + 56 ≤ (4/9)E_ar`（`log l≤l` + `nlinarith`）；对象是 `e*_mod = 2^12·3^3·5·e_mod`，不是几何。 |
| `Mzk1F7DiscLocalGlobalActual` | wrapper | 任意数域 K | **B（thin wrapper）** | 五条全是 Mathlib donor 的转述（`differentIdeal_ne_bot`、`prod_normalizedFactors_eq_self`、`absNorm_differentIdeal`、`map_multiset_prod`）；正确、可复用，但无新数学。 |
| `Mzk1F7DiscPrimeFactorActual` | actual per-prime | P 素、P≠⊥、p 素 | **B+** | `absNorm P = under^f` 是 donor `.symm`；`factorization_absNorm_eq_ite` 的 if 分裂正确；per-prime 输入落地。 |
| `Mzk1F7DiscProductActual` | actual multiset | 任意非零理想 multiset | **A-局部** | 真 `Multiset.induction` + `Nat.factorization_mul`；product 层公式落地。 |
| `Mzk1F7DiscSumActual` | actual 全局公式 | 任意数域 K、p 素 | **A-局部/B+** | 真主公式 `v_p(|disc K|)=Σ_P v_P(𝔇)·[under=p]·f_P`（multiset 计数 + 规范化因子 + per-prime 正确组装）；仍缺 tame 上界（#129）。 |

- **量词未被缩**：8 条都是 `∀ K`/`∀ ε`/`∀ tame 局部域` 的路线量词，没有把 actual 对象换成 toy；**没有把结论当假设**的唯一一处是 `P8FreyAssembly` 的 `ABCLogConjecture`——这是路线 §8.6 的**显式输入**（F9），不是伪装完成，但引用时必须写 "conditional on F9"。
- Lead 的 8 个 DONE 对 F7 的贡献是**算术/判别式字典层**；距离 `differentContribution K p ≤ log p` 还差 #129 的 tame 装配（当前 FAIL）。

### 4.40 【中·纪律】per-file log 仍会累积旧 attempt 的错误；F7Product/F7Sum/TwoChart 是活例
- `Mzk1F7DiscProductActual` 的 log（mtime 00:43:17 = DONE）仍含 24:6/49:23 的旧源码错误（行号比当前源码少 3 行），末段才是当前 attempt 的 linter warning——**不能按这两行判 R**；当前 DONE + olean fresh + Lead probe 三公理。
- `Mzk1F7DiscSumActual` 的 log（mtime 00:43:40 = FAIL）停在旧 attempt（缺 `F7DiscProduct.olean` + `P.IsPrime` synth），00:44:40 DONE 的 attempt **没有输出**（文件无 `#print`）；当前 olean fresh，Probe 6 独立三公理。旧 attempt 的 `P.IsPrime` 已由当前源码第 40 行 `haveI : P.IsPrime := ...` 修掉（真 API 修）。
- `Mzk1G1FermatTwoChartGluingActual` 的 log 570 行、30 个 `error`、10 次 `sorryAx`，但末段是当前 DONE 的三公理 `#print`；旧段属于 00:35/00:37 失败尝试。
- 规则重申（与 §0.5/§4.20 一致）：只取源码 mtime 之后/最后一次 attempt 的段；DONE + olean fresh 优先于 log 尾部残留。

### 4.41 【高·H-T/F7】tame 桥已到 local-field，全局 tame 上界仍红
- `Mzk1G1FermatRadicalSupportFinal3Actual`（00:45:07 DONE）：`radical_dvd_self_final3`/`freyConductor_*` 是真算术；`tame_count_differentIdeal_eq` 是 donor `count_differentIdeal_eq_of_tame` 在 `A=ℤ_[p]`、`B=Integers L` 的实例化（`hsepFrac`/`hsep`/`he` 是诚实假设）；`tame_localDifferentPaperOrder_le_one_of_tame` 真。Probe 6 三公理。
- **未闭合**：`Mzk1F7DiscTameBoundActual`（00:48:49 FAIL）要证 `v_p(|disc K|) ≤ finrank ℚ K`（tame count ⇒ `Σ e_P f_P` 上界），当前首错 46:8/49:8 rewrite、54:2 Type mismatch（`Finset.sum_le_sum_of_subset_of_nonneg` 的用法）。因此 §8.5 的 `differentContribution K p ≤ log p` 仍缺最后装配。
- 纪律：引用 F7 时写 "local-global formula DONE；tame ≤ log p conditional on TameCount + #129 未完成"。

### 4.42 【中·U-L】ULThetaPacket DONE：per-b 对象是 actual，但 V_a 值公式与 C1 仍缺
- `Mzk1ULThetaPacketActual`（00:45:07 DONE）把 `Mzk1URRootMassActual` 的 `normalizedLogMass_kummer_root` 推广成 `ulNormalizedLogMass_smul`（任意非零乘法平移的单位球质量 = log‖x‖，真 `distribHaarChar` 计算）；`ulFinrankF`、`ulThetaPacketUnitBall`、`ulThetaPacketRegion`（`θ_j • unit ball`）、`ulThetaPacketV` 都是 actual 对象（`rootNormedExtension`/`rootExtensionHaar`）。
- **但**：`V_a = −ord_p(θ_j)·log p` 未证；C1 形状的界未证；没有 `θ_P5 ≤ H_pkt` 的 producer。docstring 自己说这是 "next step"（mechanical instance-alignment，不是数学 gap）。判定 **B**，不能记 U-C C1/C3 进展。

### 4.43 【中·新 FAIL / 冗余】四条新红 + 两个应删文件 + 一个 copy bug
- 新 FAIL：`ProjectiveLineBoundaryActual`（51:31）、`ProjectiveLinePiOverlapActual`（106:6，且 `fermatPiOverlap_condition` 落 sorryAx）、`SmoothGeomIntegralActual`（38/46/53/58 + 192–198；**命名空间关闭写成 `...SmoothIntegralActual`**，是 copy bug）、`F7DiscTameBoundActual`（46/49/54）。
- `OmegaBasisActual`（00:52:52 再 FAIL）与 `OmegaPresentationActual`（00:47:59 FAIL）仍红：前者的 `y_pow_smul_omegaForm` 等三条落 sorryAx，后者 `omBasis.baseChange` 处 Type mismatch；G-B 的 Ω 基/展示层在本批**没有**推进。
- 两个 closed-immersion 冗余文件 00:47:56 再次 FAIL（`FermatCurveClosedActual` 28:2/31:3、`HullFermatClosedSubschemeActual` 24:2/27:9，均 sorryAx）。§4.25 结论不变：**删除**，用 `ProjClosedSubscheme4Actual` / `FermatProperFinal2Actual`。
- `Mzk1F7DiscTameBoundActual` 是新文件，仅 89 行，当前 FAIL；不要与已 DONE 的 `F7DiscProduct/Sum` 混淆。

### 4.44 【中·G-C/G-A】P¹ glued 模型 + chart transition 是本批最实的 G-C 基础设施
- `Mzk1G1ProjectiveLineGluedActual`（00:31:10 DONE）：真两图 `GlueData`（`chart0Scheme = chartInfScheme = Spec ℚ[λ]`、`overlapScheme = Spec ℚ[λ,λ⁻¹]`、`invAuto : λ↦λ⁻¹` 对合、`overlapToChartInf_isOpenImmersion` 由 `invAuto` iso 拆出）；`localChart_overlap_condition` 是 `p1GlueData.glue_condition`（真），`localChart_jointly_surjective` 是真两图覆盖。判定 **A-局部**。
- `Mzk1G1ProjectiveLineTransitionActual`（00:43:15 DONE）：任意 ℚ-代数基上 `chartMorphism0 u = chartMorphismInf u⁻¹`，证明用 `IsLocalization.Away.lift` + `localChart_overlap_condition`；Probe 6 三公理。判定 **A-局部**。
- **仍缺**：把 `FermatPi` 的两条 chart map 用这个 transition 拼成 `glueMorphisms`，得到 `π : Y_n → P¹` 与其 degree/原像；`ProjectiveLinePiOverlapActual`（#124）正在做这一步，当前 FAIL（106:6）。

### 4.45 【高·G-A】用户级 cocycle 等式：一次真实尝试、真实失败、已撤回（#135）
- 12:43:15 的 DONE **不含** `fermatOverlap_glue_condition`（Probe 7 以 unknown constant 独立证实）。12:44:54 版加入该定理，12:45:45 **FAIL**：
```
60:6: rewrite failed: pattern 𝟙 ?m.40 ≫ ?f not found
     ⊢ 𝟙 ((…).V (idx0, idx1)) ≫ (…).f idx1 idx0 = (…).f idx1 idx0
Application type mismatch: 𝟙 (V (idx0,idx1)) expected type Hom (V (idx0,idx1)) (V (idx1,idx0))
```
  根因：`J = ULift Bool`、`V p := twoChartV (p.1.down, p.2.down)`，`V(i,j)` 与 `V(j,i)` 只在**归约 match 后**相等，elab 的 defeq 检查（instances transparency）不触发，于是 `Category.id_comp` 的 `𝟙 X ≫ f` 合成对不上。
- 12:47:02 版把定理**删除**，写 TECHNICAL NOTE，给出三条修法：(a) 在通用文件里以 `V i j = V j i` 假设 + `eqToHom` 表述两索引 cocycle 引理；(b) 把 `twoChartV` 改成不在 pair 上 match 的定义；(c) 用 pullback iso 搬运 chart maps 而不在 `glue_condition` 等式里改写。
- `HullFermatGluingActual` 在 12:50:16 FAIL 后于 **12:52:54 DONE**（src 12:51:35）：`twoChartGlueDataOfIso`（W0≅W1 两 overlap 版，(b) 方向）已编译通过，**但仍没有用户级 cocycle 定理**（文件只有两组 GlueData 数据 + NOTE），所以“用户级等式未证”的结论不变。
- **结论**：`Y_n` 的 `GlueData` 本身仍是正确的（`t_fac`/`cocycle`/`f_open` 字段在结构里真证）；缺的是**用户级等式**，而它正是 `π` 的 `glueMorphisms` 输入。**任何文件不得再声称 cocycle “已证”**；引用 #135 必须写“GlueData 内部 cocycle 已证；用户级等式未证”。

### 4.46 【高·纪律】12:35–12:55 同文件高频 DONE→FAIL；per-file log 在 START 时被清空
- 本批实测 5 个文件在 4–8 分钟内翻转：`HullFermatGluing`(12:37:01→12:50:16)、`RadicalSupportFinal3`(12:41:47→12:49:10)、`OmegaFree`(12:47:03→12:51:30)、`TwoChartGluing`(12:43:15→12:45:45→12:48:27)、`SmoothLocalize`(12:43:16→12:47:06/12:50:16→12:51:31)。**“最后 DONE 时间”可能对应一个已不存在的源码**。
- 本批新事实：watchdog 在每次 START 时**清空**该文件的 per-file log（`URRootExtInstances`、`SmoothLocalize`、`OmegaFree` 均在 START 后变成 0 字节）。因此**FAIL 首错必须在 FAIL 之后、下次 START 之前读**；本批 `OmegaFree`(12:51:30) 与 `URThetaHull`(12:42:26) 的首错只能记“未取”。
- 规则（与 §0.5/§4.40 合并）：“最新状态”= `watchdog.log` 最后一条 START/DONE/FAIL，并把该时刻与源码 mtime 对照；DONE 只有 `olean mtime > 源码 mtime` 才算当前版本；axioms 只认**该 olean** 的 audit probe 或该 attempt 的 `#print` 末段。

### 4.47 【中·H-T/F7】RadicalSupport 当前红是机械错；tame 端已接近闭合
- `164:6`：`Module.Finite.of_surjective ?m.172 (Submodule.mkQ_surjective ?m.178)`——两个 metavariable 没 pin 到同一个 `Submodule.mkQ`。修法：`exact Module.Finite.of_surjective (Submodule.mkQ (maximalIdeal (Integers L))) (Submodule.mkQ_surjective _)`，或先 `letI` 固定 map。
- 旧版（12:41:47，olean 12:41:46）已给 `tame_count_differentIdeal_eq`（donor 实例化，三公理）与 `tame_localDifferentPaperOrder_le_one_of_tame`；12:53:12 版把失败的 `separable_residue` **删除**，`_glued` 改为以 hsep 为显式假设（`separable_fractionRing` 真证）→ 诚实部分装配；引用 `_glued` 时必须写“conditional on residue separability hsep + tameness he”。
- **F7 唯一数学缺口**：把 per-place tame count 组装成 `F7DiscTameBound.TameCount K p`（或直接在 RadicalSupport 内用 disc 公式装配）。因为 `differentContribution = v_p(disc)·log p / d`，`#133` 的 `v_p ≤ d` **恰好**给出 `f7_normalizedLogDisc_le` 的 `htame`。这是装配工作，不是 API 名问题。

### 4.48 【中·U-R】URRootExtension 的 mass 声明不实；URThetaPacketInstance 红是实例 diamond
- `Mzk1URRootExtensionActual` 的 docstring（15–18 行）称新增 `urRootMass_kummer`（instantiated from `Mzk1URRootMassActual`），但**全文件没有这个声明**（grep 只命中 docstring 一处）。引用该文件时写“order bridge only; mass 在 `URRootMassActual`/`ULThetaPacketActual`”。
- `URThetaPacketInstanceActual` `37:12` synthInstanceFailed `FiniteDimensional ℚ_[p] ↥(rootNormedExtension T b)`：`urRootExtensionNormedAlgebra` 是 `NormedAlgebra.restrictScalars`，`FiniteDimensional` 不会自动搬运。**12:53:05 版已 import `Mzk1URRootExtInstancesActual` 修好**（#143 补同一 Module 上的实例），#142 于 12:54:48 DONE、4 条三公理；`maxHeartbeats 4000000` 仍在，建议降到 1e6 复验。
- 该文件 `set_option maxHeartbeats 4000000`：记录（§4.26 同类），本批最慢/最脆文件之一。

### 4.49 【高·G-A/π】π 的最后一块输入到了；cocycle 是唯一剩下的 gate
- `fermatPiOverlap_condition`（#140，三公理）证明两条 chart map 在 overlap 上相等，正好是 `(fermatTwoChartGlueData n).openCover.glueMorphisms` 的兼容条件；`piChart0/piChartInf`（#113）与 P¹ glued（#107）都已是 A-局部。
- 剩下：(i) 把 §4.45 的用户级 cocycle 等式写成定理；(ii) `pi := …glueMorphisms …` 实例化；(iii) `π⁻¹(D_+(X0)) = D(x^n)` 与 `degree = n²`。
- 结论：π **不再是数学缺口**，而是 `GlueData` 在 `ULift Bool` 索引下的定义透明性/表述问题（§4.45 三条修法）。

### 4.50 【中·U-C/U-L】三套加权 hull 已并成两套；actual V/B 已接；残差 hstepVIII
- `ucWeightedHpkt_eq_ulHpkt = rfl`（#139）把 U-C 的 `ucWeightedHpkt` 与 U-L 的 `Hpkt` 证为同一函数；`ucActualV/ucActualB` 用真 per-packet 值与真 exceptional；`ucActualV_le_ucActualB` 由 donor `ulPacketVOfWitness_le_paperBound` 给出。
- 仍条件式：`ucWeightedPaper`（第三套 paper 界）仍是任意 `paper : ι → ℝ` + `hpaper` 假设；`hstepVIII` 是唯一分析残差。**不要记 U-C C1/C3/C4 accepted**。

### 4.51 【中·G-C】ProjectiveLineBoundary 的 0/∞ 命名反了（#145）
- `p1Zero := localChartInf.base '' chartPoint 0` = t-图的 t=0 = λ 图的**无穷远点** [1:0]；`p1Infinity := localChart0.base '' chartPoint 0` = λ=0 = [0:1]。注释却写 “0 = [0:1] … t-chart t=0”，自相矛盾。
- 对 `boundarySetGlued`（三点集合）无影响；但路线 §4.1 的 `ψ⁻¹(0) = D_T`、`φ_i` 的 Belyi 分支值需要正确的 0/∞ 标签——**下游引用前必须改名或改注释**。

### 4.52 【中·G-B】Ω：局部基 + 局部平凡到 A-局部；Ω 层/ω∞ 仍缺
- #131（D(x)、D(y) 上的基恒等式）与 #141（`Omega n ≃ₗ[B n] B n`、`omegaForm_is_basis`）合起来给出 A₀ 上 `Ω ≅ O`（路线 §3.1 (A4) 的仿射版本）。
- 仍缺：Away x/Away y 局部化层、scheme 层 `Ω_{Y_n/ℚ}`、`ω∞ = x^{n−3}ω₀` 的两图比较；`OmegaPresentationActual`(12:44:54 红) 与 `OmegaFreeActual`(12:51:30 红) 当前都不可引用，`Mzk1G1OmegaActual`（#70，B+）仍是唯一稳定引用点。

## 5. 给 Lead / 各 lane 的立即动作建议

1. **G-A（离出口最近的一次）**：把 `Mzk1G1FermatFiniteDegree2Actual`（rank n² / 环呈现）、`Mzk1G1FermatCurveClosed2Actual`（closed/proper + X₁^n ∈ (F,X₀,X₂)）、`Mzk1G1FermatSupportActual`（两图 finite/proper）记为 G-A **组件 gate**；**仍缺** `π : Y_n → P¹`、两图粘合实例化、scheme 层覆盖、smooth/整性、degree = n²。不要把 `Mzk1G1FermatSmoothChartActual` 当前的 `fermatA0EquivCurve` 当已证（依赖 sorryAx）。
2. **SmoothChart 修复**：见 §4.28 第一行（`Polynomial.C`、`AdjoinRoot.toRingHom_liftAlgHom`、`dvd_rfl` 前先 `rw [fermatU0Poly]`）。修好后本文件是 `A₀ ≃ ℚ[x,y]/(x^n+y^n−1)` 的真识别，可直接接 smooth（Jacobian 判据）。
3. **G-A 粘合实例化**（约 20 行）：用 `Mzk1HullFermatGluingActual.twoChartGlueData` 传 `Spec A₀`、`Spec A∞`、`Spec (Localization.Away …)` 与两个 open immersion，命名 `fermatGluing`；再补 `π`。
4. **G-B**：`OmegaActual` 只需 `pow_succ'` 方向修复；`FermatTransitionActual` 只剩 `1 * y^n = y^n`。这两条清掉后 Ω 过渡的标量/层版本才可引用。
5. **G-C**：`PsiChartMapsActual`（真 `Spec` 图）+ `PsiTwoChartCocycleActual`（真重叠恒等式）可以合成 ψ 的两图数据，但**还差** P¹ 粘合、`ψ*O(1) ≃ L`、`ψ^{-1}(0) = D_T`、以及把 `s1 = 1` 换掉。
6. **U-C/U-L**：先统一三套加权 hull（§4.22），再补 `θ_P5 ≤ H_pkt` 与 `Σ w_a B_a = κ(A−cL Q)−M` 的 actual producer；否则 `uc_c4_from_weighted` 永远只是条件式。
7. **L-H / G-K**：`KvCompact` 是唯一根因（`mem_primeFactors` 类型 + `Finset.not_mem_empty` + δ 界）；`RadicalSupport` 的 165 行 `.symm`；`FiniteDisjointBelyi` 删末尾 `#print`。`KvCompact` 不绿则 `D1Producer/LocalHeightCriterion/DisjointFamily` 继续级联红。
8. **Gate 纪律**：本批假红（§4.27）说明「FAIL 时间戳」本身不是证据；必须同时给「该文件当前源码 mtime 之后的那次尝试 + 首错 + 依赖 olean 是否 DONE」。任何引用 `fermatA0EquivCurve`、`uc_c3/uc_c4_from_weighted`、`twoChartGlueData`、`legendreJ*` 的 consumer 都要带 §2c/§4 的限制说明。
### 5b. batch 6 立即动作（快照 00:55 UTC）

1. **G-A 组件 gate 更新**：`SmoothIntegralActual`（R n 整性）与 `SmoothAttemptActual`（局部化模型 standard smooth）从 R 翻绿，判 **A-局部**；`Y_n` 两图粘合（#111）与 P¹ glued（#107）也是 A-局部。**G-A 出口仍缺**：(a) 局部化模型 ≅ `(R n)[1/x]`；(b) 用户级 cocycle 等式（当前 TODO）；(c) `π : Y_n → P¹` + degree n² + 原像；(d) `Y_n ≅ Proj(F)`。不要把 #113 的 `piChart0` 当 π。
2. **π 的下一步**（约 20–30 行）：用 #114 `chartMorphism_transition` 在 overlap 上证明 `piChart0 ≅ piChartInf`，再喂 `(fermatTwoChartGlueData n).openCover.glueMorphisms`；同步修 #124 `ProjectiveLinePiOverlapActual`（106:6 的 `↑(overlapUnit)⁻¹` 重写）。`ProjectiveLineBoundaryActual` 的 51:31 是子类型/`isPrime_span_X_sub_C` 参数问题。
3. **删除**：`Mzk1G1FermatCurveClosedActual`、`Mzk1HullFermatClosedSubschemeActual`（§4.25/§4.43，仍在 00:47:56 FAIL、sorryAx）。**修 copy bug 或删**：`Mzk1G1FermatSmoothGeomIntegralActual` 的 `end` 写错命名空间（200:0），且当前 192–198 全 unknown constant。
4. **G-B 仍红**：`OmegaBasisActual`（00:52:52）与 `OmegaPresentationActual`（00:47:59）本批无推进；Ω 基/展示的 scalar 与 baseChange 问题是下一步。`Mzk1G1OmegaActual`（#70，B+）仍可用。
5. **F7/H-T 最后装配**：`F7DiscSumActual` 主公式已 DONE（A-局部）；`F7DiscTameBoundActual` 的 `v_p(disc) ≤ finrank` 当前 FAIL（54:2 的 `Finset.sum_le_sum_of_subset_of_nonneg` 用法），修好后才能把 `TameCount` + `count_P=e_P−1` 接到 `differentContribution ≤ log p`。
6. **U-L**：`ULThetaPacketActual` 的 `ulThetaPacketV` 值公式 `V_a = −ord_p θ_j log p` 与 C1 界是下一个机械实例对齐任务；不要把它当 C1 已证。
7. **U-C/U-L 加权 hull**：`UCC3ProducerActual`（#105）DONE 只解决 prime-count 端；`uc_c3_from_weighted` 仍是 `hHpkt+hpaper` 条件式，三套加权 hull（§4.22）仍未统一。
8. **Gate 纪律（batch 6 版）**：本批新增"log 累积旧 attempt"活例（§4.40），且 `F7DiscProduct/F7DiscSum` 的成功 attempt 可以**无输出**（文件无 `#print`）——状态必须用 watchdog 的 DONE + olean mtime，而不是 log 尾部；axiom 必须用 Probe 6 或当前 attempt 的 `#print` 末段。

### 5c. batch 7 立即动作（快照 12:55 UTC）

1. **G-A π 收口**：cocycle 用户级等式三选一（§4.45），然后 `(fermatTwoChartGlueData n).openCover.glueMorphisms`（输入已由 #140 三公理给出），再写 `π⁻¹(D_+(X0)) = D(x^n)` 与 `degree = n²`。这是当前离 G-A 出口最近的一步。
2. **停止“DONE 后两分钟内再改源码”的循环**（§4.46）：本批 5 个文件在 DONE 后 4–8 分钟内被改红，导致 gate 表每秒都在过期。建议：一次落盘 → 等该文件自己的 attempt 出结果 → 再改。
3. **RadicalSupport**：`164:6` 的 `Module.Finite.of_surjective` 参数错误已被 12:53 版“删除 `separable_residue`、`_glued` 改为以 hsep 为显式假设”绕开（诚实部分装配）；下一步只剩把 per-place tame count 组装成 `TameCount`，F7 的 `differentContribution ≤ log p` 就闭合（#133 已给 `v_p ≤ d`）。
4. **URThetaPacketInstance（已完成）**：12:53:05 版 import `URRootExtInstancesActual` 后 **12:54:48 DONE**、4 条三公理，`V_a` 值公式落地；下一步把 `maxHeartbeats 4000000` 降到 1e6 复验，并考虑给 `_eq_neg_shift` 一个 C1 负项的正式出口名（§4.48）。
5. **删除 / 改名**：两个 closed 冗余文件（§4.25/#148/#149）；`FermatOverlapRingActual`（与 accepted `FermatOverlapActual.overlapSchemeIso` 同名混淆，#147）；`ProjectiveLineBoundary` 的 0/∞ 标签（§4.51）。`URThetaHullActual` 只是 4 条 donor re-export，转绿也不增加数学，可标记为 wrapper。
6. **Ω**：把 #131 + #141 的仿射 `Ω ≅ O` 升到 `Away x`/`Away y` 层，再写 scheme 层 `Ω_{Y_n/ℚ}` 与 `ω∞ = x^{n−3}ω₀` 比较（§4.52）。
7. **引用纪律（batch 7 版）**：任何 DONE 必须与 **olean mtime + 源码 mtime** 一起引用；`HullFermatGluing`(12:37)、`RadicalSupport`(12:41)、`OmegaFree`(12:47)、`TwoChartGluing`(12:43)、`SmoothLocalize`(12:43) 的旧 DONE 对本批快照时的源码**全部 STALE**。

## 6. 未运行 / 未覆盖（如实标注）

- 本报告 DONE/FAIL 全部来自 watchdog 实测（快照 **23:50 UTC**，表内最后事件 23:49:18）；**未运行** `lake env lean`，**未自起** watchdog，**未写** sorry/axiom。
- **Probe 4（本批唯一）**：`_ProbeGeom4Actual.lean`，两次排队 → DONE 23:41:15（30 定理）/ DONE **23:47:15**（36 定理，加 Support 6 条）；日志无 sorryAx。（注：Support 在 23:46:34 又改、23:49:04 重编 DONE，其自带 `#print` 8 条仍全为三公理、该日志 0 次 sorryAx；probe 的 Support 6 条对应 23:45:47 那一版。SmoothChart 在 23:49:18 以同一源码再 FAIL 一次。）
- **未运行（明确）**：
  - `Mzk1G1FermatSmoothChartActual` 的 `fermatA0EquivCurve` / `chart0RingEquiv` axioms（文件 FAIL，无法 import）；
  - `Mzk1G1B1B3ComponentActual` 当前版（stale + 级联 FAIL）；
  - `Mzk1G1LocalHeightCriterionActual` / `Mzk1G1DisjointFamilyActual` / `Mzk1G1D1ProducerActual` 只记首错，**未逐行读源码**；
  - U-R 全组（URPacket/URRootMass/URRootExtension/URThetaHull）、H-T / P8-P 组：本批无新 DONE，**未运行**语义审计；
  - `Mzk1UCHpktActual` 当前源码（23:40:20 之后）—— 本表 axioms/语义判定针对 23:34 olean 那一版；
  - `Mzk1G1FermatOverlapActual` 当前版（源码 23:42:18 之后）—— 只到末段 sorryAx 两条。
- 本批**已读源码**（语义层）：FiniteDegree2 / CurveClosed2 / SmoothChart / Support / HullFermatGluing / ProperFinal2 / OmegaTransition / UCHpkt / ULWeightedHull / ULPacketV / ULPacketHull / PsiTwoChartCocycle / PsiChartMaps / QHeight / FiniteDisjointBelyi / CurveClosed(新) / HullFermatClosedSubscheme / ProjClosedSubscheme4（donor）。
- olean 列 fresh 判据：`.olean` mtime > `.lean` mtime；stale = 源码在最后一次 DONE 后被改，该 DONE 不算数。
- 快照（23:50 UTC）之后的变化本表未审计（watchdog 仍在跑；本批已观察到 `SmoothChart` 23:49:18 再 FAIL、`Support` 23:49:04 重编 DONE）。

### 6b. batch 5 更新（快照 **00:16 UTC**；本节覆盖 §6 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_status.mjs … --err`（状态 + 首错）、`Get-Content dag/watchdog/watchdog.log` 的 START/DONE/FAIL 尾段、禁用项 grep（`sorry|admit|^axiom |PUnit|^True|toy|surrogate|maxHeartbeats`，共 30 个文件）、源码语义阅读（Omega / FermatOverlap / TwoChartGluing / FermatCurve / URPacket / LocalHeightCriterion / D1Producer / ProjectiveLineCharts / PsiChartInfCover / PsiChartToP1 / ProjectiveLineChartMaps / KvCompact / SmoothChart / SmoothIntegral / SmoothAttempt / FiniteDisjointBelyi / QHeight / F7TameOrder / P8Epsilon / P8Frey / ULPhiRealization / DisjointFamily / FermatPi 首 45 行）。
- **Probe 5**：`tmp/sheaf/xif/paper/_ProbeBatch5Actual.lean`，排队 `{"added":1,"total":72}`，**START 00:19:37 → DONE 00:20:18 (41s)**，8 条全部 [propext, Classical.choice, Quot.sound]、0 次 sorryAx（详见 §3「Probe 5」）。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom。
- **未运行 / 未覆盖（如实标注）**：
  - `Mzk1URRootMassActual`（296 行测度论）：仅 DONE + grep clean，**未逐行语义审计**。
  - `Mzk1G1FermatRadicalSupportActual`（182 行）、`Mzk1G1FermatRadicalSupportFinal3Actual`（新 FAIL 文件）：**未逐行读**；只取首错/DONE 与 grep。
  - `Mzk1UCC3ProducerActual`、`Mzk1G1OmegaPresentationActual`、`Mzk1G1OmegaBasisActual`、`Mzk1URThetaHullActual`、`Mzk1URRootExtensionActual`、`Mzk1G1FermatOverlapRingActual`、`Mzk1G1FermatCurveClosedActual`、`Mzk1HullFermatClosedSubschemeActual`：本批**只记 FAIL 时间**，未读源码、未取首错。
  - `Mzk1UCHpktActual` 当前源码（23:49:21 版）：**未重读**；§2c#45 的判定针对 23:34 olean 版。
  - `Mzk1G1DisjointFamilyActual` 当前源码（00:14:41 版）：**未编译**（olean 停在 00:08:42）。
  - `Mzk1P8FreyAssemblyActual` / `Mzk1P8EpsilonSelectionActual` / `Mzk1F7TameOrderActual` / `Mzk1G1D1ProducerActual` 等**无 `#print` 的文件**：axioms 列记 "—"，本批**未**用 probe 复算（P8Frey 原本在 Probe 5 初稿里，为守 8 条上限换成 `PsiChartToP1` 两条）。
  - U-R 全组（URPacket 除外）、G-K 递归构造、H-T 的 P8 端到端：**未运行**。
- **本批新发现并已写进正文的纪律**：§4.32（NO-OLEAN/一次 FAIL 不能直接判 red，PsiChartToP1 是活例）、§4.34（geom 三文件被反复重写，per-file log 被清空，首错随时过时）。
- 快照 00:16 UTC 之后（00:18:44 起的新 batch、以及 `_ProbeBatch5Actual` 的结果以外的一切变化）**未审计**。

### 6c. batch 6 更新（快照 **00:55 UTC**；本节覆盖 §6/§6b 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_status.mjs … --err`（对 #105–#129 共 25 个文件逐个取最后 START/DONE/FAIL 与 FAIL 首错；DONE 文件另看 log 末段与 `sorryAx` 计数）、`Get-Content dag/watchdog/watchdog.log` 的 00:35–00:55 尾段、禁用项 grep（18 个源文件，`sorry|admit|^axiom |PUnit|^True|surrogate|toy|maxHeartbeats`；仅 3 个 geom 文件的 `maxHeartbeats 800000` 与注释命中）、源码语义阅读（SmoothIntegral / SmoothAttempt / TwoChartGluing / HullFermatGluing / FermatPi / ProjectiveLineTransition / F7DiscProduct / F7DiscSum / RadicalSupportFinal3 / ULThetaPacket / ProjectiveLineGlued / UCC3Producer / DisjointFamily / FiniteDisjointBelyi / 8 个 Lead 文件 / OmegaBasis / OmegaPresentation / FermatCurveClosed / HullFermatClosedSubscheme / SmoothGeomIntegral / F7DiscTameBound / ProjectiveLinePiOverlap 的报错段）。
- **Probe 6**：`tmp/sheaf/xif/paper/_ProbeBatch6Actual.lean`，排队 `{"added":1,"total":84}`，**START 00:50:17.045Z → DONE 00:51:17.108Z (60s)**，8 条全部 [propext, Classical.choice, Quot.sound]、0 次 sorryAx（详见 §3「Probe 6」）。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn** teammate。
- **未运行 / 未覆盖（如实标注）**：
  - `Mzk1G1ProjectiveLineBoundaryActual` / `Mzk1G1ProjectiveLinePiOverlapActual` / `Mzk1G1OmegaPresentationActual` / `Mzk1G1OmegaBasisActual`：只取首错 + 报错段，**未逐行语义审计**；`OmegaBasis` 的 sorryAx 只来自 `#print` 末段。
  - `Mzk1G1FermatSmoothGeomIntegralActual` / `Mzk1F7DiscTameBoundActual`：全文读过，但只按 FAIL 首错判 R，**未做语义层证明审计**（当前也没有 DONE 可审）。
  - `Mzk1URThetaHullActual`：只确认级联缺 `URRootExtension.olean`，**未读源码**；`Mzk1URRootExtensionActual` 只读报错段（180–194），未逐行审计。
  - `Mzk1HullFermatGluingActual` 当前版 `twoChartGlueData`（def 级）：**未用 probe 复算**（文件无 `#print`；Probe 6 只经 `TwoChartGluing` import 使用它并复算 chart open immersion）。
  - `Mzk1G1ProjectiveLineGluedActual`、`Mzk1UCC3ProducerActual`、`Mzk1G1DisjointFamilyActual`、`Mzk1G1FiniteDisjointBelyiActual`：axioms 只有文件自带 `#print` (L)，**未审计 probe 独立复算**。
  - Lead 8 文件：公理来自 Lead 自建 `_ProbeP8LeadActual`（DONE 00:46:53，L*，**非 audit 独立**）；本批 audit 独立复算只覆盖 `F7DiscSumActual.disc_factorization_eq_multiset_sum` 与 `RadicalSupportFinal3` 的 tame 桥。其余 6 条（P8Epsilon/P8Frey/F7TameOrder/P6HConst/F7DiscLocalGlobal/F7DiscPrimeFactor）**未 audit-probe**。
  - `Mzk1G1FermatPiActual.piChart0` 只复算 def 级三公理；`piChartInf` 未单独 probe（同构型）。
  - U-R 全组（URPacket/URRootMass 除外）、G-K 递归构造、H-T/P8 端到端、G-B 的 Ω 基/展示：**未运行**语义审计。
- **快照 00:55 UTC 之后**：watchdog 仍在跑（本批快照时 pending=3，正在重试 `FermatOverlapRingActual` / `URRootExtensionActual` / `URThetaHullActual`）；00:55 之后的任何 DONE/FAIL 本表**未审计**。
- **本批新发现并已写进正文的纪律**：§4.40（成功 attempt 可以无输出 + log 累积旧 attempt 错误，F7Product/F7Sum/TwoChart 是活例）、§4.43（copy 文件命名空间关闭写错）、§4.38（旧 Probe 结果随源码改写变 STALE）。
- **00:53–00:55 的重复重试（本表快照前最后一次）**：`ProjectiveLinePiOverlapActual` 00:53:40 仍 FAIL、`FermatOverlapRingActual` 00:54:35 仍 FAIL、`URThetaHullActual` 00:54:45 仍 FAIL（仍为级联）；`URRootExtensionActual` 00:54:00 重试中。这些重试不改变 §2e 的 R 判定。


### 6d. batch 7 更新（快照 **12:55 UTC = 20:55 CST**；本节覆盖 §6/§6b/§6c 的旧结论，旧文保留）

- **已运行（本批）**：
  - `node tools/wd_status.mjs … --err`：对 18 个文件逐个取最后 START/DONE/FAIL；对 FAIL 读首错段（`OmegaPresentation`/`FermatOverlapRing`/两个 closed/`ProjectiveLineBoundary`/`URThetaPacketInstance`/`RadicalSupport`/`TwoChartGluing`/`HullFermatGluing`）。
  - `Get-Content dag/watchdog/watchdog.log` 的 12:34–12:52 段（提取全部 START/DONE/FAIL/RETRY）+ olean/源码 mtime 对照（18 个文件）。
  - 禁用项 grep（`sorry|admit\b|^axiom |PUnit|^True|surrogate|toy|maxHeartbeats`，14 个源文件）：唯一命中是注释与两条 `maxHeartbeats`（`SmoothLocalize 800000`、`URThetaPacketInstance 4000000`）。
  - 源码语义阅读（全读或关键段）：URRootExtension / OmegaBasis / ULHpkt / F7DiscTameBound / SmoothLocalize / TwoChartGluing（含 TECHNICAL NOTE）/ HullFermatGluing（新旧两版结构）/ DisjointFamily / RadicalSupportFinal3 / UCHpkt / ProjectiveLinePiOverlap / OmegaFree（12:47 版）/ OmegaPresentation 报错段 / URThetaHull / URThetaPacketInstance / ProjectiveLineBoundary / ProjectiveLineTransition（#140 的目标类型）。
- **Probe 7**：`tmp/sheaf/xif/paper/_ProbeBatch7Actual.lean`，`wd_add` → `{"added":1,"total":92}`；三次 attempt（两次 unknown-constant 真实失败）后 **START 12:50:56 → DONE 12:51:54（58s）**，8 条全部 [propext, Classical.choice, Quot.sound]、0 次 sorryAx（详见 §3「Probe 7」）。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未运行 / 未覆盖（如实标注）**：
  - `Mzk1URRootExtInstancesActual`（#143，92 行）：只确认 DONE + grep clean，**未语义审计**两条 mass 恒等式。
  - `Mzk1HullFermatGluingActual` 当前版（12:51:35）与 `Mzk1G1OmegaFreeActual` 当前版（12:51:02）：**首错未取**（per-file log 被下一次 START 清空）；对它们的判定只基于“源码比最后 DONE 新 + FAIL 时间戳”。
  - `Mzk1URThetaHullActual`：无 per-file log（从未生成），首错未取；只按 import 时间窗判级联 + 读源码确认是 4 条 re-export。
  - `Mzk1G1OmegaPresentationActual`：只读报错段，**未逐行**读 190 行源码。
  - `Mzk1G1ProjectiveLineBoundaryActual`、`Mzk1G1DisjointFamilyActual`：有文件自带 `#print`，**未用 audit probe 独立复算**。
  - `Mzk1G1FermatSmoothLocalizeActual` 的 `modelEval_rel_zero/_one`：**未 probe**（12:43 olean 不含、当前源码 12:51:31 才 DONE）。
  - U-R 全组（URThetaPacketInstance/URRootExtInstances 除外）、G-K 的 B1 producer、P8 端到端：**未运行**。
- **快照 12:53 UTC 之后**：watchdog 仍在跑（`HullFermatGluing` / `RadicalSupport` / `OmegaFree` / `URThetaPacketInstance` / `OmegaPresentation` 仍在被改写/重试）；12:53 之后的任何 DONE/FAIL 本表**未审计**。
- **本批新发现并已写进正文的纪律**：§4.45（用户级 cocycle 一次真实尝试→失败→撤回，Probe 的 unknown constant 是独立证据）、§4.46（per-file log 在 START 时清空，FAIL 首错必须立刻读）。

## 2g. 本批 batch 8 gate 表（快照 **13:06 UTC = 21:06 CST**；**新增 #150–#168**，含 RETIRED / closed-port 行）

grep 列 = 大小写敏感扫描 `sorry|admit\b|^axiom |PUnit|^True|surrogate|toy|maxHeartbeats`（本批 18 个文件；命中仅为注释与 `maxHeartbeats`，已人工排除）。axioms 列：(P) = 本批 `_ProbeBatch8Actual.lean` 独立复算；(L) = 文件自带 `#print` 的**当前 attempt 日志末段**；— = 无 `#print` 或未 probe。olean 列 fresh = olean mtime > 源码 mtime；**STALE = 最后一次 DONE 之后源码又被改**。

**本批纪律（新增）**：13:00:24 UTC 起 `dag/watchdog/extra-targets.txt` 已删除 4 个 RETIRED 文件与全部 `TauCetiPort/**`；因此 12:55:05 START / 12:55:46–51 FAIL 是「移除前最后一次 attempt」的尾巴，**不构成新回归**。13:00–13:06 之间 watchdog 仍在高频改写 6 个文件（`SmoothLocalize`/`URThetaPacketInstance`/`RadicalSupportFinal3`/`TwoChartGluingIso`/`PsiXi`/`OmegaFree`）；下表取 13:05:51 UTC 前最后一次 START/DONE/FAIL，并把该时刻与源码 mtime 对照。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 150 | Mzk1GlueMorphismActual | G-A/π 通用粘合态射 | **DONE** | 12:59:38 | fresh（src 12:58:28） | clean | 三公理 (P：`glueMorphism`、`glueMorphism_ι`；`glueMorphisms_compat` L+文件) | **A-局部（generic，本批关键工具）**：`glueMorphisms_compat` 从 overlap 层等式 `D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j` 推出 `pullback.fst ≫ f i = pullback.snd ≫ f j`，`glueMorphism := D.openCover.glueMorphisms f (compat …)`，`glueMorphism_ι` 为限制等式。未接 Fermat，但把「用户级 cocycle ⇒ π 的 glueMorphisms 输入」变成定理。 |
| 151 | Mzk1G1DisjointFamilyActual（覆盖 §2f#137） | G-K | **DONE** | 12:58:25 | fresh（src 12:58:10） | clean | 三公理 (P：`hasGluedBelyiFamily_of_b1`、`exists_goodChain`；L 另 5 条) | **B+**：新增 `GKCompactInput`（compact tuple space + `delta_cover`）、`GKCompactInput.exists_delta0`（用 `uniform_positive_away`）、`GKData.ofCompactInput`（量词顺序：d,V,family,δ₀,K_V 先固定）、`gk_boundary_avoids_points`、`gk_localDomain_avoids`、`B1FiniteProducer` 及适配 `b1StepProducer_of_finite`。**接口仍无 inhabitant**：`UniversalLocalFieldExists`、`GKCompactInput`、`B1StepProducer`/`B1FiniteProducer`（文件明标 NO INHABITANT）。 |
| 152 | Mzk1F7TameCountActual（新文件） | F7 tame count | **DONE** | 13:02:26（12:56:55 / 13:00:56 曾 FAIL） | fresh（src 13:01:27） | clean | 三公理 (P：`disc_factorization_le_finrank_of_tameRamifiedAt`) | **A-局部/B+（F7 的 TameCount 缺口闭合）**：`TameRamifiedAt` = 每个 P\|p 上「剩余域可分 + e 在 ℤ/p 中可逆」；`tameCount_of_tameRamifiedAt` 用 donor `count_differentIdeal_eq_of_tame` 得 `count 𝔇 P = e−1`（`TameCount`），再 `disc_factorization_le_finrank_of_tame` 得 `v_p(\|disc K\|) ≤ [K:ℚ]`。此前两次 FAIL 是 `hsep`/`he` 顺序 + `DecidableEq` 实例错（机械）。**注意：结论 conditional on `TameRamifiedAt`；不含全局 conductor/几何结论。** |
| 153 | Mzk1G1FermatSmoothLocalizeActual（grace，覆盖 §2f#134） | G-A 局部化识别 | **DONE 13:03:49，但 STALE**（src 13:04:46、13:05:46 又 START） | 13:03:49 | fresh（对 13:01:59 源码） | clean（`maxHeartbeats 800000`） | L：当前 attempt 全部三公理，含 `modelEval_rel_zero`、`modelEval_rel_one`、`modelToLocalize_X0/X1/X2`、`localizeToModel_invSelf` | **A-局部/B（双向，仍缺互逆）**：本版新增**反向** `modelToLocalize : Model n →+* Localization.Away (chartR n)`（`Ideal.Quotient.lift` + `modelAssign`）与三条 X 取值；`localizeToModel`（正向）与 `localizeToModel_invSelf` 在位。**两条复合恒等（`localizeToModel ∘ modelToLocalize = id`、反向）仍未写** → A₀ 局部化 ≅ 模型尚未证。13:04:46 又改，DONE 不可引用。 |
| 154 | Mzk1URThetaHullActual（覆盖 §2f#144） | U-R theta hull | **DONE** | 13:02:55 | fresh（src 13:01:30） | clean | 三公理 (P：`ur_negM_le_Htheta`；L 另 3 条) | **B / wrapper**：4 条全是 donor re-export（`p6_neg_M_le_HTheta2`、`actualPerB_inequality`、`actualTargetMagnitude_actual`、`urRootTheta_log_norm_eq_neg_shift`）；无新数学。`θ_P5 ≤ H_pkt` 仍无 producer（文件注释自认 consumer 直接 import donor）。转绿**不增加**数学（§5c#5 的 wrapper 结论不变）。 |
| 155 | Mzk1URThetaPacketInstanceActual（覆盖 §2f#142） | U-L V_a / C1 | **DONE 13:02:54，但 STALE**（src 13:05:02；13:05:46 重编） | 13:02:54 | stale | clean（`maxHeartbeats 4000000`） | L：4 条三公理（对 13:02 olean） | **B+/A-局部（当前版未编译）**：12:53 版的 `ulThetaPacketV_eq_log_norm/_eq_neg_order/_eq_neg_shift` 仍在；新增 `ulThetaPacketV_le_paperC1_uncond`（去掉了 `_le_paperC1` 的非负和假设，改为用 `ulDifferentSum_nonneg`/`ulExceptionalSum_nonneg`）。`maxHeartbeats 4e6` 仍在（§4.48）。 |
| 156 | Mzk1ULThetaPacketActual | U-L per-b | **DONE** | 13:02:56 | fresh（src 13:00:39） | clean | 三公理 (P：`ulDifferentSum_nonneg`) | **B**：per-b 对象与 `ulNormalizedLogMass_smul` 保持；本文件不含 V_a 值公式（在 #155）。 |
| 157 | Mzk1ULHpktActual（覆盖 §2f#132） | U-L Hpkt | **DONE** | 13:04:14 | fresh（src 13:03:08） | clean | L：7 条三公理 | **B**：`Hpkt w V = Σ w_a V_a`（def）+ `ul_hpaper_of_stepVIII` 分析归约；`w V B` 仍任意，未接 `packetVActual`/`ulDivisorWeight`，`hstepVIII` 是假设（同 §2f#132）。 |
| 158 | Mzk1G1ProjectiveLineBoundaryActual（覆盖 §2f#145） | G-C P¹ boundary | **DONE** | 13:02:21 | fresh（src 13:00:36） | clean | L：5 条 `#print`（未单独 probe） | **A-局部（点集层），§4.51 已作废**：本版把 0/∞ 标签改对了——`p1Zero = localChart0 '' V(X)`（λ=0）、`p1Infinity = localChartInf '' V(X)`（t=0 = [1:0]）；`isPrime_span_X_sub_C`、三条非空、`boundarySetGlued`、`boundaryPreimageGlued` 真。 |
| 159 | Mzk1G1FermatRadicalSupportFinal3Actual（覆盖 §2f#138） | H-T tame 桥 | **DONE 12:58:54 → FAIL 13:04:16（源码 13:02:22 又改；13:05:46 重试中）** | 13:04:16 | **stale**（olean 12:58:53） | clean | 12:41 版三公理（Probe 6）；当前版无输出 | **R 当前 / B+ 旧版**：12:58:54 的 DONE 只对应 12:56:34 源码；13:02:22 新增内容后 FAIL，**per-file log 在 13:05:46 START 时被清空，首错未取**。可引用版本仍是 12:41 版（olean 12:41:46）的 `tame_localDifferentPaperOrder_le_one_of_tame`；`_glued` 需 hsep 显式假设（§4.47 不变）。 |
| 160 | Mzk1HullFermatGluingActual（覆盖 §2f#136） | G-A generic glue | **DONE** | 13:01:16 | fresh（src 13:00:05） | clean | 旧版 def 级三公理（Probe 4）；当前版无 `#print` | **A-局部（generic 两变体）**：`twoChartGlueData`（W 同、t=𝟙）与 `twoChartGlueDataOfIso`（W0≅W1、t 由 e 给出）都是真 `Scheme.GlueData`（`t_fac`/`cocycle`/`f_open` 真证）。**仍无用户级 cocycle 定理**（§4.45 不变；用户级归约见 #162/#150）。 |
| 161 | Mzk1G1FermatTwoChartGluingIsoActual（新文件） | G-A 两 overlap 粘合 | **DONE** | 13:05:05（12:58:22 / 13:02:22 曾 FAIL） | fresh（src 13:04:15） | clean | 无 `#print` | **A-局部**：`fermatTwoChartGlueDataOfIso n` = `twoChartGlueDataOfIso` 实例化（W0=`Spec Overlap0`、W1=`Spec OverlapInf`、t 用 `overlapSchemeIso n`），`fermatCurveSchemeIso` = glued，两条 chart open immersion 由 `ι_isOpenImmersion`。这是 §4.45 修法 (b)/(c) 的落地。**⚠ 与同名 `fermatCurveScheme`（#135/#160 的等 overlap 模型）是两套 Y_n**，引用须写清模型。 |
| 162 | Mzk1G1PsiXiActual（新文件） | G-A/π ψ/π 粘合 | **FAIL** | 13:05:06 | none | clean | `overlapToChart0_chartMorphismInf`、`overlapToChartInf_chartMorphism0`、`xi` = **sorryAx**；`fermatCurveGlueMorphism` 三公理 | **R（一修即绿）**：首错 `35:42`/`55:38` **Ambiguous term `overlapToChart0`/`overlapToChartInf`**（与 `Mzk1G1ProjectiveLineGluedActual` 同名；需限定 `Mzk1G1FermatOverlapActual.overlapToChart0`），连带 `34:87`/`54:67` 两条未关目标。**真增量**：`fermatCurveGlueMorphism`（三公理）把用户级等式 `h` 作为输入证出 `fermatTwoChartGlueData n` 的 GlueData 兼容条件；`xi : fermatCurveScheme n ⟶ projectiveLineGlued` 已写出（`chartMorphismInf x0` / `chartMorphism0 r1` + `chartMorphism_transition`），但依赖上述 sorry → **xi 当前不可引用**。 |
| 163 | Mzk1G1OmegaFreeActual（覆盖 §2f#141） | G-B Ω≅O | **DONE** | 13:05:09（12:51:30 / 13:02:28 曾 FAIL 且 sorryAx） | fresh（src 13:03:26） | clean | L：当前 attempt 0 次 sorryAx；`span_dX_dY`、`omegaForm_is_basis` 均三公理 | **A-局部（仿射 Ω≅O，rev2 修好）**：`dPoly`（D(X0)=nX1^{n−1}, D(X1)=−nX0^{n−1}）、`dPoly_fermat=0`、`dPoly_kills_ideal`、商上 `D0`、`Psi`/`Phi`、`Psi_omegaForm = n`、`Phi` 单/满 ⇒ `omegaEquivO : Ω n ≃ₗ[B n] B n`、`omegaForm_is_basis`（`1 ≤ n`）。13:02:28 的 sorryAx（`span_dX_dY` 的 `restrictScalars` 目标）已被 13:03:26 版修掉。仍缺 Away x/Away y 局部化层与 ω∞ 比较（§4.52 部分作废）。 |
| 164 | **RETIRED** Mzk1G1FermatCurveClosedActual | G-A closed（冗余） | **RETIRED**（源码保留） | 最后事件 12:55:46 FAIL（移除前） | none | clean | 两定理 sorryAx（§4.25） | **RETIRED / 无 consumer**（见下表）。删除建议已被 Lead 的「保留源码+研究历史」取代；**不得引用**。 |
| 165 | **RETIRED** Mzk1HullFermatClosedSubschemeActual | G-A closed（冗余） | **RETIRED**（源码保留） | 12:55:46 FAIL（移除前） | none | clean | 两定理 sorryAx（§4.25） | **RETIRED / 无 consumer**。同上。 |
| 166 | **RETIRED** Mzk1G1OmegaPresentationActual | G-B 展示 | **RETIRED**（源码保留） | 12:55:49 FAIL（移除前） | none | clean | —（从未编译成功） | **RETIRED / 无 consumer**。G-B 展示层仍无可用文件；Ω 的稳定引用点是 #163（affine）+ #70（OmegaActual，B+）。 |
| 167 | **RETIRED** Mzk1G1FermatOverlapRingActual | G-A overlap ring（重复实现） | **RETIRED**（源码保留） | 12:55:51 FAIL（移除前） | none | clean | `beta_alpha`/`overlapEquiv`/`overlapSchemeIso` = sorryAx | **RETIRED / 无 consumer**：accepted 的 `Mzk1G1FermatOverlapActual.overlapSchemeIso`（A-局部）是唯一引用点；本文件的同名 `overlapSchemeIso` 不再并存于白名单，混淆风险解除。 |
| 168 | **RETIRED (closed-port)** TauCetiPort/** （`tmp/sheaf/xif/paper/TauCetiPort/` 全部） | port 试验 | **RETIRED / closed-port (b)** | 最后事件 12:56:30 START → 12:56:59 FAIL（2 个文件，移除前） | — | — | — | **不得当活动目标**。见下表 consumer 检查；port 试验结案 (b)，保留源码与研究历史。 |

### 2g-1 RETIRED 白名单移除与 consumer 检查（本批 Lead 指示 1、2）

- **移除时间**：`dag/watchdog/extra-targets.txt` 在 13:00:24 UTC（本批首次读取时的 mtime）已不含下列 4 个文件与全部 `TauCetiPort/**`；13:06 版 targets=90（含本批 probe）。13:00:24 之后 watchdog.log 中**没有**这 4 个文件与 TauCetiPort 的任何 START/DONE/FAIL。
- **consumer 检查（全 `tmp/sheaf/xif/paper` 递归，`import tmp.sheaf.xif.paper.<模块>`；另做了一遍排除 `TauCetiPort` 自身的 `tmp`+`LeanFormal` 全仓扫描）**：
  - `Mzk1G1FermatOverlapRingActual`：**0 处 import**（仅自身 namespace 声明 2 行）。
  - `Mzk1G1FermatCurveClosedActual`：**0 处 import**（仅自身 2 行）。
  - `Mzk1HullFermatClosedSubschemeActual`：**0 处 import**（仅自身 2 行）。
  - `Mzk1G1OmegaPresentationActual`：**0 处 import**（仅自身 2 行）。
  - `TauCetiPort`：**1 处外部 consumer** —— `tmp/sheaf/xif/paper/Mzk1TauCetiHaarScalingBridgeActual.lean:1`：`import tmp.sheaf.xif.paper.TauCetiPort.TauCeti.MeasureTheory.Group.LocalFieldScaling`。该 bridge **不在白名单、`.lake/build/lib/lean/.../Mzk1TauCetiHaarScalingBridgeActual.olean` 不存在（src 2026-11-14，从未编译成功）**，且无其它文件 import 它 → 属**休眠 consumer**，不会把 TauCetiPort 拉回活动队列；但若将来有人 import 该 bridge，会因 port 已 RETIRED 而红。建议 Lead 决定：删除该 bridge，或把它改写成不依赖 port 的版本。
- 附：12:56:30 的 2 个 TauCetiPort START（`RingTheory/Valuation/ValuativeRel/Extension`、`NumberTheory/LocalField/NormalizedValuation`）发生在 13:00:24 移除**之前**，是该 port 在旧白名单里的最后残留，不作为活动目标。

## 3b. Probe 8（本批 batch 8）：`tmp/sheaf/xif/paper/_ProbeBatch8Actual.lean`

- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch8Actual.lean` → `{"added":1,"total":90}`。
- watchdog：**START 2026-11-16T13:04:31.418Z → DONE 13:05:31.808Z（60s）**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch8Actual.lean.log`（1070 B，本 attempt **0 次 error、0 次 sorryAx**）。
- 8 条独立复算（原样抄录，**全部 [propext, Classical.choice, Quot.sound]**）：

| 定理（namespace 见文件） | axioms | 覆盖行 |
|---|---|---|
| `Mzk1GlueMorphismActual.glueMorphism`（def） | [propext, Classical.choice, Quot.sound] | #150 |
| `Mzk1GlueMorphismActual.glueMorphism_ι` | [propext, Classical.choice, Quot.sound] | #150 |
| `G1DisjointFamilyActual.hasGluedBelyiFamily_of_b1` | [propext, Classical.choice, Quot.sound] | #151 |
| `G1DisjointFamilyActual.exists_goodChain` | [propext, Classical.choice, Quot.sound] | #151 |
| `Mzk1F7TameCountActual.disc_factorization_le_finrank_of_tameRamifiedAt` | [propext, Classical.choice, Quot.sound] | #152 |
| `Mzk1URThetaHullActual.ur_negM_le_Htheta` | [propext, Classical.choice, Quot.sound] | #154 |
| `Mzk1G1ProjectiveLineBoundaryActual.isPrime_span_X_sub_C` | [propext, Classical.choice, Quot.sound] | #158 |
| `Mzk1ULThetaPacketActual.ulDifferentSum_nonneg` | [propext, Classical.choice, Quot.sound] | #156 |

- **未覆盖（明确未运行）**：`Mzk1GlueMorphismActual.glueMorphisms_compat`（未单独 probe，但 `glueMorphism` 的 def 三公理已蕴含其干净）；`Mzk1G1FermatSmoothLocalizeActual`（13:03:49 DONE 后 13:04:46 又改，probe 排队时不可稳定引用，**未 probe**；其当前 attempt 的 `#print` 逐条三公理，属 (L)）；`Mzk1G1PsiXiActual` 的 `xi`（红，不可 probe）；`Mzk1G1OmegaFreeActual`、`Mzk1G1FermatTwoChartGluingIsoActual`（DONE 时间晚于 probe 排队，未覆盖，仅文件自带 `#print` / 无 `#print`）。
- 结论：**kernel 层本批新 DONE 的 8 条关键定理没有伪证**；风险全在语义层与「DONE 后又被改写」（#153/#155/#159/#162）。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 8 续）

### 4.53 【高·G-A/π】用户级 cocycle 已被**归约**为 overlap 层等式；π 只差一个名字歧义
- `Mzk1GlueMorphismActual`（#150，DONE 12:59:38，Probe 8 三公理）：`glueMorphisms_compat` 把 overlap 层等式 `h : D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j` 转成 `openCover.glueMorphisms` 需要的 pullback 层等式；`glueMorphism` 是 `D.openCover.glueMorphisms f (compat f h)`，`glueMorphism_ι` 给出 `D.ι i ≫ glueMorphism f h = f i`。这是**通用**构造（任意 `Scheme.GlueData`）。
- `Mzk1G1PsiXiActual`（#162，FAIL 13:05:06）：`fermatCurveGlueMorphism`（三公理）以 `h : overlapToChart0 n ≫ f0 = overlapToChartInf n ≫ f1` 为**输入**，证出 `fermatTwoChartGlueData n` 的 GlueData 兼容条件；即**用户级 cocycle 等式被形式化为 glueMorphisms 的唯一输入**，而不再是空白 TODO。`xi : fermatCurveScheme n ⟶ projectiveLineGlued` 已完全写出（`chartMorphismInf x0` / `chartMorphism0 r1` + `chartMorphism_transition`）。
- **但 xi 当前是 sorryAx**：`overlapToChart0_chartMorphismInf`（35:42）与 `overlapToChartInf_chartMorphism0`（55:38）因 `overlapToChart0`/`overlapToChartInf` **与 `Mzk1G1ProjectiveLineGluedActual` 同名而 Ambiguous term**，另有 34:87/54:67 两条未关目标（`Spec.map_comp` 方向）。`#print axioms xi` = [propext, **sorryAx**, choice, Quot.sound] → **禁止引用 xi**。
- **纪律**：任何文件不得再称 cocycle「已证」。正确表述：**「GlueData 内部 cocycle 字段已证；用户级等式 h 仍未证，但已归约为 `glueMorphisms` 的唯一输入；`xi` 的两个 transport 引理因名字歧义落 sorryAx，未证」**。修法是机械限定名 + 两条 `Spec.map_comp` 目标，修好后 G-A 的「Y_n → P¹」应可直接落地（degree/原像仍需另写）。

### 4.54 【中·G-A】SmoothLocalize 双向映射已齐，但**两条互逆恒等仍缺**（#153）
- 13:03:49 DONE 的版本（src 13:01:59）新增反向 `modelToLocalize : Model n →+* Localization.Away (chartR n)`（`Ideal.Quotient.lift` 到 `modelAssign`）与 `modelToLocalize_X0/X1/X2`，加上 12:51 版的 `localizeToModel`（`IsLocalization.Away.lift`）、`modelEval_rel_zero/_one`、`localizeToModel_invSelf`。当前 attempt 的 `#print` 逐条三公理。
- **仍缺**：`localizeToModel (modelToLocalize m) = m` 与 `modelToLocalize (localizeToModel a) = a`（两条复合恒等），即 `(R n)[1/(n x^{n−1})] ≅ fermatModelRing n` 尚未证。§4.36 的缺口 (i) 从「反向未写」缩小到「两条 round-trip」。
- 该文件在 13:04:46 又被改、13:05:46 重编 → 13:03:49 的 DONE 对本批快照时的源码 **STALE**；引用必须核对 olean（当前 olean 仍是 13:03:49 版）。

### 4.55 【高·H-T/F7】TameCount producer 闭合：`TameRamifiedAt ⇒ v_p(disc) ≤ [K:ℚ]`（#152）
- `Mzk1F7TameCountActual`（DONE 13:02:26）定义 `TameRamifiedAt K p` = 对每个 `P | p`（`absNorm (under P) = p`）有「`𝒪_K/P` 在 `ℤ/p` 上可分」且「`e_P` 在 `ℤ/p` 中非零」；`tameCount_of_tameRamifiedAt` 用 donor `count_differentIdeal_eq_of_tame` 得 `TameCount K p`（`count 𝔇 P = e_P − 1`），再经 #133 的 `disc_factorization_le_finrank_of_tame` 得 `(disc K).natAbs.factorization p ≤ finrank ℚ K`。
- 这闭合了 §4.47/§5c#3 的「唯一数学缺口」：per-place tame count → `TameCount` 的组装已有。**但**：结论条件在 `TameRamifiedAt`（诚实的标准 tame 假设，不是把结论当假设）；**不**含 `differentContribution ≤ log p` 的最终归一化陈述（那由 RadicalSupport 的 `f7_normalizedLogDisc_le` 侧接），且 RadicalSupportFinal3 当前又红（#159）。
- 纪律：引用 F7 时写「local-global 公式 DONE；`TameCount` 已由 `TameRamifiedAt` 生产；`differentContribution ≤ log p` 仍取决于 RadicalSupport 当前版转绿」。

### 4.56 【中·G-A】两套 `Y_n` 模型并存：`fermatCurveScheme` 与 `fermatCurveSchemeIso`（#160/#161）
- `Mzk1G1FermatTwoChartGluingIsoActual`（DONE 13:05:05）用 `twoChartGlueDataOfIso`（W0=`Spec Overlap0`、W1=`Spec OverlapInf`、transition = `overlapSchemeIso n`）得到 `fermatCurveSchemeIso n`，两条 chart open immersion 真。这对应 §4.45 修法 (b)/(c)，**结构上避免了 `t = 𝟙` + `V(i,j)=V(j,i)` 的 defeq 问题**。
- 但 G-A 现有两套 glued 模型：`Mzk1G1FermatTwoChartGluingActual.fermatCurveScheme`（等 overlap，t=𝟙）与 `fermatCurveSchemeIso`（双 overlap）。`xi` 用的是**前者**；两条 chart map 的 transport 又引用了 `ProjectiveLineGlued` 的同名 `overlapToChart0/Inf`。**下游引用必须写清是哪一套模型**，否则会出现「同一个 `Y_n` 有两种不兼容陈述」的风险。
- 另：`fermatTwoChartGlueDataOfIso`/`twoChartGlueDataOfIso` 的 `t` 由 iso 给出后，`t_fac`/`cocycle` 字段虽真证，但**用户级 overlap 等式仍没有任何文件陈述**；#150 的 `glueMorphisms_compat` 恰好是这条缺失陈述的通用替代。

### 4.57 【中·G-B】Ω 仿射层闭合（OmegaFree 转绿），展示层 RETIRED
- `Mzk1G1OmegaFreeActual`（#163，DONE 13:05:09）rev2 把 13:02:28 的 sorryAx 清掉：`dPoly`、`dPoly_fermat = 0`、`dPoly_kills_ideal`、商上 `D0`、`Psi(ω₀) = n`、`Phi` 单/满、`omegaEquivO : Ω n ≃ₗ[B n] B n`、`omegaForm_is_basis`（`1 ≤ n`），当前 attempt `#print` 0 次 sorryAx 且全部三公理。加上 #131（D(x)/D(y) 基恒等式），**A₀ 上 `Ω ≅ O` 的仿射层已闭合**（路线 §3.1 (A4) 仿射版）。
- 仍缺：`Away x`/`Away y` 局部化层、scheme 层 `Ω_{Y_n/ℚ}`、`ω∞ = x^{n−3}ω₀` 两图比较。`OmegaPresentationActual` 已 RETIRED（#166），G-B 展示层**无活动文件**；稳定引用点 = `Mzk1G1OmegaActual`（#70，B+）+ `OmegaBasisActual`（#131，A-局部）+ `OmegaFreeActual`（#163，A-局部）。

### 4.58 【中·纪律/项目级】RETIRED 与 TauCetiPort 的收尾，以及 watchdog 的最后残留
- 4 个 RETIRED 文件：**无任何 consumer**（全 paper 递归 `import` 扫描 0 处；全仓 `tmp`+`LeanFormal` 扫描同样 0 处），13:00:24 之后无 watchdog 事件。它们最后的状态（12:55:46–51 FAIL、sorryAx）**不再进入 gate**，只在历史里保留。
- TauCetiPort：唯一外部 consumer 是 `Mzk1TauCetiHaarScalingBridgeActual.lean:1`（见 §2g-1）；该 bridge 无 olean、不在白名单、无 consumer，属休眠残留。**若不处理，未来任何对该 bridge 的 import 都会立刻红**（port 已 closed）。
- watchdog 侧：`extra-targets.txt` 在 13:00:24 被重写（移除上述目标）时 watchdog **仍在跑**，且 12:55:05 BATCH 已把这些文件排进内存队列，所以 12:55:46–51 仍出现它们的 FAIL —— 这是**队列残留**，不是「移除后又跑红」。判 gate 时以 `extra-targets.txt` 当前内容 + 移除时间为准。

### 4.59 【低·G-C/wrapper】0/∞ 命名修正；两个 wrapper 转绿不增加数学
- `Mzk1G1ProjectiveLineBoundaryActual`（#158）已把 §4.51 的 0/∞ 命名改对：`p1Zero` = λ=0、`p1Infinity` = t=0 = [1:0]。§4.51 的「下游引用前必须改名」警告**作废**（点集层）。
- `Mzk1URThetaHullActual`（#154）仍是 4 条 donor re-export（`p6_neg_M_le_HTheta2`、`actualPerB_inequality`、`actualTargetMagnitude_actual`、`urRootTheta_log_norm_eq_neg_shift`），转绿**不增加**数学；`θ_P5 ≤ H_pkt` 的 actual producer 仍不存在（文件注释明说 consumer 直接 import donor `p6_possibleImages_subset_packetHull`）。
- `Mzk1ULHpktActual`（#157）与 §2f#132 判定相同：`Hpkt` 定义 + 分析归约，`w V B` 任意、`hstepVIII` 假设。

## 5d. batch 8 立即动作（快照 13:06 UTC）

1. **G-A π 收口（最优先，一次性机械修）**：`Mzk1G1PsiXiActual` 的 35:42 / 55:38 两处 `overlapToChart0`/`overlapToChartInf` 加限定名 `Mzk1G1FermatOverlapActual.…`，再补 34:87/54:67 的 `Spec.map_comp` 方向；绿后 `xi` 即为 A-局部的 `Y_n → P¹`。之后只剩 `π⁻¹(D_+(X0)) = D(x^n)`、`degree = n²`、以及与 `fermatCurveSchemeIso` 模型的同一性。**不要再声称 cocycle「已证」**（§4.53）。
2. **SmoothLocalize**：补两条复合恒等 `localizeToModel (modelToLocalize m) = m`、`modelToLocalize (localizeToModel a) = a`（用 `IsLocalization.ringHom_ext` / `Ideal.Quotient.ringHom_ext` 分 chart 生成元）。这是 G-A 局部化识别（§4.36 (i)）的最后一步。
3. **停止 DONE 后两分钟内再改源码**（本批 #153/#155/#159/#162 均如此）：`SmoothLocalize`（13:03:49 DONE → 13:04:46 改）、`URThetaPacketInstance`（13:02:54 → 13:05:02）、`RadicalSupportFinal3`（12:58:54 → 13:02:22 → 13:04:16 FAIL）、`TwoChartGluingIso`（13:05:05 DONE，此前 12:58/13:02 两红）。要么落盘等结果，要么用独立 probe 锁定版本。
4. **RadicalSupportFinal3**（#159）：13:04:16 的 FAIL 首错未取（log 在 13:05:46 START 时被清空）；恢复为 12:58:54 的「hsep 显式假设」版后，再决定是否继续补 `he` 的算术输入。F7 的 `TameCount` 已由 #152 提供，本文件只剩 `_glued` 的 hsep。
5. **RETIRED 收尾**：4 个文件已无 consumer，无需再动；TauCetiPort 的休眠桥 `Mzk1TauCetiHaarScalingBridgeActual` 建议删除或改写（§4.58）。
6. **G-B**：因 `OmegaPresentation` 已 RETIRED，`Ω_{Y_n/ℚ}` 的 scheme 层与 `ω∞` 比较需要新文件；先用 #163 + #131 + #70 作为组件，不要再对 `OmegaPresentation` 排 watchdog。
7. **引用纪律（batch 8 版）**：引用任何 DONE 必须同时给 **src mtime + olean mtime + 时间**；`SmoothLocalize`(13:03:49)、`URThetaPacketInstance`(13:02:54)、`RadicalSupportFinal3`(12:58:54) 对本批快照时的源码 **全部 STALE**；`xi`、`overlapToChart0_chartMorphismInf`、`overlapToChartInf_chartMorphism0` **禁止引用**（sorryAx）。

### 6e. batch 8 更新（快照 **13:06 UTC = 21:06 CST**；本节覆盖 §6/§6b/§6c/§6d 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_status.mjs … --err`（对 18 个文件逐个取最后 START/DONE/FAIL 与首错；`SmoothLocalize`/`RadicalSupportFinal3`/`OmegaFree`/`PsiXi` 的 log 被 START 清空的情况已如实标注）、`Get-Content dag/watchdog/watchdog.log` 的 12:55–13:06 段（START/DONE/FAIL/RETRY 全量尾段）、olean/源码 mtime 对照（14 个文件）、禁用项 grep（18 个源文件，`sorry|admit\b|^axiom |PUnit|^True|surrogate|toy|maxHeartbeats`，仅注释/`maxHeartbeats` 命中）、**consumer 扫描**（4 个 RETIRED 模块 + TauCetiPort，paper 递归 + `tmp`/`LeanFormal` 全仓）、源码语义阅读（GlueMorphism 全文、PsiXi 全文、F7TameCount 全文、SmoothLocalize 关键段/声明表、OmegaFree 声明表、TwoChartGluingIso 全文、DisjointFamily 88–268、URThetaHull 全文、ProjectiveLineBoundary 全文、URThetaPacketInstance 声明表）。
- **Probe 8**：`_ProbeBatch8Actual.lean`，`wd_add` → `{"added":1,"total":90}`，**START 13:04:31.418Z → DONE 13:05:31.808Z（60s）**，8 条全部 [propext, Classical.choice, Quot.sound]、0 次 sorryAx（详见 §3b）。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未运行 / 未覆盖（如实标注）**：
  - `Mzk1URRootExtInstancesActual`（#143）：仍只确认 DONE，**未语义审计**（本批无新变化）。
  - `Mzk1URThetaPacketInstanceActual` 当前源码（13:05:02）：**未编译**（12:05:46 重编中），`ulThetaPacketV_le_paperC1_uncond` 只按源码读出，未做语义审计。
  - `Mzk1G1FermatRadicalSupportFinal3Actual` 13:04:16 FAIL：**首错未取**（log 被 START 清空）。
  - `Mzk1G1PsiXiActual`：`fermatCurveGlueMorphism`（三公理）**未单独 probe**；`xi` 不可 probe。
  - `Mzk1HullFermatGluingActual` 当前版 `twoChartGlueData`/`twoChartGlueDataOfIso` 的 def 级 axioms：**未 probe**（未在 Probe 8 内）。
  - `Mzk1G1OmegaFreeActual` 与 `Mzk1G1FermatTwoChartGluingIsoActual`：**未 probe**（DONE 晚于 probe 排队；前者有自带 `#print` 0 sorryAx，后者无 `#print`）。
  - `Mzk1G1ProjectiveLineBoundaryActual`、`Mzk1G1DisjointFamilyActual` 的其余定理：只 probe 了表中 2+1 条，未用 audit probe 覆盖全部。
- **快照 13:06 UTC 之后**：watchdog 仍在跑（13:05:46 已 START `SmoothLocalize`、`URThetaPacketInstance`、`RadicalSupportFinal3`，另有 `QHeight`、`PsiXi` 等）；13:06 之后的任何 DONE/FAIL 本表**未审计**。
- **本批新发现并已写进正文的纪律**：§4.53（cocycle 归约 ≠ 已证；`xi` 的 Ambiguous term 是独立证据）、§4.56（两套 `Y_n` 模型的引用歧义）、§4.58（白名单移除时 watchdog 队列残留）、§4.59（0/∞ 命名修正作废 §4.51）。

## 2h. 本批 batch 9 gate 表（快照 **13:18 UTC = 21:18 CST**；**新增 #169–#183**，覆盖 13:06 之后全部 DONE/FAIL + STALE/RETIRED）

grep 列 = 大小写敏感扫描 `sorry|admit\b|^axiom |PUnit|^True|surrogate|toy|maxHeartbeats`（本批 14 个文件；唯一命中是 `UCHpkt` 注释里的 "surrogate" 与 `SmoothLocalize` 的 `maxHeartbeats 800000`，均人工排除）。axioms 列：(P) = 本批 `_ProbeBatch9Actual.lean` 独立复算；(L) = 当前 attempt 自带 `#print` 的**日志末段**；— = 无 `#print` 或未 probe。olean 列 fresh = olean mtime > 源码 mtime；**STALE = 最后一次 DONE 之后源码又被改，或最后一次 attempt 是 FAIL**。

**13:06–13:18 事件全量（`watchdog.log`，只列 DONE/FAIL；★ = 本批关键转绿）**

| 时间 (UTC) | 事件 | 文件 | 备注 |
|---|---|---|---|
| 13:06:21 | FAIL | FermatSmoothLocalize | 13:11:08 转绿前的红（§4.64） |
| 13:06:42 | DONE ★ | URThetaPacketInstance | 57s；batch 8 的 STALE 解除（#177） |
| 13:06:46 | FAIL | RadicalSupportFinal3 | 连续红的开始（§4.65） |
| 13:07:36 | FAIL | FermatPi | 35s；无 per-file log，首错当时未取（#175） |
| 13:07:36 | FAIL | PsiXi | 13:13:08 转绿前 |
| 13:07:38 | FAIL | QHeight | 13:08:51 转绿前 |
| 13:07:39 | FAIL | LpFiniteness | 四次 FAIL 的第一次（§4.66） |
| 13:07:43 | FAIL | OmegaTransitionGlobal | 13:09:51 转绿前 |
| 13:08:04 | DONE | ULThetaPacket | 63s（#178） |
| 13:08:49 | DONE | TwoChartGluingIso | 31s（#180） |
| 13:08:51 | DONE | QHeight | 33s；源码 13:12:02 再改（后由 13:18:10 覆盖） |
| 13:08:56 | FAIL | FermatSmoothLocalize | |
| 13:09:02 | DONE | HullFermatGluing | 44s（#179） |
| 13:09:49 | FAIL | PsiXi | Ambiguous term 阶段（§4.60） |
| 13:09:51 | DONE ★ | OmegaTransitionGlobal | 35s（#171） |
| 13:09:52 | FAIL | LpFiniteness | |
| 13:10:16 | FAIL | UCHpkt | 13:14:26 转绿前 |
| 13:10:19 | FAIL | RadicalSupportFinal3 | |
| 13:11:02 | DONE | FiniteDisjointBelyi | 28s（#181） |
| 13:11:08 | DONE | FermatSmoothLocalize | 35s，但源码 13:12:23 起又改 → **STALE**（#174） |
| 13:11:53 | FAIL | PsiXi | |
| 13:11:56 | FAIL | LpFiniteness | |
| 13:12:19 | FAIL | UCHpkt | |
| 13:12:22 | FAIL | RadicalSupportFinal3 | |
| 13:13:08 | DONE ★ | PsiXi | 31s；`xi`、两条 transport、`fermatCurveGlueMorphism` 全绿（#169，§4.60） |
| 13:13:08 | DONE | QHeight | 31s（被 13:18:10 覆盖） |
| 13:13:09 | DONE | DisjointFamily | 32s（#182） |
| 13:13:15 | FAIL | FermatSmoothLocalize | 首现 3 条 sorryAx（§4.64） |
| 13:14:01 | FAIL | LpFiniteness | |
| 13:14:26 | DONE ★ | UCHpkt | 56s（#172，§4.67） |
| 13:14:29 | FAIL | RadicalSupportFinal3 | 首错 215:8 Algebra 实例（§4.65） |
| 13:15:15 | FAIL | LpFiniteness | |
| 13:16:14 | DONE ★ | LpFiniteness | 四条三公理（#170，§4.66） |
| 13:16:18 | FAIL | FermatSmoothLocalize | |
| 13:16:41 | FAIL | RadicalSupportFinal3 | |
| 13:17:23 | FAIL | FermatPi | 首错 36:27/40:27 `glueMorphism_ι` 的 D 未 pin（§4.62） |
| 13:18:10 | DONE | QHeight | src 13:17:03，fresh（#173） |
| 13:18:17 | FAIL | FermatSmoothLocalize | src 13:16:57，当前红（#174） |
| 13:19:21 | DONE ★ | FermatPi | src 13:18:10；henry 用 `(D := fermatTwoChartGlueData n)` 修好，`pi_ι0/pi_ι1` 三公理（快照后补记，§4.62 附注） |

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 169 | Mzk1G1PsiXiActual（覆盖 §2g#162） | G-A/π ψ | **DONE** | 13:13:08 | fresh（src 13:12:31 / olean 13:13:08） | clean | 三公理 (P：`xi`、`fermatCurveGlueMorphism`、`overlapToChart0_chartMorphismInf`；L 另 3 条) | **A-局部（batch 8 的 R 已修）**：两条 transport 引理改为 `chartInf_transport_core[_inf]`（`← Spec.map_comp` + `Polynomial.ringHom_ext`，按 C/X 生成元）后，`overlapToChart0_chartMorphismInf`/`overlapToChartInf_chartMorphism0`/`xi` 全部三公理。**`xi` 是 x-坐标态射**（U0 上 t=x，U∞ 上 λ=1/x），**不是 π**（§4.60/§4.61）。 |
| 170 | Mzk1LpFinitenessActual（新文件） | G-K §7.2 step 6 | **DONE** | 13:16:14 | fresh（src 13:15:21 / olean 13:16:13） | clean | 三公理 (L：`padic_krasner_mem`、`padic_krasner_same_extension`、`universalLocalFieldExists_of_finite`、`universalLocalFieldExists_intermediateField`) | **A-局部/B+（条件式）**：用 `I := {M // FiniteDimensional ∧ finrank ≤ d}` + ⨆ `normalClosure` 真造出 L，每个 M 经 `IsAlgClosed.lift` 嵌入并落在 normalClosure；**条件 `BoundedDegreeFinitelyManyFields d`（step 2 未形式化）**（§4.66）。 |
| 171 | Mzk1G1OmegaTransitionGlobalActual（新文件） | G-B A3 stage 1 | **DONE** | 13:09:51 | fresh（src 13:08:22 / olean 13:09:51） | clean | 三公理 (P：`overlap_derivation_relation`；L 另 2 条) | **A-局部/B+**：`Overlap0` 上 `KaehlerDifferential` 的 `du/dw/diu`、`u0^n+w0^n−1=0` 推导出 `n u^(n-1)du + n w^(n-1)dw = 0`，`d(iu0) = −iu0² du0`；这是**overlap 环层**的 A3 预备，不含 scheme 层 Ω 与 ω∞ 比较。 |
| 172 | Mzk1UCHpktActual（覆盖 §2g#157 邻域） | U-C C3 | **DONE** | 13:14:26 | fresh（src 13:13:03 / olean 13:14:25） | clean（注释一处 "surrogate"） | 三公理 (P：`uc_c3_paperConstants`；L：`hprime_paperConstants`/`uc_c3_of_primeCounting`) | **B+（条件式）**：`hprime_paperConstants` 把 §5.4.4 素数计数输入压缩成显式 `hπ : π(η) ≤ 4η/(3 log η)`（donor `primeCounting_mul_log_le_four_thirds`）；`uc_c3_paperConstants` 只剩 `hstepVIII`。**hπ 与 hstepVIII 都是假设，C3 未无条件**（§4.67）。 |
| 173 | Mzk1G1QHeightActual（覆盖 §2g 旧行） | L-H 高度/字典 | **DONE** | 13:18:10 | fresh（src 13:17:03 / olean 13:18:10） | clean | 三公理 (P：`legendreJ_eq_div`；L 另 5 条) | **B+**：假命题 `legendreJ_zero/one` **已删**；现有真 j 不变量 `256(1−λ+λ²)³/(λ²(1−λ)²)`、齐次性、`h(j) ≤ C + 6h(λ)`（Mathlib `Height.logHeight_eval_le'`）、非负性。D3 `HeightDictionaryInterface` 仍无 inhabitant。 |
| 174 | Mzk1G1FermatSmoothLocalizeActual（覆盖 §2g#153） | G-A 局部化识别 | **FAIL** | 13:18:17（13:11:08 曾 DONE） | **STALE**（src 13:16:57 / olean 13:11:08） | clean（`maxHeartbeats 800000`） | L：`localizeToModel_modelToLocalize` 三公理；`modelToLocalize_chartToModel`/`modelToLocalize_localizeToModel`/`localizeEquiv` = **sorryAx** | **R（当前）/ 部分增量**：Model 侧 round-trip 已证；Loc 侧 `modelToLocalize ∘ chartToModel` 与 `localizeEquiv` 仍 sorryAx（证明失败所致，非字面 sorry）。首错 334:30/351:51/365:51/415:25 `Ideal.Quotient.lift_mk` 不匹配 + 395:4 Type mismatch（§4.64）。**`localizeEquiv` 禁引用**。 |
| 175 | Mzk1G1FermatPiActual（覆盖 §2g#162 邻域） | G-A/π | **DONE（13:19:21，快照后补记）** | 13:19:21（src 13:18:10） | fresh（olean 13:19:21） | clean | 三公理 (L：`pi_ι0`、`pi_ι1`；`pi` def 无 `#print`) | **A-局部（π 落地）**：13:16:11 版改回**等 overlap canonical 模型** `fermatCurveScheme` 并复用 `fermatCurveGlueMorphism`（与 xi 同模型），`pi := λ=x^n`；13:17:23 首错 36:27/40:27 是 `glueMorphism_ι` 的 D 未 pin，henry 以 `(D := fermatTwoChartGlueData n)` 修好 → 13:19:21 DONE、两条 ι 引理三公理。**与 xi（x-坐标）不可互换；degree/原像仍未写**（§4.62）。 |
| 176 | Mzk1G1FermatRadicalSupportFinal3Actual（覆盖 §2g#159） | H-T tame 桥 | **FAIL / START 13:17:37** | 最后 FAIL 13:16:41（src 13:17:29） | **STALE**（olean 12:58:53） | clean | 旧 12:41 版三公理；当前 attempt 无有效 `#print` | **R**：13:14:29 首错 215:8 synthInstanceFailed `Algebra (ℤ ⧸ span{↑p}) (𝓞 K ⧸ P)`，`residue_separable_global` 落 sorryAx；后续 attempt 的 log 均在下一次 START 被清空。可引用版本仍只有 12:41 版 `tame_localDifferentPaperOrder_le_one_of_tame`（§4.65）。 |
| 177 | Mzk1URThetaPacketInstanceActual（覆盖 §2g#155） | U-L V_a/C1 | **DONE** | 13:06:42 | fresh（src 13:05:02 / olean 13:06:42） | clean（4e6 heartbeat） | L：4 条三公理 | **B+**：batch 8 的 STALE 解除（13:06:42 编的是 13:05:02 源码）；含 `ulThetaPacketV_le_paperC1_uncond`。`maxHeartbeats 4000000` 仍在（§4.48 记录）。 |
| 178 | Mzk1ULThetaPacketActual（覆盖 §2g#156） | U-L per-b | **DONE** | 13:08:04 | fresh（src 13:06:59 / olean 13:08:03） | clean | L：3 条三公理 | **B**：per-b 对象 + `ulNormalizedLogMass_smul`；V_a 值公式仍在 #177。 |
| 179 | Mzk1HullFermatGluingActual（覆盖 §2g#160） | G-A generic glue | **DONE** | 13:09:02 | fresh（src 13:08:17 / olean 13:09:01） | clean | 无 `#print`（旧版 def 级三公理） | **A-局部（generic）**：`twoChartGlueData` / `twoChartGlueDataOfIso` 真 `Scheme.GlueData`；**仍无用户级 cocycle 定理**（§4.60 不变）。 |
| 180 | Mzk1G1FermatTwoChartGluingIsoActual（覆盖 §2g#161） | G-A 两 overlap 模型 | **DONE** | 13:08:49 | fresh（src 13:08:17 / olean 13:08:49） | clean | 三公理 (P：`fermatCurveSchemeIso` def；无 `#print`) | **A-局部（第二模型）**：`fermatCurveSchemeIso := (fermatTwoChartGlueDataOfIso n).glued`，`fermatChart0ToCurveIso/Inf` = `D.ι`；与 `fermatCurveScheme` 是**两套 Y_n**（§4.63）。 |
| 181 | Mzk1G1FiniteDisjointBelyiActual（覆盖 §2g 旧行） | G-K 有限族 | **DONE** | 13:11:02 | fresh（src 13:09:39 / olean 13:11:01） | clean | 未 probe（文件自带 `#print`） | **B（未变）**：仍是陈述 + 接口，**无族 inhabitant**；转绿不增加数学。 |
| 182 | Mzk1G1DisjointFamilyActual（覆盖 §2g#151） | G-K §7.1 | **DONE** | 13:13:09 | fresh（src 13:12:02 / olean 13:13:09） | clean | 未 probe（batch 8 已 P 2 条） | **B+（接口，无 inhabitant）**：`UniversalLocalFieldExists`/`ContainsBoundedExtensions`/`GKCompactInput` 仍是**接口**；#170 给出了 `UniversalLocalFieldExists` 的**条件 producer**（带 `BoundedDegreeFinitelyManyFields` 假设），但 **`GKCompactInput` 仍 NO INHABITANT**。 |
| 183 | **RETIRED 不变**：`FermatCurveClosedActual`、`HullFermatClosedSubschemeActual`、`OmegaPresentationActual`、`FermatOverlapRingActual`、`TauCetiPort/**` | — | **RETIRED** | 13:06 之后 **0 事件** | none | — | — | 白名单仍不含它们；**bridge 已 retired**：`Mzk1TauCetiHaarScalingBridgeActual.lean` 已从 paper 移走，现存 `coord/retired-port/Mzk1TauCetiHaarScalingBridgeActual.lean.retired`（1305 B），全 paper **0 处 import**（§4.60 第 4 条）。 |

## 3c. Probe 9（本批 batch 9）：`tmp/sheaf/xif/paper/_ProbeBatch9Actual.lean`

- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch9Actual.lean` → `{"added":1,"total":93}`。
- watchdog：**START 2026-11-16T13:15:41.307Z → DONE 13:16:37.355Z（约 56s）**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch9Actual.lean.log`（909 B，本 attempt **0 次 error、0 次 sorryAx**）。
- 7 条独立复算（原样抄录，**全部 [propext, Classical.choice, Quot.sound]**）：

| 定理/定义（全名见文件） | axioms | 覆盖行 |
|---|---|---|
| `Mzk1G1PsiXiActual.xi` | [propext, Classical.choice, Quot.sound] | #169（**x-坐标**，非 π） |
| `Mzk1G1PsiXiActual.fermatCurveGlueMorphism` | [propext, Classical.choice, Quot.sound] | #169（h 为输入） |
| `Mzk1G1PsiXiActual.overlapToChart0_chartMorphismInf` | [propext, Classical.choice, Quot.sound] | #169 |
| `Mzk1G1OmegaTransitionGlobalActual.overlap_derivation_relation` | [propext, Classical.choice, Quot.sound] | #171 |
| `Mzk1UCHpktActual.uc_c3_paperConstants` | [propext, Classical.choice, Quot.sound] | #172 |
| `G1QHeightActual.legendreJ_eq_div` | [propext, Classical.choice, Quot.sound] | #173 |
| `Mzk1G1FermatTwoChartGluingIsoActual.fermatCurveSchemeIso` | [propext, Classical.choice, Quot.sound] | #180（第二模型 def） |

- **未覆盖（明确未运行）**：`Mzk1LpFinitenessActual` 四条（probe 排队时该文件仍在 FAIL 迭代、无 olean；DONE 13:16:14 晚于 probe 的 import 集，其公理只有 (L) 日志末段）；`Mzk1G1FermatPiActual` 的 `pi`（当前无 olean，红）；`Mzk1G1FermatSmoothLocalizeActual` 的 `localizeEquiv`（当前 attempt 是 sorryAx 且 olean STALE，**不可 probe**）；`Mzk1HullFermatGluingActual` 的 `twoChartGlueDataOfIso`（未单独 probe）。
- 结论：**kernel 层本批 7 条关键定理/定义无伪证**；风险全在语义层（xi 的含义、条件式 hπ/hstepVIII、`BoundedDegreeFinitelyManyFields`）与「DONE 后又被改写」（#174/#175/#176）。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 9 续）

### 4.60 【高·纪律 / 强制】cocycle 只能这样表述：GlueData 内部字段已证 + 用户级等式归约为 h（h 未证）
- 事实：#150 `glueMorphisms_compat`、#169 `fermatCurveGlueMorphism` 都是把 **overlap 层等式 h**（`overlapToChart0 n ≫ f0 = overlapToChartInf n ≫ f1`）作为**输入假设**，输出 `glueMorphisms` 需要的 pullback 层兼容性；**没有任何文件证明 h 本身**。Y_n 的 `Scheme.GlueData` 里 `t_fac`/`cocycle`/`f_open` 字段确实真证（#179）。
- 强制写法：**「GlueData 内部 t_fac/cocycle 字段已证；用户级等式 h 未证，但已归约为 `glueMorphisms` 的唯一输入」**。凡出现「cocycle 已证 / glue_condition 已证 / 用户级 cocycle 已闭合」即违规，必须撤回。
- 本条同时写入 `coord/ROUTE-COMPLIANCE-20261116.md`（§16）。

### 4.61 【高·纪律】xi 的引用：已证可引用，但只是 x-坐标；「未证且禁引用」是 batch 8 的状态
- batch 8 的记录（**保留**）：`xi` 与两条 transport 因 `overlapToChart0/Inf` 与 `ProjectiveLineGluedActual` 同名而 Ambiguous，`xi` = sorryAx，**未证且禁引用**。
- batch 9 更新：13:13:08 attempt（src 13:12:31）**已修**——不是简单加限定名，而是把两条 transport 改成 `chartInf_transport_core`/`chartInf_transport_core_inf`（`← Spec.map_comp`、`← CommRingCat.ofHom_comp`，再对 `Polynomial` 的 C/X 生成元 `Polynomial.ringHom_ext`），歧义源被结构性消除；Probe 9 三条全三公理。
- **语义边界（必须写）**：`xi` 在 U0 用 `chartMorphismInf (x0 n)`（t = x），在 U∞ 用 `chartMorphism0 (r1 n)`（λ = 1/x）→ 它是 **x-坐标** `Y_n ⟶ P¹`（degree n），**不是** π（π 是 λ = x^n，degree n²，见 #175）。把 xi 当 π、或据此声称 degree n²，均属换题。
- 见 §4.62：π 已于 **13:19:21 DONE**（源码 13:18:10；`pi_ι0/pi_ι1` 三公理），不再 red；但 π = λ=x^n，与 xi（x-坐标）是**两个不同态射**，引用必须分别写明。

### 4.62 【高·G-A/π】FermatPi 的 `glueMorphism_ι` D 未 pin（13:19:21 已修，π DONE）；π def 回到单模型
- 13:17:23 首错：`36:27` / `40:27` `Application type mismatch: { down := false } has type ULift Bool but is expected to have type (Scheme.GlueData.toGlueData ?m.12).J`，即 `glueMorphism_ι _ _ (ULift.up false)` 里 D 的隐式参数没被目标类型 pin 住（`unfold pi fermatCurveGlueMorphism ...` 之后 `D.glued` 的 D 不再以 `fermatTwoChartGlueData n` 出现）。
- 修法（一处机械）：`exact glueMorphism_ι (D := fermatTwoChartGlueData n) _ _ (ULift.up false)`，或先 `show (fermatTwoChartGlueData n).ι (ULift.up false) ≫ _ = _` 固定 D 与 J。修好后 `pi`/`pi_ι0`/`pi_ι1` 一并可引用。
- 进展：13:16:11 版把 `pi` 从**双 overlap 模型**改回**等 overlap 模型** `fermatCurveScheme`，并复用 #169 的 `fermatCurveGlueMorphism` + #140 的 `fermatPiOverlap_condition` → xi 与 π 现在是**同一模型上的两个不同态射**（x 与 x^n），比 13:06 版混用两个模型更一致。但 13:18:10 又改源码，当前无 olean。
- **快照后补记（13:19:21 DONE）**：henry 在主文件里正好用 `exact glueMorphism_ι (D := fermatTwoChartGlueData n) _ _ (ULift.up false/true)` 修掉 §4.62 首错；13:19:21 DONE，`pi_ι0`/`pi_ι1` 三公理（日志末段），olean 13:19:21 > src 13:18:10 → **π 当前可引用**。剩余：`π⁻¹(D_+(X0)) = D(x^n)`、`degree = n²`、`IsFinite π` 的 scheme 层装配（AUDIT-ROUTE §5e#1 与 ROUTE-COMPLIANCE §17）。

### 4.63 【中·纪律】引用 Y_n 必须写明模型
- `fermatCurveScheme`（`Mzk1G1FermatTwoChartGluingActual`，经 `FermatCurveActual` 转出）：等 overlap、t = 𝟙、V(i,j)=V(j,i)；`fermatCurveScheme_eq_glued : fermatCurveScheme n = (fermatTwoChartGlueData n).glued` 是 rfl。
- `fermatCurveSchemeIso`（`Mzk1G1FermatTwoChartGluingIsoActual`）：W0=Spec Overlap0、W1=Spec OverlapInf、t = `overlapSchemeIso n`；Probe 9 复算其 def 为三公理。
- 当前 xi 与 π 都用**前者**；任何引用必须写全名，不得只写 "Y_n"；若用后者，须同时写 transition 来源与「与前者尚未证同构」。

### 4.64 【中·G-A】SmoothLocalize：Model 侧 round-trip 已证；Loc 侧两条与 `localizeEquiv` 仍 sorryAx
- 13:18:17 attempt（src 13:16:57）首错：`334:30`/`351:51`/`365:51`/`415:25` `rewrite failed: did not find (Ideal.Quotient.lift ?I ?f ?H) ((Ideal.Quotient.mk ?I) ?a)`，因为目标是 `(Ideal.Quotient.mk I).comp (rename fermatVarCast).toRingHom` 的**复合**（不是裸 mk）；`395:4` Type mismatch。
- 公理实测：`localizeToModel_modelToLocalize` 三公理（真证）；`modelToLocalize_chartToModel`、`modelToLocalize_localizeToModel`、`localizeEquiv` 三条 **sorryAx**（证明失败被 Lean 记为 sorryAx，源码无字面 sorry）。
- 纪律：**`localizeEquiv` 有名字 ≠ 已证**；A₀ 局部化 ≅ Model 仍未闭合（§4.54 的缺口从「两条 round-trip」缩到「Loc 侧一条 + 复合」）。修法：先把复合下的 mk 用 `change`/`← RingHom.comp_apply` 化成裸 mk 再 `Ideal.Quotient.lift_mk`；`commutes'` 用 `IsScalarTower.algebraMap_apply` 链到 `chartToModel_algebraMap`。

### 4.65 【中·F7/H-T】RadicalSupport 的新红：residue separability 的 Algebra 实例
- 13:14:29 首错 `215:8` synthInstanceFailed `Algebra (ℤ ⧸ Ideal.span {↑p}) (𝓞 K ⧸ P)`；`residue_separable_global` 落 sorryAx。这正是 #152 `TameRamifiedAt` 的 (a) 输入（剩余域可分）的形式化尝试。
- 修法：`letI : Algebra (Int ⧸ span{p}) (𝓞 K ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap hle` 的隐式参数（R、S、I、J）需显式 pin；且 `exact Algebra.IsAlgebraic.isSeparable_of_perfectField` 前用 `haveI` 让实例对目标可见（当前 `letI` 在 `by` 内本应可见，故更可能是 `algebraQuotientOfLEComap` 的 `I`/`J` 与 `P.comap` 方向未合）。
- 现状：olean 仍 12:58:53；引用只能引 12:41 版 `tame_localDifferentPaperOrder_le_one_of_tame`；`_glued` 的 hsep 仍是显式假设（§4.47）。

### 4.66 【中·G-K】LpFiniteness 转绿：§7.2 step 6 的条件式闭合
- 构造（全三公理，L）：`I := {M : IntermediateField ℚ_[p] (PadicAlgCl p) // FiniteDimensional … ∧ finrank ≤ d}`，`hfin : Finite I`；`L := ⨆ i, normalClosure (M i)`；`FiniteDimensional` / `Normal` 由 `normalClosure.is_finiteDimensional` / `normalClosure.normal` 逐项给出；每个 M 经 `IsAlgClosed.lift : M →ₐ[ℚ_p] PadicAlgCl p` 嵌入，其 `fieldRange` 属 I 且 ≤ normalClosure，故 `ContainsBoundedExtensions` 成立。
- **诚实边界**：`BoundedDegreeFinitelyManyFields d` 只被**定义**（文件第 90 行），全文件**没有证明**；引用写「conditional on bounded-degree finiteness（Eisenstein 系数有限性 + Krasner 的 step 2 未形式化）」。不能记 G-K 的 L_p 或 §7.1 递归构造已完成；`GKCompactInput` 仍无 inhabitant（#182）。
- 13:07–13:15 的四次 FAIL 全是机械：`normalClosure.is_finiteDimensional`/`normalClosure.normal` 未给显式参数（118/129）、`LinearEquiv.finrank_eq` 方向（202）；13:15:21 版已修。

### 4.67 【低·U-C/L-H】UCHpkt 常数端闭合（条件设 hπ）；QHeight 假命题已删
- #172：`hprime_paperConstants` 用 donor `primeCounting_mul_log_le_four_thirds`，把 Section2 素数计数不等式作为**输入 hπ**；`uc_c3_paperConstants` 只剩 `hstepVIII`。Probe 9 三公理。**不要记 C3 无条件，也不要记 hstepVIII 已证**（U-L 的 `ul_hpaper_assembled_paperConstants` 仍需它）。
- #173：§5c#2 要求删的假命题 `legendreJ_zero/one` 已删；现在有真实 j 不变量 `j(λ) = jNum.eval/jDen.eval`、`jNum/jDen` 齐次 6、`∃ C, h(j(λ)) ≤ C + 6h(λ)`（Mathlib 高度函子性）、非负性；D3 仍 NO INHABITANT。转绿是**真增量**，但只到 D3 接口之前。

## 5e. batch 9 立即动作（快照 13:18 UTC）

1. **π 已修（13:19:21 DONE，快照后补记）**：henry 用 `(D := fermatTwoChartGlueData n)` 修好 `pi_ι0/pi_ι1`，π 可引用（三公理，olean fresh）。**π = λ=x^n、xi = x-坐标，两者不可互换**；下一步只剩 `π⁻¹(D_+(X0)) = D(x^n)`、`degree = n²`、`IsFinite π`（§4.61/§4.62，ROUTE-COMPLIANCE §17）。
2. **SmoothLocalize**：Loc 侧 `modelToLocalize_chartToModel` 的四处 `rewrite（lift_mk 在复合下不触发）先 `change` 再 rewrite；`commutes'` 用 `chartToModel_algebraMap`。绿之前 `localizeEquiv` 标「未证」。
3. **RadicalSupport**：`residue_separable_global` 的 `Ideal.Quotient.algebraQuotientOfLEComap` 参数显式化；绿后 #152 的 `TameRamifiedAt` 才有 (a) 的 producer。
4. **停止「DONE 后 1–2 分钟内再改源码」**：本批 #173（13:18:10 DONE，src 13:17:03）、#174（13:11:08 DONE → 13:13/13:16/13:18 连续红）、#175（13:17:23 FAIL 后 13:18:10 又改）、#176（源码 13:17:29 又改）——gate 表每秒在过期。
5. **RETIRED 收尾已完成**：4 文件 + TauCetiPort 已不在白名单，bridge 已移到 `coord/retired-port/*.retired` 且 0 import；**不要再对它们排 watchdog**（§4.60 第 4 条）。
6. **引用纪律（batch 9 版，强制）**：cocycle 只写「GlueData 内部字段已证 + 用户级 h 未证」；xi 只作 x-坐标引用；Y_n 必写 `fermatCurveScheme`/`fermatCurveSchemeIso`；`pi`/`pi_ι0`/`pi_ι1`、`localizeEquiv` 一律先核 olean；`BoundedDegreeFinitelyManyFields`、`hπ`、`hstepVIII` 都是**假设**。

## 6f. batch 9 更新（快照 **13:18 UTC = 21:18 CST**；覆盖 §6/§6b/§6c/§6d/§6e 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_status.mjs … --err`（15 个文件逐个取最后 START/DONE/FAIL；对 FAIL 读首错：SmoothLocalize、FermatPi、RadicalSupport、LpFiniteness）；`Get-Content dag/watchdog/watchdog.log -Tail 80` + 13:06–13:18 的 DONE/FAIL 全量抽取；olean/源码 mtime 对照（14 个文件）；禁用项 grep（14 个源文件）；源码语义阅读（PsiXi 全文 139 行、LpFiniteness 全文 221 行、OmegaTransitionGlobal 全文 80 行、QHeight 关键段、Pi 全文、SmoothLocalize 286–419、RadicalSupport 195–219、UCHpkt 185–236、HullFermatGluing/TwoChartGluingIso/FermatCurveActual 的模型 def、DisjointFamily 85–125）；**retired-port 与 bridge 位置核查**（`coord/retired-port`、0 import）。
- **Probe 9**：`_ProbeBatch9Actual.lean`，`wd_add` → `{"added":1,"total":93}`，**START 13:15:41.307Z → DONE 13:16:37.355Z（56s）**，7 条全部 [propext, Classical.choice, Quot.sound]、0 次 sorryAx（详见 §3c）。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未运行 / 未覆盖（如实标注）**：
  - `Mzk1LpFinitenessActual` 四条：只取 (L) 日志末段，**未 audit-probe**（DONE 晚于 probe 排队）。
  - `Mzk1G1FermatPiActual`：13:17:23 FAIL 的 log 已给首错，但 13:18:10 源码又改、**当前版未编译**；`pi` def 未单独 probe。
  - `Mzk1G1FermatRadicalSupportFinal3Actual`：13:14:29 之后各 attempt 的 log 均被下一次 START 清空，**后续首错未取**；只读过 195–219 段。
  - `Mzk1G1FermatSmoothLocalizeActual`：当前版 **不可 probe**（olean STALE + sorryAx）；只按源码与日志末段判。
  - `Mzk1URThetaPacketInstanceActual`、`Mzk1ULThetaPacketActual`、`Mzk1HullFermatGluingActual`、`Mzk1G1FiniteDisjointBelyiActual`、`Mzk1G1DisjointFamilyActual`：只取 DONE + 文件自带 `#print`/(L)，**未逐行语义重审**（batch 8 已审过的部分不重复）。
  - U-R 全组（除 #177）、G-K 递归构造、H-T 的 F1–F4/F8、P8-P 端到端：**未运行**。
- **快照 13:18 UTC 之后**：watchdog 仍在跑（13:17:37 START RadicalSupport；SmoothLocalize/FermatPi/QHeight 的源码刚被改写）。**快照后唯一已复核的事件**：FermatPi **DONE 13:19:21**（src 13:18:10，olean 13:19:21，`pi_ι0/pi_ι1` 三公理；已补记 #175/§4.62/§5e#1）。其余 13:18:17 之后的任何 DONE/FAIL 本表**未审计**。
- **本批新发现并已写进正文的纪律**：§4.60（cocycle 表述强制）、§4.61（xi 的引用边界：已证但只是 x-坐标）、§4.63（Y_n 双模型必写全名）、§4.66（`BoundedDegreeFinitelyManyFields` 是假设不是定理）。





## 2i. 本批 batch 10 gate 表（快照 **13:33 UTC = 21:33 CST**；**新增 #184–#199**，覆盖 13:18 之后全部 DONE/FAIL/START + STALE/RETIRED）

grep 列 = 大小写敏感扫描 `sorry|admit\b|^axiom |PUnit|^True|surrogate|toy|maxHeartbeats`（本批 9 个文件：FermatPi / FermatPiPreimage / ProjectiveLineChartPreimage / PsiAffineOverlap / LpDifferentBound / LpFiniteness / SmoothLocalize / JHeightBezout / HullFermatGluing / RadicalSupportFinal3；唯一命中是 `SmoothLocalize` 头注释里的 "sorry/admit/axiom" 字样与 `set_option maxHeartbeats 800000`，均人工排除）。axioms 列：(P) = 本批 `_ProbeBatch10Actual.lean` 独立复算；(L) = 该 attempt 自带 `#print` 的日志末段；— = 无 `#print` 或未 probe。olean 列 fresh = olean mtime > 源码 mtime；**STALE = 最后一次 DONE 之后源码又被改**。

**本批日志纪律（实测修订 §4.40/§4.46）**：本批观察到两种行为并存——`FermatPiPreimage` 的 per-file log **累积了两个 attempt**（13:29:52 的 FAIL 段 + 13:31:50 的 DONE 段，6267 B）；而 `ProjectiveLineChartPreimage` 在 13:22:23 / 13:24:35 / 13:27:49 三次 FAIL 后 `wd_status --err` 报 **no log file**，13:29:25 START 后才出现 0 B→573 B 的新文件。结论：**不能假设 log 一定累积、也不能假设一定保留**；FAIL 首错必须在 FAIL 后立刻读，log 缺失时只能从源码推断（本表已如实标注哪几条首错未取）。

### 2i-1 13:18:52–13:32:08 事件全量（`watchdog.log`，只列 DONE/FAIL/新目标；★ = 关键转绿）

| 时间 (UTC) | 事件 | 文件 | 备注 |
|---|---|---|---|
| 13:19:21 | DONE ★ | FermatPi | 29s；π 可引用（§4.62 修好，#184） |
| 13:19:24 / 13:19:25 | FAIL | LpDifferentBound / LpFiniteness | LpFiniteness 13:21:30 转绿 |
| 13:20:11 | FAIL | PsiAffineOverlap | `R` 未开 namespace（#187） |
| 13:20:19 / 13:20:40 / 13:22:32 / 13:24:44 / 13:27:58 | FAIL | FermatSmoothLocalize | 13:29:11 转绿（#190） |
| 13:21:29 | FAIL | JHeightBezout | 13:23:38 转绿，13:27:51 又红，13:29:04 再绿（#191） |
| 13:21:30 | DONE | LpFiniteness | 36s（#189） |
| 13:21:39 | FAIL | HullFermatGluing | 13:23:49 转绿（#192） |
| 13:22:23 / 13:24:35 / 13:27:49 / 13:29:52 / 13:31:49 | FAIL | ProjectiveLineChartPreimage | 五次红；前三次首错丢失（无 log），后两次首错已取（#186） |
| 13:22:54 | DONE（后 STALE） | RadicalSupportFinal3 | 60s；src 13:25:57 又改 → 13:25:08 起连续红（#193） |
| 13:23:38 | DONE | JHeightBezout | 29s（后被 13:27:51 红覆盖，13:29:04 再绿） |
| 13:23:49 | DONE | HullFermatGluing | 40s，fresh（#192） |
| 13:24:03–13:27:04 | RETRY ×3 → DONE | `_ProbeURC2Actual`（Lead 的 U-R C2 probe，非本 lane） | 52s；本表不引用其结论 |
| 13:27:51 | FAIL | FermatPiPreimage | Ambiguous `fermatChart0ToCurve` + `sorry ⊔ sorry`（#185 前半） |
| 13:29:04 | DONE ★ | JHeightBezout | 31s，src 13:28:18，fresh |
| 13:29:05 | DONE | LpDifferentBound | 32s（src 13:27:25） |
| 13:29:11 | DONE ★ | FermatSmoothLocalize | 38s，src 13:28:15，fresh；`localizeEquiv` 三公理 |
| 13:29:52 | FAIL | FermatPiPreimage | 58:12 rewrite 失败（`piChartInf x` 不在目标中） |
| 13:30:36 | DONE | LpDifferentBound | 30s，src 13:29:46，fresh（第二次绿） |
| 13:31:03 | FAIL | RadicalSupportFinal3 | 214:25 `minpoly.irreducible` 实例不匹配；`residue_separable_global` = sorryAx |
| 13:31:50 | DONE ★ | FermatPiPreimage | 32s，src 13:30:59，olean 13:31:49，fresh；`pi_preimage_eq` 三公理（#185） |
| 13:31:51 | FAIL | PsiAffineOverlap | 51:31 / 60:26 `R` unknown（#187） |
| 13:31:53 | DONE | `_ProbeBatch10Actual`（本 lane） | 35s，8 条三公理，0 error / 0 sorryAx（§3d） |
| 13:32:08 | START | JHeightLower（新文件） | 齐次性引理；快照时无结果（#197） |

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 184 | Mzk1G1FermatPiActual（覆盖 §2h#175） | G-A/π | **DONE** | 13:19:21 | fresh（src 13:18:10 / olean 13:19:21） | clean | 三公理 (P：`pi` def、`pi_ι0`；L：`pi_ι1`) | **A-局部（π 真落地）**：`piChart0 = chartMorphism0 (x0^n)`、`piChartInf = chartMorphismInf (r1^n)`、`pi := fermatCurveGlueMorphism n piChart0 piChartInf (fermatPiOverlap_condition n)` = `D.openCover.glueMorphisms` ⇒ **是 glued scheme 间的真态射**（`fermatCurveScheme n ⟶ projectiveLineGlued`），不是 chart map wrapper；`pi_ι0/pi_ι1` 是两条 chart 限制。**关键细化**：其用户级 overlap 等式 h 由 `Mzk1G1ProjectiveLinePiOverlapActual.fermatPiOverlap_condition`（DONE 12:44:51，自带 `#print` 三公理）**真证**，π 不依赖任何未证 h。**Y_n 用 canonical `fermatCurveScheme`**（= `(fermatTwoChartGlueData n).glued`，`fermatCurveScheme_eq_glued` 为 rfl）。 |
| 185 | Mzk1G1FermatPiPreimageActual（新文件） | G-A/π⁻¹ | **DONE** | 13:31:50（此前 13:27:51 / 13:29:52 FAIL） | fresh（src 13:30:59 / olean 13:31:49） | clean | 三公理 (L：`fermatCurve_cover`、`pi_preimage_eq`；13:27 attempt 的 `pi_preimage_eq` 曾 = sorryAx) | **A-局部（簿记，非最终目标）**：`fermatCurve_cover`（两 chart opensRange 上确界 = ⊤，用 `ι_jointly_surjective`）、`pi_apply_chart0/Inf`（`← comp_apply` + `pi_ι0/ι1`）、`pi_preimage_eq`（`(pi)⁻¹V = chart0 ''ᵁ (piChart0⁻¹V) ⊔ chartInf ''ᵁ (piChartInf⁻¹V)`，ext + `change` 把 ∈ 化成 `(pi y) ∈ V`）。**注意：文件里没有 `pi⁻¹(D_+(X0)) = D(x^n)` 这条目标陈述**，它只是分解式；G-A 的 π⁻¹ 目标仍未完成。 |
| 186 | Mzk1G1ProjectiveLineChartPreimageActual（新文件） | G-C P¹ chart 原像 | **FAIL** | 13:31:49（五次 FAIL） | none | clean | —（无 `#print`；无 olean） | **R（机械）**：首错已从「`rw` 无法重写 `localChart0/localChartInf`（33:21/41:6）」推进到「unsolved goals 31:79 / 40:77：`opensRange (p1GlueData.f (true,false)) = opensRange overlapToChartInf`」。13:22/13:24/13:27 三次的首错**未取**（log 缺失）。`preimage_opensRange_ι`（一般 GlueData 的 `(D.ι i)⁻¹(D.ι j).opensRange = (D.f i j).opensRange`）在源码中已写出但整文件红，**禁引用**。 |
| 187 | Mzk1G1PsiAffineOverlapActual（新文件） | B1 ψ 仿射 overlap | **FAIL** | 13:31:51（13:18:09 / 13:20:11 / 13:31:51） | none | clean | 三公理 (L：`isUnit_q`、`isUnit_r`) | **R（机械）/ B0**：首错 51:31、60:26 `Function expected at R`——`R` 定义在 `Mzk1G1FermatAffineChartActual`，本文件只 open 了 SecondChart/Overlap/PsiChartMaps/ProjectiveLineTransition，`autoImplicit` 把 `R` 当隐式变量。内容仅环层：`overlapRing = Away (q_T * r)`、`r2ToOverlap`、`isUnit_q/isUnit_r`（真证）、`infToOverlap/qToOverlap`；**scheme 层 chart0ToOverlap/chartInfPieceToOverlap 与 ψ 的 overlap 相容性均未完成**，B1 第一段无新数学可用。 |
| 188 | Mzk1LpDifferentBoundActual（新文件） | G-K §7.2 step 3-4 | **DONE** | 13:30:36（13:21:29 也曾 DONE，13:19:24 首绿前红） | fresh（src 13:29:46 / olean 13:30:36） | clean | 三公理 (P：`localDifferentPaperOrder_le_boundedDegree`、`localDifferentOrder_eq_paperOrder_mul_ramification`；L：另 1 条) | **B+ / A-局部（transport + 一条新推论）**：`localDifferentPaperOrder_le_degree_padicVal'` 是 donor `localDifferentPaperOrder_le_degree_padicVal` 的逐字转出；**新**的是 `localDifferentPaperOrder_le_boundedDegree`（`[L:K] ≤ d ⇒ ord_p(𝔇_L) ≤ ord_p(𝔇_K) + log_p d + 1/e(K)`，用 `padicValNat_le_nat_log` + `Nat.log_mono_right` + linarith）与归一化字典 `localDifferentOrder = localDifferentPaperOrder * e`。**没有**新的 local-global 结论；G-K 的 step 3 输入现在是可引用的条件式。 |
| 189 | Mzk1LpFinitenessActual（覆盖 §2h#170） | G-K §7.2 step 6 | **DONE** | 13:21:30 | fresh（src 13:20:42 / olean 13:21:30） | clean | 三公理 (P：`boundedDegreeFinitelyManyFields_of_fixed_degree`；L：另 5 条) | **B+（条件式，边界收紧）**：13:20:42 版新增 `boundedDegreeFinitelyManyFields_of_fixed_degree`（由**每个固定次数**的有限性推出 `BoundedDegreeFinitelyManyFields d`：`I` 按 `finrank = n`（n ≤ d）分层 + `Set.finite_iUnion`）与反向 `fixed_degree_finite_of_boundedDegree`。**`BoundedDegreeFinitelyManyFields` 仍只是定义（第 90 行）**，全文件没有证明固定次数有限性 ⇒ 引用必须写 "conditional on per-degree finiteness (Eisenstein + Krasner step 2 未形式化)"。`GKCompactInput` 仍 NO INHABITANT（#182 不变）。 |
| 190 | Mzk1G1FermatSmoothLocalizeActual（覆盖 §2h#174；**§4.64 缺口闭合**） | G-A A₀ 局部化识别 | **DONE ★** | 13:29:11（13:11:08 DONE → 13:13–13:27 连续 5 红） | fresh（src 13:28:15 / olean 13:29:11） | clean（`maxHeartbeats 800000`） | 三公理（L 全部：`modelToLocalize_chartToModel`、`modelToLocalize_localizeToModel`、`localizeEquiv` 等；P：`localizeEquiv`） | **A-局部（真增量，本批最大）**：`localizeEquiv : Model n ≃ₐ[ℚ] Localization.Away (chartR n)`，`toFun = modelToLocalize`、`invFun = localizeToModel`，两条 round-trip 真证——`localizeToModel_modelToLocalize`（Model 侧，按 X0/X1/X2 生成元）与 `modelToLocalize_localizeToModel`（Loc 侧：用 `IsLocalization.Away.sec_spec` + 消去单位）。**batch 8/9 的 sorryAx（`modelToLocalize_chartToModel`/`modelToLocalize_localizeToModel`/`localizeEquiv`）全部消失**，三条 `#print axioms` 均三公理、0 次 sorryAx。即 `(R n)[1/(n x^{n-1})] ≅ fermatModelRing n`（A₀ 的 `D(x)` 局部化）已证。 |
| 191 | Mzk1G1JHeightBezoutActual（新文件） | L-H j 映射高度 | **DONE** | 13:29:04（13:21:29 / 13:27:51 曾 FAIL） | fresh（src 13:28:18 / olean 13:29:04） | clean | 三公理 (L：`jBezUZ`、`jBezVZ`；P：`jBezUZ`) | **A-局部（初等但真）**：`jNumZ = 256(U²−UV+V²)³`、`jDenZ = U²V²(V−U)²`，用显式整数系数 `jQ00Z..jQ11Z` 证出两条 **kernel 检查的 Bézout 恒等式** `q00 A + q01 B = 256 X0^10`、`q10 A + q11 B = 256 X1^10`（`ring`）。这是 `h(j(λ)) ≥ 6h(λ) − C` 的代数输入，**但下界本身（高度比较）不在本文件**；`JHeightLower`（#197）正在写其齐次性引理。 |
| 192 | Mzk1HullFermatGluingActual（覆盖 §2h#179） | G-A generic glue | **DONE** | 13:23:49 | fresh（src 13:22:38 / olean 13:23:48） | clean | 无 `#print`（def 级；Probe 4/9 判过三公理） | **A-局部（generic，无新定理名）**：整文件仍只有 `twoChartU/V/F/T/twoChartT'`、`twoChartGlueData`、`twoChartVOfIso/FOfIso/t_of_iso/twoChartGlueDataOfIso` 等 def/abbrev（`t_fac/cocycle/f_open` 字段真证）。**第 136–148 行的 TECHNICAL NOTE 仍在**：user-facing cocycle 等式 `twoChartGlue_condition` **未陈述**（`J` 只 defeq ULift Bool）⇒ §4.60 风险条目不变，本批无任何文件称 cocycle 已证。 |
| 193 | Mzk1G1FermatRadicalSupportFinal3Actual（覆盖 §2h#176） | H-T tame 桥 | **DONE 13:22:54 → STALE → FAIL 13:31:03** | 13:31:03（src 13:25:57） | stale（olean 12:58:53，src 13:25:57） | clean | 旧段三公理（L：`tame_count_differentIdeal_eq`、`tame_localDifferentPaperOrder_le_one_of_tame`、`_glued`、`separable_fractionRing`、`quotient_span_mk_ne_zero_iff`、`ramificationIdx_invertible_of_dvd`）；**`residue_separable_global` = sorryAx** | **R（当前）**：13:31:03 首错 `214:25` Application type mismatch — `Algebra.IsIntegral.isIntegral x` 的 `IsIntegral` 实例是 quotient 环的 `commRing`/`instRingQuotient`，而 `minpoly.irreducible` 期望 `Field.toCommRing`（隐式参数 `?m.151/?m.152` 未 pin）。可引用版本仍只有 **12:41/12:58 版**的 `tame_localDifferentPaperOrder_le_one_of_tame`（hsep 显式假设，§4.47 不变）；13:22:54 的 DONE 只对应 13:25:57 之前的源码，**已 STALE**。`TameRamifiedAt` 的输入 (a)（剩余域可分）**仍无 producer**。 |
| 194 | Mzk1G1PsiChartToP1Actual（旧 DONE，本批复核） | G-C/B1 ψ 第一段 | **DONE** | 00:12:00（13:18 后无 attempt） | fresh（src 08:10 CST / olean 08:11 CST） | clean | 三公理 (P：`psiChart0ToP1_preimage_basicOpen`；L：另 2 条) | **A-局部，但目标 P¹ 是第三套模型**：`psiChart0ToP1 := Proj.fromOfGlobalSections …` 映到 **`projectiveLine`（Proj 模型）**，不是 π/xi 用的 `projectiveLineGlued`；`psiChart0ToP1_preimage_basicOpen` 给出 `ψ₀⁻¹ D_+(X0) = basicOpen (psiChart0Global X0)`（= D(∏(x−t)) 的图像）。**这是 B1 零纤维段的真组件**，但与 π/ξ 的 P¹ 不是同一个对象（§4.70）。 |
| 195 | IsFinite/IsProper 装配组（FermatSupport 23:49、FiniteDegree2 23:39、ProperFinal2 23:35、SmoothChart 00:13） | G-A proper/finite | **无 13:18 后 attempt** | 最后事件均 ≤ 00:57 | 全部 fresh | clean | 无 `#print`（Support 有，未 probe） | **B / 缺口明确**：现有 `IsFinite`/`IsProper` 只到 **chart 结构态射到 `Spec ℚ[λ]`**（`fermatChart0Map_isFinite/isProper`、`fermatChartInfMap_*`，有限 ⇒ proper）与**旧 closed-subscheme 模型**的 `fermatCurveι`（`fermatCurve_proper_support`）。**没有 `IsFinite (pi n)`，也没有 canonical `fermatCurveScheme n ⟶ Spec ℚ` 的 `IsProper`**；grace 的 "用 chart IsFinite/IsProper + P¹/ℚ proper 装配" 尚未开始（无新文件、watchdog 白名单里也无新 proper 目标）。 |
| 196 | **RETIRED 不变**（FermatCurveClosed / HullFermatClosedSubscheme / OmegaPresentation / FermatOverlapRing / TauCetiPort） | — | **RETIRED** | 13:18 后 **0 事件** | none | — | — | 白名单（99 项）仍不含它们；bridge 仍在 `coord/retired-port/*.retired`。**不得引用、不得再排 watchdog**（§4.60 第 4 条不变）。 |
| 197 | Mzk1G1JHeightLowerActual（**新文件**） | L-H j 下界 | **START 13:32:08（无结果）** | 13:32:08 | none | clean | — | **未判定**：45 行，仅含 `jQ00Z_isHomogeneous : jQ00Z.IsHomogeneous 4` 与两个 private 齐次性引理；快照时 attempt 仍在跑。**不得当 DONE 引用**。 |
| 198 | `_ProbeBatch10Actual`（本 lane） | audit probe | **DONE** | 13:31:53 | fresh（src 13:31:01 / olean 13:31:53） | — | 8 条全三公理，0 error / 0 sorryAx | 见 §3d。 |
| 199 | Mzk1G1PsiXiActual / Mzk1GlueMorphismActual / Mzk1G1ProjectiveLinePiOverlapActual（provider 复核，无 13:18 后变化） | G-A 工具 | **DONE** | 13:13:08 / 12:59:38 / 12:44:51 | fresh | clean | P9 三公理 | **A-局部（不变）**：`fermatCurveGlueMorphism`（h 为**输入**，xi 内联证 h）、`glueMorphisms_compat`、`fermatPiOverlap_condition`（π 的 h，三公理）。 |

## 3d. Probe 10（本批 batch 10）：`tmp/sheaf/xif/paper/_ProbeBatch10Actual.lean`

- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch10Actual.lean` → `{"added":1,"total":100}`。
- watchdog：**START 2026-11-16T13:31:18.665Z → DONE 13:31:53.441Z（35s）**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch10Actual.lean.log`（1093 B；**0 次 error、0 次 sorryAx、8 条 `depends on axioms`**）。
- 8 条独立复算（原样抄录，**全部 [propext, Classical.choice, Quot.sound]**）：

| 定理/定义（全名见文件） | axioms | 覆盖行 |
|---|---|---|
| `Mzk1G1FermatPiActual.pi`（def） | [propext, Classical.choice, Quot.sound] | #184（π 本体） |
| `Mzk1G1FermatPiActual.pi_ι0` | [propext, Classical.choice, Quot.sound] | #184 |
| `Mzk1LpDifferentBoundActual.localDifferentPaperOrder_le_boundedDegree` | [propext, Classical.choice, Quot.sound] | #188 |
| `Mzk1LpDifferentBoundActual.localDifferentOrder_eq_paperOrder_mul_ramification` | [propext, Classical.choice, Quot.sound] | #188 |
| `Mzk1G1FermatSmoothLocalizeActual.localizeEquiv`（def） | [propext, Classical.choice, Quot.sound] | #190（**关键**） |
| `G1JHeightBezoutActual.jBezUZ`（namespace 无 Mzk1 前缀） | [propext, Classical.choice, Quot.sound] | #191 |
| `Mzk1LpFinitenessActual.boundedDegreeFinitelyManyFields_of_fixed_degree` | [propext, Classical.choice, Quot.sound] | #189 |
| `Mzk1G1PsiChartToP1Actual.psiChart0ToP1_preimage_basicOpen` | [propext, Classical.choice, Quot.sound] | #194 |

- **未覆盖（明确未运行）**：`Mzk1G1FermatPiPreimageActual.pi_preimage_eq`（DONE 晚于本 probe 排队；只有 (L) 三公理）；`Mzk1G1FermatPiActual.pi_ι1`（只有 (L)）；`Mzk1G1PsiAffineOverlapActual.isUnit_q/isUnit_r`（文件 FAIL，无 olean，**不可 probe**）；`Mzk1HullFermatGluingActual` 的 def 级公理（未单独 probe）；`Mzk1LpFinitenessActual` 其余 5 条（只有 (L)）；`Mzk1G1FermatRadicalSupportFinal3Actual` 全部（当前 FAIL，不可 probe）。
- 结论：**kernel 层本批 8 条关键定理/定义无伪证**；风险全在语义层（π⁻¹ 目标未陈述、P¹ 双模型、BoundedDegree/固定次数有限性仍是假设、`residue_separable_global` 未证）与「DONE 后又被改写」（#193）。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 10 续）

### 4.68 【中·G-A】π 已真落地；π⁻¹ 只完成**分解簿记**，目标陈述仍缺
- #184：π 是 `fermatCurveGlueMorphism` 造出的 `fermatCurveScheme n ⟶ projectiveLineGlued`，chart 限制 = `chartMorphism0 (x0^n)` / `chartMorphismInf (r1^n)`；Probe 10 对 `pi`（def）与 `pi_ι0` 复算三公理。**这是 A-局部的真 `Y_n → P¹`，可以引用**（每次引用须带 olean 21:19:21 / src 21:18:10）。
- #185：`pi_preimage_eq` 只给出 `(pi)⁻¹V = chart0 ''ᵀ(piChart0⁻¹V) ⊔ chartInf ''ᵀ(piChartInf⁻¹V)`（诚实的集合层分解）。**文件里没有 `pi ⁻¹ᵁ D_+(X0) = D(x^n)` 或 `pi ⁻¹ᵁ D_+(X1) = D(r^n)` 的陈述**。G-A 的「π⁻¹ 原像」目标 = 分解式 + chart 原像事实（#186 红）+ π 的 λ=x^n 计算，**仍未闭合**。
- 纪律：**不得写「π⁻¹ 已证」**；正确表述是「π 的 chart 分解已证（`pi_preimage_eq`，三公理），两条 `D_+` 原像等式尚未陈述/证明」。

### 4.69 【高·G-A，好消息】A₀ 局部化识别闭合：`localizeEquiv` 已是真 AlgEquiv（#190）
- 13:29:11 DONE 的版本（src 13:28:15）：`localizeEquiv : Model n ≃ₐ[ℚ] Localization.Away (chartR n)`，两条 round-trip 都真证；Probe 10 复算 `localizeEquiv` = 三公理；日志 0 sorryAx。**batch 9 的 §4.64（Loc 侧两条 + `localizeEquiv` = sorryAx）作废**——不是改名，是证明修好。
- 仍缺（不变）：`Away x`/`Away y` 的第二层局部化、scheme 层 `Ω_{Y_n/ℚ}`、smoothness 的 scheme 层装配（`SmoothChart` 00:13 DONE 只到 chart 环 smooth，`SmoothGeomIntegral` 00:57 DONE 是 geometric integral）。
- 纪律：引用写「A₀ 的 `D(x)` 局部化 ≅ Model 已证（三公理）；scheme 层 smooth/proper 未装配」。

### 4.70 【高·G-A/G-C】**P¹ 出现两套模型**：`projectiveLineGlued`（π、xi）vs `projectiveLine`（ψ 第一段）
- π（#184）与 xi（#169）都用 **`Mzk1G1ProjectiveLineGluedActual.projectiveLineGlued`**（两张 `Spec ℚ[λ]`/`Spec ℚ[t]` 的 glue）。
- ψ 第一段（#194）用 **`projectiveLine = Proj ℚ[X0,X1]`**（`Proj.fromOfGlobalSections`）。两者**没有任何文件证明同构**（没有 iso、没有 transport 引理）。
- 风险：B1/B2 要把 ψ 与 π 复合（B2/B3 用 π），一旦混用就是换题；把它写成「同一个 P¹」即违规。**Lead 需裁决**：(a) 在 `projectiveLineGlued` 上重写 ψ 第一段（用 `chartMorphism0/Inf` + `u = ∏(x−t)`），或 (b) 先证 `projectiveLine ≅ projectiveLineGlued`（把 Proj→glued 的 chart 同构 + cocycle 拼起来），再给 transport。
- 纪律：引用 ψ 与 π 时必须分别写全名 `projectiveLine` / `projectiveLineGlued`；**不得写 "P¹" 了事**（与 §4.63 的 Y_n 双模型同级）。

### 4.71 【高·纪律】**修正 §4.60**：π 的具体用户级等式 h 已证；「cocycle 未证」只对**通用陈述**成立
- 证据：`fermatPiOverlap_condition`（PiOverlap DONE 12:44:51；自带 `#print` = 三公理）= `overlapToChart0 n ≫ chartMorphism0 (x0^n) = overlapToChartInf n ≫ chartMorphismInf (r1^n)`，正是 π 传给 `fermatCurveGlueMorphism` 的 h；xi 的 h 在 #169 里内联证（`chartMorphism_transition` + `overlapToChart*_spec`）。**GlueData 的 `t_fac/cocycle/f_open` 亦真证**（#192）。
- 因此本批的准确表述分三层：**(i) 通用装配器 `glueMorphisms_compat`/`fermatCurveGlueMorphism` 把 h 当输入（h 不作为定理存在）；(ii) 两个实际消费者 xi、π 各自的 h 已证（三公理）；(iii) `HullFermatGluingActual` 第 136–148 行的 user-facing cocycle 等式 `twoChartGlue_condition` 仍未陈述。**
- **风险条目「cocycle 用户级 h 未证」继续留在表中**（不删），但引用 π/xi 时**不得**再说「依赖未证的 h」——那是错的；说「π/xi 的 h 已证，通用 cocycle 陈述缺失」才对。

### 4.72 【中·G-C】π⁻¹ 的 P¹ chart 原像仍红：`p1GlueData.f` 与 `overlapToChart*` 未接
- #186 当前首错：`31:79/40:77` unsolved goals `opensRange (p1GlueData.f (true,false)) = opensRange overlapToChartInf`（对称地 `(false,true)` vs `overlapToChart0`）。即 `localChart0/localChartInf` 与 `p1GlueData.ι` 的 defeq 已能展开，但 `p1GlueData.f` 与 `ProjectiveLineGlued` 里命名的 `overlapToChart*` 需要一条 `rfl`/`simpa [p1GlueData, overlapToChartInf]` 的桥。
- 修法（机械）：在 `ProjectiveLineGluedActual` 里为 `p1GlueData.f (ULift.up true) (ULift.up false) = overlapToChartInf`（及对称）补两条 `rfl` 引理，再 `rw`；`localChart0_opensRange_sup_localChartInf` 用 `Scheme.Opens.ext` + `ι_jointly_surjective`（`D.ι_jointly_surjective` 而非 `localChart_jointly_surjective` 的点集版）。
- 前三次 FAIL（13:22/13:24/13:27）首错**未取**（log 缺失，见 §2i 纪律）——不得据此判 "新回归"。

### 4.73 【中·F7/H-T】`residue_separable_global` 仍是 (a) 的唯一缺口；首错是实例 pin
- #193 13:31:03 首错 `214:25`：`minpoly.irreducible (Algebra.IsIntegral.isIntegral x)` 里 `IsIntegral` 用的是 `Ideal.Quotient.commRing`/`instRingQuotient`，而目标要求 `Field.toCommRing`。修法：不要走 `@Algebra.IsAlgebraic.isSeparable_of_perfectField` 的 7 个隐式参数全给 `_`；改为 `exact Algebra.IsSeparable.of_integral (K := Int ⧸ span{p}) ...`，或先用 `haveI : IsScalarTower ...`/`letI : Field (𝓞 K ⧸ P)` 把两个 `Field` 实例固定，再 `exact isSeparable_of_perfectField`（同时给 `(K := …) (L := …)`）。
- 现状：`olean` 仍 12:58:53，**当前源码不可引用**；F7 的 `TameRamifiedAt → TameCount` 链（#152）仍缺 (a)，因此 **F7 的 htame 不能记完成**。

### 4.74 【中·G-K】Lp 侧本批两个条件式闭合，但 `BoundedDegreeFinitelyManyFields` 仍是假设
- #188：`localDifferentPaperOrder_le_boundedDegree`（`[L:K] ≤ d` ⇒ `ord_p(𝔇_L) ≤ ord_p(𝔇_K) + log_p d + 1/e_K`）与归一化字典都可引用（Probe 10 三公理）。
- #189：`BoundedDegreeFinitelyManyFields d` 现在**精确等价于**「每个 `n ≤ d` 的固定次数有限性」（正反两条都证了），但固定次数有限性本身**没有证明**（Eisenstein 系数有限性 + Krasner 的 step 2 仍未形式化）。`universalLocalFieldExists_of_finite`/`_intermediateField` 因此仍是**条件 producer**；`GKCompactInput` 仍 NO INHABITANT。
- 纪律：G-K 的 L_p 只能记「由 per-degree finiteness 条件生产」，**不得记无条件**。

### 4.75 【低·L-H】`jBezUZ/jBezVZ` 是真 ring 恒等式，但高度下界尚未组装
- #191 的两条 Bézout 恒等式（`q00A + q01B = 256X0^10`、`q10A + q11B = 256X1^10`）由 `ring` 证出、三公理；这是 `h(j) ≥ 6h(λ) − C` 的**代数**输入。下界需要 `JHeightLower`（#197，START 13:32:08）的齐次性 + `Height` 函子性，**当前未完成**；D3 的 `HeightDictionaryInterface` 仍无 inhabitant。

## 5f. batch 10 立即动作（快照 13:33 UTC）

1. **π⁻¹ 目标陈述（henry，最高优先）**：在 `Mzk1G1FermatPiPreimageActual` 里加两条目标定理：`pi_preimage_chart0 : (pi n) ⁻¹ᵁ (D_+(X0)) = basicOpen (x0 n ^ n)`、`pi_preimage_chartInf : (pi n) ⁻¹ᵁ (D_+(X1)) = basicOpen (r1 n ^ n)`，用 `pi_preimage_eq` + `chartMorphism0_preimage_basicOpen`（需先在 P¹ glued 侧证）组合。这是 G-A 的唯一剩余接口。
2. **P¹ chart 原像（emmy/henry）**：`ProjectiveLineChartPreimageActual` 补 `p1GlueData.f (true,false) = overlapToChartInf` 两条 rfl 引理；`localChart0_opensRange_sup_localChartInf` 改用 `D.ι_jointly_surjective`。
3. **ψ 的 P¹ 模型（Lead 裁决，§4.70）**：二选一——在 `projectiveLineGlued` 上重写 ψ 第一段，或先证 `projectiveLine ≅ projectiveLineGlued`。**在裁决前，禁止把 ψChart0ToP1 与 π 复合。**
4. **PsiAffineOverlap（emmy，一处机械）**：补 `import/open Mzk1G1FermatAffineChartActual`（`R` 在那里定义）。绿了才有 B1 的 overlap 环层。
5. **RadicalSupport（sophie，一处机械）**：按 §4.73 固定 `Field` 实例后重证 `residue_separable_global`；绿之前 F7 的 (a) 记「未证」，`_glued` 仍带 hsep 显式假设。
6. **IsFinite/IsProper 装配（grace）**：canonical `fermatCurveScheme` 上的 `IsProper` / `IsFinite (pi n)` 还没有任何文件；现有 `fermatChart0Map_*` 只到 `Spec ℚ[λ]`，不能直接当 P¹ 的 proper 用。建议新建 `Mzk1G1FermatProperGluedActual`，用 `IsProper` 的 `openCover`/`locally` 判据 + P¹ 的 `IsProper`。
7. **引用纪律（batch 10 版，强制）**：
   - π：`Mzk1G1FermatPiActual.pi`（三公理，olean 21:19:21）；**π⁻¹ 只有分解式**。
   - `localizeEquiv`：可引用（三公理，olean 21:29:11）。
   - `residue_separable_global`、`pi_preimage_eq` 之外的 RadicalSupport 当前版、`JHeightLower`：**禁引用**。
   - P¹ 必写 `projectiveLineGlued` / `projectiveLine`；Y_n 必写 `fermatCurveScheme` / `fermatCurveSchemeIso`。
   - cocycle：见 §4.71 三层表述。

## 6g. batch 10 更新（快照 **13:33 UTC = 21:33 CST**；覆盖 §6/§6b–§6f 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_status.mjs … --err`（对 20 个文件逐个取最后 START/DONE/FAIL 与首错：Pi、PiPreimage、ChartPreimage、PsiAffineOverlap、LpDifferentBound、LpFiniteness、SmoothLocalize、JHeightBezout、HullFermatGluing、RadicalSupportFinal3、ProperFinal2、Support、FiniteDegree2、SmoothChart、SmoothGeomIntegral、SmoothIntegral、PsiChartToP1、GlueMorphism、PsiXi、PiOverlap）；`watchdog.log` 13:18:52–13:32:08 的 DONE/FAIL/RETRY 全量抽取 + 13:11 起的尾段对照；olean/源码 mtime 对照（21 个文件）；禁用项 grep（9 个源文件，唯一命中为 `SmoothLocalize` 头注释与 `maxHeartbeats 800000`）；源码语义阅读（Pi 全文 43 行、PiPreimage 全文 71 行、ChartPreimage 全文 53 行、PsiAffineOverlap 全文 70 行、LpDifferentBound 全文 85 行、SmoothLocalize 300–419、JHeightBezout 1–70、JHeightLower 全 45 行、LpFiniteness 85–278、RadicalSupport 185–216、Support 1–68、FermatCurveActual 模型 def、PiOverlap 80–107、PsiXi 的 xi/glue 段、PsiChartToP1 全文、HullFermatGluing 声明表 + TECHNICAL NOTE、`fermatChart0Map` 的 codomain）。
- **Probe 10**：`_ProbeBatch10Actual.lean`，`wd_add` → `{"added":1,"total":100}`，**START 13:31:18.665Z → DONE 13:31:53.441Z（35s）**，8 条全部 [propext, Classical.choice, Quot.sound]，0 error / 0 sorryAx（详见 §3d）。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未运行 / 未覆盖（如实标注）**：
  - `Mzk1G1FermatPiPreimageActual.pi_preimage_eq`：DONE 晚于 probe 排队，**未 audit-probe**（只有 (L) 三公理）。
  - `Mzk1G1ProjectiveLineChartPreimageActual` 13:22/13:24/13:27 三次 FAIL 的**首错未取**（per-file log 不存在）；只有 13:29:52 / 13:31:49 两次的首错。
  - `Mzk1G1PsiAffineOverlapActual`：文件 FAIL、无 olean ⇒ `isUnit_q/isUnit_r` **只能引 (L)**，未 probe。
  - `Mzk1G1FermatRadicalSupportFinal3Actual`：当前版 FAIL，**不可 probe**；13:22:54 DONE 的 olean（12:58:53）与当前源码差 27 分钟，**未审计该版本**。
  - `Mzk1LpFinitenessActual` 其余 5 条、`Mzk1HullFermatGluingActual` def 级、`Mzk1G1FermatSupportActual` 五条：只有 (L)/旧结论，**未 audit-probe**。
  - `Mzk1G1JHeightLowerActual`：START 13:32:08，**快照时无结果**。
  - U-R 全组（除 PiOverlap/URTheta* 的旧结论）、G-K 递归构造、H-T 的 F1–F4/F8、P8-P 端到端：**未运行**语义审计。
- **快照 13:33 UTC 之后**：watchdog 仍在跑（13:32:08 已 START `JHeightLower`，pending=1；`PiPreimage`/`ChartPreimage`/`PsiAffineOverlap`/`RadicalSupportFinal3` 仍在高频重试）。13:33 之后的任何 DONE/FAIL 本表**未审计**。
- **本批新发现并已写进正文的纪律**：§4.69（`localizeEquiv` 已证）、§4.70（**P¹ 双模型**：`projectiveLineGlued` vs `projectiveLine`，新增高风险）、§4.71（§4.60 的三层修正：π/xi 的 h 已证，通用 cocycle 陈述仍缺）、§4.72（`p1GlueData.f` 与 `overlapToChart*` 的桥缺失）、§2i 的日志纪律（log 有时累积、有时不存在）。


### 2i-2 快照后补记（13:33–13:34 UTC；只补事件，不改 §2i 表内已记录的判定）

| 时间 (UTC) | 事件 | 文件 | 备注 |
|---|---|---|---|
| 13:32:41 | FAIL | Mzk1G1JHeightLowerActual | 31s；**per-file log 不存在**（`wd_status --err` 报 no log file），首错未取；src 13:33:50 又被改，当前版未编译 ⇒ #197 更正为 **FAIL（首错未取）**，禁引用 |
| 13:33:02 | FAIL | Mzk1LpHenselNearRootActual（**新文件**，kurt） | 6s；首错 `19:0 invalid 'import' command, it must be used in the beginning of the file`（文件头 `/-! … -/` 模块文档 + 5 条 import 的排版问题，机械）；内容：**G-K §7.2 step 2 的域级 Hensel 近根存在性**（`‖f.eval a‖ < ‖f.derivative.eval a‖^2 ⇒ ∃ b, ‖b−a‖ < ‖f' a‖`，Newton 迭代留在闭单位球；`set_option maxHeartbeats 4000000`，注释声明非语义捷径）。**R（机械），无 olean，禁引用**；若修好，这是 `BoundedDegreeFinitelyManyFields` 所需的 Eisenstein/Krasner 输入的第一块 |

- 这两条不改变 §2i 的其余判定；快照后的其它任何变化本表**未审计**。

## 2j. 本批 batch 11 gate 表（快照 **14:09 UTC = 22:09 CST**；**新增 #200–#220**，覆盖 13:33–14:08 的全部 DONE/FAIL/START + STALE/RETIRED）

grep 列 = 大小写敏感扫描 sorry|admit|axiom|PUnit|surrogate|toy|maxHeartbeats|True（本批 18 个源文件；命中仅为文件头注释里的禁项字样、set_option maxHeartbeats（ChartFinite/2 1.6e6、JHeightLower 4×8e5、PiProper 8e5）、URThetaRegion 的 "surrogate" 注释，均人工排除；P1Proper/PsiAffineCompat 当前源码 **0 处字面 sorry**，早期 attempt 的 "declaration uses sorry" 警告属于旧版本，不得沿用）。axioms 列：(P11)/(P11b)/(P11c) = 本批三个 audit probe 独立复算；(L) = 当前 attempt 自带 #print 的**日志末段**；— = 无 #print 或未 probe。olean 列 fresh = olean mtime > 源码 mtime；**STALE = 最后一次 DONE 之后源码又被改，或最后一次 attempt 是 FAIL**。

**13:33–14:08 DONE/FAIL 全量（按文件压缩；D = DONE，F = FAIL）**

| 文件 | DONE 时刻 (UTC) | FAIL 时刻 (UTC) |
|---|---|---|
| Mzk1G1PsiAffineOverlapActual | 13:37:13, **13:45:20** | 13:40:19, 13:42:53, 13:44:07 |
| Mzk1G1ProjectiveLineChartPreimageActual | 13:34:42, **13:37:12** | — |
| Mzk1G1FermatChartFiniteActual | **13:48:28** | 13:34:43, 13:37:13, 13:41:32, 13:44:08, 13:46:02 |
| Mzk1G1FermatChartFinite2Actual | **13:53:28** | 13:51:20 |
| Mzk1G1FermatPiPreimageActual | 13:31:50（本批无 attempt） | — |
| Mzk1G1FermatPiPreimageChartActual | — | 13:40:19, 14:02:59, 14:04:11, 14:06:54, 14:08:47 |
| URThetaRegion | **13:37:19** | 13:35:25 |
| Mzk1URJ1Actual | 13:52:36（旧 6 定理版） | 13:36:17, 13:47:41, 13:50:28, 13:58:17, 14:00:58, 14:03:26, 14:05:23, **14:07:10** |
| Mzk1URRootExtInstancesActual | **13:54:41** | 13:42:01, 13:44:34, 13:47:44, 13:50:31, 13:52:38 |
| Mzk1G1FermatRadicalSupportFinal3Actual | 13:33:55, 13:46:29, 13:52:40, **14:03:30** | 13:37:48, 13:40:48, 13:43:22, 13:50:32, 13:58:21, 14:02:11 |
| Mzk1G1JHeightLowerActual | 13:47:14, **13:59:51** | 13:35:00, 13:37:29, 13:39:37, 13:42:11, 13:44:41, 13:49:13, 13:51:21, 13:53:29, 13:55:27, 13:57:51 |
| Mzk1G1PsiProductIdentityActual | **13:51:22** | 13:48:28 |
| Mzk1HullFermatGluingActual | **13:37:25** | 13:34:55 |
| Mzk1UCHpktActual | **13:37:42** | 13:33:52 |
| Mzk1P1ProperActual | **14:04:12** | 13:53:28, 13:57:01, 13:59:07, 14:01:42, 14:03:00 |
| Mzk1G1PsiAffineCompatActual | 14:01:43（旧版） | 13:53:28, 13:55:25, 13:59:07, **14:03:01**, 14:08:37 |
| Mzk1G1FermatPiProperActual | 13:59:06, **14:07:52** | 13:56:11 |
| Mzk1F7SeparableResidueActual | — | 13:57:51, 13:59:08, 14:01:44 |
| Mzk1G1FermatCurveToSpecActual | **14:00:33** | 13:57:49 |
| Mzk1LpHenselNearRootActual | — | 13:33:02, 13:37:03, 13:42:48, 13:44:01, 13:47:07, 13:48:21, 13:51:13, 13:53:21, 13:55:20, 13:57:42, 14:02:53, 14:05:59, **14:07:47** |
| Mzk1F7TameCountGlobalActual | **14:07:09** | — |
| _ProbeBatch11Actual / 11b / 11c | 13:56:36 / 14:05:22 / **14:09:01** | — |
| _ScratchEmmyStatement / _ScratchEmmyStmt3 | 14:06:43（scratch） | 14:04:55（scratch） |

| # | 文件（tmp/sheaf/xif/paper/） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 200 | Mzk1G1PsiAffineOverlapActual（覆盖 §2i#187） | B1 ψ 仿射 overlap | **DONE** | 13:45:20（src 21:44:47） | fresh（olean 21:45:20） | clean | 三公理 (P11：chartMorphism0_comp / chartMorphismInf_comp；L：isUnit_q / isUnit_r) | **A-局部（通用 chart 换基 + B1 overlap 环）**：两个通用引理**定理名确认**：chartMorphismInf_comp (hf : f.comp (algebraMap ℚ A) = algebraMap ℚ B) (a : A) : Spec.map (ofHom f) ≫ chartMorphismInf (R:=A) a = chartMorphismInf (R:=B) (f a)，chartMorphism0_comp 同型；即沿任意 **Q-代数 ring hom** 运输 chart 态射。chartMorphism0 a = Spec.map (evalAt a) ≫ localChart0（evalAt a : ℚ[λ]→R，λ↦a），所以引理是到 **P¹ 的 chart 态射**的复合，不是仿射 Spec.map (evalAt a) 的等式；**不能直接当 IsFinite 运输接口**（见 §4.77）。B1 环层 overlapRing = Away(q_T · r)、isUnit_q/isUnit_r 真证；scheme 层 chart0ToOverlap/chartInfPieceToOverlap 与 ψ 相容性仍未证。 |
| 201 | Mzk1G1ProjectiveLineChartPreimageActual（覆盖 §2i#186） | G-C P¹ chart 原像 | **DONE** | 13:37:12（src 21:36:21） | fresh（olean 21:37:11） | clean | 三公理 (P11：preimage_opensRange_ι；L：全部 4 条) | **A-局部（§4.72 机械缺口闭合）**：四条全绿——preimage_opensRange_ι (D : Scheme.GlueData) (i j) : (D.ι i) ⁻¹ᵁ (D.ι j).opensRange = (D.f i j).opensRange（通用 GlueData 引理，用 D.ι_eq_iff/D.Rel，真证）；localChartInf_preimage_localChart0 / localChart0_preimage_localChartInf（p1GlueData 实例 + rfl）；localChart0_opensRange_sup_localChartInf（两 chart 覆盖，localChart_jointly_surjective）。**这是 P¹ chart 原像工具，不是 π⁻¹ 目标**；见 §4.78。 |
| 202 | Mzk1G1FermatChartFiniteActual（新文件，覆盖 §2i#195） | G-A/π λ-chart finite | **DONE** | 13:48:28（src 21:47:26） | fresh（olean 21:48:28） | clean（头注释禁项字样 + maxHeartbeats 1600000） | 三公理 (P11：chartRing_finite / lamHom_finite / lamHomSpec_isFinite；L：另 7 条) | **A-局部（λ-chart 的 IsFinite 核心）**：R n = ℚ[X0,X1]/(X0^n+X1^n−1)，lamHom n : ℚ[λ]→R n，λ↦x0^n；x0 整（monic X^n−λ）、y1 整（monic X^n−(1−λ)），adjoin {x0,y1}=⊤，Algebra.IsIntegral.finite 得 Module.Finite，再 IsFinite.SpecMap_iff 得 lamHomSpec_isFinite : IsFinite (Spec.map (ofHom (lamHom n)))。**这是 piChart0 = chartMorphism0 (x0^n) 的仿射底层 Spec R→Spec ℚ[λ] 有限性；不是 IsFinite (pi n)**（见 §4.76）。 |
| 203 | Mzk1G1FermatChartFinite2Actual（新文件） | G-A/π ∞-chart finite | **DONE** | 13:53:28（src 21:52:18） | fresh（olean 21:53:28） | clean（头注释禁项字样 + maxHeartbeats 1600000） | 三公理 (P11b：chartRing_finite2 / lamHom2Spec_isFinite；L：另 4 条) | **A-局部（∞-chart 的 IsFinite 核心）**：R2 n = ℚ[X0,X1]/(1+X0^n−X1^n)，lamHom2 n : ℚ[t]→R2 n，t↦z1^n；z1、z0 整，adjoin=⊤，同上得 lamHom2Spec_isFinite。z1 与 r1 定义上同为 mk (X1)（idealInf = span{secondEquation} 是 abbrev），所以这是 piChartInf = chartMorphismInf (r1^n) 的仿射底层。**两块 chart finite 至此都绿；仍无 IsFinite (pi n)**。 |
| 204 | Mzk1G1FermatPiPreimageActual（§2i#185，不改） | G-A/π⁻¹ 簿记 | **DONE** | 13:31:50（src 21:30:59） | fresh（olean 21:31:49） | clean | 三公理 (P11：pi_preimage_eq；L：fermatCurve_cover) | **A-局部（分解式，非目标）**：pi_preimage_eq (V) : (pi n) ⁻¹ᵁ V = chart0 ''ᵁ (piChart0⁻¹V) ⊔ chartInf ''ᵁ (piChartInf⁻¹V)，用 fermatCurve_cover + pi_apply_chart0/Inf。**文件里仍没有 pi⁻¹(D_+(X0)) = D(x0^n) / pi⁻¹(D_+(X1)) = D(r1^n) 的陈述**；不得写「π⁻¹ 已证」（§4.78）。 |
| 205 | Mzk1G1FermatPiPreimageChartActual（新文件，14:02 重建） | G-A/π⁻¹ chart 目标 | **FAIL** | 14:08:47（14:02:59/14:04:11/14:06:54 亦红；src 22:05:47） | none | clean | —（无 #print） | **R（机械）**：新增 8 条：specMap_preimage_primeBasicOpen、primeBasicOpen_pow_le、overlapToChartInf_opensRange、overlapToChart0_opensRange、piChart0_preimage_chart0 = ⊤、piChartInf_preimage_chart0 = basicOpen(r1^n)、piChart0_preimage_chartInf = basicOpen(x0^n)、piChartInf_preimage_chartInf = ⊤。首错：overlapToChartInf/0 rewrite 失败（等式定理不可用）；Mzk1G1ProjectiveLineGluedActual.overlapSchemeIso **unknown**（该 iso 实际在 Mzk1G1FermatOverlapActual）；IsOpenImmersion ?m stuck；Ideal.pow_mem_of_mem p.asIdeal hf n 参数类型。**π⁻¹ 目标仍未闭合**。 |
| 206 | URThetaRegion（覆盖 §2i#197 邻域） | U-R J1 θ 区域 | **DONE** | 13:37:19（src 21:36:12） | fresh（olean 21:37:18） | clean（"surrogate" 注释） | 三公理 (L：ur_thetaRegion_subset_hull) | **B−/C（定义自反）**：ur_thetaRegion_subset_hull = arithmeticTupleStepVPossibleImages places tuple istar varpi ⊆ p6PacketHull places tuple e istar varpi，而 p6PacketHull 按定义是 possibleImages 的 holomorphic hull，故是 A ⊆ hull(A)；虽然用了 actual p6 数据与真正非零 varpi，但**不是 C2 的 θ_P5 ≤ H_pkt**。不得当 θ 侧 producer（§4.81）。 |
| 207 | Mzk1URJ1Actual（覆盖 §2i#197） | U-R J1 | **FAIL / STALE** | 14:07:10（旧 6 定理版 DONE 13:52:36；src 22:05:57） | stale（olean 21:52:35） | clean | 旧版 6 条三公理 (L)；新版 ur_cNorm_eq_localNormOrder、urM_eq_half_qMagnitude = **sorryAx** | **R（当前）/ B+（旧版）**：旧 6 条全绿（ur_qRootLattice_int、ur_thetaSourceSpan_int、ur_thetaRegion_subset_hull、ur_qReading_root_formula、ur_perB_q_le_theta、ur_qReading_theta_order）——J1 的机械修红完成，但其中 ur_thetaRegion_subset_hull 是 #206 的 C wrapper，ur_perB_q_le_theta 是 donor re-export。新版加 C2 q-side 归一化：ur_cNorm_eq_localNormOrder 在 97:74 因 Real.logb 的除号/负号未归位；urM_eq_half_qMagnitude 在 121:2 Finset.sum_congr 不匹配（LHS 已提 1/(2l)、RHS 未提），两条均 sorryAx。**M = Q/(2l) 的加权求和仍未证**（§4.81）。 |
| 208 | Mzk1URRootExtInstancesActual（覆盖 §2i#197 邻域） | U-R q 侧实际质量 | **DONE** | 13:54:41（src 21:53:06） | fresh（olean 21:54:41） | clean（头注释禁项字样） | 三公理 (P11b：urRootAlpha_mass；L：另 4 条) | **A-局部（C2 q 侧 step 1 闭合）**：urRootAlpha_mass 把 donor normalizedLogMass_kummer_root 实例化到实际 b 的 (rootNormedExtension T b, urRootAlpha T b, d=2l, q_b)，得 (1/finrank)·(log μ(α·O)−log μ(O)) = (1/(2l))·log‖q_b‖；urRootAlpha_mass_order 转成 −(1/(2l))·ord_p(q_b)·log p。urRootTheta_mass、urRootTheta_mass_neg_order、urRootQ_log_norm_order 亦三公理。**这是 C2 q 侧缺失的「actual per-b 实例化」，已真证**；仍缺按 nativeBadLocalWeight 求和成 M 与 P5 读数同一性（#207 正尝试，红）。 |
| 209 | Mzk1G1FermatRadicalSupportFinal3Actual（覆盖 §2i#193） | F7/H-T tame 桥 | **DONE** | 14:03:30（src 22:02:25） | fresh（olean 22:03:30） | clean | 三公理 (P11b：residue_separable_global；L：tame_count_differentIdeal_eq、tame_localDifferentPaperOrder_le_one_of_tame、_glued、separable_fractionRing、quotient_span_mk_ne_zero_iff、ramificationIdx_invertible_of_dvd、ramificationIdx_invertible_zmod) | **A-局部（F7(a) producer 落地，本批最重要转绿）**：新增 residue_separable_global (P) [P.IsMaximal] [P.LiesOver span{p}] : Algebra.IsSeparable (ℤ⧸(p)) (𝓞K⧸P)，走 ZMod 路线（ZMod p 有限 ⇒ PerfectField.ofFinite；Int.quotientSpanNatEquivZMod 传 Fintype；Ideal.absNorm_ne_zero_iff 给 residue finite；Algebra.IsAlgebraic.of_finite；inferInstance 出 separable）。**三公理、0 sorryAx，F7(a) 的 producer 成立**。注意：TameRamifiedAt 还要求 P.IsPrime + P.LiesOver + absNorm(under)=p 推出 P.IsMaximal（由 prime+ne_bot），消费者由 #218 完成；tame_localDifferentPaperOrder_le_one_glued 的**局部** hsep 仍是显式假设（局部域 ≠ 全局数域，见 §4.85）。 |
| 210 | Mzk1G1JHeightLowerActual（覆盖 §2i#197） | L-H j 下界 | **DONE（仅齐次性）** | 13:59:51（src 21:58:42） | fresh（olean 21:59:50） | clean（4×maxHeartbeats 800000） | 三公理 (L：jQ00Z/jQ01Z/jQ10Z/jQ11Z_isHomogeneous) | **B−/A-局部（只到代数输入）**：当前源码只含 4 条 jQ**Z_isHomogeneous : IsHomogeneous 4；**没有** jBezK_left/right、jBez_relation、logHeight_jHeight_ge、jHeight_relation。13:48:11 的扩展版曾把这些写成 sorryAx（MvPolynomial.map_pow 等 unknown），随后被回退。**D3 的 h(j) ≥ 6h(λ)−C 仍未证**；HeightDictionaryInterface 仍 NO INHABITANT。 |
| 211 | Mzk1G1PsiProductIdentityActual（新文件） | B1 ψ 乘积 | **DONE** | 13:51:22（src 21:49:51） | fresh（olean 21:51:22） | clean | 三公理 (L：psi_algebraMap、psi_psiChart0Coord) | **A-局部（B1 真增量）**：psi_psiChart0Coord (T) : psi (∏_{t∈T}(x−t)) = iu1^|T| · algebraMap(q)，其中 q = psiChartInfDenom = ∏(1−t·r)，iu1 = 1/u1 是单位；用 psi_linear_factor 逐因子、Finset.prod_mul_distrib。这是 ψ 的 overlap 相容性核心恒等式；消费者 PsiAffineCompat 仍红（#213）。 |
| 212 | Mzk1P1ProperActual（新文件，覆盖 13:53/13:57 红） | G-A P¹ proper | **DONE** | 14:04:12（src 22:03:34） | fresh（olean 22:04:11） | clean | 三公理 (L：p1ProjToBase_isProper、subsingleton_hom_spec_rat、p1GluedToBase def) | **A-局部，但只到 Proj 模型 + 构造**：p1ProjToBase_isProper : IsProper p1ProjToBase（Proj.toSpecZero Gr 经 degree-zero ≅ ℚ 的 iso 传到 **projectiveLine（Proj 模型）**）；subsingleton_hom_spec_rat (X) : Subsingleton (X ⟶ Spec ℚ)；p1GluedToBase : projectiveLineGlued ⟶ Spec ℚ 由两张 chart 粘合，localChart0/Inf_p1GluedToBase 三公理。**没有 p1GluedToBase_isProper**——P¹_glued proper 仍未证；且 Proj 模型 vs glued 模型无 iso（§4.70/§4.83）。**快照后 22:11:44 源码又被改，当前 src 22:11:44 > olean 22:04:11 ⇒ STALE；本行判定只对 14:09 快照的 22:03:34 版有效。** |
| 213 | Mzk1G1PsiAffineCompatActual（新文件） | B1 ψ 仿射相容 | **FAIL / STALE** | 14:08:37（14:01:43 曾 DONE；src 22:02:12） | stale（olean 22:01:42 < src） | clean（无字面 sorry） | 旧 DONE 版 axioms 未取（log 被清）；当前 FAIL 无 #print | **R（当前）/ B1 未闭**：14:01:43 的版本含 rUnit/qUnit/psiUnit、qToOverlap_coord、rToOverlap_coord；31s 后源码扩到 8.2KB，加 rToOverlap_rat/qToOverlap_rat/affine_compat，随后 14:03:01/14:08:37 连续红。首错：126:34 把 val_pow 的结果当 Function.symm 投影；128:65 ?a⁻¹ ^ ?n rewrite 不匹配（目标 ↑(rUnit)⁻¹ ^ T.card * ↑qUnit = ↑qUnit * ↑(rUnit^T.card)⁻¹）。**B1 的 scheme 层相容性仍未闭合**。 |
| 214 | Mzk1G1FermatPiProperActual（覆盖 13:59 版） | G-A Y_n proper | **DONE** | 14:07:52（13:59:06 亦 DONE；src 22:06:37） | fresh（olean 22:07:51） | clean（maxHeartbeats 800000） | 三公理 (L：fermatChart0/InfToCurve_fermatCurveToBase、fermatCurveToBase_eq_pi_comp、fermatCurveToBase_isProper、subsingleton_hom_spec_rat) | **B（条件式装配）**：fermatCurveToBase : fermatCurveScheme n ⟶ Spec ℚ 由 (fermatTwoChartGlueData n).openCover.glueMorphisms 粘两张 chart base map（相容性 Subsingleton.elim）；fermatCurveToBase_eq_pi_comp : fermatCurveToBase = pi ≫ p1GluedToBase（Subsingleton）；fermatCurveToBase_isProper **假设 hfin : IsFinite (pi n) 与 hP1 : IsProper p1GluedToBase**，finite⟹proper + proper 复合。**两个假设都无 producer**（见 §4.76）；IsFinite (pi n) 全树仍无。 |
| 215 | Mzk1F7SeparableResidueActual（新文件） | F7(a) 独立版 | **FAIL** | 14:01:44（src 22:00:12） | none | clean | —（无 #print） | **R（机械）/ 可 retire**：separable_residue 在 46:28 用 Module.Finite.of_fg_top ⟨Finset.univ, by simp⟩，构造子类型推断成 Eq.refl；50:10 又报 Field (ℤ⧸span{p}) synthInstanceFailed。**#209 的 residue_separable_global 已用另一种写法成功**，本文件可 retire，不要再排 watchdog。 |
| 216 | Mzk1G1FermatCurveToSpecActual（新文件） | G-A Y_n→Spec ℚ | **DONE** | 14:00:33（src 21:59:22） | fresh（olean 22:00:33） | clean | 三公理 (P11b：fermatCurveToSpec def；L：fermatOverlapToSpec_compat、fermatCurveToSpec_ι0/ι1) | **A-局部（canonical 结构态射）**：fermatCurveToSpec = fermatCurveGlueMorphism n fermatChart0ToSpec fermatChartInfToSpec fermatOverlapToSpec_compat，fermatChart0ToSpec/InfToSpec 是 Q-代数结构 Spec.map (algebraMap ℚ _)；两条 ι 限制三公理。**与 #214 的 fermatCurveToBase 重复构造**（两者都真；引用时写全名）。properness 仍缺。 |
| 217 | Mzk1LpHenselNearRootActual（新文件，kurt） | G-K §7.2 step 2 | **FAIL** | 14:07:47（src 22:04:58） | none | clean | —（无 #print） | **R（机械，多错）**：首错 45:51 max_eq_left (LT.lt.le h) 被当 ≤ 用；46:9 unknown le_or_lt；82:2 ‖↑(n+1)‖ vs ‖↑n+1‖；100:57 rfl 目标不匹配；156:10 rewrite motive 不正确；219:4 linarith 失败。**G-K step 2 仍未落地**；BoundedDegreeFinitelyManyFields 无 producer。 |
| 218 | Mzk1F7TameCountGlobalActual（新文件） | F7 htame | **DONE** | 14:07:09（src 22:06:xx） | fresh（src 22:05:45 / olean 22:07:08） | clean | 三公理 (P11c：tameCount_of_div_ramification、disc_factorization_le_finrank_of_div_ramification) | **A-局部/条件式（F7 htame 的真正 consumer）**：tameCount_of_div_ramification (hdiv) (hpn) : TameCount K p，内部用 #209 的 residue_separable_global P 得 (a)，用 ramificationIdx_invertible_of_dvd 得 e 在 ℤ⧸(p) 中非零，再 count_differentIdeal_eq_of_tame；disc_factorization_le_finrank_of_div_ramification 给 v_p(|disc K|) ≤ [K:ℚ]。**条件只剩算术输入 hdiv（每个 normalized factor 的 e_P ∣ n）与 hpn : ¬ p ∣ n**；这正是 F7 的 htame 条件式闭合，不是无条件。 |
| 219 | **RETIRED 不变**：FermatCurveClosedActual、HullFermatClosedSubschemeActual、OmegaPresentationActual、FermatOverlapRingActual、TauCetiPort/** | — | **RETIRED** | 13:33 之后 **0 事件** | none | — | — | 白名单仍不含；bridge 仍在 coord/retired-port/Mzk1TauCetiHaarScalingBridgeActual.lean.retired，全 paper 0 import。**不得引用、不得再排 watchdog**。 |
| 220 | _ProbeBatch11/11b/11c（本 lane） | audit probe | **DONE** | 13:56:36 / 14:05:22 / 14:09:01 | fresh | — | 8 + 6 + 2 条，全部 [propext, Classical.choice, Quot.sound] | 见 §3e/§3f/§3g。 |

## 3e. Probe 11（本批 batch 11）：tmp/sheaf/xif/paper/_ProbeBatch11Actual.lean

- 排队：node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch11Actual.lean → {"added":1,"total":111}。
- watchdog：**START 2026-11-16T13:55:41.513Z → DONE 13:56:36.943Z（55s）**；日志 dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch11Actual.lean.log（1115 B；**0 次 error、0 次 sorryAx、8 条 depends on axioms**）。
- 8 条独立复算（原样抄录，**全部 [propext, Classical.choice, Quot.sound]**）：

| 定理/定义（全名见文件） | axioms | 覆盖行 |
|---|---|---|
| Mzk1G1PsiAffineOverlapActual.chartMorphism0_comp | [propext, Classical.choice, Quot.sound] | #200 |
| Mzk1G1PsiAffineOverlapActual.chartMorphismInf_comp | [propext, Classical.choice, Quot.sound] | #200 |
| Mzk1G1ProjectiveLineChartPreimageActual.preimage_opensRange_ι | [propext, Classical.choice, Quot.sound] | #201 |
| Mzk1G1FermatChartFiniteActual.chartRing_finite | [propext, Classical.choice, Quot.sound] | #202 |
| Mzk1G1FermatChartFiniteActual.lamHom_finite | [propext, Classical.choice, Quot.sound] | #202 |
| Mzk1G1FermatChartFiniteActual.lamHomSpec_isFinite | [propext, Classical.choice, Quot.sound] | #202 |
| Mzk1G1FermatPiPreimageActual.pi_preimage_eq | [propext, Classical.choice, Quot.sound] | #204 |
| Mzk1G1FermatRadicalSupportFinal3Actual.ramificationIdx_invertible_zmod | [propext, Classical.choice, Quot.sound] | #209 |

## 3f. Probe 11b（补充）：tmp/sheaf/xif/paper/_ProbeBatch11bActual.lean

- 排队：{"added":1,"total":116}；**START 14:04:26.650Z → DONE 14:05:22.405Z（56s）**；日志 6 条 depends on axioms，0 error、0 sorryAx。
- 6 条（全部三公理）：

| 定理/定义 | axioms | 覆盖行 |
|---|---|---|
| Mzk1G1FermatRadicalSupportFinal3Actual.residue_separable_global | [propext, Classical.choice, Quot.sound] | #209（**F7(a)**） |
| Mzk1G1FermatChartFinite2Actual.chartRing_finite2 | [propext, Classical.choice, Quot.sound] | #203 |
| Mzk1G1FermatChartFinite2Actual.lamHom2Spec_isFinite | [propext, Classical.choice, Quot.sound] | #203 |
| Mzk1URRootExtInstancesActual.urRootAlpha_mass | [propext, Classical.choice, Quot.sound] | #208（C2 q 侧） |
| Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec（def） | [propext, Classical.choice, Quot.sound] | #216 |
| Mzk1G1FermatPiProperActual.fermatPi_isProper | [propext, Classical.choice, Quot.sound] | #214（条件式） |

## 3g. Probe 11c（补充）：tmp/sheaf/xif/paper/_ProbeBatch11cActual.lean

- 排队：{"added":1,"total":117}；**START 14:08:06.746Z → DONE 14:09:01.767Z（55s）**；2 条三公理，0 error、0 sorryAx。
- Mzk1F7TameCountGlobalActual.tameCount_of_div_ramification、...disc_factorization_le_finrank_of_div_ramification 均 [propext, Classical.choice, Quot.sound]。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 11 续）

### 4.76 【高·G-A，本批最大进展】IsFinite/IsProper 装配：两块 chart finite 已绿，缺 IsFinite π 与 IsProper P¹_glued
- 现有真件：ChartFinite（λ-chart，lamHom = λ↦x0^n，probe 三公理）与 ChartFinite2（∞-chart，lamHom2 = t↦z1^n = r1^n，probe 三公理）。两者分别是 piChart0/piChartInf 去掉 localChart0/Inf 后的仿射底层 Spec R→Spec ℚ[±] 有限性。
- 装配件：P1Proper 只证 **Proj 模型** p1ProjToBase : projectiveLine ⟶ Spec ℚ proper，并构造 p1GluedToBase : projectiveLineGlued ⟶ Spec ℚ，**没有 p1GluedToBase_isProper**；PiProper 用两张 chart base map 造出 fermatCurveToBase : fermatCurveScheme n ⟶ Spec ℚ，并给出 fermatCurveToBase = pi ≫ p1GluedToBase；fermatCurveToBase_isProper 仅条件式：hfin : IsFinite (pi n) + hP1 : IsProper p1GluedToBase。
- **仍缺**：(i) IsFinite (pi n) 的 scheme 层装配（把两块 chart finite 经 target 的 D_+(X0)/D_+(X1) 开覆盖 + 局部化传递）；(ii) IsProper p1GluedToBase（或 projectiveLine ≅ projectiveLineGlued 的 iso + transport）。在这两条之前，**不得写「π finite/proper 已证」「Y_n proper 已证」**；只能写「两块 chart finite 已证 + 条件式装配器已证」。
- 另：FermatCurveToSpec（#216）与 PiProper.fermatCurveToBase（#214）都构造了 Y_n→Spec ℚ，互为重复；引用必须写全名，不能说「唯一结构态射已证 proper」。

### 4.77 【中·G-A】PsiAffineOverlap 的 chart 换基引理不是 IsFinite 接口
- 事实：chartMorphism0_comp / chartMorphismInf_comp 的结论是 **到 P¹ 的 chart 态射** Spec.map (ofHom f) ≫ chartMorphism0 (R:=A) a = chartMorphism0 (R:=B) (f a)；chartMorphism0 a 本身还复合了 localChart0（开浸入，不是有限态射）。引理没有 Module.Finite f / IsFinite (Spec.map f) 假设。
- 因此**不能直接作为 IsFinite 运输接口**。IsFinite 需要的是仿射层等式 Spec.map (evalAt (f a)) = Spec.map f ≫ Spec.map (evalAt a)（证明里的 hring : f.comp (evalAt a) = evalAt (f a) 已经内证，但没有导出成定理），并且要加 Module.Finite f 再用「有限态射复合」。
- 建议 grace 补一条 evalAt_comp（rfl/congr 级）与一条 isFinite_specMap_evalAt_of_finite，再把它接到 #202/#203 的 chart finite；在那之前，**不要把 #200 当 IsFinite 运输接口引用**。B1 环层（overlapRing=Away(q*r)、isUnit_q/r）仍是真增量。

### 4.78 【中·G-C】P¹ chart 原像四引理已绿；π⁻¹ 目标仍未陈述/未证
- #201 四条全绿：preimage_opensRange_ι（通用 GlueData，A-局部）、localChartInf_preimage_localChart0、localChart0_preimage_localChartInf、localChart0_opensRange_sup_localChartInf。§4.72 的机械缺口（p1GlueData.f 与 overlapToChart* 的桥）已闭合。
- 但 #204 pi_preimage_eq 只是集合层分解；#205 PiPreimageChart 仍红（overlapSchemeIso 命名空间写错、overlapToChart* rewrite 失败、IsOpenImmersion stuck）。**仍没有 pi⁻¹(D_+(X0)) = D(x0^n) / pi⁻¹(D_+(X1)) = D(r1^n) 的定理**；不得写「π⁻¹ 已证」。下一步：把 #205 的 overlapSchemeIso 改成 Mzk1G1FermatOverlapActual.overlapSchemeIso，并把 overlapToChart* 的等式用 overlapToChart*_def/rfl 展开后再 rw。

### 4.79 【高·B1】ψ 的乘积恒等式已证，但 scheme 层仿射相容仍红；P¹ 双模型风险不变
- #211 psi_psiChart0Coord 三公理，是 B1 overlap 相容的真正代数核心：ψ(∏(x−t)) = iu1^|T| · q。psi_linear_factor 用 iu1·u1=1 把每个线性因子变成单位倍。
- #213 PsiAffineCompat **14:11:02 DONE**（src 22:09:43 / olean 22:11:01；affine_compat 三公理，0 sorryAx）：chart0ToOverlap n T ≫ chartMorphismInf (psiChart0Coord n T) = chartInfPieceToOverlap n T ≫ chartMorphism0 (psiChartInfCoord n T)，用 #200 的 chartMorphismInf_comp/chartMorphism0_comp + rToOverlap_rat/qToOverlap_rat + chartMorphism_transition。**B1 的仿射 overlap 相容已闭合**；此前 14:01:43 DONE → 14:03:01/14:08:37 FAIL 的反复属于同文件中间版本，当前版已绿（仍须在每次引用前核 src/olean）。
- P¹ 仍是两套模型：ψ 第一段 psiChart0ToP1 : … ⟶ projectiveLine（Proj，§4.70），π/xi 用 projectiveLineGlued；#212 的 p1ProjToBase 是 Proj 模型、p1GluedToBase 是 glued 模型，两者无 iso。**引用必须分别写全名；不得把 p1ProjToBase_isProper 当 glued P¹ proper 用**。

### 4.80 【高·F7/H-T】F7(a) 已由 ZMod 路线落地；F7 htame 只剩算术输入 hdiv/hpn
- #209 residue_separable_global 三公理（probe 11b）：对 [P.IsMaximal] [P.LiesOver span{p}]，Algebra.IsSeparable (ℤ⧸(p)) (𝓞K⧸P) 真证。构造链：ZMod p 有限 ⇒ PerfectField.ofFinite；Int.quotientSpanNatEquivZMod 传 Fintype；Ideal.absNorm_ne_zero_iff 给 residue Finite；Algebra.IsAlgebraic.of_finite；inferInstance 出 separable。**F7(a) 不再缺 producer**。
- #218 tameCount_of_div_ramification 三公理（probe 11c）把 (a) 与 ramificationIdx_invertible_of_dvd 组合，证 TameCount K p；disc_factorization_le_finrank_of_div_ramification 给 v_p(|disc K|) ≤ [K:ℚ]。**条件只剩 hdiv（每个 normalized factor 的 e_P ∣ n）与 hpn : ¬ p ∣ n**；这两个是真正的算术输入，不能记「无条件 htame」。
- 注意区分：tame_localDifferentPaperOrder_le_one_glued 里的 **局部** hsep : IsSeparable (ℤ_[p]⧸p) (Integers L⧸P) 是局部域 residue，不是 #209 的全局数域 residue；**不得用 #209 直接消去局部 hsep**。F7SeparableResidue（#215）独立版仍红，已由 #209 取代；建议 retire。
- 结论：F7 的 (a) 记 **已证（全局）**；F7 的 htame 记 **条件式（hdiv/hpn）**；TameRamifiedAt 作为 hypothesis 仍不是无条件 inhabitant。

### 4.81 【高·U-R/C2】J1 旧版转绿但 C2 仍 BLOCKED；q 侧 per-b 质量已证，M=Q/(2l) 仍红
- #206 URThetaRegion 的唯一“区域包含”是 possibleImages ⊆ p6PacketHull（hull 按定义就是 possibleImages 的 holomorphic hull）⇒ **C wrapper**，不是 θ_P5 ≤ H_pkt。#207 旧 6 定理版（13:52:36）全绿，但 ur_thetaRegion_subset_hull 就是这条 C wrapper；ur_perB_q_le_theta 是 donor re-export；ur_qReading_root_formula 带 DistinguishedScalarData 假设。J1 的机械修红完成，**C2 的 θ 侧 producer 仍缺**。
- q 侧：#208 urRootAlpha_mass 三公理，actual per-b (1/(2l))log‖q_b‖ 已证；这是 C2 缺失的实例化，**真增量**。#207 新版试图证 urM_eq_half_qMagnitude : (1/(2l))·Q = −Σ_b w_b·(1/(2l))·log‖q_b‖，但 ur_cNorm_eq_localNormOrder（Real.logb 符号/除法）与 urM_eq_half_qMagnitude（Finset.sum_congr 前未提 1/(2l)）都 sorryAx，**当前 R/STALE**。
- **C2 仍 BLOCKED**，但缺口从「q 侧无 actual producer」缩到「q 侧 M 归一化求和 + P5 读数同一性 + θ 侧 H_pkt producer」。不得写「C2 已证」；也不得把 #206 的 A⊆hull(A) 当 θ 侧证据。**batch 12 更新（§4.88）**：q 侧 M=Q/(2l) 已由 #228 `urM_eq_half_qMagnitude` 14:30:29 闭合（P12b 三公理）；本条“M 归一化未证”作废，C2 只剩 θ 侧。

### 4.82 【中·L-H】JHeightLower 只到齐次性；D3 下界仍缺；JHeightBezout 不变
- #210 当前 JHeightLower 只有 4 条 jQ**Z_isHomogeneous（三公理）。13:48:11 的扩展版曾含 jBezK_left/right、jBez_relation、logHeight_jHeight_ge、jHeight_relation，但编译成 sorryAx，随后被回退；**不要引用这些名字为已证**。
- JHeightBezout（13:29:04 DONE，unchanged）的 Bézout 恒等式仍是真代数输入；h(j) ≥ 6h(λ)−C 的高度比较**未组装**；HeightDictionaryInterface（D3）**NO INHABITANT** 不变。

### 4.83 【中·G-A】P¹ proper 的双模型陷阱：Proj proper ≠ glued proper
- #212 p1ProjToBase_isProper 是 **Proj 模型** projectiveLine = Proj ℚ[X0,X1] 的 proper；p1GluedToBase 是 **glued 模型**的结构态射，二者没有 iso（§4.70）。PiProper.fermatCurveToBase_isProper 需要 hP1 : IsProper p1GluedToBase，而 #212 **没有**这条定理。
- 因此「P¹ proper 已证」只能写成「Proj 模型 P¹ proper 已证；glued 模型结构态射已构造，properness 未证」。下一步：证 IsProper p1GluedToBase（例如用 p1GlueData.openCover 的局部 proper 判据 + 两张 chartBase proper），或先证 projectiveLine ≅ projectiveLineGlued 再 transport。

### 4.84 【高·纪律】本批再次出现“DONE 后 1–2 分钟改写”：gate 必须同时钉 src/olean
- 实例：PsiAffineCompat 14:01:43 DONE → 22:02:12 源码扩写 → 14:03:01/14:08:37 FAIL，olean 22:01:42 已旧于 src；URJ1 13:52:36 DONE（旧 6 定理）→ 22:01/22:05 改写 → 连续 FAIL；RadicalSupport 13:46:29/13:52:40 DONE → 22:56 前后多次改写 → 14:03:30 才最终绿；PiProper 13:59:06 DONE → 22:06:37 改写 → 14:07:52 再 DONE；JHeightLower 13:47:14/13:59:51 DONE 但只对应 45 行齐次性版。
- 规则：**引用前必须 Get-Item 同时看 src 与 olean**；只要 src > olean 或最后一次 attempt 是 FAIL，就写「STALE/未编译」，不得引用该文件的任何定理（哪怕日志里曾有三公理）。#207/#213/#215/#217 是本批具体教训。

### 4.85 【中·F7】residue_separable_global 的 [P.IsMaximal] 不是免费：消费者必须从 P.IsPrime + P ≠ ⊥ 推出
- #209 的签名是 (P) [P.IsMaximal] [P.LiesOver span{p}]；TameRamifiedAt 的量化是 [P.IsPrime] [P.LiesOver span{p}] + absNorm(under)=p。消费者要先 haveI : P.IsMaximal := hPisPrime.isMaximal hPne（hPne 由 P.LiesOver 与 p≠0 得），再 residue_separable_global P。**不要以为 TameRamifiedAt 的定义直接匹配**；#218 已按此写对，可作为模板。
- residue_separable_global 是**全局数域**结论；局部 tame_localDifferentPaperOrder_le_one_glued 的 hsep 是 ℤ_[p]⧸p 到 Integers L⧸P 的局部 residue 可分，两者不能互换。F7(a) 记「全局已证」；局部 hsep 仍显式假设。

### 4.86 【低·纪律】“CanonicalPi” 在本批不存在
- 本批在 tmp/sheaf/xif/paper、extra-targets.txt、watchdog.log 中检索 CanonicalPi|canonicalPi **0 命中**；没有名为 CanonicalPi 的文件/目标。canonical π 仍是 #184 Mzk1G1FermatPiActual.pi（DONE 13:19:21，fresh；pi = fermatCurveGlueMorphism ...，Y_n 用 fermatCurveScheme），本批无新 attempt。IsFinite 相关新 DONE 是 #202/#203（chart finite）与 #214（条件式 proper）；若 Lead 的 “CanonicalPi” 指别的目标，需给出准确文件名。

## 5g. batch 11 立即动作（快照 14:09 UTC）

1. **grace（IsFinite π，最高优先）**：用 #202/#203 的 lamHomSpec_isFinite/lamHom2Spec_isFinite + IsFinite 在 target 开覆盖 D_+(X0)/D_+(X1) 上的局部判据，装配 IsFinite (pi n)；需要局部化传递（Module.Finite 局部化）与 pi⁻¹(D_+(X0))=D(x0^n)（#205 目标）。若走 #200 的 chart 换基，先补 §4.77 的 evalAt_comp，不要直接把 #200 当接口。
2. **grace（P¹_glued proper）**：证 IsProper p1GluedToBase（#212 只到构造），或先证 projectiveLine ≅ projectiveLineGlued 再 transport；之后用 #214 fermatCurveToBase_isProper 得 Y_n ⟶ Spec ℚ proper。**不要把 Proj 模型的 p1ProjToBase_isProper 当 glued proper**。
3. **henry/emmy（π⁻¹）**：#205 先把 Mzk1G1ProjectiveLineGluedActual.overlapSchemeIso 改成 Mzk1G1FermatOverlapActual.overlapSchemeIso，overlapToChart* 的 rewrite 改成先展开 overlapToChart*/rfl；完成 piChartInf_preimage_chart0 = basicOpen(r1^n) 等 4 条后，再与 #204 pi_preimage_eq 组合成 pi_preimage_chart0/Inf。
4. **URJ1（C2 q 侧）**：修 ur_cNorm_eq_localNormOrder（Real.logb 的 logb = log/log 方向与负号）与 urM_eq_half_qMagnitude（先 rw [Finset.mul_sum]，RHS 也提 1/(2l)，再用 Finset.sum_congr + urRootQ_log_norm_order）；绿后 q 侧 M=Q/(2l) 才有 producer。**θ 侧 H_pkt 仍缺**，不要用 #206 的 A⊆hull(A) 代替。
5. **F7**：以 #218 为模板，补 hdiv（每个 normalized factor 的 e_P ∣ n）与 hpn 的算术证明；F7SeparableResidue（#215）可 retire，改引 #209 residue_separable_global。局部 hsep 仍按 §4.85 显式保留。
6. **PsiAffineCompat 已绿（14:11:02）**：affine_compat 三公理（chart0ToOverlap ≫ chartMorphismInf(psiChart0Coord) = chartInfPieceToOverlap ≫ chartMorphism0(psiChartInfCoord)）。下一步：用这条仿射相容 + 两 chart 的 ring map 造 ψ 的 scheme 层态射（或零纤维段的 glue），并核对 P¹ 是 projectiveLine 还是 projectiveLineGlued（§4.79 双模型）；引用写全名。
7. **JHeightLower**：当前只有 4 条齐次性；要补 jBezK_left/right、jBez_relation、logHeight_jHeight_ge，但 13:48 版的 MvPolynomial.map_add/mul/pow/sub 名字不存在（应用 map_add/map_mul 非 MvPolynomial. 前缀），修好再重排；D3 仍 open。
8. **LpHenselNearRoot**：先修 §4.84/#217 的 6 处机械错（max_eq_left 的 ≤、le_or_lt 的命名、norm_natCast、rfl 目标、rewrite motive、linarith）；绿后才有 G-K step 2 的域级近根 producer。
9. **引用纪律（batch 11 版，强制）**：
   - F7(a)：只写 residue_separable_global（#209，三公理）；F7 htame 只写「条件于 hdiv/hpn」；F7SeparableResidue 禁引用。
   - IsFinite π、IsProper p1GluedToBase：**均无定理**；只写「两块 chart finite 已证 + 条件式 proper 装配」。
   - P¹ 必写 projectiveLine（Proj）/projectiveLineGlued；p1ProjToBase_isProper 只属于前者。
   - Y_n 必写 fermatCurveScheme（canonical）或 fermatCurveSchemeIso（aux）；fermatCurveToSpec 与 fermatCurveToBase 都真但不可混名。
   - xi 是 x-坐标，π 是 λ=x^n；cocycle 只写「GlueData 内部 t_fac/cocycle/f_open 已证 + 用户级 h 未证（π/xi 的 h 已证）」（§4.60/§4.71 不变）。
   - JHeightLower 当前只有齐次性；HeightDictionaryInterface 仍 NO INHABITANT。
   - STALE 一律先查 src/olean；#207/#213/#215/#217 不得引用。

## 6h. batch 11 更新（快照 **14:09 UTC = 22:09 CST**；覆盖 §6/§6b–§6g 的旧结论，旧文保留）

- **已运行（本批）**：node tools/wd_status.mjs … --err（对 20+ 文件逐个取最后 START/DONE/FAIL；对失败读首错：F7SeparableResidue、RadicalSupport、P1Proper、PiProper、PsiAffineCompat、LpHenselNearRoot、JHeightLower、ChartFinite2、PiPreimageChart、URJ1）；watchdog.log 13:32–14:08 的 DONE/FAIL/START 全量抽取 + 按文件压缩；olean/源码 mtime 对照（18 个文件）；禁用项 grep（18 个源文件；唯一命中为文件头注释、maxHeartbeats、URThetaRegion 的 "surrogate" 注释）；源码语义阅读（PsiAffineOverlap 全文 124 行、ChartPreimage 全文 60 行、ChartFinite 全文 169 行、ChartFinite2 全文 154 行、PiPreimageChart 全文 109 行、PiPreimage 全文 72 行、PsiProductIdentity 67 行、P1Proper 126 行、PiProper 81 行、CurveToSpec 53 行、F7SeparableResidue 53 行、F7TameCountGlobal 63 行、URThetaRegion 50 行、URJ1 146 行、URRootExtInstances 174 行、RadicalSupport 282 行、JHeightLower 关键段、LpHenselNearRoot 首错段）。
- **Probe 11/11b/11c**：8 + 6 + 2 条，全部 [propext, Classical.choice, Quot.sound]，0 error、0 sorryAx（详见 §3e/§3f/§3g）。**未运行** lake env lean、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未运行 / 未覆盖（如实标注）**：
  - Mzk1G1FermatPiProperActual.fermatCurveToBase_isProper、P1Proper.p1GluedToBase、Mzk1F7TameCountGlobalActual 之外的新定理：只有 (L) 或未 probe；F7 两条已 probe (P11c)，fermatCurveToBase_isProper 只有 (L) 三公理。
  - Mzk1URJ1Actual 新版 urM_eq_half_qMagnitude：当前 FAIL，**不可 probe**；只有旧 6 定理的 (L)。
  - Mzk1G1PsiAffineCompatActual：14:01:43 DONE 版 log 已被清，当前 FAIL/STALE；**axioms 未取**。
  - Mzk1G1FermatPiPreimageChartActual：当前 FAIL、无 olean；四个 chart 原像目标未证。
  - Mzk1G1JHeightLowerActual：只有 4 条齐次性；jHeight_relation 等已回退，**未证**。
  - Mzk1LpHenselNearRootActual：当前 FAIL、无 olean；只取首错，**未判数学内容**。
  - Mzk1UCHpktActual.uc_c4_of_paperConstants：本批 DONE 但**无 #print**，未 probe；仍条件于 hP5/htheta/hstepVIII/hπ。
  - U-R 全组（除 #206/#207/#208）、G-K 递归构造、H-T 的 F1–F4/F8、P8-P 端到端：**未运行**语义审计。
- **快照 14:09 UTC 之后**：watchdog 仍在跑；**14:09–14:11 的补记已写入 §2j-3**（LpHenselNearRoot DONE 14:09:42 后 STALE；PiFiniteAssembly DONE 14:11:01 条件式；P1Proper 再红）。**14:11 之后的任何 DONE/FAIL 本表未审计**。
- **本批新发现并已写进正文的纪律**：§4.76（IsFinite/IsProper 装配缺口）、§4.77（chart 换基 ≠ IsFinite 接口）、§4.78（P¹ chart 原像已绿但 π⁻¹ 目标未陈述）、§4.79（B1 乘积恒等式绿、仿射相容红、P¹ 双模型）、§4.80（F7(a) 已证 + htame 条件式）、§4.81（C2 q 侧实例化绿、M 归一化红、θ 侧仍缺）、§4.83（Proj proper ≠ glued proper）、§4.84（DONE 后改写 → STALE 纪律）、§4.85（residue_separable_global 的 IsMaximal 前提与局部/全局区分）。

- 本批写入范围：本表 + **新建** tmp/sheaf/xif/paper/_ProbeBatch11Actual.lean、_ProbeBatch11bActual.lean、_ProbeBatch11cActual.lean；未改其它 Lean 文件；未 spawn_teammate、未 lake env lean、未自起 watchdog。

### 2j-3 快照后补记（14:09–14:11 UTC；只补事件与对 §4.76/§4.84 的更正，不改 #200–#220 表内已记录判定）

| 时间 (UTC) | 事件 | 文件 | 备注 |
|---|---|---|---|
| 14:09:42 | DONE | Mzk1LpHenselNearRootActual | 24s；src 22:04:58 / olean 14:09:42；日志两条三公理：exists_root_close_of_norm_lt、eq_of_roots_close（0 sorryAx）。**但 src 22:11:07 又改（30.7KB），olean 14:09:42 已旧 ⇒ 当前 STALE；引用前必须重编，不得直接用 14:09:42 的 olean 当当前版。** |
| 14:09:48 | FAIL | Mzk1P1ProperActual | 30s；随后 src 22:11:44 又改 → 当前 STALE；#212 的 DONE 只对应 22:03:34 版。 |
| 14:10:13 | FAIL | Mzk1URJ1Actual | 55s；当前仍 R（urM_eq_half_qMagnitude 未证）。 |
| 14:10:27 | START | Mzk1G1FermatRadicalSupportActual（**新文件名**，无 Final3） | 与 Final3 的关系未判；快照时无结果；不得当 #209 的替代。 |
| 14:11:01 | DONE | Mzk1G1FermatPiFiniteAssemblyActual（**新文件**） | 34s；src 22:10:00 / olean 22:11:00；isFinite_of_two_chart_restrict、isFinite_pi_of_chart_restrict 两条三公理（0 sorryAx）。**条件式**：h0 : IsFinite (pi |_ localChart0.opensRange)、h1 : IsFinite (pi |_ localChartInf.opensRange)；仍无 IsFinite (pi n) producer。 |
| 14:11:01 | FAIL | Mzk1P1ProperActual | 第二次红；当前 src 22:11:44。 |

- **对 §4.76 的更新**：Mzk1G1FermatPiFiniteAssemblyActual.isFinite_pi_of_chart_restrict 已把「两 chart 限制有限 ⇒ π 有限」的 Zariski-local 总装证出（三公理，条件式）。因此 IsFinite π 的剩余缺口**不再是**一般 local-to-global 装配，而是**两条 chart 限制** IsFinite (pi |_ localChart0.opensRange) 与 IsFinite (pi |_ localChartInf.opensRange)——它们需要 #205 的 pi⁻¹(D_+(X0))=D(x0^n) 与 #202/#203 的 chart 环有限性（+ 局部化传递）。仍**不得写「IsFinite π 已证」**。
- **对 §4.84 的更新**：本补记再次出现「DONE 后 1–2 分钟改写」——LpHenselNearRoot 14:09:42 DONE → 22:11:07 改写；P1Proper 14:04:12 DONE → 22:11:44 改写。引用前必须同时核 src/olean；本补记之后（14:11 以后）的变化仍未审计。
- _ProbeBatch11c DONE 14:09:01（F7 两条三公理）；_ProbeP8LeadActual（14:10:27 START）是 Lead 的 probe，不属本 lane，本表不引用其结论。
- **14:11:02 更正 #213**：Mzk1G1PsiAffineCompatActual **DONE**（src 22:09:43 / olean 22:11:01，fresh；affine_compat 三公理，0 sorryAx）。affine_compat : chart0ToOverlap n T ≫ chartMorphismInf (psiChart0Coord n T) = chartInfPieceToOverlap n T ≫ chartMorphism0 (psiChartInfCoord n T)，证明直接用 #200 的 chartMorphismInf_comp/chartMorphism0_comp + rToOverlap_rat/qToOverlap_rat + chartMorphism_transition。**B1 的仿射 overlap 相容已闭合**；这是 #200 的 chart 换基引理的第一个实际消费者（不是 IsFinite 用途）。
- **14:11:27 FAIL**：Mzk1G1FermatRadicalSupportActual（无 Final3 的新文件名）55s；与 #209 的关系未判，快照时无结果；不得当 #209 的替代。
- **14:11:41 START**：Mzk1URQNormalizationActual（新文件）与 Mzk1URJ1Actual 重试；14:11 之后未审计。

### 2j-4 14:11–14:13 最终状态补记（覆盖 §2j-3 的 LpHenselNearRoot/P1Proper/URJ1 行；以本表为准）

| 时间 (UTC) | 事件 | 文件 | 备注 |
|---|---|---|---|
| 14:12:06 | DONE | Mzk1LpHenselNearRootActual | src 22:11:07 / olean 22:12:05，fresh；日志两条三公理：exists_root_close_of_norm_lt、eq_of_roots_close（0 sorryAx）。**G-K §7.2 step 2 的域级近根存在性当前已编译、可引用**（此前 §2j-3 的 STALE 记法作废）。 |
| 14:12:38 | DONE | Mzk1URJ1Actual | src 22:11:02 / olean 22:12:38，fresh；**源码回退到 5 条旧定理版**（ur_qRootLattice_int、ur_thetaSourceSpan_int、ur_qReading_root_formula、ur_perB_q_le_theta、ur_qReading_theta_order；#print 另含 URThetaRegion 的 C wrapper）。**ur_cNorm_eq_localNormOrder / urM_eq_half_qMagnitude 已被删除，不再存在**；C2 q 侧 M=Q/(2l) 仍未证。 |
| 14:13:21 | DONE | Mzk1P1ProperActual | src 22:11:44 / olean 22:13:21，fresh；新增 chartBase_locallyOfFiniteType、p1GluedToBase_locallyOfFiniteType、p1GluedToBase_quasiCompact（另 chartBase_quasiCompact/quasiSeparated、projectiveLineGlued_compactSpace）均三公理；**仍无 p1GluedToBase_isProper**——P¹_glued proper 未证，只到 locally-of-finite-type + quasi-compact。 |
| 14:11:27 | FAIL | Mzk1G1FermatRadicalSupportActual（无 Final3 的新文件名） | 55s；与 #209 的关系未判；不得当 #209 的替代。 |
| 14:12:36 | FAIL | Mzk1URQNormalizationActual（新文件） | 与 C2 的 M=Q/(2l) 可能相关；当前 FAIL，未审计。 |

- **对 §4.81 的更新**：URJ1 最终 DONE 但 M 归一化两条已删除；#208 的 actual per-b 质量仍是 q 侧唯一真件。C2 仍 BLOCKED；不得写「M=Q/(2l) 已证」。**batch 12 更正**：kurt 已在 `Mzk1URQNormalizationActual` 恢复并证出 `urM_eq_half_qMagnitude`（14:30:29 DONE，P12b 三公理），见 §4.88；本条“M 未证”作废。
- **对 §4.76 的更新**：P1Proper 最终版把 P¹_glued 的 LocallyOfFiniteType + QuasiCompact 补上，但 **properness 仍缺**；PiFiniteAssembly 只差两条 chart 限制。IsFinite π 与 IsProper P¹_glued 仍都无定理。
- **对 §4.82 的更新**：LpHenselNearRoot 最终 DONE（两条三公理）；这是 G-K step 2 的候选 producer，但 BoundedDegreeFinitelyManyFields 的总装/固定次数有限性仍未证，不要直接记 G-K 完成。
- **快照 14:13 UTC**：14:13 之后 watchdog 仍在跑（14:12:52 START P1Proper 重试；URQNormalization 红）；**14:13 之后的变化本表未审计**。

## 2k. 本批 batch 12 gate 表（快照 **14:35 UTC = 22:35 CST**；**#221–#241**，覆盖 14:13–14:34 全部 DONE/FAIL + Lead 指定 6 项复核）

grep 列 = 大小写敏感扫描 `sorry|admit|axiom|PUnit|surrogate|toy|True|maxHeartbeats`（本批 12 个源文件：F7TameCountGlobal / PiFiniteAssembly / LpHenselNearRoot / URJ1 / P1Proper / PsiAffineCompat / PiPreimageChart / URQNormalization / RadicalSupportActual / P1Valuative / P1ProperAssembly / ChartSwap；命中仅为文件头注释、`#print axioms`、`Set.mem_univ`/`true` 分支、PiFinite/ChartSwap 的 `maxHeartbeats`，均人工排除；0 个字面 `sorry`/`admit`/`axiom` 声明）。axioms 列：(P12) = 本批 `_ProbeBatch12Actual.lean` 独立复算（扩展版 8 条）；(L) = 当前 attempt 自带 `#print` 的日志末段；— = 无 `#print` 或未 probe。olean 列 fresh = olean mtime > 源码 mtime；**STALE = 最后一次 DONE 之后源码又被改，或最后一次 attempt 是 FAIL**。

**13:49–14:26 DONE/FAIL 全量（按文件；13:49–14:13 的判定已在 §2j #200–#220，本表只标“本批复核/新增”）**

| 文件 | DONE 时刻 (UTC) | FAIL 时刻 (UTC) | 本批 |
|---|---|---|---|
| Mzk1URJ1Actual | 13:52:36, **14:12:38** | 13:50:28, 13:58:17, 14:00:58, 14:03:26, 14:05:23, 14:07:10, 14:09:04, 14:10:13 | #224 复核 |
| Mzk1URRootExtInstancesActual | 13:54:41 | 13:50:31, 13:52:38 | 不变（#208） |
| Mzk1G1FermatRadicalSupportFinal3Actual | 13:52:40, **14:03:30** | 13:50:32, 13:58:21, 14:02:11 | 不变（#209） |
| Mzk1G1FermatChartFinite2Actual | 13:53:28 | 13:51:20 | 不变（#203） |
| Mzk1G1PsiProductIdentityActual | 13:51:22 | — | 不变（#211） |
| Mzk1LpHenselNearRootActual | 14:09:42, **14:12:06** | 13:51:13, 13:53:21, 13:55:20, 13:57:42, 14:02:53, 14:05:59, 14:07:47 | #223 复核 |
| Mzk1G1PsiAffineCompatActual | 14:01:43, **14:11:02** | 13:53:28, 13:55:25, 13:59:07, 14:03:01, 14:08:37 | #226 复核 |
| Mzk1P1ProperActual | 14:04:12, 14:13:21, 14:23:31, **14:28:59** | 13:53:28, 13:57:01, 13:59:07, 14:01:42, 14:03:00, 14:09:48, 14:11:01, 14:17:55, 14:22:18 | #225 复核 |
| Mzk1G1JHeightLowerActual | 13:59:51 | 13:49:13, 13:51:21, 13:53:29, 13:55:27, 13:57:51 | 不变（#210） |
| Mzk1G1FermatPiProperActual | 13:59:06, **14:07:52** | 13:56:11 | 不变（#214） |
| Mzk1F7SeparableResidueActual | — | 13:57:51, 13:59:08, **14:01:44** | #233 RETIRED |
| Mzk1G1FermatCurveToSpecActual | 14:00:33 | 13:57:49 | 不变（#216） |
| Mzk1F7TameCountGlobalActual | **14:07:09** | — | #221 复核 |
| Mzk1G1FermatPiFiniteAssemblyActual | **14:11:01** | — | #222 复核 |
| Mzk1G1FermatPiPreimageChartActual | — | 14:02:59, 14:04:11, 14:06:54, 14:08:47, 14:11:13, 14:13:32, 14:15:48, 14:16:58, 14:23:29, **14:25:52** | #227 |
| Mzk1G1FermatRadicalSupportActual | 14:16:02, **14:26:18** | 14:17:13, 14:23:56 | #229 新增（修复后绿） |
| Mzk1URQNormalizationActual | **14:30:29** | 14:12:36, 14:14:53, 14:17:14, 14:21:34, 14:22:43, 14:25:06, 14:27:29 | #228 新增（修复后绿） |
| Mzk1P1ValuativeActual | 14:24:40, **14:33:26** | 14:21:07, 14:22:18, 14:28:59, 14:31:13 | #230 新增（修复后绿） |
| Mzk1URThetaMonotoneActual | — | **14:34:04** | #241 新增 |
| Mzk1G1FermatChartSwapActual | **14:31:12** | 14:23:30, 14:25:52, 14:28:58 | #232 新增（修复后绿） |
| Mzk1G1OmegaTransitionGlobalActual | — | 14:27:09, 14:28:15, **14:32:27** | #237 新增 |
| Mzk1UCHpktActual | **14:29:25** | — | #238 新增（快照后补记） |
| Mzk1P1ProperAssemblyActual | —（**无 watchdog 事件**） | — | #231 新增 |
| _ProbeBatch12Actual | 14:23:57（6 条）, **14:26:19**（8 条） | — | #234 |
| _ProbeP8LeadActual（Lead lane） | 14:11:26 | — | 不属本 lane，不引用 |
| _ScratchEmmyStmt3 / _P1OpenScratch | 14:06:43 / 14:21:06 | — | scratch，不作证据 |

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 221 | Mzk1F7TameCountGlobalActual（Lead 指定 1） | H-T / F7 htame | **DONE** | 14:07:09 | fresh（src 22:05:45 / olean 22:07:08） | clean | 三公理 (P12：`tameCount_of_div_ramification`；L 日志 0 B，未取) | **A-条件式（确认：不是无条件）**：`tameCount_of_div_ramification (hdiv) (hpn) : TameCount K p`；`hdiv` = 对每个 `P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K))` 且 `absNorm (under ℤ P) = p`，有 `ramificationIdx' (span{p}) P ∣ n`；`hpn : ¬ p ∣ n`。内部用 #209 `residue_separable_global`（得 (a)）、`ramificationIdx_invertible_of_dvd`（e 在 ℤ⧸p 中非零）、`count_differentIdeal_eq_of_tame`。`disc_factorization_le_finrank_of_div_ramification` 同条件。**只能写“条件于 hdiv/hpn 的 htame”**。 |
| 222 | Mzk1G1FermatPiFiniteAssemblyActual（Lead 指定 2） | G-A IsFinite π 装配 | **DONE** | 14:11:01 | fresh（src 22:10:00 / olean 22:11:00） | clean（`maxHeartbeats 800000`） | 三公理 (P12：`isFinite_pi_of_chart_restrict`；L 2 条) | **A-条件式（确认：只条件于两条 chart 限制）**：通用 `isFinite_of_two_chart_restrict (f) (U0 U1) (hU) (h0) (h1)` 用 `IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)` 真装；特化 `isFinite_pi_of_chart_restrict n (h0 : IsFinite (pi n ∣_ localChart0.opensRange)) (h1 : IsFinite (pi n ∣_ localChartInf.opensRange)) : IsFinite (pi n)`，其中 `hU` 由 #201 的 `localChart0_opensRange_sup_localChartInf` 真证。**假设只有 h0/h1**；二者无 producer。 |
| 223 | Mzk1LpHenselNearRootActual（Lead 指定 3） | G-K §7.2 step 2 | **DONE** | 14:12:06 | fresh（src 22:11:07 / olean 22:12:05） | clean | 三公理 (P12 两条；L 2 条) | **A-局部（真 Hensel 近根，integral form）**：`exists_root_close_of_norm_lt [CompleteSpace L] (f : L[X]) (a : L) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖^2) : ∃ b, f.eval b = 0 ∧ ‖b − a‖ < ‖f.derivative.eval a‖`；`eq_of_roots_close` 给同球内唯一性。Newton 迭代留在闭单位球，0 sorryAx。**边界**：条件含 `hf/ha`（系数与 a 在单位球）与 `[CompleteSpace L]`；这是“整形式”，不是任意完备非阿基米德域的无条件 Hensel；尚未接到 `BoundedDegreeFinitelyManyFields`/Krasner。 |
| 224 | Mzk1URJ1Actual（Lead 指定 4） | U-R J1 / C2 | **DONE（5 条旧版）** | 14:12:38 | fresh（src 22:11:02 / olean 22:12:37） | clean | 三公理 (L：5 条 + `URThetaRegion.ur_thetaRegion_subset_hull`) | **B+（5 条）/ C2 未证**：源码回退到 5 条：`ur_qRootLattice_int`、`ur_thetaSourceSpan_int`、`ur_qReading_root_formula`（带 `DistinguishedScalarData` 假设）、`ur_perB_q_le_theta`（donor `actualPerB_inequality` re-export）、`ur_qReading_theta_order`（donor `urRootTheta_log_norm_eq_neg_shift` re-export）。**`ur_cNorm_eq_localNormOrder`/`urM_eq_half_qMagnitude` 不在本文件**；C2 q 侧 M=Q/(2l) 已由 #228（URQNormalization 14:30:29）证。`ur_thetaRegion_subset_hull` 是 A⊆hull(A) 的 C wrapper（§4.81 不变）。 |
| 225 | Mzk1P1ProperActual（Lead 指定 5） | G-A P¹ proper | **DONE（14:13:21/14:23:31 均曾 STALE；当前 14:28:59 版 fresh）** | 14:28:59（14:13:21 → FAIL 14:17:55 → 14:23:31 → 14:28:59） | fresh（src 22:27:54 / olean 22:28:59） | clean | 三公理 (P12：`p1ProjToBase_isProper`、`p1GluedToBase_quasiSeparated`；L：LFT/QC/chart_intersection/QS 等 5–6 条) | **A-局部 / B（route）**：当前版含 Proj 模型 `p1ProjToBase_isProper`、`p1GluedToBase`（两 chart base 粘合）、两条 chart 限制等式、`LocallyOfFiniteType`、`QuasiCompact`、`QuasiSeparated`（正是 `IsProper.of_valuativeCriterion` 的三个 side condition），以及 `chart_intersection_isCompact`/`projectiveLineGlued_quasiSeparatedSpace`。**仍无 `p1GluedToBase_isProper`**。14:13:21 的 8.4KB 版已被后续两次改写取代（22:17:00 尝试 14:17:55 FAIL；22:22:31 版 14:23:31 DONE；22:27:54 版 14:28:59 DONE，新增 `overlap_range_eq`/`chart_ranges_inf`）；**引用必须用 src 22:27:54 / olean 22:28:59 这一版**，且仍无 `p1GluedToBase_isProper`。 |
| 226 | Mzk1G1PsiAffineCompatActual（Lead 指定 6） | B1 ψ 仿射 overlap | **DONE** | 14:11:02 | fresh（src 22:09:43 / olean 22:11:01） | clean | 三公理 (P12：`affine_compat`；L 1 条) | **A-局部（仿射相容）**：`affine_compat : chart0ToOverlap n T ≫ chartMorphismInf (psiChart0Coord n T) = chartInfPieceToOverlap n T ≫ chartMorphism0 (psiChartInfCoord n T)`，证明用 #200 的 `chartMorphismInf_comp`/`chartMorphism0_comp` + `rToOverlap_rat`/`qToOverlap_rat` + `chartMorphism_transition`，坐标互逆由 `psiUnit` 给出。**这是 overlap 上两个 chart 态射的相等，不是 scheme 层 ψ 态射/GlueData**；B1 仍未闭合，且 ψ 的 P¹ 仍是 `projectiveLine`（Proj）而非 `projectiveLineGlued`。 |
| 227 | Mzk1G1FermatPiPreimageChartActual（henry） | G-A π⁻¹ chart 目标 | **FAIL** | 14:23:29（14:25:52 重试；src 22:24:22） | **none** | clean | —（无 #print） | **R（机械）**：现有 4 条 chart 原像（`piChart0_preimage_chart0 = ⊤`、`piChartInf_preimage_chart0 = basicOpen (r1^n)`、`piChart0_preimage_chartInf = basicOpen (x0^n)`、`piChartInf_preimage_chartInf = ⊤`）+ `infImage_le_chart0`。**仍没有 `(pi n) ⁻¹ᵁ (localChart0.opensRange) = basicOpen (x0 n ^ n)`（或 `D_+(X0)` 记法）的最终陈述**。首错：`p1_overlapToChartInf_opensRange` 中 `PrimeSpectrum.basicOpen Polynomial.X` 的类型是 `Opens (PrimeSpectrum ↑(CommRingCat.of (Polynomial ℚ)))`，而目标要求 `chartInfScheme.Opens`（unfold `chartInfScheme` 的 defeq 被 instances transparency 卡住）；此前还有 `overlapToChartInf` 等式 rewrite 失败、`IsOpenImmersion ?m` stuck。**不得写“π⁻¹ 已证”**。 |
| 228 | Mzk1URQNormalizationActual（kurt 恢复 urM） | U-R/C2 q 侧 M=Q/(2l) | **DONE（14:30:29 转绿）** | 14:30:29（14:12–14:27 七次红） | fresh（src 22:28:35 / olean 22:30:29） | clean | 三公理 (L：`ur_cNorm_eq_localNormOrder`、`ur_gen_eq_sourceRootQUnit`、`urM_eq_half_qMagnitude`；P12b 复算三公理) | **A-局部（C2 q 侧 M=Q/(2l) 已闭合，本批第二重要转绿）**：`urM_eq_half_qMagnitude : (1/(2l))·actualQPilotMagnitudeClassical T = -∑_b nativeBadLocalWeight T b · ((1/(2l))·Real.log ‖sourceRootQUnit T b‖)`，内部用 `ur_cNorm_eq_localNormOrder`（actual normalized coefficient = actual `localNormOrder`）、`ur_gen_eq_sourceRootQUnit`（rfl）、donor `urRootQ_log_norm_order`；14:27 前的 `ring` 归一化错误已修。**这是 C2 q 侧 M=Q/(2l) 的 actual producer，可引用（须带 src 22:28:35 / olean 22:30:29）**。C2 仍 BLOCKED 于 θ 侧 H_pkt（#238 C4 仍假设 `htheta`），**不得写“C2 已证”**。 |
| 229 | Mzk1G1FermatRadicalSupportActual（sophie，新文件，无 Final3） | F7 radical support | **DONE（14:26:18，修复后）** | 14:26:18（14:16:02 首绿；14:17:13/14:23:56 为修复前红） | fresh（src 22:24:25 / olean 22:26:18） | clean | 三公理 (L：`differentContribution_le_log_of_factorization_le`、`f7_normalizedLogDisc_le_of_tame`、`f7_normalizedLogDisc_le_of_div_ramification`) | **A-条件式（修复后当前 DONE）**：稳定段（38–257）是真初等数论：radical 的整除/素支撑、`log rad(abc)` 的求和、`normalizedLogDisc` 与 `differentContribution` 的分解、`f7_sum_bound`、`f7_normalizedLogDisc_le_of_tame`（条件 hzero/htame/hbad）。14:16:02 首绿后曾追加 `f7_normalizedLogDisc_le_of_div_ramification` 并在 14:17:13/14:23:56 红（`Fact p.Prime` 缺失、hdiv 形状不匹配）；22:24:25 版修好（`haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩`，hdiv 对齐 `(a*b*c).primeFactors`），14:26:18 DONE、三公理。**当前可引用（条件于 hzero/hdiv/hbad）**；消费者即 #221 的 `disc_factorization_le_finrank_of_div_ramification`。 |
| 230 | Mzk1P1ValuativeActual（alan/david，新文件） | G-A P¹ val. criterion | **DONE（14:33:26 修复后）** | 14:33:26（14:24:40 首绿；14:28:59/14:31:13 红；src 22:32:12） | fresh（src 22:32:12 / olean 22:33:26） | clean | —（无 #print；未 probe） | **B−（预备）/ 路线仍 R**：5 条一般引理：`range_eq_singleton_specField`（Spec K 的像单点）、`range_subset_of_closedPoint_mem`（赋值环闭点落在开浸入像 ⇒ 整个像落在其中）、`specMap_eq_of_comp_eq`（分式域上相同 ⇒ Spec R 态射相同）、`eq_chartMorphism0_of_lift`/`eq_chartMorphismInf_of_lift`（chart 态射的坐标刻画；universe 已修为 `K : Type`/`Scheme`）。**仍无 `p1GluedToBase_valuativeCriterion`，没有 `ValuativeCriterion p1GluedToBase`**；P¹ 的 properness 还差主定理。 |
| 231 | Mzk1P1ProperAssemblyActual（**新文件，未排队**） | G-A IsProper P¹_glued | **NO-EVENT / 无 olean** | 源码 22:17:06 | **none** | clean | — | **R / 幻影 producer（高风险）**：文件声称 `p1GluedToBase_isProper := IsProper.of_valuativeCriterion … p1GluedToBase_valuativeCriterion`，但 `p1GluedToBase_valuativeCriterion` **在全树只出现在本文件的引用处，没有任何定义/证明**（grep 仅 1 处，line 14）。它 import 的 #230 当前 FAIL（universe 错），且只到 3+2 条预备引理。该文件**不在 extra-targets、无 watchdog 事件、无 olean**；若有人 grep 到它并引用 `p1GluedToBase_isProper` 即违规。side condition（QC/QS/LFT）已由 #225 备齐，只差 valuative criterion 本体。 |
| 232 | Mzk1G1FermatChartSwapActual（新文件） | G-A x↔y 对称 | **DONE（14:31:12 转绿）** | 14:31:12（14:23:30/14:25:52/14:28:58 前红） | fresh（src 22:29:58 / olean 22:31:12） | clean（`maxHeartbeats 800000`） | 三公理 (L：`swapA2_fermatEquation`、`map_span_fermatEquation`、`swapR`) | **A-局部（x↔y 自同构基础设施）**：`swapA2 : A2 ≃ₐ[ℚ] A2`（`MvPolynomial.renameEquiv` 交换 X0/X1）、`swapA2_fermatEquation`、`map_span_fermatEquation`、`swapR : R n ≃ₐ[ℚ] R n`（`Ideal.Quotient.quotientEquivAlg` 的正确名字修好后）三公理；另有 `modelSwapRel`/`ModelSwap`（y-侧局部化模型）定义。**用途**：把 r-侧 smooth/localization 结果运输到 y-侧（r' = n y^{n-1}），不是路线出口；无新 scheme 层结论。 |
| 233 | Mzk1F7SeparableResidueActual | F7(a) 独立版 | **RETIRED** | 最后 FAIL 14:01:44；之后 **0 次 attempt** | none | clean | — | **RETIRED**：已被 #209 `residue_separable_global`（ZMod 路线，三公理）取代；文件仍在磁盘但**不得引用、不得再排 watchdog**。Lead 的“已删”按“已退出活动队列”理解；实际文件未删。 |
| 234 | _ProbeBatch12Actual（本 lane） | audit probe | **DONE** | 14:23:57（6 条）；**14:26:19（8 条）** | fresh | — | 8 条全部 [propext, Classical.choice, Quot.sound]，0 error / 0 sorryAx | 见 §3h。 |
| 235 | _ScratchEmmyStmt3 / _P1OpenScratch / _ProbeP8LeadActual | scratch / Lead probe | DONE | 14:06:43 / 14:21:06 / 14:11:26 | — | — | — | **不作证据**：scratch 与 Lead-lane probe 不计入本 lane 判定，也不得由本表引用其结论。 |
| 236 | 13:49–14:13 的 #200–#220 | — | 见 §2j | — | — | — | — | 本批不重复判定；仅对 Lead 指定 6 项重核了当前 src/olean（#221–#226）。 |
| 237 | Mzk1G1OmegaTransitionGlobalActual | G-A Ω transition | **FAIL / STALE** | 14:32:27（14:27:09/14:28:15 亦红） | stale（src 22:27:42 / olean 21:09:51） | clean | —（无 #print） | **R（首错未取：per-file log 不存在）**：13:08 版旧 DONE 的 olean 21:09:51 已远旧于 src 22:27:42；当前多次 attempt（14:27:09/14:28:15/14:32:27/14:34:53）均 FAIL，**不可引用**。本批未读源码，不判数学内容。 |
| 238 | Mzk1UCHpktActual（14:28:16 新源码） | U-C C4 | **DONE** | 14:29:25 | fresh（src 22:28:16 / olean 22:29:24） | clean | 三公理 (L：`uc_c3_of_primeCounting`、`hprime_paperConstants`、`uc_c3_paperConstants`、`uc_c4_paperConstants_of_p6`；P12b 复算三公理) | **B（条件式装配，非新 closure）**：新增 `uc_c4_of_paperConstants`/`uc_c4_paperConstants_of_p6`：用 `uc_sandwich` + C3 + **假设** `hP5 : -M ≤ theta`、`htheta : theta ≤ H_pkt`（或 `actualThetaHullLogRoot ≤ ucWeightedHpkt`）+ `hstepVIII` 得 C4。`uc_c4_paperConstants_of_p6` 的 P5 下界由 donor `p6_neg_M_le_HTheta2` 提供，但 **θ 侧读数界 `htheta` 仍是显式假设**；C2 θ 侧 producer 仍缺。 |
| 239 | `_ProbeBatch12bActual`（本 lane，补充 probe） | audit probe | **DONE** | 14:32:45 | fresh | — | 3 条全部 [propext, Classical.choice, Quot.sound]，0 error / 0 sorryAx | 见 §3i；#228/#229/#238 的 kernel 层独立确认完成。 |
| 240 | 14:30–14:34 新 DONE/FAIL 补记（URQNormalization / ChartSwap / P1Valuative / Probe12b / Omega） | — | — | — | — | — | — | URQNormalization 14:30:29、ChartSwap 14:31:12、P1Valuative 14:33:26 绿；Omega 14:27:09/14:28:15/14:32:27 FAIL（无 log）。 |
| 241 | Mzk1URThetaMonotoneActual（新文件，θ 侧） | U-R/C2 θ 侧 | **FAIL** | 14:34:04 | **none** | clean | — | **R（机械）/ B− 骨架**：`urThetaHullLog_le_weighted`（三公理）把 θ 侧上界归约为**逐 b 集合包含** `actualLocalHullLog T b ≤ packetHullLog b`；但 `urHullLog_mono` 在 60:49 因 `whnf` heartbeat 200000 超时，导致 `82:14` unknown identifier，整文件红。当前无 olean；**θ 侧 producer 仍缺**（per-b 同载体包含未证）。 |

## 3h. Probe 12（本批 batch 12）：`tmp/sheaf/xif/paper/_ProbeBatch12Actual.lean`

- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch12Actual.lean` → `{"added":1,"total":124}`；扩展后再次 `wd_add` → `{"added":0,"total":123}`（仍在白名单）。
- 第一次：**START 14:22:57.706Z → DONE 14:23:57.754Z（60s）**，6 条。扩展为 8 条后：**START 14:25:22.555Z → DONE 14:26:19.456Z（57s）**。日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch12Actual.lean.log` 1917 B，**0 次 error、0 次 sorryAx、14 个 `depends on axioms` 块（= 6 条首跑 + 8 条扩展跑；日志跨 attempt 累积，取末段 8 条）**。
- 8 条独立复算（原样抄录，**全部 [propext, Classical.choice, Quot.sound]**）：

| 定理/定义（全名见文件） | axioms | 覆盖行 |
|---|---|---|
| `Mzk1F7TameCountGlobalActual.tameCount_of_div_ramification` | [propext, Classical.choice, Quot.sound] | #221（条件式） |
| `Mzk1G1FermatPiFiniteAssemblyActual.isFinite_pi_of_chart_restrict` | [propext, Classical.choice, Quot.sound] | #222（条件式） |
| `Mzk1LpHenselNearRootActual.exists_root_close_of_norm_lt` | [propext, Classical.choice, Quot.sound] | #223 |
| `Mzk1LpHenselNearRootActual.eq_of_roots_close` | [propext, Classical.choice, Quot.sound] | #223 |
| `Mzk1URJ1Actual.ur_qReading_theta_order` | [propext, Classical.choice, Quot.sound] | #224 |
| `Mzk1G1PsiAffineCompatActual.affine_compat` | [propext, Classical.choice, Quot.sound] | #226 |
| `Mzk1P1ProperActual.p1ProjToBase_isProper` | [propext, Classical.choice, Quot.sound] | #225（**Proj 模型**） |
| `Mzk1P1ProperActual.p1GluedToBase_quasiSeparated` | [propext, Classical.choice, Quot.sound] | #225（glued 模型 QS） |

- **未覆盖（明确未运行）**：`Mzk1G1FermatRadicalSupportActual` 三条（14:26:18 DONE，但 Probe 12 排队早于其 DONE，**未独立复算**；只有 (L) 三公理）；`Mzk1URQNormalizationActual.ur_cNorm_eq_localNormOrder`（文件 FAIL、无 olean，只有 (L) 三公理）；`Mzk1G1FermatPiPreimageChartActual` 四条 chart 原像（FAIL，无 olean）；`Mzk1P1ValuativeActual` 三条（14:28:59 FAIL，未 probe）；`Mzk1P1ProperActual.p1GluedToBase_isProper`（**不存在**）。 
- 结论：**kernel 层本批 8 条无伪证**；风险全在语义层（条件式 hdiv/hpn、两条 chart 限制、integral-form Hensel、ψ 只在仿射层、P¹ proper 缺主定理、M=Q/(2l) 仍 sorryAx）与“DONE 后改写/幻影 producer”。

## 3i. Probe 12b（补充）：`tmp/sheaf/xif/paper/_ProbeBatch12bActual.lean`

- 排队：`node tools/wd_add.mjs tmp/sheaf/xif/paper/_ProbeBatch12bActual.lean` → `{"added":1,"total":124}`；**START 14:31:52.492Z → DONE 14:32:45.943Z（53s）**；日志 `dag/watchdog/logs/tmp_sheaf_xif_paper__ProbeBatch12bActual.lean.log` 432 B，**0 次 error、0 次 sorryAx、3 个 `depends on axioms` 块**。
- 3 条独立复算（原样抄录，**全部 [propext, Classical.choice, Quot.sound]**）：

| 定理/定义（全名见文件） | axioms | 覆盖行 |
|---|---|---|
| `Mzk1URQNormalizationActual.urM_eq_half_qMagnitude` | [propext, Classical.choice, Quot.sound] | #228（**C2 q 侧**） |
| `Mzk1G1FermatRadicalSupportActual.f7_normalizedLogDisc_le_of_div_ramification` | [propext, Classical.choice, Quot.sound] | #229 |
| `Mzk1UCHpktActual.uc_c4_paperConstants_of_p6` | [propext, Classical.choice, Quot.sound] | #238（条件式 C4） |

- **结论**：#228 的 M=Q/(2l)、#229 的 F7 div-ramification consumer、#238 的 C4 装配在 **kernel 层均无伪证**（0 sorryAx）。语义边界不变：#229 条件于 hzero/hdiv/hbad；#238 条件于 htheta/hstepVIII；**不得把 kernel 三公理当“C2/C4 整体闭合”**。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 12 续）

### 4.87 【高·G-A】P¹_glued proper 仍缺主定理；`P1ProperAssembly` 是**幻影 producer**
- 当前真件（#225，14:28:59 DONE，src 22:27:54 / olean 22:28:59）：`p1ProjToBase_isProper`（**Proj 模型**）、`p1GluedToBase`（glued 模型构造）、`p1GluedToBase_locallyOfFiniteType`、`p1GluedToBase_quasiCompact`、`p1GluedToBase_quasiSeparated`、`projectiveLineGlued_quasiSeparatedSpace`、`chart_intersection_isCompact`、`overlap_range_eq`、`chart_ranges_inf`。其中 LFT/QC/QS 三条恰是 Mathlib `IsProper.of_valuativeCriterion`（`ValuativeCriterion.lean:339`，要求 `[QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]` + `ValuativeCriterion f`）的三个 side condition。
- **仍无 `p1GluedToBase_isProper`**。`Mzk1P1ProperAssemblyActual`（源码 22:17:06，**无 watchdog 事件、无 olean**）写了一个 `p1GluedToBase_isProper`，但它调用的 `Mzk1P1ValuativeActual.p1GluedToBase_valuativeCriterion` **在全树不存在**（grep 只有该文件 line 14 的引用）；#230 现在 14:33:26 DONE（universe 已修为 `K : Type`/`Scheme`），但只有 5 条预备引理，**仍无 `ValuativeCriterion`**。**这是源码层幻影定理**：任何人 grep 到它并引用都违规。
- 纪律：**不得写“P¹ proper 已证”“p1GluedToBase proper”**；只能写“Proj 模型 proper 已证；glued 模型 properness 已把 QC/QS/LFT 备齐，差 `ValuativeCriterion`”。下一步：universe 已修；直接证 `p1GluedToBase_valuativeCriterion`（存在性 + 唯一性），最后才排队 assembly；在此之前不要给 assembly 排 watchdog（它会因 unknown identifier 直接红）。

### 4.88 【高·U-R/C2】q 侧 `M=Q/(2l)` 已闭合（14:30:29）；C2 只剩 θ 侧 H_pkt
- #228 **14:30:29 DONE**（src 22:28:35 / olean 22:30:29，fresh）：`ur_cNorm_eq_localNormOrder`、`ur_gen_eq_sourceRootQUnit`、`urM_eq_half_qMagnitude` 三条均三公理、0 sorryAx。`urM_eq_half_qMagnitude : (1/(2l))·actualQPilotMagnitudeClassical T = -∑_b nativeBadLocalWeight T b · ((1/(2l))·Real.log ‖sourceRootQUnit T b‖)` 是 **C2 q 侧的 actual producer**（用 actual `localNormOrder`、rfl 的 generator 同一性与 donor `urRootQ_log_norm_order`）。14:12–14:27 的七次红（`ring` 不能闭合）已被修掉。
- #224 URJ1 仍是 5 条旧定理（不含 `urM`）；q 侧 producer 现在在 URQNormalization，不在 URJ1。**引用必须写 `Mzk1URQNormalizationActual.urM_eq_half_qMagnitude` 并带 src/olean 时间**。
- **C2 仍 BLOCKED，但缺口只剩 θ 侧**：`htheta : actualThetaHullLogRoot ≤ ucWeightedHpkt`（即 H_pkt 上界）没有 producer；#238 UCHpkt 14:29:25 的 `uc_c4_paperConstants_of_p6` 仍把它当显式假设（§4.87/#238）。#206 的 A⊆hull(A) 不是 θ 侧证据。**不得写“C2 已证”**；正确表述是“q 侧 M=Q/(2l) 已证；θ 侧 H_pkt 仍缺”。
- Probe 12b **DONE 14:32:45**（§3i）：`urM_eq_half_qMagnitude` 三公理、0 sorryAx；本条 kernel 层独立确认完成。C2 仍只剩 θ 侧。
- θ 侧新文件 #241 `Mzk1URThetaMonotoneActual`（14:34:04 FAIL）：`urThetaHullLog_le_weighted` 三公理，但把 θ 上界归约为**逐 b 集合包含** `actualLocalHullLog T b ≤ packetHullLog b`（显式 hperB）；工具引理 `urHullLog_mono` 在 `60:49` 因 `whnf` heartbeat 200000 超时，导致 `82:14` unknown identifier，整文件红、无 olean。**这不是 θ 侧 producer**；只是把缺口缩到“同载体包含 + heartbeat”。

### 4.89 【高·G-A/G-C】**P¹ 三处模型**：`projectiveLine`（Proj，至少三份局部定义）vs `projectiveLineGlued`
- π/xi（#184/#169）用 `Mzk1G1ProjectiveLineGluedActual.projectiveLineGlued`；ψ 第一段（#194 `psiChart0ToP1`）、P1Proper 的 `p1ProjToBase`、`Mzk1G1FiniteDisjointBelyiActual` 自己的 `def projectiveLine := Proj (homogeneousSubmodule (Fin 2) ℚ)` 都用 **Proj 模型**。全树**未发现** `projectiveLine ≅ projectiveLineGlued` 的 iso 或 transport 引理（grep 同文件双模型只命中 FiniteDisjointBelyi，且是并置而非 iso）。
- 风险升级：`Mzk1G1FiniteDisjointBelyiActual` 的 §7.1 递归以 **它自己的 `projectiveLine`（Proj）** 为靶，而 #218/#208 的 G-A/G-K 用 glued π；B1/B2 一旦把 φ 与 π 复合就是换题。**Lead 必须裁决**（§4.70 旧裁决仍有效）：(a) 把 ψ/φ 全部重写到 `projectiveLineGlued`；或 (b) 先证两模型 iso 再 transport。
- 纪律：任何 “P¹” 必写 `projectiveLine`（Proj）或 `projectiveLineGlued`；`p1ProjToBase_isProper` 只属于前者。

### 4.90 【中·G-C】π⁻¹ 目标仍**没有陈述**；chart 原像四引理红在类型别名
- #227 现有四条是 **chart 层** `piChart0/Inf_preimage_chart0/Inf`（其中两条已写成 `basicOpen (x0^n)`/`basicOpen (r1^n)`），但**没有** `(pi n) ⁻¹ᵁ localChart0.opensRange = basicOpen (x0 n ^ n)` 这样的最终 `(pi n) ⁻¹ᵁ D_+(X0)` 陈述；#204 `pi_preimage_eq` 只是集合层分解。
- 首错（当前）：`p1_overlapToChartInf_opensRange` 的 RHS 类型 `PrimeSpectrum.basicOpen Polynomial.X` 与目标 `chartInfScheme.Opens` 不统一（instances transparency 下 `chartInfScheme` 未展开）；修法是先 `show … (chartInfScheme).Opens` 或 `change` 到 `Spec (CommRingCat.of (Polynomial ℚ))` 的 Opens 再 `simpa`。**不得写“π⁻¹ 已证”**；正确表述是“chart 原像四条之中两条已成，最终 `D_+` 陈述未写”。

### 4.91 【中·G-K】Hensel 近根是真定理，但只是 **integral form**，尚未接到 GK 输入
- #223 两条三公理、0 sorryAx，是 G-K §7.2 step 2 所需的域级近根/唯一性；但假设 `hf : ∀ n, ‖f.coeff n‖ ≤ 1`、`ha : ‖a‖ ≤ 1`、`[CompleteSpace L]`。这是“整形式”（Eisenstein 多项式在适当缩放后满足），**不是任意完备非阿基米德域的无条件 Hensel**，也没有接到 `BoundedDegreeFinitelyManyFields`/Krasner 的 step 2。
- `BoundedDegreeFinitelyManyFields` 仍只是定义；`GKCompactInput` 仍 NO INHABITANT（§4.74 不变）。不得写“G-K 的 step 2 已闭合”或“L_p 已构造”。

### 4.92 【中·纪律 / F7】RadicalSupportActual 修复后 14:26:18 DONE：F7 div-ramification consumer 条件式落地
- 时间线：14:16:02 首绿（olean 22:16:01）→ src 22:16:16 追加 consumer → 14:17:13 FAIL；22:18:21/22:24:25 两次改写后 14:23:56 仍 FAIL；22:24:25 的修复版 14:26:18 **DONE**，olean 22:26:18 fresh。
- 修复内容：`f7_normalizedLogDisc_le_of_div_ramification`（当前 264–281）在 277 行加 `haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩`，并把 `hdiv` 的 `p` 限定到 `(a*b*c).primeFactors`（逐字对齐 #221 的 hdiv 形状）。现在三条 `#print axioms`（`differentContribution_le_log_of_factorization_le`、`f7_normalizedLogDisc_le_of_tame`、`f7_normalizedLogDisc_le_of_div_ramification`）都是三公理、0 sorryAx。
- **引用边界**：可引用，但**必须带条件** `hzero`（abc 外无分歧）、`hdiv`（p∈(abc).primeFactors、¬p|n 时每个 normalized factor 的 e_P ∣ n）、`hbad`（p|n 部分 ≤ C）；消费者是 #221 `disc_factorization_le_finrank_of_div_ramification`。**不得写“F7 无条件”**；该三条只有 (L)，本批 probe 排队早于其 DONE，未独立复算。

### 4.93 【中·L-H】D3 仍无 inhabitant；JHeightLower 仍只有齐次性
- `Mzk1G1QHeightActual.HeightDictionaryInterface` 仍只是 `def`（line 40），全树 grep 只有这一处：**NO INHABITANT**。`JHeightLower` 13:59:51 DONE 只有 4 条 `jQ**Z_isHomogeneous`；`jBezK_left/right`、`jBez_relation`、`logHeight_jHeight_ge`、`jHeight_relation` 未证。`JHeightBezout` 的 Bézout 恒等式仍是代数输入。**不得写“h(j) ≥ 6h(λ)−C 已证”**。

### 4.94 【高·纪律】本批再次出现“DONE 后改写”，且日志/白名单会变化
- P1Proper：14:13:21 DONE → src 22:17:00（quasiSeparated 尝试）→ 14:17:55 FAIL（`inf_self` unknown，新定理 sorryAx）→ src 22:22:31 → 14:23:31 DONE → src 22:27:54（新增 `overlap_range_eq`/`chart_ranges_inf`）→ 14:28:59 DONE。**只有 14:28:59 这版可引用**；§2j-4 的 14:13:21 行与 §2k 初稿的 14:23:31 行均已过期。
- RadicalSupportActual 14:16:02 DONE → 15 秒后改写 → 14:17:13/14:23:56 红 → 22:24:25 修复 → 14:26:18 DONE（§4.92，**已可引用但带 hzero/hdiv/hbad 条件**）。PiPreimageChart 14:23:29 FAIL 后 src 22:24:22 又改；URQNormalization 14:27:29 仍 FAIL、无 olean；P1Valuative 14:24:40 DONE → 22:27:56 改写 → 14:28:59 FAIL（universe），当前无 fresh olean；OmegaTransitionGlobal 14:27:09/14:28:15 FAIL（无 log，首错未取）。
- 日志纪律再确认：Probe 12 的日志跨两次 attempt 累积（6+8=14 块），**判 axiom 必须取末段 8 块**；`Mzk1URQNormalizationActual` 的 per-file log 在 14:24:12 START 时被清成 0 B，14:25:05 才有新内容 ⇒ “START 清空”与“跨 attempt 累积”**两种行为并存**（§2i 纪律不变）。**引用前必须同时 `Get-Item` src 与 olean**；只要 src > olean 或最后 attempt 是 FAIL，就标 STALE/不可引用。

### 4.95 【低·纪律】F7SeparableResidue RETIRED；scratch/Lead probe 不作证据
- `Mzk1F7SeparableResidueActual` 最后 FAIL 14:01:44，此后 0 次 attempt；已被 #209 `residue_separable_global`（三公理）取代。**RETIRED：不得引用、不得再排 watchdog**（文件仍在磁盘，Lead 的“已删”按“退出活动队列”理解）。
- `_ScratchEmmyStmt3`（14:06:43）、`_P1OpenScratch`（14:21:06）、`_ProbeP8LeadActual`（14:11:26，Lead lane）都**不是本 lane 证据**；不得把它们的三公理/结论写进 gate 表。

## 5h. batch 12 立即动作（快照 14:35 UTC）

1. **P¹_glued proper（alan/david，最高优先）**：#230 `P1ValuativeActual` 14:33:26 已 DONE（universe 修好，5 条预备引理），下一步直接证 `p1GluedToBase_valuativeCriterion`（`ValuativeCriterion p1GluedToBase`，存在性 + 唯一性）。#225（14:28:59）已把 QC/QS/LFT 三个 side condition 备齐，`IsProper.of_valuativeCriterion` 可直接用；**在 `p1GluedToBase_valuativeCriterion` 存在前，不要排队 `Mzk1P1ProperAssemblyActual`**（它引用的名字不存在，必红），也不得引用其 `p1GluedToBase_isProper`。
2. **π⁻¹ 目标（henry/emmy）**：在 `Mzk1G1FermatPiPreimageChartActual` 里先修 `p1_overlapToChartInf_opensRange` 的类型别名（`change`/`show` 到 `Spec (CommRingCat.of (Polynomial ℚ))` 的 Opens），再把四条 chart 原像组合成最终 `pi_preimage_chart0 : (pi n) ⁻¹ᵁ localChart0.opensRange = basicOpen (x0 n ^ n)` 与 `pi_preimage_chartInf`。**当前没有这两条陈述**。
3. **C2 q 侧（kurt，已完成）**：`Mzk1URQNormalizationActual` **14:30:29 DONE**（src 22:28:35 / olean 22:30:29），`ur_cNorm_eq_localNormOrder`/`ur_gen_eq_sourceRootQUnit`/`urM_eq_half_qMagnitude` 三条三公理（P12b 复算）。**q 侧 M=Q/(2l) 可引用**；不要再改 `ring`。剩余 θ 侧：`Mzk1URThetaMonotoneActual` 14:34:04 FAIL（`urHullLog_mono` heartbeat），`urThetaHullLog_le_weighted` 仍假设 per-b 包含；#238 C4 仍假设 `htheta`。C2 不能记整体闭合。
4. **F7 radical support（sophie）**：14:26:18 已修复并 DONE（src 22:24:25 / olean 22:26:18）；`f7_normalizedLogDisc_le_of_div_ramification` 三公理，消费者 #221。引用必须带 `hzero/hdiv/hbad`；**不要再回退**。若要把该条加入 probe，需在下一批重新排队（本批 Probe 12 早于其 DONE）。
5. **F7(a)**：继续只引 #209 `residue_separable_global`（三公理）；`F7SeparableResidue` RETIRED（§4.95）。
6. **IsFinite π（grace）**：只剩两条 chart 限制 `IsFinite (pi n ∣_ localChart0.opensRange)` / `… localChartInf.opensRange`（#222）。用 #202/#203 的 chart 环有限性 + π⁻¹ 等式 + 局部化传递；**不要**把 #200 的 `chartMorphism*_comp` 当 IsFinite 接口（§4.77 不变）。
7. **P¹ 双模型（Lead 裁决，§4.89）**：在裁决前禁止把 `psiChart0ToP1`（Proj）与 π（glued）复合；`FiniteDisjointBelyi` 自己的 `projectiveLine` 是第三处 Proj 定义，也必须写明。
8. **D3 / L-H**：`HeightDictionaryInterface` 仍 NO INHABITANT；`JHeightLower` 只有齐次性；不得写“j 高度下界已证”。
9. **引用纪律（batch 12 版，强制）**：
   - #221 F7 htame：**条件于 hdiv/hpn**；#222 IsFinite π：**条件于 h0/h1**；#225 P¹ proper：**Proj 模型 only**，glued proper 无定理（当前 14:28:59）；#228 M=Q/(2l)：**未证**；#238 C4：**条件于 htheta/hstepVIII**。
   - #225 P1Proper：只引 22:27:54 版（olean 22:28:59）；§2j-4 的 14:13:21 行与 14:23:31 版均已过期。
   - #227 PiPreimageChart、#228 URQNormalization、#230 P1Valuative、#232 ChartSwap、#237 OmegaTransitionGlobal：**当前红/无 fresh olean，全部禁引**；#229 RadicalSupportActual 已 DONE（可引，但带 hzero/hdiv/hbad）。
   - #231 P1ProperAssembly：**幻影 producer，禁引**；`p1GluedToBase_valuativeCriterion` 不存在。
   - F7SeparableResidue：RETIRED；scratch/Lead probe：不作证据。
   - STALE 一律先查 src/olean；日志 axiom 只取末段（Probe 12 日志 14 块 = 6+8）。
10. **U-C C4（#238）**：`uc_c4_paperConstants_of_p6` 14:29:25 DONE（三公理），但 `htheta : actualThetaHullLogRoot ≤ ucWeightedHpkt` 与 `hstepVIII` 都是显式假设；q 侧 #228 的 M 已可用，但 **θ 侧上界仍缺**。只能记“C4 条件式装配”，**不得记 C4 闭合**，也不得把 `p6_neg_M_le_HTheta2` 当 θ 侧上界。

## 6i. batch 12 更新（快照 **14:35 UTC = 22:35 CST**；覆盖 §6/§6b–§6h 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_status.mjs … --err`（对 22 个文件逐个取最后 START/DONE/FAIL；对 FAIL 读首错：PiPreimageChart、URQNormalization、P1Valuative、ChartSwap、RadicalSupportActual、P1Proper 的 14:17:55 段；Omega 无 log）；`watchdog.log` 13:49–14:29 全量抽取 + 按文件压缩；olean/源码 mtime 对照（16 个文件）；禁用项 grep（12 个源文件；唯一命中为注释/`#print axioms`/`true` 分支/`maxHeartbeats`，人工排除）；源码语义阅读（F7TameCountGlobal 全文 63 行、PiFiniteAssembly 全文 50 行、LpHensel 尾部 600–645 与头部、URJ1 全文 91 行、P1Proper 全文 279 行、PsiAffineCompat 全文 172 行、PiPreimageChart 全文 124 行、URQNormalization 全文 91 行、RadicalSupportActual 99–284、P1Valuative 全文 107 行、P1ProperAssembly 全文 17 行、ChartSwap 全文 64 行、UCHpkt 236–311、QHeight 25–43、FiniteDisjointBelyi 1–45、Mathlib `ValuativeCriterion.lean` 的 `IsProper.of_valuativeCriterion`）。
- **Probe 12/12b**：`_ProbeBatch12Actual.lean` 6 条首跑 DONE 14:23:57（60s），扩展 8 条 DONE 14:26:19（57s），**8 条全部 [propext, Classical.choice, Quot.sound]**；`_ProbeBatch12bActual.lean` 3 条 DONE 14:32:45（53s），**`urM_eq_half_qMagnitude`、`f7_normalizedLogDisc_le_of_div_ramification`、`uc_c4_paperConstants_of_p6` 全部三公理**。两次日志均 0 error / 0 sorryAx（详见 §3h/§3i）。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未运行 / 未覆盖（如实标注）**：
  - `Mzk1G1FermatRadicalSupportActual`：14:26:18 DONE（src 22:24:25 / olean 22:26:18），三条 (L) 三公理；但 **Probe 12 早于其 DONE，未独立复算**（下一批可加）。
  - `Mzk1URQNormalizationActual`：14:30:29 DONE（src 22:28:35 / olean 22:30:29），三条均三公理；Probe 12b 已独立复算 `urM_eq_half_qMagnitude`。**C2 q 侧已闭合。**
  - `Mzk1P1ValuativeActual`（14:33:26 DONE，5 条预备引理；无 #print）、`Mzk1URThetaMonotoneActual`（14:34:04 FAIL，无 olean）、`Mzk1P1ProperActual` 的 LFT/QC/QS 其余条目：**未 audit-probe**（Probe 12 只覆盖 `p1ProjToBase_isProper` 与 `p1GluedToBase_quasiSeparated`）。
  - `Mzk1G1FermatPiPreimageChartActual` 四条 chart 原像：FAIL、无 olean，未 probe。
  - `Mzk1P1ProperAssemblyActual`：无 watchdog 事件、无 olean，**未编译**；其 `p1GluedToBase_isProper` 未验证且名字引用不存在。`Mzk1G1FermatChartSwapActual` 14:31:12 DONE（三公理）但只到 x↔y 自同构基础设施，未 probe。`Mzk1UCHpktActual` 14:29:25 DONE（C4 条件式），Probe 12b 已复算。
  - `_ProbeP8LeadActual` / `_ScratchEmmyStmt3` / `_P1OpenScratch`：不属本 lane 或 scratch，未判数学内容。
  - U-R 全组（除 #224/#228）、G-K 递归构造、H-T 的 F1–F4/F8、P8-P 端到端：**未运行**语义审计。
- **快照 14:35 UTC 之后**：watchdog 仍在跑（14:33:00 起 URThetaMonotone/P1Valuative；14:33:26 P1Valuative DONE、14:34:04 URThetaMonotone FAIL、14:34:19 Omega 重试）。**14:35 之后的任何 DONE/FAIL 本表未审计**。
- **本批新发现并已写进正文的纪律**：§4.87（P¹_glued proper 缺主定理 + P1ProperAssembly 幻影 producer；P1Valuative 14:33:26 只到 5 条预备引理）、§4.88（**C2 q 侧 M=Q/(2l) 14:30:29 闭合、Probe 12b 三公理；只剩 θ 侧 H_pkt**；URThetaMonotone 14:34:04 红、UCHpkt C4 仍假设 htheta）、§4.89（P¹ 三处模型，FiniteDisjointBelyi 的第三份 Proj 定义）、§4.90（π⁻¹ 目标仍未陈述）、§4.91（Hensel integral form 未接 GK）、§4.92（RadicalSupportActual 修复后条件式落地 + Probe 12b）、§4.94（DONE 后改写 + 日志两种行为并存）。

- 本批写入范围：本表 + **更新** `tmp/sheaf/xif/paper/_ProbeBatch12Actual.lean`（6→8 条）；未改其它 Lean 文件；未 spawn_teammate、未 `lake env lean`、未自起 watchdog、未写 sorry/axiom。

## 2l. 本批 batch 13 gate 表（快照 **14:46 UTC = 22:46 CST**；**#242–#256**，覆盖 14:35–14:46 全部 DONE/FAIL + Lead 指定 6 项复核）

- 证据版本：src / olean 均按 `Get-Item` 实测（`.lake/build/lib/lean/tmp/sheaf/xif/paper/<file>.olean`）；`(P13)` / `(P13b)` / `(P13c)` = 本批独立 probe 复算。**14:46 UTC 之后未审计**（watchdog 仍在跑；P1Valuative src 22:46:09 待重试、P6P5ThetaHullControl2 src 22:44:03 红、URThetaPacketCarrier src 22:45:24 红）。
- **14:35–14:46 事件全量**（按块计，不按累计行）：14:35:34 P1Valuative FAIL（src 22:34:51，首错 `Inhabited ↥(Spec (CommRingCat.of R))`）→ 22:37:11 重写 → 14:38:13 DONE → 22:42:01 追加 existence → **14:44:22 FAIL**（271:22 `No goals to be solved`）→ src 22:46:09 待重试；14:35:54 / 14:43:36 / 14:46:10 P6P5ThetaHullControl2 三连 FAIL（无 log，src 22:44:03）；14:36:40 URThetaMonotone DONE；14:37:23 PiPreimageChart FAIL；14:37:24 ChartSwap FAIL（log 0 B）→ 22:40:22 重写 → **14:41:05 DONE**（olean 22:41:04 fresh）；14:37:31 Omega DONE → 22:38:30 改写 → 14:42:34 FAIL → 22:43:13 改写 → **14:44:30 DONE**（olean 22:44:30 fresh）；14:38:41 / 14:41:44 / 14:45:02 URThetaPacketCarrier 三连 FAIL（无 log，src 22:45:24）；14:40:34 Probe 13 START → 14:41:30 DONE（56s）；14:44:20 Probe 13b DONE（30s）；14:45:44 Probe 13c DONE。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 242 | Mzk1UCHpktActual | U-C C4 | **DONE** | 14:29:25 | fresh（src 22:28:16 / olean 22:29:24） | clean | 三公理 (P13) | **B：条件式装配**。`uc_c4_paperConstants_of_p6` 显式假设 `htheta : actualThetaHullLogRoot ≤ ucWeightedHpkt w V` 与 `hstepVIII : (∑ w B) ≤ κ(...) − actualQPilotMagnitudeClassical`；P5 下界走 accepted `p6_neg_M_le_HTheta2`。**C4 未闭合**：htheta 正是缺的 θ 上界，hstepVIII 是 U-L Step(viii) 输入；不得写“C4 已证”，也不得把 `p6_neg_M_le_HTheta2` 当 θ 侧上界。 |
| 243 | Mzk1URQNormalizationActual | U-R C2 q 侧 | **DONE** | 14:30:29 | fresh（src 22:28:35 / olean 22:30:29） | clean | 三公理 (P13) | **B−：归一化恒等式**。语句确为 **/(2l) 形式**：`(1/(2·l)) * Q = −∑_b w_b ((1/(2·l)) * log‖q_b‖)`，且非 `rfl`；但 `localNormOrder := −log‖x‖/log p`，`ur_cNorm_eq_localNormOrder` 是 unfolding、`ur_gen_eq_sourceRootQUnit` 是 `rfl`、`urRootQ_log_norm_order` 是 field_simp ⇒ 实质是把定义搬过来。**不得当“M=Q/(2l)”独立数学定理或 C2 实质突破**；θ 侧仍完全缺。 |
| 244 | Mzk1G1FermatChartSwapActual（覆盖 §6i 的 14:31:12 行） | G-A x↔y 对称 | **DONE** | **14:41:05** | fresh（src 22:40:22 / olean 22:41:04） | clean | 三公理 (P13b：`ModelSwapEquiv`、`modelSwap_isStandardSmooth`) | **A-局部**：`swapR : R n ≃ₐ[ℚ] R n`、`ModelSwapEquiv : Model n ≃ₐ[ℚ] ModelSwap n`、`modelSwap_isStandardSmooth : Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (ModelSwap n)`（沿 equiv 从 r-侧运输）。此前 14:37:24 FAIL（log 0 B，首错未取）已被 22:40:22 版覆盖。**仍无 `(R n)[1/r] ≃ (R n)[1/r']` / `[1/y]` 与 scheme 层 smooth**（ledger 的下一步 3–6），不得记 G-A smooth 闭合。 |
| 245 | Mzk1P1ValuativeActual | G-A P¹_glued proper | **FAIL** | **14:44:22**（此前 14:38:13 / 14:41:05 DONE） | STALE（src 22:42:01 / olean 22:41:05） | clean | 三公理 (P13：`specMap_comp_chartMorphism0`，只对 154 行预备版有效) | **R / 未完成（near-miss）**：最新 attempt 首次写 `valuativeCriterion_existence : ValuativeCriterion.Existence p1GluedToBase`，在 271:22 `rwa` 处 `No goals to be solved` 而红。14:38:13 DONE 的 154 行版只有 `range_eq_singleton_specField`、`range_subset_of_closedPoint_mem`、`specMap_eq_of_comp_eq`、`eq_chartMorphism{0,Inf}_of_lift`、`specMap_comp_chartMorphism{0,Inf}`、`chartMorphism{0,Inf}_mem_chart*`。**当前无 `p1GluedToBase_valuativeCriterion`、无已编译的 `ValuativeCriterion` 定理**；**NOT properness producer**。 |
| 246 | Mzk1P1ProperActual | G-A P¹ proper 侧条件 | **DONE** | 14:28:59 | fresh（src 22:27:54 / olean 22:28:59） | clean | 三公理 (P13：`chart_ranges_inf`) | **A-局部**：QC/QS/LFT 三 side condition（`LocallyOfFiniteType`/`QuasiCompact`/`QuasiSeparated`）+ `overlap_range_eq`、`chart_ranges_inf`（两 chart 开集交 = overlap 像）。**仍无 `p1GluedToBase_isProper`**；不得写 P¹_glued proper 已证。 |
| 247 | Mzk1P1ProperAssemblyActual | G-A 幻影装配 | **NO-EVENT** | —（src 22:17:06） | **none** | clean（未编译） | — | **PHANTOM（未删除）**：858 B，无 watchdog 事件、无 olean；引用的 `p1GluedToBase_valuativeCriterion` 在当前 paper 目录 **0 命中**（P1Valuative 的最新尝试叫 `valuativeCriterion_existence`，且 14:44:22 红）。**仍禁排队、禁引用其 `p1GluedToBase_isProper`**。 |
| 248 | Mzk1G1FermatPiProperActual | G-A Y_n proper | **DONE** | 14:19:57 | fresh（src 22:19:07 / olean 22:19:57） | clean | 三公理 (P13：`fermatCurveToSpec_isProper`) | **B：条件式**。`fermatCurveToSpec_isProper (hfin : IsFinite (pi n)) (hP1 : IsProper p1GluedToBase) : IsProper fermatCurveToSpec`；`fermatCurveToBase_eq_fermatCurveToSpec` 是 `subsingleton_hom_spec_rat` 的 `Subsingleton.elim`（真但廉价）。两个输入都未交付；不得写 IsProper(Y_n) 已证。 |
| 249 | Mzk1SchemeOpensRangeInterfaceActual | Opens coercion 接口 | **DONE** | 14:19:56 | fresh（src 22:19:02 / olean 22:19:56） | clean | 三公理 (P13：`opensRange_coe_eq_range`) | **A-局部（通用接口）**：4 条 `opensRange_coe_eq_range` / `mem_opensRange_iff` / `opens_eq_iff_coe_eq` / `opens_eq_of_forall_mem`；无 π 内容，只是后续 π⁻¹ 等式要用的 coercion 层。 |
| 250 | Mzk1URThetaMonotoneActual | U-R C2 θ 侧 | **DONE** | 14:36:40 | fresh（src 22:35:32 / olean 22:36:40） | clean | 三公理 (P13：`urThetaHullLog_le_weighted`) | **C/B−：条件式和**。只剩 `urThetaHullLog_le_weighted`（`hperB : ∀ b, actualLocalHullLog b ≤ packetHullLog b` ⇒ 加权和）；上批 14:34:04 红掉的 `urHullLog_mono` 已不在文件中。**“修复”= 删掉红引理，不是证出 θ≤H_pkt**；核心几何输入仍假设。 |
| 251 | Mzk1G1OmegaTransitionGlobalActual | G1-B Ω A3 过渡 | **DONE** | **14:44:30** | fresh（src 22:43:13 / olean 22:44:30） | clean | 三公理 (P13c：`n_smul_omega0O`、`omegaInfRaw_eq_pow_smul_omega0O`) | **A-局部**：overlap 上 `overlap_derivation_relation`、`diu_eq`、`omegaInfRaw_eq`、A3 `omegaInfRaw = u0^(n−3) • omega0O`（n≥3）；真实微分计算，非标量恒等式。仍是局部 overlap，未粘成 G-B 全局 Ω 层；**14:37:31 的 DONE 已被 22:38:30 改写作废，只有 14:44:30 版可引**。 |
| 252 | Mzk1P6P5ThetaHullControl2 | U-R C2 θ 侧(A) | **FAIL** | **14:46:10**（此前 14:35:54 / 14:43:36） | none（src 22:44:03） | clean（未编译） | — | **R**：`actualLocalHullLog_mono` / `thetaHullLog_le_ucHpkt` / `thetaHullLog_le_ulHpkt` 全部条件于 `hperB`；未证 per-b 包含，且无 log 可取首错。不得引用。 |
| 253 | Mzk1G1FermatPiPreimageChartActual | G-A π⁻¹ chart | **FAIL** | **14:37:23** | none（src 22:24:22） | clean（未编译） | — | **R**：首错仍是 opensRange 类型别名 / coercion（37、43、51：`PrimeSpectrum.basicOpen Polynomial.X` 期望 `chartInfScheme.Opens`）；π⁻¹ 目标仍未陈述。与 batch 12 的失败类型相同。 |
| 254 | Mzk1URThetaPacketCarrierActual | U-R C2 θ 侧(B) | **FAIL** | **14:45:02**（此前 14:38:41 / 14:41:44） | none（src 22:45:24） | clean（未编译） | — | **R（在跑）**：首次尝试 per-b same-carrier 包含 `urThetaPossibleImages ⊆ urThetaPacketHull`（经 `p6_possibleImages_subset_packetHull`，T-side carrier = `qVFamTensorBlock`），方向正确但未编译；即便转绿，仍需 `p6PacketHull` 与 U-L `ucActualV` 的同一性。 |
| 255 | Mzk1G1FermatRadicalSupportActual（覆盖 §4.92 的 14:26:18 行） | F7 div-ramification | **DONE** | 14:31:37 | fresh（src 22:30:23 / olean 22:31:36） | clean | 三公理 (P13) | **A-局部 / 条件式**：`f7_normalizedLogDisc_le_of_div_ramification` 仍带 `hzero`、`hdiv`（`e_P ∣ n`）、`hbad`；batch 12 的“未独立复算”缺口已关闭。F7 htame 不得写无条件；消费者 #221 引用必须带三条件。 |
| 256 | Mzk1F7SeparableResidueActual / Mzk1G1QHeightActual | F7(a) / L-H D3 | RETIRED / DONE | 14:01:44 / 13:18:10 | — / fresh | clean | 三公理（QHeight 旧行） | F7SeparableResidue **RETIRED**（最后 FAIL 14:01:44，此后 0 attempt；已被 #209 取代）；`HeightDictionaryInterface` 仍只是 `def`（Mzk1G1QHeightActual:40），**NO INHABITANT**。 |

### 2l-1 缺口表（Lead 指定 8 项，逐项核对）

| 缺口 | 当前证据（14:46 UTC） | 状态 |
|---|---|---|
| P¹ 双模型 | 3 处 `projectiveLine` 定义：`Mzk1G1ProjectiveLineChartsActual:15`（Proj）、`Mzk1G1FiniteDisjointBelyiActual:20`（第三份 Proj）、`Mzk1G1ProjectiveLineGluedActual:136`（glued）；**无 Proj ≅ glued 的 iso** | 未闭合，禁复合 |
| D3 no inhabitant | `Mzk1G1QHeightActual:40` 只有 `def HeightDictionaryInterface`，全树无实例；`JHeightLower` 仍只有 4 条齐次性（§4.93 不变） | **NO INHABITANT** |
| IsFinite π 条件式 | `isFinite_pi_of_chart_restrict`（Probe 12 三公理）已在；只差 `IsFinite (pi n ∣_ localChart0.opensRange)` 与 `… localChartInf.opensRange` 两条 | 条件式，差两条 |
| π⁻¹(D_+(X0))=D(x0^n) | `Mzk1G1FermatPiPreimageActual.pi_preimage_eq` 的一般两 chart 分解已证；**具体 chart 等式无陈述**；`Mzk1G1FermatPiPreimageChartActual` 14:37:23 红 | 无陈述 |
| IsProper p1GluedToBase | P1Proper 有 QC/QS/LFT（14:28:59 fresh）；P1Valuative existence 14:44:22 **FAIL**；`p1GluedToBase_valuativeCriterion` 0 命中；P1ProperAssembly 幻影 | **无 producer** |
| C2 只差 θ H_pkt | q 侧是归一化恒等式（#243）；θ 侧两个 wrapper 均假设 `hperB`（#250/#252）；`URThetaPacketCarrier` 红；T-side `p6PacketHull` vs U-L `ucActualV` 同一性未证 | 未闭合 |
| F7SeparableResidue | 最后 FAIL 14:01:44，0 attempt；#209 `residue_separable_global` 三公理替代 | **RETIRED** |
| phantom P1ProperAssembly | src 22:17:06，无 olean，NO-EVENT；引用名不存在 | **PHANTOM，禁引** |

### 2l-2 alan 的“删除动作”核对
- **未观察到任何 paper 目录文件被删除**（`P1ProperAssemblyActual` 仍在磁盘 858 B；`Mzk1P1DVR*` 等旧文件也都在）。可观察到的“删/改”是 **P1Valuative 的两次重写**：22:37:11 把 14:35:34 失败的 `Inhabited ↥(Spec R)` 段删掉；22:46:09 又把 14:44:22 的 `No goals to be solved` 处重写。若 Lead 指“删掉幻影 producer”，该动作**没有发生**；§2l#247 仍然成立。

## 3j. Probe 13（本批 batch 13）：`tmp/sheaf/xif/paper/_ProbeBatch13Actual.lean`

- 队列：`wd_add` 14:40:34 → **DONE 14:41:30（56s）**；log 1118 B，**0 error / 0 sorryAx**。
- 8 条全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | 对应 gate 行 |
|---|---|---|
| `UCHpktActual.uc_c4_paperConstants_of_p6` | [propext, Classical.choice, Quot.sound] | #242 |
| `URQNormalizationActual.urM_eq_half_qMagnitude` | [propext, Classical.choice, Quot.sound] | #243 |
| `P1ProperActual.chart_ranges_inf` | [propext, Classical.choice, Quot.sound] | #246 |
| `G1FermatPiProperActual.fermatCurveToSpec_isProper` | [propext, Classical.choice, Quot.sound] | #248 |
| `SchemeOpensRangeInterfaceActual.opensRange_coe_eq_range` | [propext, Classical.choice, Quot.sound] | #249 |
| `G1FermatRadicalSupportActual.f7_normalizedLogDisc_le_of_div_ramification` | [propext, Classical.choice, Quot.sound] | #255 |
| `URThetaMonotoneActual.urThetaHullLog_le_weighted` | [propext, Classical.choice, Quot.sound] | #250 |
| `P1ValuativeActual.specMap_comp_chartMorphism0` | [propext, Classical.choice, Quot.sound] | #245（仅预备版） |

## 3k. Probe 13b / 13c（补充）

- `_ProbeBatch13bActual.lean`：14:43:51 排入 → **DONE 14:44:20（30s）**；log 272 B；`G1FermatChartSwapActual.ModelSwapEquiv`、`modelSwap_isStandardSmooth` **均三公理**（#244 新增内容，batch 12 未覆盖）。
- `_ProbeBatch13cActual.lean`：14:44:30 后排入 → **DONE 14:45:44**；log 289 B；`G1OmegaTransitionGlobalActual.n_smul_omega0O`、`omegaInfRaw_eq_pow_smul_omega0O` **均三公理**（#251）。
- 三次 probe 合计 12 条，全部三公理，0 sorryAx。**未 probe**（因 STALE/红）：P1Valuative existence、P6P5ThetaHullControl2、URThetaPacketCarrier、PiPreimageChart。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 13 续）

### 4.96 【高·G-A】P¹_glued proper 仍无 producer；P1Valuative 只是 near-miss
- P1Proper（14:28:59）已交 QC / QS / LFT 与两 chart 开集交；但真正的主定理 `p1GluedToBase_isProper` 仍不存在。P1Valuative 14:44:22 在 `valuativeCriterion_existence` 的 271:22 处 `No goals to be solved` 红，说明存在性证明接近完成但**未编译**；全树仍无 `p1GluedToBase_valuativeCriterion`。
- **纪律**：在 existence+uniqueness 都编译且 `IsProper.of_valuativeCriterion` 组装 DONE 之前，(i) 不得排队 `Mzk1P1ProperAssemblyActual`（引用名不存在，必红），(ii) 不得引用其 `p1GluedToBase_isProper`，(iii) 不得把 PiProper 的 `fermatCurveToSpec_isProper` 当无条件 proper。

### 4.97 【高·U-R/C2】θ 侧仍无 producer；q 侧只是归一化恒等式
- q 侧 #243：语句形状正确（/(2l)），但 `localNormOrder := −log‖x‖/log p`、`ur_gen_eq_sourceRootQUnit` 是 `rfl`，整条是把定义搬过来；**不能算 C2 的实质突破**。
- θ 侧：#250 只剩条件式和；#252 是同一个 `hperB` 的条件包装；#254 首次尝试真正的 per-b `urThetaPossibleImages ⊆ urThetaPacketHull`（同 carrier `qVFamTensorBlock`），但 14:45:02 仍红。即便 #254 转绿，也还需要 `p6PacketHull` 与 U-L `ucActualV`（`ulPacketVOfWitness`）的同一性，才能喂给 UCHpkt 的 `htheta`。**不得写“C2 已闭合”或“θ_P5 ≤ H_pkt 已证”**。

### 4.98 【高·纪律】14:35–14:46 再次“DONE 后立即改写”；日志清空/累积两种行为并存
- Omega：14:37:31 DONE → src 22:38:30 → 14:42:34 FAIL → src 22:43:13 → 14:44:30 DONE；**只有 14:44:30 版可引**。
- ChartSwap：14:31:12 DONE → 22:36:19/22:38:26 改写 → 14:37:24 FAIL → 22:40:22 → 14:41:05 DONE；**只有 14:41:05 版可引**。
- P1Valuative：14:38:13 DONE → 14:41:05 DONE → 22:42:01 改写 → 14:44:22 FAIL；**当前红**。
- 日志：ChartSwap 14:37:24 的尝试 log **0 B**、P6P5ThetaHullControl2 与 URThetaPacketCarrier **无 log**（首错未取）；PiPreimageChart log 45 KB 跨 attempt 累积（只能取末段）。**“START 清空”与“跨 attempt 累积”仍并存**，引用前必须同时 `Get-Item` src 与 olean。

### 4.99 【中·G-A/π】π⁻¹ 具体 target、IsFinite π、P¹ 三模型
- `Mzk1G1FermatPiPreimageActual.pi_preimage_eq` 只给一般分解 `(pi n)⁻¹V = chart0 像 ⊔ chartInf 像`；**`π⁻¹(D_+(X0)) = D(x0^n)` 与 `π⁻¹(D_+(X1)) = D(...)` 仍无陈述**；`Mzk1G1FermatPiPreimageChartActual` 14:37:23 红在 coercion。
- `IsFinite (pi n)` 只差两条 chart restriction，组装引理已在（#222 不变）。
- P¹ 三处模型（Proj ×2 + glued）仍无 iso；`psiChart0ToP1`（Proj）与 π（glued）的复合在裁决前禁止（§4.89 不变）。

### 4.100 【中·F7】div-ramification 已独立复算；仍条件式；F7Sep 已 RETIRED
- #255 三公理已由 Probe 13 独立确认（batch 12 的“未独立复算”缺口关闭）；但 `hzero/hdiv/hbad` 三条件不可省。F7SeparableResidue 最后 FAIL 14:01:44、此后 0 attempt，**RETIRED**，不得再排队或引用。

### 4.101 【中·L-H】D3 仍 NO INHABITANT
- `HeightDictionaryInterface`（Mzk1G1QHeightActual:40）仍只是 `def`；`JHeightLower` 仍只有齐次性；不得写“j 高度下界已证”或“D3 已交”。

## 5i. batch 13 立即动作（快照 14:46 UTC）

1. **P¹_glued proper（alan/david，最高优先）**：P1Valuative 14:44:22 的 `No goals to be solved` 在 271:22（`by_contra hne` 分支内的 `rwa`）；删掉多余的 `rwa`/改成 `simpa` 后重编，再把 Existence 与 Uniqueness 组成 `p1GluedToBase_valuativeCriterion`，最后用 `IsProper.of_valuativeCriterion` 在**单独文件**（可保留 `P1ProperAssembly` 名，但必须先让引用名存在）组装。**在此之前禁引 `p1GluedToBase_isProper`**。
2. **C2 θ 侧（kurt/sophie）**：优先修 `Mzk1URThetaPacketCarrierActual` 的 per-b 包含（同 carrier，方向正确）；转绿后补 `p6PacketHull` 与 U-L `ucActualV` 的同一性，再用 `thetaHullLog_le_ucHpkt` / `thetaHullLog_le_ulHpkt` 产生 UCHpkt 的 `htheta`。`Mzk1P6P5ThetaHullControl2` 现在红，先别引用。
3. **ChartSwap（grace）**：14:41:05 已 fresh DONE，可引 `ModelSwapEquiv` / `modelSwap_isStandardSmooth`（三公理）；下一步做 `(R n)[1/r] ≃ (R n)[1/r']`（局部化函子性）与 `[1/r'] ≃ [1/y]`，再走 scheme 层 smooth。
4. **Omega（grace）**：14:44:30 已 fresh DONE，可引 A3 overlap 过渡；下一步把局部 `omegaInfRaw` 粘成全局 Ω 层并接 ω∞。
5. **π⁻¹ chart（henry）**：先修 `Mzk1G1FermatPiPreimageChartActual` 的 coercion（37/43/51，需 `change`/`show` 到 `chartInfScheme.Opens`），再把四条 chart 原像合成 `π⁻¹(D_+(X0)) = D(x0^n)` 与 `π⁻¹(D_+(X1)) = D(x1^n)`。
6. **IsFinite π（grace/henry）**：只差两条 `IsFinite (pi n ∣_ localChart*.opensRange)`；用 #202/#203 的 chart 环有限性 + π⁻¹ 等式 + 局部化传递；不要用 `chartMorphism*_comp` 当 IsFinite 接口（§4.77 不变）。
7. **引用纪律（batch 13 版，强制）**：#242 C4 **条件于 htheta/hstepVIII**；#243 只是 q 侧归一化恒等式；#245 P1Valuative **不是** properness producer；#246 无 `p1GluedToBase_isProper`；#247 P1ProperAssembly **PHANTOM 禁引**；#248 Y_n proper **条件于 hfin/hP1**；#250/#252 θ 侧均条件于 hperB；#251 Omega 只引 14:44:30 版；#255 F7 带 `hzero/hdiv/hbad`；#256 F7Sep RETIRED、D3 NO INHABITANT。
8. **P¹ 双模型 / π 复合**：裁决前禁止 `psiChart0ToP1`（Proj）与 π（glued）复合；`FiniteDisjointBelyi` 的第三份 Proj 定义必须写明（§4.89 不变）。

## 6j. batch 13 更新（快照 **14:46 UTC = 22:46 CST**；覆盖 §6–§6i 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_status.mjs`（15 个目标，逐个取最后 START/DONE/FAIL；对 FAIL 读首错：P1Valuative、PiPreimageChart；ChartSwap/P6P5/Carrier 的 log 为 0 B 或无 log）；`Get-Item` src/olean 对照（16 个文件）；`watchdog.log` 14:35–14:46 全量按块抽取；源码语义阅读（UCHpkt 全文 312 行、URQNormalization 全文 91 行、ChartSwap 全文 164 行、P1Valuative 全文 282 行、P1Proper 250–279、PiProper 全文 97 行、OpensRange 全文 37 行、URThetaMonotone 全文 69 行、P6P5ThetaHullControl2 全文 109 行、URThetaPacketCarrier 全文 69 行、Omega 全文 211 行、RadicalSupport 240–294、QHeight 40 附近、URRootExtInstances 的 `urRootQ_log_norm_order`、`localNormOrder` 定义）；名字 grep：`p1GluedToBase_valuativeCriterion` **0 命中**、`projectiveLine` **3 处定义**、`pi_preimage` 现状。
- **Probe 13**：8 条 DONE 14:41:30（56s），**全部三公理**；**Probe 13b**：2 条 DONE 14:44:20（30s），**全部三公理**；**Probe 13c**：2 条 DONE 14:45:44，**全部三公理**。三次日志合计 0 error / 0 sorryAx。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未运行 / 未覆盖（如实标注）**：P1Valuative 的 existence（红，未 probe）；P6P5ThetaHullControl2 / URThetaPacketCarrier（红，未 probe）；PiPreimageChart（红，未 probe）；ChartSwap 14:37:24 的首错（log 0 B）；P6P5 / Carrier 的首错（无 log）；U-R 其余 θ 侧、G-K 递归、H-T 的 F1–F4/F8、P8-P 端到端仍未做语义审计。
- **14:46 UTC 之后**：watchdog 仍在跑（P1Valuative src 22:46:09 待重试；P6P5 src 22:44:03、Carrier src 22:45:24 红）。**14:46 之后的任何 DONE/FAIL 本表未审计**。
- 本批写入范围：本表 + **新建** `tmp/sheaf/xif/paper/_ProbeBatch13Actual.lean`、`_ProbeBatch13bActual.lean`、`_ProbeBatch13cActual.lean`；未改其它 Lean 文件；未 spawn_teammate、未 `lake env lean`、未自起 watchdog、未写 sorry/axiom。

### 2l-3 快照后补记（14:46:10–14:48:47；只补事件，不覆盖 §2l 表内 #245 的 FAIL 判定）
- **P1Valuative DONE 14:46:50**（src 22:46:09 / olean 22:46:50 fresh，27s）：`valuativeCriterion_existence : ValuativeCriterion.Existence p1GluedToBase` 已编译；Probe 13d（DONE 14:48:47，log 138 B）**三公理**。**仍无 `p1GluedToBase_valuativeCriterion`（Existence ∧ Uniqueness）与唯一性定理**；P1ProperAssembly 引用的名字仍 0 命中 ⇒ **仍无 `IsProper p1GluedToBase` 的 producer**。#245 的“FAIL 14:44:22”作为当时状态保留；现状更新为 **A-局部（existence 部分已证）**。
- **URThetaPacketCarrier FAIL 14:47:28**（src 22:45:24，无 log/olean）：连续第 4 次红，per-b 包含仍未编译（#254 现状不变）。**P6P5ThetaHullControl2** 最后 FAIL 14:46:10（src 22:44:03），无新 attempt（#252 不变）。
- 本补记只到 14:48:47；此后未审计。Probe 13d 亦为 `_Probe*Actual.lean`（写入范围不变）。









## 2m. 本批 batch 14 gate 表（快照 **15:02 UTC = 23:02 CST**；**#257–#272**，覆盖 14:46–15:02 全部 DONE/FAIL + Lead 指定复核）

- 证据版本：src / olean 均按 `Get-Item` 实测；`(P14)`/`(P14b)`/`(P14c)` = 本批独立 probe 复算（§3l）。**15:02 UTC 之后未审计**；此刻 watchdog 仍有 1 个 activity（ChartLocalizeSwap 15:01:58 重试），Uniqueness/ULStepVIII/URThetaTransport 刚红。
- **14:46–15:02 事件全量**（按 attempt 计）：14:47:42 PiPreimageChart → 14:48:06 FAIL（首错 25:6）；14:48:21 P6P5 → **14:49:12 DONE**；14:49:25 P1Valuative → **14:49:52 DONE**；14:49:25 Carrier → **14:50:17 DONE**；14:51:14 P1UniversallyClosed → **14:51:44 DONE**；14:53:20 ChartLocalizeSwap v1 → 14:53:48 FAIL（69:2）；14:54:02 Htheta v1 → 14:54:59 FAIL（log 0 B）；14:55:13 Uniqueness v1 → **14:55:42 DONE**（146 行）；14:55:13 Omega v1 → 14:55:44 FAIL（无 log）；14:56:51 Htheta v2 FAIL（log 0 B）；14:57:05 Omega v2 → 14:57:34 FAIL（log 0 B）；14:57:05 Htheta v3 → **14:57:57 DONE**；14:58:11 ULStepVIII v1 → 14:58:17 FAIL（22:0 invalid import）；14:58:11 ChartLocalizeSwap v2 → **14:58:40 DONE**（5013 B，仅 chart 层）；14:58:33 Uniqueness 改写 → 14:59:22 FAIL（155:6）；14:58:54 Omega v3 → **14:59:24 DONE**；14:59:24 ChartLocalizeSwap v3（6817 B）→ 15:00:09 FAIL（115:30）；15:00:32 Uniqueness 再改 → 15:01:14 FAIL（155:6/162:48）；15:00:46 ULStepVIII v2 → 15:01:44 FAIL（145:4 linarith）；15:00:46 URThetaTransport v1 → 15:01:42 FAIL（109:23 omega）。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 257 | Mzk1P1ValuativeActual | G-A P¹ existence | **DONE** | **14:49:52** | fresh（src 22:48:47 / olean 22:49:52） | clean | 三公理 (P14) | **A-局部 / NOT properness producer**。290 行；`valuativeCriterion_existence : ValuativeCriterion.Existence p1GluedToBase`（Mathlib 定义：∀ `S : ValuativeCommSq f`, `S.commSq.HasLift`，非空、非平凡；证明按 chart 覆盖 + 整数性 `IsInteger lam`/`lam⁻¹` 构造 lift）。**无 Uniqueness、无 `p1GluedToBase_valuativeCriterion`**（全树 grep 0）。14:44:22 的 `No goals to be solved` 已修为 273 行 `rwa [show …]`；P13d 已确认 14:46:50 版，P14 复算当前版。**不得写“P¹ proper 已证”**。 |
| 258 | Mzk1P1UniversallyClosedActual（**新文件**） | G-A P¹ universally closed | **DONE** | **14:51:44** | fresh（src 22:51:00 / olean 22:51:44） | clean | 三公理 (P14) | **A-局部（IsProper 的真成分）**。941 B/18 行：`p1GluedToBase_universallyClosed : UniversallyClosed p1GluedToBase`，组装 = `UniversallyClosed.of_valuativeCriterion` + #257 的 existence + P1Proper 的 `QuasiCompact` **instance**（14:28:59；Mathlib 该引理需 typeclass `[QuasiCompact f]`）。Mathlib `IsProper = ValuativeCriterion ⊓ QComp ⊓ QSep ⊓ LFT`、`ValuativeCriterion = Existence ⊓ Uniqueness` ⇒ **已得 Existence+UC，仍差 Uniqueness（⇒IsSeparated）**。不是 IsProper。 |
| 259 | Mzk1P1ProperAssemblyActual | G-A 装配 | **PHANTOM 已清除** | src 22:38:35（446 B） | **none** | clean（**无定理**） | — | **PHANTOM CLEARED（alan 已删定理）**：现文件只有 7 行注释（“DRAFT — NOT FOR WATCHDOG, NOT IN WHITELIST … Do NOT queue this file”），`p1GluedToBase_isProper` 已被删除。全仓 **Lean 文件** grep `p1GluedToBase_valuativeCriterion` **0 命中**（只剩 `coord/*.md` 文档）。无 watchdog 事件、无 olean。`p1GluedToBase_valuativeCriterion` 仍不存在 ⇒ **仍无 IsProper producer**；该文件**仍禁排队、禁引用**。 |
| 260 | Mzk1P6P5ThetaHullControl2 | U-R C2 θ (A) | **DONE** | **14:49:12** | fresh（src 22:47:51 / olean 22:49:11） | clean | 三公理 (P14) | **B−：条件式和，非 analytic half**。全文 80 行只有 2 条：`thetaHullLog_le_ucHpkt` / `thetaHullLog_le_ulHpkt`，均假设 `hperB : ∀ b, actualLocalHullLog b ≤ packetV b`（`actualThetaHullLogRoot = ∑ b, w_b · actualLocalHullLog b` 展开 + `Finset.sum_le_sum`）。**docstring 第 8–11 行声称的 `actualLocalHullLog_mono` 与 `actualLocalHullLog_le_packetHullLog` 都不在文件中**；所谓“修复”= 删掉心跳失败的单调性引理。**不是 θ 侧 producer**，只是 P6P5 到 UCHpkt 的加权求和 wrapper。 |
| 261 | Mzk1URThetaPacketCarrierActual | U-R C2 θ (B) | **DONE（五次红后首绿）** | **14:50:17** | fresh（src 22:48:31 / olean 22:50:16） | clean | 三公理 (P14) | **A-局部（同载体集合包含）**：`urThetaPossibleImages T b varpi ⊆ urThetaPacketHull T b e varpi`，T-side 实际 places/tuple（`qVFamTensorPlaces`/`qVFamTensorTuple`），`e` 为显式分解；底层 = `p6_possibleImages_subset_packetHull`。**不是 hperB**：`actualLocalHullLog` 的区域是 `actualLocalHullRegion = closure(⋃_j thetaTensorScaledRegion (gaussExponent j * actualRootCoeff))`，而本定理是 `arithmeticTupleStepVPossibleImages = {φ(ϖ·x)}`；全树**无**两者相连的定理（grep `actualRootThetaImageSet`/`urThetaPossibleImages` 无交集）。仍需 (i) 区域桥，(ii) `arithmeticTupleNormalizedLogVolume_mono` 或直接 `actualLocalHullLog ≤ logVol(packetHull)`。 |
| 262 | Mzk1G1FermatPiPreimageChartActual | G-A π⁻¹ chart | **FAIL** | **14:58:39**（14:37:23 / 14:48:06 同） | none（src 22:24:22） | clean（未编译） | — | **R**：当前 attempt（log 45 KB，末块起于第 582 行）首错 **25:6**：`rw [Scheme.Hom.coe_opensRange]` 失败，carrier 是 `↥(Spec (CommRingCat.of R))` 而 membership 期望 `PrimeSpectrum R`；37:6 motive 不 type-correct（`chartInfScheme.Opens` vs `basicOpen Polynomial.X`）、43:6、51:6 同因。**π⁻¹ 目标仍无陈述**；src 自 22:24:22 未改，无 olean。 |
| 263 | Mzk1G1FermatChartLocalizeSwapActual | G-A 局部化对换 | **FAIL（v3）；14:58:40 曾 DONE 后 STALE** | **15:00:09** | **STALE**（src 22:59:24 / olean 22:58:40） | clean | 五条 chart 层定理三公理（日志 + P14c，**只对 22:58:40 版**） | **R（仍在改）**：v1（22:53:07）首错 69:2 `simp` 无进展（`Chart n` vs `R n` 类型不匹配）；v2（22:57:19，5013 B）14:58:40 DONE，证 `swapChart : Chart n ≃ₐ[ℚ] Chart n`、`swapChart_chartR/chartR2`（chart 级 x↔y）；v3（22:59:24，6817 B）追加局部化段后首错 **115:30** `rewrite` pattern 不存在。**`Localization.Away chartR ≃ₐ Localization.Away chartR2` 仍无**；14:58:40 的 olean 已 STALE，不可引。 |
| 264 | Mzk1URThetaHthetaActual（**新文件**） | U-R C2 θ 组装 | **DONE（条件式）** | **14:57:57** | fresh（src 22:57:03 / olean 22:57:57） | clean | 三公理 (P14c) | **B−：条件式组装**。`ur_htheta_of_scaling (hscale : ∀ b, RootHullScalingFormulaAt b) (hpacket : ∀ b, -thetaCoefficientContribution b ≤ packetV b) : actualThetaHullLogRoot ≤ ucWeightedHpkt …`；`ur_htheta_of_halfScalingData` 用 `RootHullHalfScalingDataGap`（half-generator supply + hull equality）；`ur_thetaCoeff_eq_neg_localNormOrder` 把 -`thetaCoefficientContribution` 写成 `-localNormOrder ϖ · log p`。**hscale/hpacket 都是未交付输入**（2l-root 在 completion 中不存在，见 §4.103）；不是 θ 上界。 |
| 265 | Mzk1P1ValuativeUniquenessActual（**新文件**） | G-A uniqueness | **DONE（146 行）→ FAIL（185 行）** | 14:55:42 / 14:59:22 / **15:01:14** | **STALE**（src 23:00:32 / olean 22:55:42） | clean（当前未编译） | 七条三公理 (P14b，**仅 22:55:42 版**) | **R**：14:55:42 的 146 行 infra 版（chart 单射、`lift` 分解）已独立复算；22:58:33 改写为 185 行后 14:59:22 / 15:01:14 均红：首错 **155:6**（`opensRange` 重写 motive；`chartInfScheme.Opens` vs `basicOpen Polynomial.X`—与 #262 同一类），162:48 `unknown constant IsOpenImmersion.preimage_opensRange`。**全文件仍无 `ValuativeCriterion.Uniqueness` 定理**（grep 0）。 |
| 266 | Mzk1G1OmegaInfinityActual（**新文件**） | G1-B Ω∞ 局部基 | **DONE（v3）** | **14:59:24** | fresh（src 22:58:15 / olean 22:59:24） | clean | 三公理（自身 #print；未入 probe） | **A-局部（真微分计算）**：`derivation_relation_inf : n s^{n-1} ds − n r^{n-1} dr = 0`（由 `1+s^n=r^n` 求导 + `nsmul_smul_eq`）、`n_s_pow_smul_omegaInf = −(n•dr)`、`n_r_pow_smul_omegaInf = −(n•ds)`，`omegaInfForm = s dr − r ds`。**仍是 infinity chart 局部**，未粘成 G-B 全局 Ω。v1/v2（14:55:44/14:57:34）无 log。 |
| 267 | Mzk1ULStepVIIIActual（**新文件**） | U-C Step VIII | **FAIL** | **15:01:44**（14:58:17 v1） | none（src 23:00:11） | clean（未编译） | — | **R**：v1 首错 **22:0 invalid import**（module docstring `/-! … -/` 写在 imports 之前）；v2 把 imports 提前后首错 **145:4 linarith**（`harch2 : P.arch ≤ κ·4` 太弱）、171:4 type mismatch。`PaperStepVIIIRetained` 的 hiii/hvi/hvii 三字段仍 **NO INHABITANT**。 |
| 268 | Mzk1URThetaTransportActual（**新文件**） | U-R C2 θ transport | **FAIL** | **15:01:42** | none（src 22:59:51） | clean（未编译） | — | **R**：首错 **109:23 `omega` counterexample**（`a := ↑l.value` 需要 `l.value ≥ 5`，未提供/未展开 `PrimeGeFive`），114:2 linarith。root-extension transport 仍红，与 §4.103 的 2l-root 缺口同源。 |
| 269 | Mzk1G1FermatChartSwapActual | G-A x↔y | **DONE** | 14:41:05 | fresh（src 22:40:22 / olean 22:41:04） | clean | 三公理（P13b + P14 复算） | 维持 #244：`ModelSwapEquiv`、`modelSwap_isStandardSmooth` 三公理；**14:37:24 的 `map_natCast` 缺省 / `of_algEquiv` 参数顺序首错已在 22:40:22 修复**（现 106/119 行 `map_natCast` 显式、156 行 `of_algEquiv (1)`），**不需重新诊断**。仍无 `(R n)[1/r] ≃ (R n)[1/r']`（现由 #263 接手，红）与 scheme 层 smooth。 |
| 270 | UCHpkt / URQNormalization / RadicalSupport / F7TameCountGlobal / URJ1 / P1Proper / URThetaMonotone / PiFiniteAssembly | 旧行 | 无新事件 | 14:11–14:36 | 各自 fresh | clean | 三公理 | 14:46Z 之后无新 attempt；引用边界同 §2l（#242 条件于 htheta/hstepVIII；#243 q 侧归一化；#246 无 `p1GluedToBase_isProper`；#250/#260 θ 均条件于 hperB；#255 F7 带 hzero/hdiv/hbad；#222 差两条 chart restriction）。 |
| 271 | Mzk1G1FermatRadicalSupportFinal3 / Mzk1G1FermatPiProper / Mzk1G1FermatChartFinite* 等 | G-A 旧件 | 无新事件 | ≤14:49 | fresh（各自） | clean | 三公理 | 未重审语义；不作为本批新证据。 |
| 272 | Mzk1F7SeparableResidueActual | F7(a) | **RETIRED** | 14:01:44 | none | — | — | 最后 FAIL 14:01:44，此后 0 attempt；#209 `residue_separable_global` 三公理替代。**不得再排队/引用**。 |

### 2m-1 缺口表（快照 15:02 UTC，逐项核对）

| 缺口 | 当前证据 | 状态 |
|---|---|---|
| P¹ 三模型 | `Proj` ×2（`Mzk1G1ProjectiveLineChartsActual:15` 等、`Mzk1G1FiniteDisjointBelyiActual:20`）+ `projectiveLineGlued`（`Mzk1G1ProjectiveLineGluedActual:136`）；grep `≅`/`projectiveLineIso` **0** | **无 iso，禁复合** |
| D3 no inhabitant | `Mzk1G1QHeightActual:40` 仍是唯一 `def HeightDictionaryInterface`（全 paper 1 命中） | **NO INHABITANT** |
| IsFinite π 条件式 | `isFinite_pi_of_chart_restrict`（h0/h1 = 两条 chart restriction）仍在（PiFiniteAssembly:40，14:11:01 fresh，P12 三公理） | 条件式，**差两条** |
| π⁻¹(D_+(X0))=D(x0^n) | `Mzk1G1FermatPiPreimageActual.pi_preimage_eq` 只给一般分解；`PiPreimageChart` 14:58:39 仍红（25:6），**无具体 chart 等式陈述** | **无陈述** |
| IsProper p1GluedToBase | existence ✓（14:49:52）+ UniversallyClosed ✓（14:51:44）+ QC/QS/LFT instances（14:28:59）；**uniqueness ✗**（Uniqueness 文件 155:6 红）⇒ IsSeparated ✗ ⇒ **IsProper ✗**；P1ProperAssembly 已删（无 producer） | **仍无 producer** |
| C2 θ H_pkt | 集合层 per-b 包含 ✓（#261，14:50:17）；条件式组装 ✓（#264，14:57:57）；**hperB / RootHullHalfScalingDataGap / hpacket 均未交付**；区域桥（actualLocalHullRegion vs possibleImages）与 log-volume 单调性仍缺；2l-root 在 completion 不存在（S342） | **无 θ producer** |
| F7SeparableResidue | 最后 FAIL 14:01:44，0 attempt | **RETIRED** |
| phantom P1ProperAssembly | 定理已删（446 B 注释文件，src 22:38:35，无 olean/事件） | **已清除；仍禁排队** |

### 2m-2 alan 的“删除动作”核对（本批）
- **确有删除**：`Mzk1P1ProperAssemblyActual` 从 858 B 缩为 **446 B**（mtime 22:38:35），内容只剩 7 行注释，**`p1GluedToBase_isProper` 定理体已删除**；§2l#247 的“幻影定理”不再存在于源码。全树 Lean 文件对 `p1GluedToBase_valuativeCriterion` 的引用 **0 命中**。
- 未观察到其它 paper 文件被删；本批新增 6 个文件（`Mzk1P1UniversallyClosedActual`、`Mzk1P1ValuativeUniquenessActual`、`Mzk1URThetaHthetaActual`、`Mzk1URThetaTransportActual`、`Mzk1ULStepVIIIActual`、`Mzk1G1OmegaInfinityActual`）与 1 个重写（`Mzk1G1FermatChartLocalizeSwapActual`）。

## 3l. Probe 14 / 14b / 14c（本批 batch 14）

- `_ProbeBatch14Actual.lean`：`wd_add` 14:54:02 → **DONE 14:54:57（55s）**；log 1117 B，**0 error / 0 sorryAx**。8 条全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | gate |
|---|---|---|
| `Mzk1P1ValuativeActual.valuativeCriterion_existence` | [propext, Classical.choice, Quot.sound] | #257 |
| `Mzk1P1ValuativeActual.chart_coord_compat` | [propext, Classical.choice, Quot.sound] | #257 |
| `Mzk1P1UniversallyClosedActual.p1GluedToBase_universallyClosed` | [propext, Classical.choice, Quot.sound] | #258 |
| `Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt` | [propext, Classical.choice, Quot.sound] | #260 |
| `Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ulHpkt` | [propext, Classical.choice, Quot.sound] | #260 |
| `Mzk1URThetaPacketCarrierActual.urThetaPossibleImages_subset_packetHull` | [propext, Classical.choice, Quot.sound] | #261 |
| `Mzk1G1FermatChartSwapActual.ModelSwapEquiv` | [propext, Classical.choice, Quot.sound] | #269 |
| `Mzk1G1FermatChartSwapActual.modelSwap_isStandardSmooth` | [propext, Classical.choice, Quot.sound] | #269 |

- `_ProbeBatch14bActual.lean`（Uniqueness infra 7 条）：START 14:58:11 → **DONE 14:58:40（28s）**；log 1051 B；**七条全部三公理**（`chartMorphism0_injective`、`chartMorphismInf_injective`、`chart_coord_compat_lift`、`eq_chartMorphism0_of_lift'`、`eq_chartMorphismInf_of_lift'`、`lift_eq_chartMorphism0_of_closedPoint_mem`、`lift_eq_chartMorphismInf_of_closedPoint_mem`）。**只对 22:55:42 的 146 行 olean 有效**；22:58:33 改写后该 olean 已 STALE（见 #265/#4.106）。
- `_ProbeBatch14cActual.lean`（Htheta 3 + LocalizeSwap 2）：START 14:59:39 → **DONE 15:00:31（53s）**；log 700 B；**五条全部三公理**（`ur_htheta_of_scaling`、`ur_htheta_of_halfScalingData`、`ur_thetaCoeff_eq_neg_localNormOrder`、`swapChart_chartR`、`swapChart_chartR2`）。**LocalizeSwap 两条只对 22:58:40 版有效**（v3 22:59:24 已红）；Htheta 版仍 fresh。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 14 续）

### 4.102 【高·G-A】P¹_glued：existence + UniversallyClosed 已交付，仍无 IsProper；幻影已清除
- 现有真件：existence（#257，14:49:52，三公理）、`UniversallyClosed`（#258，14:51:44，三公理，依赖 P1Proper 的 QC instance）、QC/QS/LFT instances 与两 chart 开集交（#246，14:28:59）。
- Mathlib 分解：`IsProper = ValuativeCriterion ⊓ QuasiCompact ⊓ QuasiSeparated ⊓ LocallyOfFiniteType`，`ValuativeCriterion = Existence ⊓ Uniqueness`。因此**所缺恰为 Uniqueness（⇒ `IsSeparated`）**。Uniqueness 文件已有 7 条 infra（chart 单射、lift 分解），但当前 185 行版红在 155:6（opensRange alias）与 162:48（`IsOpenImmersion.preimage_opensRange` 不存在），**全文件无 `ValuativeCriterion.Uniqueness` 定理**。
- `Mzk1P1ProperAssemblyActual` 的幻影定理**已被删除**（§2m-2），但文件仍是注释草稿 ⇒ (i) 仍禁排队，(ii) 不得引用 `p1GluedToBase_isProper`，(iii) 不得写“P¹ proper 已证”。`UniversallyClosed` 只是 IsProper 的一个真成分，**不是 properness**。

### 4.103 【高·U-R/C2】θ 侧：集合包含已绿、条件式组装已绿，但 hperB 仍无 producer
- #261 首次把 `urThetaPossibleImages ⊆ urThetaPacketHull` 在**实际 T-side 载体**上编译；#264 把 htheta 归约为 `hscale : RootHullScalingFormulaAt` + `hpacket : -thetaCoefficientContribution ≤ packetV`，二者均三公理。这是真实的中间进展（之前的 5 次红 / 心跳超时被绕过）。
- 但 **hperB（`actualLocalHullLog b ≤ packetV b`）依旧没有 producer**，原因有三：(a) #261 的区域是 `arithmeticTupleStepVPossibleImages`，而 `actualLocalHullLog` 的区域是 `actualLocalHullRegion = closure(⋃_j thetaTensorScaledRegion…)`，全树无二者桥接定理；(b) 即使有包含，还需要 `arithmeticTupleNormalizedLogVolume_mono`（#260 的 docstring 提到但文件里没有该引理）；(c) `hscale` 需要 `RootHullHalfScalingDataGap`（2l-root 半生成元 + hull 等式），而 `S342QVFamilyRootImpossibleActual` 说明 completion 中不存在该 2l-root ⇒ 必须走 root-extension → tensor transport，而这正是 #268 正在尝试且 15:01:42 仍红的文件；`hpacket` 需要 `localNormOrder ϖ = c_norm/(2l)` 的实际 Kummer 元素。
- **#260 的 docstring 与内容不符**（声称 `actualLocalHullLog_mono`/`Le_packetHullLog`，实际只有 2 条条件式）：引用时必须只按内容说“加权求和 wrapper”。**不得写“C2 已闭合”“htheta 已证”“θ ≤ H_pkt 已证”**。

### 4.104 【中·G-A/π】π⁻¹ chart 三次全红在同一处；仍无目标陈述
- #262 自 22:24:22 起 14:37:23 / 14:48:06 / 14:58:39 三次 attempt 同一组错：首错 **25:6**（`↥(Spec …)` 与 `PrimeSpectrum …` membership 不匹配），37:6 opensRange 重写 motive（`chartInfScheme.Opens` vs `basicOpen Polynomial.X`），43:6/51:6 重写失败。**没有任何 `(pi n)⁻¹ᵁ localChart0.opensRange = basicOpen (x0 n ^ n)` 陈述**；与 batch 12/13 的失败类型完全相同。修法仍是 `change`/`show` 到 `Spec (CommRingCat.of (Polynomial ℚ))` 的 Opens 或先 `rw [show chartInfScheme = Spec …]`，而不是继续 `rw [overlapToChartInf]`。

### 4.105 【中·G-A】x↔y 对换：chart 级已绿（后 STALE），局部化 iso 仍红
- #263 的 v2 在 14:58:40 绿了 `swapChart : Chart n ≃ₐ[ℚ] Chart n` 与 `swapChart_chartR/chartR2`（把 `Chart n = ⧸fermatCurveIdeal` 上的 x↔y 自同构做出来；v1 的 `Chart n` vs `R n` 混淆由此解决）。但 v3（22:59:24）追加局部化段后 15:00:09 红在 **115:30** `rewrite` pattern 不存在 ⇒ `Localization.Away chartR ≃ₐ Localization.Away chartR2` 仍无，`(R n)[1/r] ≃ (R n)[1/r']` 仍无。**14:58:40 的 olean 已 STALE，不得引**；P14c 的两条只证明当时版本。

### 4.106 【高·纪律】本批“DONE 后立即改写”达 3 例；日志 0 B 情况增多
- Uniqueness：14:55:42 DONE（146 行）→ src 22:58:33（185 行）→ 14:59:22 FAIL → src 23:00:32 → 15:01:14 FAIL。**只有 22:55:42 版可被 P14b 引用，且该版不含 Uniqueness 定理**；当前 src 无 olean。
- LocalizeSwap：14:58:40 DONE（5013 B）→ src 22:59:24（6817 B）→ 15:00:09 FAIL → 15:01:58 重试。**只有 22:58:40 版可被 P14c 引用**。
- Htheta：14:54:59 FAIL（log 0 B）→ 14:56:51 FAIL（log 0 B）→ 14:57:57 DONE（fresh）。**只有 14:57:57 版可引**。
- Omega：14:55:44/14:57:34 FAIL（均无 log）→ 14:59:24 DONE（fresh）。
- 日志纪律再确认：`PiPreimageChart` 45 KB 为跨 attempt 累积（末块起于第 582 行，首错 25:6；第 1–520 行的旧块含已删除的 `ChartInfRing`/`OverlapInf` 报错，**不得当当前首错**）；`Htheta`/`Omega`/`URThetaTransport` 的 FAIL 日志为 0 B 或无 log（首错未取）；**“START 清空”与“跨 attempt 累积”仍并存**。引用前必须同时 `Get-Item` src 与 olean；src > olean 或最后 attempt FAIL ⇒ 标 STALE/禁引。

### 4.107 【低·语义】已编译语句的“真值”抽查（本批）
- `valuativeCriterion_existence`：语句就是 Mathlib `ValuativeCriterion.Existence`（∀ `S : ValuativeCommSq`, `HasLift`），`ValuativeCommSq` 含 `[IsDomain R] [ValuationRing R] [IsFractionRing R K]`，非空类；证明构造 lift，未用 `sorry`/`axiom`。
- existence 中的 `Subsingleton.elim _ _` 不是作弊：P1Proper 的 `subsingleton_hom_spec_rat`（line 106）用 `ext_to_Spec` + `RingHom.ext_rat` 证明 `Subsingleton (X ⟶ Spec ℚ)`，合法 instance。
- `p1GluedToBase_universallyClosed` 依赖 P1Proper 的 `p1GluedToBase_quasiCompact` **instance**（line 183，affine 判据），不是额外假设。
- `thetaHullLog_le_ucHpkt`/`_ulHpkt` 只是 `Finset.sum_le_sum` + 权重非负，**数学内容 = 0**；`urThetaPossibleImages_subset_packetHull` 是 donor 的实际数据实例化（`p6_possibleImages_subset_packetHull`），内容真实但**不是 log-volume 不等式**。
- 三个 probe 的 20 条全部 `[propext, Classical.choice, Quot.sound]`、0 `sorryAx`；kernel 层无伪证。

## 5j. batch 14 立即动作（快照 15:02 UTC）

1. **P¹_glued proper（alan/david，最高优先）**：先修 `Mzk1P1ValuativeUniquenessActual` 的 **155:6**（用 `change`/`show` 把目标改到 `Spec (CommRingCat.of (Polynomial ℚ))` 的 Opens，或先 `rw [show chartInfScheme = Spec …]`；不要再 `rw [overlapToChartInf]`）与 **162:48**（`IsOpenImmersion.preimage_opensRange` 不存在，改用 `Scheme.Hom.opensRange_comp_of_isIso`/`opensRange_eq` 等现有引理）。Uniqueness 转绿后：`IsSeparated.of_valuativeCriterion`（需 `[QuasiSeparated]` instance，已有）→ 与 #258 `UniversallyClosed` + LFT instance 组装 `IsProper`（或先组 `ValuativeCriterion` 再用 `IsProper.of_valuativeCriterion`）。**在 `p1GluedToBase_valuativeCriterion`/`p1GluedToBase_isProper` 真实存在前，不排队 P1ProperAssembly、不引用其名。**
2. **C2 θ（kurt/sophie/sophie）**：两条并行：(a) 修 #268 的 109:23 `omega`（补 `l.value ≥ 5` 的实例/展开）与 114:2 `linarith`；(b) 在 `Mzk1URThetaPacketCarrierActual` 之后接区域桥：`actualLocalHullRegion ⊆ p6PacketHull`（先证 `actualRootThetaImageSet ⊆ ⋃ φ(ϖ·O_hol)` 或反向），再用 `arithmeticTupleNormalizedLogVolume_mono` 得 `actualLocalHullLog ≤ logVol(p6PacketHull)`，最后才用 #264。**#260 的 docstring 需修正**（删掉未实现的 `actualLocalHullLog_mono`/`Le_packetHullLog` 声称）。
3. **π⁻¹ chart（henry）**：#262 三次同一首错；先只做 `p1_overlapToChart0_opensRange`（改 carrier 层 `change`），再 `p1_overlapToChartInf_opensRange`，再 Y-side 两条；**最后才写 `π⁻¹(D_+(X0)) = D(x0^n)` 陈述**。不要同时改四个 def。
4. **局部化对换（grace）**：#263 v3 的 115:30 是 `Localization.Away` 侧的 rewrite pattern；先单独 `#check` 目标等式，再决定用 `IsLocalization.algEquiv`/局部化泛性质而不是 `rw`。转绿后才谈 `(R n)[1/r] ≃ (R n)[1/r']` 与 scheme 层 smooth。
5. **U-C Step VIII（kurt）**：#267 v1 的 import 顺序已修；当前首错 145:4 `linarith`（`harch2` 只给 `≤ 4κ`，目标需要 `(l+1)/4·log π ≤ …` 的常数匹配），先手工算系数再用 `nlinarith`/`positivity`；171:4 type mismatch 次之。三字段仍 NO INHABITANT。
6. **G1-B Ω∞（grace）**：#266 已 fresh DONE，可引三条局部基恒等式；下一步把 `omegaInfForm` 粘成全局 Ω 层（接 #251 overlap 过渡）。
7. **引用纪律（batch 14 版，强制）**：
   - #257 existence：**只是 Existence，不是 ValuativeCriterion/IsProper**；#258 UC：**只是 UniversallyClosed**；#259 P1ProperAssembly：**幻影已删，仍禁引/禁排队**。
   - #260 只按“hperB ⇒ 加权和”引用（无 `actualLocalHullLog_mono`）；#261 是“集合包含”，不是 log-volume 不等式；#264 条件于 hscale/hpacket。
   - #263 只引 22:58:40 版（且仅 chart 层）；#265 只引 22:55:42 版（仅 infra）；#266 引 14:59:24 版。
   - #262/#267/#268 红、无 olean，全部禁引；F7Sep RETIRED；D3 NO INHABITANT；π⁻¹ 无陈述；IsFinite π 差两条。

## 6k. batch 14 更新（快照 **15:02 UTC = 23:02 CST**；覆盖 §6–§6j 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_add.mjs`（Probe 14 / 14b / 14c，3 次）；`Get-Content watchdog.log -Tail` 多次（14:46–15:02 全量事件按 attempt 抽取）；`Get-Item` src/olean 对照（20+ 文件）；per-file log 逐个读取（P1Valuative、P6P5、Carrier、PiPreimageChart 45 KB 末块 582–697、ChartLocalizeSwap 2946 B、Uniqueness 6860/7147 B、Omega 925 B、Htheta、ULStepVIII、URThetaTransport）；源码阅读（P1Valuative 全文 290 行、P1UniversallyClosed 18 行、P1ProperAssembly 7 行、P6P5 80 行、Carrier 77 行、PiPreimageChart 67 行、ChartSwap 164 行、ChartLocalizeSwap 104 行、Uniqueness 146/185 行、Htheta 116 行、Omega 182 行、ULStepVIII 头部、URThetaTransport 头部、Mathlib `ValuativeCriterion.lean` 41–107 与 228–240）；grep（`p1GluedToBase_valuativeCriterion` 0、`ValuativeCriterion.Uniqueness` 0、`HeightDictionaryInterface` 1、模型 iso 0、`actualRootThetaImageSet`/`urThetaPossibleImages` 无桥接、`projectiveLine` 3 处）。
- **Probe 14**：8 条 DONE 14:54:57（55 s），**全部三公理**；**Probe 14b**：7 条 DONE 14:58:40，**全部三公理**；**Probe 14c**：5 条 DONE 15:00:31，**全部三公理**。三次日志合计 0 error / 0 sorryAx。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未运行 / 未覆盖（如实标注）**：Uniqueness 当前 185 行版（红，只到 P14b 的旧 olean）；LocalizeSwap v3（红）；PiPreimageChart（红）；ULStepVIII / URThetaTransport / Htheta 首错之外的后续错误未逐条展开；Omega 三条未入 probe（自身 #print 三公理）；U-R 其余 θ 侧、G-K、H-T 的 F1–F4/F8、P8-P 端到端仍未做语义审计。
- **15:02 UTC 之后**：watchdog 仍有活动（ChartLocalizeSwap 15:01:58 重试；Uniqueness/ULStepVIII/URThetaTransport 刚红）。**之后的任何 DONE/FAIL 本表未审计**。
- 本批写入范围：本表 + **新建** `_ProbeBatch14Actual.lean`、`_ProbeBatch14bActual.lean`、`_ProbeBatch14cActual.lean`；未改其它 Lean 文件；未 spawn_teammate、未 `lake env lean`、未自起 watchdog、未写 sorry/axiom。

## 2n. 本批 batch 15 gate 表（快照 **15:29 UTC = 23:29 CST**；**#273–285**，覆盖 15:02–15:29 全部 DONE/FAIL + Lead 指定 8 项复核）

- 证据版本：src / olean 均按 `Get-Item` 实测；`(P15)` = 本批独立 probe 复算（§3m）。**15:29:22 之后由 §2n-3 补记至 15:31:30；15:31:30 之后未审计**：15:29:36 起三文件重试，其中 Uniqueness 15:30:04 DONE（7 helper）、CurveSmooth 15:30:05 FAIL、URThetaHullUpper 15:30:06 FAIL、Bridge 15:31:04 FAIL、ULStepVIII 15:31:30 DONE。
- **14:48–15:02 的 DONE/FAIL 已由 §2m #257–272 覆盖**（P1Valuative 14:49:52、P6P5 14:49:12、Carrier 14:50:17、UniversallyClosed 14:51:44、Uniqueness 14:55:42、Htheta 14:57:57、LocalizeSwap 14:58:40、Omega 14:59:24、ULStepVIII v1/v2 14:58:17/15:01:44、URThetaTransport v1 15:01:42、PiPreimage 14:58:39）；本批从 **15:02:27** 起。
- **15:02–15:29 事件全量（按 attempt 计）**：15:02:27 LocalizeSwap FAIL → 15:03:08 Uniq FAIL → 15:03:37 ULStepVIII FAIL → 15:04:18 LocalizeSwap FAIL → 15:04:43 URThetaTransport FAIL → 15:05:25 Uniq FAIL → **15:05:51 P6P5 DONE** → 15:05:54 ULStepVIII FAIL → 15:06:35 LocalizeSwap FAIL → 15:07:00 URThetaTransport FAIL → **15:07:43 LocalizeSwap DONE（后 STALE）** → 15:07:55 Uniq FAIL → 15:08:11 ULStepVIII FAIL → 15:09:16 URThetaTransport FAIL → 15:09:58 PiPreimage FAIL → 15:10:02 LocalizeSwap FAIL → 15:10:12 Uniq FAIL → 15:10:26 ULStepVIII FAIL → 15:11:31 URThetaTransport FAIL → **15:12:13 Uniq DONE** → **15:12:16 LocalizeSwap DONE** → 15:12:40 ULStepVIII DONE（后改） → 15:13:48 URThetaTransport FAIL → 15:14:30 P1Separated FAIL（后删源） → 15:14:31 Uniq FAIL → 15:14:58 ULStepVIII FAIL → 15:15:38 CurveSmooth FAIL → 15:16:46 URThetaTransport FAIL → 15:16:48 ULStepVIII FAIL → 15:17:30 CurveSmooth FAIL → 15:17:30 Uniq FAIL → 15:17:33 Omega FAIL → **15:18:55 ULStepVIII DONE** → **15:19:37 CurveSmooth DONE（仅 span）** → 15:19:38 Uniq FAIL → 15:19:41 Omega FAIL → **15:20:04 URThetaTransport DONE** → 15:20:46 PiPreimage FAIL → 15:20:47 Uniq FAIL → 15:21:30 CurveSmooth FAIL → 15:21:33 Omega FAIL → 15:22:31 Uniq FAIL → 15:23:15 CurveSmooth FAIL → **15:23:17 Omega DONE** → 15:24:13 Uniq FAIL → 15:24:56 URThetaHullUpper FAIL → **15:25:39 CurveSmooth DONE（chartRing_smooth 版）** → **15:26:06 ULStepVIII DONE（当前）** → 15:26:50 URThetaHullUpper FAIL → 15:27:36 CurveSmooth FAIL（新源） → 15:28:16 Uniq FAIL → 15:28:36 ULPacketBPerLabelBridge FAIL（新文件） → **15:29:22 Probe15 DONE**。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 273 | Mzk1P6P5ThetaHullControl2 | U-R C2 θ (A) | **DONE** | **15:05:51** | fresh（src 23:04:38 / olean 23:05:50） | clean | 三公理（log 272 B） | **B−：docstring 已按 #260 修正且与内容一致**。全文 78 行仍只有 `thetaHullLog_le_ucHpkt` / `thetaHullLog_le_ulHpkt` 两条，均假设 `hperB : ∀ b, actualLocalHullLog b ≤ packetV b`；docstring 现在明确写“exactly two theorems”、`hperB` 未证、2l-root 在 completion 不存在（S342）、无 `actualLocalHullLog_mono`/`Le_packetHullLog` 声称。**仍是条件加权和 wrapper，不是 θ producer**；不得写“C2 已闭合”。 |
| 274 | Mzk1ULStepVIIIActual | U-C Step VIII | **DONE（15:18:55 后改，15:26:06 再 DONE）** | **15:26:06** | fresh（src 23:24:35 / olean 23:26:06） | clean（注释含“not axioms, not sorry”字样，非 gate token） | 五条三公理（log 622 B + P15 两条） | **B：retained 口径**。286 行；`PaperStepVIIIRetained` 三字段 **hiii / hviPacket / hvii**（IUT IV L1553–1582 / L1701–1783 / L1819–1859）+ `hl`/`hQ`: 0≤Q / `hM`: M=Q/(2l)（另有 hlog*/hlstar/hn 参数约束）；`hviProcession` 由 DONE StepV 链**已证**；`hstepVIII_of_retained` 是纯代数收尾（arch_container_le + hviProcession + hiii + hgap）；`uc_c4_of_retained` 把 htheta（经 hscale/hpacket）与 hstepVIII 作为显式假设交给 `uc_c4_paperConstants_of_p6`。**三字段仍 NO INHABITANT（retained ≠ 已证）**；不是无条件 hstepVIII/htheta producer。 |
| 275 | Mzk1G1OmegaInfFreeActual（**新文件**） | G1-B Ω∞ 自由性 | **DONE** | **15:23:17** | fresh（src 23:22:38 / olean 23:23:17） | clean | 九条三公理（log 1332 B + P15） | **A-局部（真实、非草稿）**。276 行：`dPolyInf`（D(X0)=−nX1^{n−1}, D(X1)=−nX0^{n−1}）kill `secondEquation = 1+X0^n−X1^n`；`DInf` 由 `Derivation.liftOfSurjective` 下降到 `R2 n`；`PsiInf` 对偶；`span_dS_dR`、`PhiInf_injective`、`PhiInf_surjective`、`phiInfEquiv : R2 n ≃ₗ ΩInf`、`omegaInfForm_is_basis`。**这是 ∞ 图 Ω 的自由性/基，不是全局 Ω 线丛**；全局仍需两 chart 过渡/Ω≅O(n−3)。 |
| 276 | Mzk1G1FermatChartLocalizeSwapActual | G-A 局部化对换 | **DONE** | **15:12:16** | fresh（src 23:11:07 / olean 23:12:16） | clean | 十一条三公理（log 2238 B + P15 两条） | **A-局部（真实）**。219 行：`swapChart : Chart n ≃ₐ[ℚ] Chart n`（x↔y）、`swapChart_chartR/chartR2`、`localizeSwapHom`/`localizeSwapHom2`（`IsLocalization.Away.lift`）、两条复合恒等、**`localizeSwapEquiv : (R n)[1/r] ≃ₐ[ℚ] (R n)[1/r2]` 完整 AlgEquiv**、`loc_chartR_isStandardSmooth` / `loc_chartR2_isStandardSmooth`。三声明均三公理；**不是 scheme 层 smooth**，但为 `chartRing_smooth` 提供两块局部输入。 |
| 277 | Mzk1URThetaTransportActual | U-R C2 θ transport | **DONE** | **15:20:04** | fresh（src 23:18:05 / olean 23:20:04） | clean | 四条三公理（log 566 B + P15） | **B：task-13 接口，不是 producer**。`RootTensorVolumeAlignmentAt b := actualLocalHullLog b = log‖urRootAlpha b‖`；`WithCorrection`；`ur_alpha_log_norm_eq`（由 `urRootAlpha_pow` 取 log）、`thetaCoeff_eq_neg_alpha_log`（−thetaCoeff = log‖r_b‖）、`rootHullScalingFormulaAt_of_alignment`、`ur_htheta_of_alignment`。**alignment 无 inhabitant**；且按 Lead §35，精确等式 `actualLocalHullLog b = log‖r_b‖` 与值群离散（`padicFractionalLattice` 的 ceil）**一般不等**，所以这不是“待证事实”，而是不能作为最终 datum 的等式（见 §4.109）。 |
| 278 | Mzk1P1ValuativeUniquenessActual | G-A uniqueness | **DONE（15:12:13，7 helper）→ STALE → FAIL** | 15:12:13 / **15:28:16** | **STALE**（src 23:27:27 / olean 23:12:13） | clean | 七条三公理（P15 一条代表；15:12:13 版） | **R（无最终定理）**。15:12:13 DONE 只含 7 条 helper（chart 单射、lift 分解、closed-point chart 化），**全文件无 `ValuativeCriterion.Uniqueness`**（grep 0）。23:27:27 改写加入 `chartMorphismInf_zero_ne_chartMorphism0_zero` 后连续红：15:28:16 首错 **156:26**（`rw [hx0]` pattern `x0p` 不在目标；`↥(Spec …)` vs `PrimeSpectrum` carrier 混用），159:24、171:4、175:4、179:10 同源。**不能引当前源；P15 只证明 23:12:13 版 helper。** |
| 279 | Mzk1G1FermatCurveSmoothActual | G-A R n smooth | **DONE（15:19:37 仅 span）→ DONE（15:25:39 chartRing_smooth）→ 新源 FAIL** | 15:25:39 / **15:27:36** | **STALE**（src 23:26:57 / olean 23:25:39） | clean（无 literal token） | 五条（15:19:37 span 部分）+ P15 `chartRing_smooth`（**只对 23:25:39 olean**） | **A-局部 span + STALE 的 chartRing_smooth + R 的新声明**。15:19:37 版仅 span 覆盖（natCast_isUnit/chartX_mul_chartR/chartY_mul_chartR2/chartX_chartR_add/chartR_span_eq_top）；23:25:39 版把 `loc_isSmooth` + `chartRing_smooth : Algebra.Smooth ℚ (Chart n)` 编绿（P15 三公理）；随后 23:26:57 新源追加 `chartRing_exists_standardSmooth_localized`，15:27:36 首错 **108:12** `p.ne_top` invalid field（`p : Submodule`），log 1383 B 对失败声明给出 **sorryAx**（错误恢复，不是 literal sorry）。**当前源红、olean STALE；chartRing_smooth 只能引 23:25:39 版。** |
| 280 | Mzk1G1FermatPiPreimageChartActual | G-A π⁻¹ chart | **FAIL** | **15:20:46** | none（src 22:24:22） | clean（未编译） | — | **R**。55.7 KB 跨 attempt 累积；最后块首错 **37:6**（`rw` motive：`Scheme.Hom.opensRange _a = PrimeSpectrum.basicOpen X`），43:6、51:6 同因；核心仍是 `PrimeSpectrum.basicOpen X`（`PrimeSpectrum (Polynomial ℚ)` 的 Opens）与 `chartInfScheme.Opens` 类型不匹配。**π⁻¹ 目标仍无陈述**；src 自 22:24:22 未改，无 olean。 |
| 281 | Mzk1P1SeparatedActual | G-A IsSeparated/IsProper | **FAIL 后源文件已删除（retracted）** | 15:14:30 | none | —（文件 MISSING） | log 含 **sorryAx** | **R / RETRACTED，禁止引用**。15:14 的 log（788 B）显示 `terminal.from` unknown、`IsProper.mk` 字段不足，且 `projectiveLineGlued_isSeparated` / `p1GluedToBase_isSeparated` / **`p1GluedToBase_isProper`** 三条均 `[propext, sorryAx, …]`（失败证明的错误恢复）。源文件已从磁盘删除、已不在 extra-targets；**无 olean、绝不能引 `p1GluedToBase_isProper`**。 |
| 282 | Mzk1URThetaHullUpperActual（**新文件**） | U-R C2 θ (≤ 路线) | **FAIL** | **15:26:50**（15:24:56 同） | none（src 23:25:38 / 3753 B） | clean | — | **R / WIP，no producer**。当前 81 行只证 `le_ceilExp`、`norm_prime_eq_inv`、`exists_norm_pow_eq_prime_zpow`，并把 **`BallCeilEqualityAt` 记为 retained Prop（不假设）**；主目标 `actualLocalHullLog ≤ -thetaCoefficientContribution`/最终 htheta **尚未交付**。15:24:56 的 log（1157 B）首错 `Nat.cast_eq_algebraMap` unknown、norm 类型不匹配、`unfold ceilExp` 失败、无 ext 定理；15:26:50 仍 FAIL（log 0 B）。15:29:36 重试中。**这是 §35 批准的新 ≤ 路线，不是已闭；不得写“θ 侧无 producer”为最终结论，也不得引本文件。** |
| 283 | Mzk1ULPacketBPerLabelBridgeActual（**新文件**） | U-L C1 bridge | **FAIL** | **15:28:36** | none（src 23:28:08 / 3501 B） | clean | — | **R（import 顺序）**。log 151 B 首错 **16:0 invalid import**：模块 docstring `/-! … -/` 写在 imports 前。内容本身是条件 bridge：`packetB_eq_perLabelBound`（`localNormOrder varpi = stepVLambda …` 下 packetB = S3014PerLabelBound）与 procession 平均；`hλ` 是真实输入（2l-root 不存在，S342），**无 inhabitant**。修 import 顺序后可重编。 |
| 284 | UCHpkt / URQNormalization / RadicalSupport / F7TameCountGlobal / URJ1 / P1Proper / PiFiniteAssembly / P1Valuative / P1UniversallyClosed / OmegaInfinity / Htheta | 旧行 | 无新 attempt | 14:07–15:00 | 各自 fresh | clean | 三公理 | 15:02 之后无新事件；引用边界同 §2m/§2l：C4 条件于 htheta/hstepVIII；q 侧归一化；F7 条件于 hdiv/hpn；P1Valuative 只是 Existence；UniversallyClosed 只是 IsProper 的一个成分；Htheta 条件于 hscale/hpacket。 |
| 285 | Mzk1P1ProperAssemblyActual / Mzk1F7SeparableResidueActual / D3 / P¹ 模型 | 旧缺口 | 无新事件 | — | P1ProperAssembly 无 olean；F7Sep 无 olean | clean（P1ProperAssembly 仅注释） | — | P1ProperAssembly 仍 446 B 注释、**phantom/禁排队/禁引**；F7Sep RETIRED；D3 仍 NO INHABITANT；P¹ 仍三模型无 iso。 |

### 2n-1 缺口表（快照 15:29 UTC，逐项核对）

| 缺口 | 当前证据 | 状态 |
|---|---|---|
| P¹ 三模型 | `Mzk1G1FiniteDisjointBelyiActual:20` + `Mzk1G1ProjectiveLineChartsActual:15`（两份 `projectiveLine`）+ `Mzk1G1ProjectiveLineGluedActual:136` `projectiveLineGlued`；`≅`/iso 仍 0 | **无 iso，禁复合** |
| D3 no inhabitant | `Mzk1G1QHeightActual:40` 仍是唯一 `HeightDictionaryInterface`（全 paper 1 命中） | **NO INHABITANT** |
| IsFinite π 条件式 | `isFinite_pi_of_chart_restrict (h0) (h1)`（PiFiniteAssembly:40，14:11:01 fresh） | 条件式，**差 h0/h1 两条 chart restriction** |
| π⁻¹(D_+(X0)) 具体等式 | `PiPreimageChart` 15:20:46 仍红（37/43/51 同一类型错），无任何具体 chart 等式陈述 | **无陈述** |
| IsProper p1GluedToBase | existence ✓（#257）+ UniversallyClosed ✓（#258）+ QC/QS/LFT instances；**Uniqueness ✗**（#278 只有 7 helper，当前源红）；P1Separated 已删（log 有 sorryAx 的 `p1GluedToBase_isProper`）；P1ProperAssembly phantom | **仍无 producer** |
| C2 θ / task-13 | **BLOCKED(named)**：唯一 datum `htheta`（等价 `∀ b, RootTensorVolumeAlignmentAt`）；不可得性：`RootHullHalfScalingDataGap` 需 q 的 (2l) 次根 generator（S342 证不存在）、`DistinguishedScalarData` 无实例、精确等式与值群离散不符（§35）。C3/P5 侧不受影响：`thetaHullLog_le_ucHpkt` 保留；`uc_c4_paperConstants_of_p6` 把 htheta 作显式假设（UCHpkt:293）。**≤ 路线**（URThetaHullUpper）WIP、无 olean/FAIL | **named BLOCKED（精确 transport）；≤ 路线未交付** |
| J3 | 只在 `DistinguishedScalarData.j ≠ 1` 时需要；若 j=1 则 per-b 退化为体积等式（θ 侧 `actualLocalHullLog_b = −(c_norm/2l)log p`；packet 侧 `ϖ·O_hol ⊆ packetHull` + 单调性），不需要 J3。**`DistinguishedScalarData` 全树无实际实例**（结构在 `Mzk1BoxDistinguishedScalarActual:43`，j 是字段；16 处出现全是 binder）；`Mzk1ULPacketVActual` 文件头明确“no completion instance” | **条件性备选（仅 j≠1）；j=1 分支不可实例化** |
| F7 htame | `Mzk1F7TameCountGlobalActual.tameCount_of_div_ramification` 仍假设 `hdiv`（e_P∣n）+ `hpn`（p∤n）；`RadicalSupport` 仍假设 `htame`/`hbad`；F7Sep RETIRED | **条件式；不等同无条件** |

### 2n-2 删除 / 撤回核对（本批）
- **`Mzk1P1SeparatedActual` 源文件已删除**（glob 0），且已不在 `extra-targets.txt`；只剩 `dag/watchdog/logs/...P1SeparatedActual.lean.log`（788 B）。该 log 明确显示三条 `[propext, sorryAx, …]`，其中包含 `p1GluedToBase_isProper`：**这是失败证明的错误恢复，不是已证；绝不能引，也不能据此写“P¹ proper 已证”。**
- `Mzk1P1ProperAssemblyActual` 仍为 446 B 注释草稿、无 olean、无事件；**仍禁排队/禁引**。本批未观察到其它源文件被删除；新增 `Mzk1URThetaHullUpperActual`、`Mzk1ULPacketBPerLabelBridgeActual`、`Mzk1G1OmegaInfFreeActual`。

### 2n-3 快照后补记（15:29:22–15:31:30；覆盖 #278 的状态列，不改 #273–285 其它已记录判定）

- **#278 状态更新（重要）**：`Mzk1P1ValuativeUniquenessActual` 在 15:30:04 **再次 DONE**：src 23:29:23 / 7724 B，olean 23:30:04，fresh；源已回退到 **7 条 helper**（删除失败的 `chartMorphismInf_zero_ne_chartMorphism0_zero`），log 547 B 只有两条 linter warning，**无 #print axioms 输出**（源内已删 #print）。全文件仍只有 7 条 theorem（chartMorphism*_injective、chart_coord_compat_lift、eq_chartMorphism*_of_lift'、lift_eq_chartMorphism*_of_closedPoint_mem），**仍无 `ValuativeCriterion.Uniqueness` 最终定理**。P15 的 `lift_eq_chartMorphism0_of_closedPoint_mem` 三公理结果仍成立（同一 helper 现在也在 23:30:04 olean 中，未重跑 probe）。**引用纪律：#278 现在可引 23:30:04 版 7 helper，但仍不得写“uniqueness 已证”。**
- **CurveSmooth**：15:30:05 仍 FAIL（src 23:26:57，108:12 `p.ne_top`；log 已清 0 B）；**chartRing_smooth 仍只对 23:25:39 olean 有效**，当前 STALE。
- **URThetaHullUpper**：15:30:06 仍 FAIL（src 23:25:38 / 3753 B，无 olean）；≤ 路线主定理未交。
- **ULPacketBPerLabelBridge**：15:30:21 又改源（3499 B）后 15:31:04 FAIL；首错变为 **41:6 / 54:6 `unexpected token 'λ'`**（binder `hλ` 用了 Lean 不接受的 λ 字符），67:14/68:14 因之 unknown constant。仍是 R/无 olean；修法：把 `hλ` 改名为 `hlam`（或 `hLam`）。
- **ULStepVIII**：15:31:30 对同一源再 DONE（src 23:24:35 / olean 23:31:30），确认 15:26:06 版内容；五条三公理不变。


## 3m. Probe 15（本批 batch 15）：`tmp/sheaf/xif/paper/_ProbeBatch15Actual.lean`

- `node tools/wd_add.mjs` 排队 → START 15:28:31 → **DONE 15:29:22（50s）**；log 1115 B，**0 error / 0 sorryAx**；8 条全部 `[propext, Classical.choice, Quot.sound]`：

| 定理 | axioms | 证据版本 / gate |
|---|---|---|
| `Mzk1ULStepVIIIActual.hstepVIII_of_retained` | [propext, Classical.choice, Quot.sound] | 23:26:06 olean（#274） |
| `Mzk1ULStepVIIIActual.uc_c4_of_retained` | [propext, Classical.choice, Quot.sound] | 23:26:06 olean（#274） |
| `Mzk1G1OmegaInfFreeActual.omegaInfForm_is_basis` | [propext, Classical.choice, Quot.sound] | 23:23:17 olean（#275） |
| `Mzk1G1FermatChartLocalizeSwapActual.localizeSwapEquiv` | [propext, Classical.choice, Quot.sound] | 23:12:16 olean（#276） |
| `Mzk1G1FermatChartLocalizeSwapActual.loc_chartR2_isStandardSmooth` | [propext, Classical.choice, Quot.sound] | 23:12:16 olean（#276） |
| `Mzk1URThetaTransportActual.ur_htheta_of_alignment` | [propext, Classical.choice, Quot.sound] | 23:20:04 olean（#277） |
| `Mzk1G1FermatCurveSmoothActual.chartRing_smooth` | [propext, Classical.choice, Quot.sound] | **只对 23:25:39 olean**；当前源 23:26:57 已红（#279） |
| `Mzk1P1ValuativeUniquenessActual.lift_eq_chartMorphism0_of_closedPoint_mem` | [propext, Classical.choice, Quot.sound] | **只对 23:12:13 olean**（同一 helper 在 23:30:04 DONE 版中也在；未重跑）；23:30:04 版见 §2n-3 |

- **版本纪律**：probe 的 import 使用磁盘上的 olean；`chartRing_smooth` 与 `lift_eq_chartMorphism0_of_closedPoint_mem` 在**当前源已红/STALE**时仍能被 #print 出来，是因为对应 olean 仍在。**这正说明“P15 三公理”不等于“当前源 DONE”**；引用时必须同时写 olean 时间。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 15 续）

### 4.108 【高·纪律】CurveSmooth 是本批最强“源码 grep ≠ DONE 版本内容”实例
- 15:19:37 DONE（仅 span 覆盖）→ 23:24:42 版加 `loc_isSmooth` + `chartRing_smooth` → **15:25:39 DONE**（P15 只对这个 olean 有效）→ 23:26:57 再加 `chartRing_exists_standardSmooth_localized` → **15:27:36 FAIL**（108:12 `p.ne_top` on `Submodule`）；olean 仍是 23:25:39，**STALE**。
- 当前源 117 行，无 literal `sorry`/`axiom`，但失败声明在 log 中显示 **sorryAx**（Lean 对失败证明的错误恢复）。**不得把 `chartRing_exists_standardSmooth_localized` 或当前文件当绿；也不得据 grep 说 `chartRing_smooth` 现在 DONE**——只有 23:25:39 的 olean 可引。

### 4.109 【高·U-R/C2】task-13 精确 transport = BLOCKED(named)；≤ 路线 WIP
- `Mzk1URThetaTransportActual` 把 htheta 归约为 `hscale`（`RootHullScalingFormulaAt`）+ `hpacket`，再把 hscale 归约为 `∀ b, RootTensorVolumeAlignmentAt`；`thetaCoeff_eq_neg_alpha_log` 证明后者与 hscale 等价。四条三公理，但 **alignment 无 inhabitant**。
- 不可得性证据（Lead §33/§35）：`RootHullHalfScalingDataGap`（BadPlaceRootHullScalingFormulaActual:87）要求 q 的 2l 次根 generator + hull_eq；`S342QVFamilyRootImpossibleActual` 证 completion 中不存在该 2l-root；`DistinguishedScalarData` 全树无实际实例。并且 §35 指出**精确等式本身不是值群正确的陈述**：`actualLocalHullLog` 是 ceil 后的 step function，`log‖r_b‖` 是连续值，一般不等。故 alignment 不能作为最终 datum；它是“条件式接口”，不是“待证事实”。
- **C3/P5 不受影响**：`Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt` 仍是合法条件式；`Mzk1UCHpktActual.uc_c4_paperConstants_of_p6` 把 `htheta` 作为显式假设（UCHpkt:293）。**口径**：C2 θ 的精确 transport = **BLOCKED(named)**；但 §35 已把“θ 侧无 producer”修正为“≤ 方向可证、待实现”，所以不得把 BLOCKED 写成最终数学不可能。当前 ≤ 路线 `Mzk1URThetaHullUpperActual` 仍 FAIL/无 olean。

### 4.110 【高·U-R/J3】J3 只是条件性备选；`DistinguishedScalarData.j` 无实际实例
- `Mzk1BoxDistinguishedScalarActual:43` 的结构有字段 `j : Nat`，`distinguished_theta_order` 给出 `ord(θ_j) = (j²/(2l)) ord(q)`；但**全树 16 处 `DistinguishedScalarData` 出现全部是 `(X : DistinguishedScalarData p K)` binder**，没有任何 `instance`/具体 inhabitant；`Mzk1ULPacketVActual` 文件头明确写“no completion `DistinguishedScalarData` is asserted”。
- 因此“j=1 ⇒ 体积等式 ⇒ 不需要 J3”这一支**目前不可实例化**；J3 仍是“仅 j≠1 时”的条件性备选，不是已决定必须。kurt 的“确认 j 实际实例化”尚无可引结果；J3 新文件（`Mzk1URThetaHullJ3Actual`）在本快照不存在/无事件。

### 4.111 【高·G-A】P¹ proper：uniqueness 仍无最终定理；retracted 文件带 sorryAx
- #278：15:12:13 DONE 只有 7 helper；15:30:04 回退到 7-helper 绿版（见 §2n-3）；中间 191 行源新增 `chartMorphismInf_zero_ne_chartMorphism0_zero` 后 15:28:16 首错 156:26（`↥(Spec …)` 与 `PrimeSpectrum` carrier 混用；同类 159/171/175/179），**全文件仍无 `ValuativeCriterion.Uniqueness (p1GluedToBase)`**。P15 只证明 23:12:13 版 helper。
- `Mzk1P1SeparatedActual` 15:14:30 FAIL 后**源被删除**；其 log 的 `p1GluedToBase_isProper` 带 sorryAx。这是一次“写过又撤回”的伪 producer：**当前无源/无 olean，永不可引**。`P1ProperAssembly` 仍 phantom。P¹ proper 仍缺 IsSeparated/Uniqueness，**无 `p1GluedToBase_isProper`/`p1GluedToBase_valuativeCriterion`**（grep Lean 0）。

### 4.112 【中·G-A/π】π⁻¹ 无陈述、IsFinite π 条件式、P¹ 三模型
- `PiPreimageChart` 15:20:46 最后块首错 37:6，43:6/51:6 同因，仍是 `PrimeSpectrum.basicOpen X` 与 `chartInfScheme.Opens` 类型不匹配；**没有任何 `π⁻¹(D_+(X0)) = D(x0^n)` 陈述**。
- `isFinite_pi_of_chart_restrict` 仍要 h0/h1 两条 chart restriction；本批无新 producer。P¹ 仍两份 `projectiveLine` + 一份 `projectiveLineGlued`，iso 0；**禁复合**。

### 4.113 【中·F7】F7 仍条件式，无新 producer
- `tameCount_of_div_ramification` 仍假设 `hdiv`（e_P∣n）+ `hpn`（p∤n）；`RadicalSupport` 的 `f7_*` 仍假设 `htame`/`hbad`；`Mzk1F7SeparableResidueActual` RETIRED。**不得写“F7 已无条件闭合”**；本批无新 F7 DONE/FAIL。

### 4.114 【中·新文件】ULPacketBPerLabelBridge import 顺序红；URThetaHullUpper 无 producer
- #283：模块 docstring 在 imports 前 ⇒ 16:0 invalid import；内容为 `packetB = S3014PerLabelBound` 的条件 bridge（hλ = localNormOrder 匹配，2l-root 不存在，故 hλ 是真输入）。修 import 顺序后可重编，**当前 R/无 olean**。
- #282：`URThetaHullUpper` 只有 ceil 不等式/‖p‖/值群幂三条 + retained `BallCeilEqualityAt`；主定理未交，15:24:56/15:26:50 均红，15:29:36 重试。

### 4.115 【低·语义】本批已编译语句真值抽查
- `hstepVIII_of_retained`：纯代数，输入是结构字段（非 axiom/sorry）；`hviProcession` 由 `p6_stepVAverages_ivInequality` 真证；`uc_c4_of_retained` 真是 `uc_c4_paperConstants_of_p6` 的实例化，htheta/hstepVIII 显式。retained 三字段仍无 inhabitant。
- `OmegaInfFree`：`DInf` 的符号与 `secondEquation = 1+X0^n−X1^n` 相符（D(X0)=−nX1^{n−1}, D(X1)=−nX0^{n−1} 使方程导数为 0）；`PsiInf_omegaInfForm` 用 `sum_eq_one_inf` 得 n；`phiInfEquiv` 由 injective+surjective 构造，非定义自反。
- `localizeSwapEquiv`：`left_inv`/`right_inv` 由两条 `IsLocalization.ringHom_ext` 复合恒等给出，非 `rfl`；`loc_chartR*_isStandardSmooth` 经 `of_algEquiv` 运输已有 standard smooth 实例。
- `ur_alpha_log_norm_eq`/`thetaCoeff_eq_neg_alpha_log` 是真 log 恒等式（`urRootAlpha_pow` + `urRootQ_log_norm_order`）；但 `ur_htheta_of_alignment` 的条件 `halign` 无 inhabitant，整体是条件式。

## 5k. batch 15 立即动作（快照 15:29 UTC）

1. **CurveSmooth（grace/alan，最高优先）**：先把当前 117 行源的 **108:12** 修掉（`p.ne_top` 在 `Submodule` 上不存在；改用 `p.IsPrime.ne_top` 或 `(Ideal.eq_top_iff_one).mp` 的否定形式），再重编；**在 15:27:36 之后没有新 DONE 前，`chartRing_exists_standardSmooth_localized` 禁引**。`chartRing_smooth` 只能引 23:25:39 olean（P15）。修好后重新交 `chartRing_exists...` + scheme 层 smooth。
2. **P¹ proper（david/alan）**：#278 已于 **15:30:04** 回退到 7-helper 绿版（fresh，仍无最终定理）。下一步直接在绿版上加具名 `valuativeCriterion_uniqueness : ValuativeCriterion.Uniqueness (p1GluedToBase)`；若继续做 zero_ne，先把 `x0` 统一成 `PrimeSpectrum` 类型（避免 156:26 的 `↥(Spec …)` 混用）。**uniqueness 真绿前不排队 P1ProperAssembly、不引 `p1GluedToBase_isProper`；P1Separated 已撤回，禁引。**
3. **C2 θ（kurt）**：精确 transport 按 **BLOCKED(named)** 记录（htheta / RootTensorVolumeAlignmentAt / RootHullHalfScalingDataGap；S342 + 无 DistinguishedScalarData + §35 值群问题）；同时推进 §35 的 ≤ 路线：修 `URThetaHullUpper` 的 `Nat.cast_eq_algebraMap`/norm/unfold 错误，主定理 `ur_localHullLog_le_neg_thetaCoeff` 出来前**不写 htheta 已证**。**J3 只在 j≠1 时；先确认 `DistinguishedScalarData.j` 实际实例化（当前无实例）。**
4. **π⁻¹（henry）**：#280 仍是 37/43/51 类型错；先只做 `overlapToChart0_opensRange`（`change` 到 `Spec (CommRingCat.of (Polynomial ℚ))` 的 Opens），再 Inf/Y-side，最后才写 π⁻¹ 陈述。
5. **新文件 import 纪律（全员）**：#283 与 §2l 的 ULStepVIII v1 同为“docstring 在 imports 前”；新 Lean 文件一律 imports 第一行，再写 `/-! … -/`。
6. **G-B（alan）**：#275 已给 ∞ 图 Ω 自由性；下一步两 chart 过渡/Ω≅O(n−3)/ramification，不要把它写成全局 Ω 已闭。
7. **引用纪律（batch 15 版，强制）**：
   - #273 只按“hperB ⇒ 加权和”引，无 mono；#274 三字段 retained，≠ 已证；#275/#276 是局部真件；#277 alignment 无 inhabitant；#278 只引 23:12:13 版 7 helper；#279 chartRing_smooth 只引 23:25:39 版、当前 STALE；#280/#282/#283 红、无 olean，禁引；#281 已撤回且 log 有 sorryAx，永禁引；F7 条件式；D3 NO INHABITANT；P¹ 三模型无 iso；IsFinite π 差 h0/h1；IsProper 无 producer。

## 6l. batch 15 更新（快照 **15:29 UTC = 23:29 CST**；覆盖 §6–§6k 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_add.mjs`（Probe 15）；`node tools/wd_status.mjs` 多次；`Get-Content watchdog.log -Tail` / 时间窗过滤（15:02–15:29 全量事件按 attempt 抽取）；`Get-Item` src/olean/log 对照（11+ 文件）；per-file log 逐个读取（P6P5 272 B、Omega 1332 B、LocalizeSwap 2238 B、URThetaTransport 566 B、ULStepVIII 622 B、CurveSmooth 1383 B、Uniqueness 4770 B、URThetaHullUpper 1157 B、PiPreimage 末块、P1Separated 788 B、bridge 151 B）；源码阅读（P6P5 78 行、ULStepVIII 286 行、OmegaInfFree 276 行、LocalizeSwap 219 行、URThetaTransport 167 行、Uniqueness 191 行、CurveSmooth 117 行、URThetaHullUpper 81 行、Htheta 118 行、UCHpkt 282–309、BadPlace 55–119、S342 1–60、BoxDistinguishedScalar 65 行、F7TameCountGlobal 63 行、PiFiniteAssembly 50 行、bridge 71 行）；grep（`DistinguishedScalarData` 16、`RootHullHalfScalingDataGap` 12、`p1GluedToBase_valuativeCriterion` Lean 0、`HeightDictionaryInterface` 1、`projectiveLine` 3、J3 只在 transport docstring/coord）。
- **Probe 15**：8 条 DONE 15:29:22（50 s），**全部三公理、0 sorryAx**。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**；仅写本表与 `_ProbeBatch15Actual.lean`。
- **未覆盖 / 未运行（如实标注）**：15:29:36 起 CurveSmooth/Uniqueness/URThetaHullUpper 的重试结果；CurveSmooth 108:12 修复后版本；Uniqueness 最终 `ValuativeCriterion.Uniqueness`；URThetaHullUpper 主定理；PiPreimageChart 最新块之外的旧错误；P1Proper/IsFinite π/P¹ 模型等旧缺口未重新做全语义审计；G-K/H-T/P8-P 的 F1–F4/F8 与端到端仍未做。
- **15:29:22–15:31:30 已补记于 §2n-3**（Uniqueness 15:30:04 DONE 7 helper；CurveSmooth 15:30:05 FAIL；URThetaHullUpper 15:30:06 FAIL；Bridge 15:31:04 FAIL；ULStepVIII 15:31:30 DONE）。**15:31:30 之后** watchdog 仍在跑；之后的任何 DONE/FAIL 本表未审计。
- 本批写入范围：本表 + **新建** `_ProbeBatch15Actual.lean`；未改其它 Lean 文件；未 spawn_teammate、未 `lake env lean`、未自起 watchdog、未写 sorry/axiom。

## 2o. 本批 batch 16 gate 表（快照 **15:45 UTC = 23:45 CST**；**#286–296**，覆盖 15:31:30–15:44:42 全部 DONE/FAIL + Lead 指定 4 项复核）

- 证据版本：src / olean 均按 `Get-Item` 实测；`(P16)` / `(P16b)` = 本批独立 probe 复算（§3n）。**15:44:56 起的一波（G1PsiCover 新文件、PointSep、ULStepVIII、Uniqueness、PiPreimage）在飞，未审计**。
- **15:31:30–15:44:42 事件全量（按 attempt 计）**：15:31:30 ULStepVIII DONE（同源再编译）；15:32:13 PiPreimageChart FAIL；**15:32:15 CurveSmooth DONE**（5 声明，含 `chartRing_smooth`/`chartRing_exists_standardSmooth_localized`）；15:32:16 URThetaHullUpper DONE（旧 81 行版，olean 无新主定理）；15:32:58 PointSep FAIL；15:33:02 Bridge FAIL（λ/import）→ 15:35:14 DONE；15:33:46 HullUpper FAIL；15:34:26 Uniqueness FAIL（174/179 `Spec.map_apply`）；15:35:13 HullUpper FAIL；15:35:57 PointSep FAIL；15:35:57 Uniqueness FAIL（180:54 carrier）；15:36:57 HullUpper FAIL；15:37:43 PointSep FAIL；**15:37:44 Uniqueness DONE（8 helper，无 Uniqueness 定理）**；**15:37:48 Probe16 DONE**；15:39:41 PointSep FAIL；**15:39:41 Probe16b DONE**；**15:40:24 HullUpper DONE（98 行回退壳）**；15:40:01 UCHCor312 FAIL（import 顺序）；15:41:07 Uniqueness FAIL（327/444 `Inv S.R`）；15:41:52 PointSep FAIL；15:41:54 D1D3 FAIL；15:43:05 UCHCor312 FAIL（末段 rewrite）；15:43:56 PiPreimage FAIL；15:43:56 PointSep FAIL；15:43:58 Uniqueness FAIL；15:43:58 CurveSmooth FAIL（新 `chartRing_locally_standardSmooth`）；**15:43:58 D1D3 DONE**；15:44:42 HullUpper FAIL（113:2 ext）。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 286 | Mzk1G1FermatCurveSmoothActual | G-A R n smooth | **FAIL（当前源）；15:32:15 曾 DONE** | **15:43:58** / 15:32:15 | **STALE**（src 23:43:17 / 7161 B；olean 23:32:15） | clean（无 literal token） | 旧 olean：`chartRing_smooth`、`chartRing_exists_standardSmooth_localized`、`chartR_span_eq_top`、`loc_isSmooth` 四条三公理（P16）；新声明 sorryAx（错误恢复） | **A-局部（只对 23:32:15 olean）/ 当前 R**。23:43:17 新源追加 `chartRing_locally_standardSmooth : RingHom.Locally (…rel dim 1) (algebraMap ℚ (Chart n))`（scheme 层输入），15:43:58 首错 **127:67 / 130:67**：`RingHom.isStandardSmoothOfRelativeDimension_algebraMap` 是 `∀ n, … ↔ …`，不能直接 `.mpr`，需先应用 `1`。**当前源无 olean；不得说 CurveSmooth 现在 DONE**。
| 287 | Mzk1ULPacketBPerLabelBridgeActual | U-L C1 bridge | **DONE** | **15:35:14** | fresh（src 23:34:16 / 3510 B；olean 23:35:14） | clean | 两条三公理（P16） | **B：条件 bridge**。import 顺序已修（imports 16–18），`hλ` 改为 `hlam`，15:33:02 的 41:6 λ binder 已消失；`packetB_eq_perLabelBound`、`avg_packetB_eq_processionAverage` 均三公理。`hlam : localNormOrder p varpi = stepVLambda …` 是真实输入（completion 无 2l-root，S342），**无 inhabitant**；内容是定义展开 + `ring`，不是 C1 闭合。
| 288 | Mzk1URThetaHullUpperActual | U-R C2 θ (≤ 路线) | **FAIL（当前源）；15:40:24 曾 DONE** | **15:44:42** / 15:40:24 | **STALE**（src 23:44:06 / 8338 B；olean 23:40:24） | clean（当前源 0 个 literal sorry；仅 docstring 词） | 15:40:24 版三条三公理；15:44:42 新定理 sorryAx（错误恢复） | **WIP / 无 producer**。15:40:24 DONE 是 **98 行回退壳**：只证 `le_ceilExp`、`norm_prime_eq_inv`、`exists_norm_pow_eq_prime_zpow`，`BallCeilEqualityAt` 仍是 retained Prop；**无 htheta≤ 主定理**。23:44:06 又加 `padicFractionalLattice_eq_intCeil`（96 行起），15:44:42 首错 **113:2** `ext` 找不到 ext 定理。**Lead 所指 literal sorry 120/125 是瞬时 WIP，已被覆盖，磁盘当前不存在**；15:35/36/44 日志中的 sorryAx 是失败证明的错误恢复。**该文件仍在 `extra-targets.txt` 第 144 行**，§38 移出白名单未阻止 watchdog 事件。
| 289 | Mzk1P1ValuativeUniquenessActual | G-A uniqueness | **FAIL（当前源）；15:37:44 曾 DONE 8 helper** | **15:43:58** / 15:37:44 | **STALE**（src 23:44:19 / 23847 B；olean 23:37:44） | clean | 15:37:44 版 8 helper 三公理（P16b 两条代表）；当前新定理 sorryAx | **R / near-miss（重大）**。15:40:02 版首次写出 **`valuativeCriterion_uniqueness : ValuativeCriterion.Uniqueness (p1GluedToBase)`（207 行）**；15:41:07 首错 **327:28 / 444:28** `Inv S.R` 实例缺失（`r = r0⁻¹` 在 `S.R` 上用了 `⁻¹`）。15:43:58 再 FAIL（log 0 B，首错未取）。**全文件仍无已编译的 Uniqueness 定理**；15:37:44 DONE 只有 8 helper，不得写 uniqueness 已证。
| 290 | Mzk1P1PointSeparationActual（**新文件**） | G-A 点分离 | **FAIL** | **15:43:56**（15:32:58 / 15:35:57 / 15:37:43 / 15:39:41 / 15:41:52 同） | none（src 23:42:53 / 3224 B） | clean（未编译） | —（log 两条 sorryAx 错误恢复） | **R**。首错 **30:6** `rw [PrimeSpectrum.mem_basicOpen]` 无匹配；**54:4** 类型不匹配；此前 27/35 为 `basicOpen` 的 Opens/Set coercion、38 为 `Membership ↥chart0Scheme` vs `PrimeSpectrum`。无 olean；不是可用点分离定理。
| 291 | Mzk1G1FermatPiPreimageChartActual | G-A π⁻¹ chart | **FAIL** | **15:43:56**（15:32:13 同） | none（src 23:42:54 / 4813 B，henry 改写） | clean（未编译） | — | **R**。首错 **39:6** motive（`Spec` carrier vs `PrimeSpectrum`），**51:6** rewrite 无匹配，**60:21 / 71:23** `Chart0Ring`/`ChartInfRing` unknown（未限定 namespace）。新 helper `specMap_preimage_primeBasicOpen` 未编译。**仍无 `π⁻¹(D_+(X0)) = D(x0^n)` 陈述**；15:32:13 的 log 已从磁盘消失（只剩较早的 PiPreimage 非 Chart 日志），该 attempt 首错未取。
| 292 | Mzk1UCHCor312FromP5Actual（**新文件**） | U-C C4 (P5 路线) | **FAIL** | **15:43:05**（15:40:01 import 顺序） | none（src 23:41:45 / 3708 B） | clean（未编译） | 自身 `#print`：`cL_mul_le_paperA_of_thm110` 三公理；`uc_c4_of_P5_certificate` sorryAx | **R / 条件式重编码**。import 顺序已修；末段 `rw [heStarMod]` 目标不匹配（`paperEar` 展开后 eStar 位置）。**语义风险**：`C : S2953CThetaUpperCertificate` 的字段 `hupper : thetaLogVolume ≤ CThetaPaper * |log q|` 本身就是目标不等式；`certificateOfFloorData` 构造还需 `htheta`、`hCTheta`、floor data。因此 **“no htheta” 只是把 htheta 换名进证书**，不是 C4 无条件闭合；证出前禁引。
| 293 | Mzk1D1D3DonorProbeActual（**新文件**） | L-H D3 供体探测 | **DONE** | **15:43:58** | fresh（src 23:43:09 / 2673 B；olean 23:43:58） | clean | 六条三公理（log）：含 `d3_rat_of_abcTriple`、`legendreJ_eq_legendreCurve_j` | **B-局部 / D3 供体，不是 inhabitant**。`d3_rat_of_abcTriple {a b c} (h : IsABCTriple a b c) : |jHeight (legendreJ …) − 6·lambdaHeight …| ≤ Real.log 256`，消费 accepted ABCBridge 的 Legendre j-height bounds；**只覆盖 rational ABC 点**，未触及 `HeightDictionaryInterface`（仍只有 def）。
| 294 | Mzk1ULStepVIIIActual | U-C Step VIII | **DONE（同源重编）** | **15:31:30** | fresh（src 23:30:21；olean 23:31:30） | clean | 五条三公理不变 | 维持 #274：`PaperStepVIIIRetained` 三字段 retained；不等于已证。
| 295 | Mzk1G1PsiCoverActual（**新文件**） | G1-B ψ cover | **START（在飞）** | 15:44:56 START | none（src 23:44:46 / 2239 B） | 未审 | — | **未判**。15:44:56 波开始，快照时无 DONE/FAIL；下一批必须补审。
| 296 | P1ProperAssembly / F7SeparableResidue / P1Separated / 旧缺口 | 旧件 | 无新事件 | — | 三个源文件均 **MISSING** | — | — | 见 §2o-2；引用纪律不变。

### 2o-1 缺口表（快照 15:45 UTC，逐项核对）

| 缺口 | 当前证据 | 状态 |
|---|---|---|
| P¹ 三模型 | 两份 `projectiveLine`（`Mzk1G1ProjectiveLineChartsActual:15`、`Mzk1G1FiniteDisjointBelyiActual:20`）+ `projectiveLineGlued`（`Mzk1G1ProjectiveLineGluedActual:136`）；grep `≅`/`projectiveLineIso` **0** | **无 iso，禁复合** |
| D3 no inhabitant | `HeightDictionaryInterface` 仍只有 `Mzk1G1QHeightActual:40` 一处 def；新 D1D3 只给 rational ABC 供体（#293），未构造接口实例 | **NO INHABITANT**（但有 rational 供体） |
| IsFinite π 条件式 | `isFinite_pi_of_chart_restrict (h0) (h1)`（PiFiniteAssembly:40–43，14:11:01 fresh）仍要两条 chart restriction | 条件式，**差 h0/h1** |
| π⁻¹(D_+(X0)) 具体等式 | `PiPreimageActual.pi_preimage_eq` 只给一般分解；`PiPreimageChart` 15:43:56 仍红（39/51/60/71），**无任何具体 chart 等式陈述** | **无陈述** |
| IsProper p1GluedToBase | existence ✓（#257）+ UniversallyClosed ✓（#258）+ QC/QS/LFT；**uniqueness 定理语句已在 #289（207 行）但当前红**；`p1GluedToBase_isProper` / `p1GluedToBase_valuativeCriterion` grep **0**；P1Separated、P1ProperAssembly 均 MISSING | **仍无 producer** |
| C2 θ / task-13 | 精确 transport 仍 **BLOCKED(named)**；≤ 路线 #288 当前 FAIL（113:2），15:40:24 只是 98 行回退壳；无 htheta producer；#273/#274 口径不变 | **WIP，未交付** |
| J3 | 仍只 j≠1 条件备选；`DistinguishedScalarData` 全 paper 仍无实际实例（结构在 `Mzk1BoxDistinguishedScalarActual:43`，16 处全是 binder） | **条件性备选** |
| F7 htame / F7Sep | `F7TameCountGlobal`/`RadicalSupport` 无新事件，仍带 `hdiv/hpn`/`htame/hbad`；`Mzk1F7SeparableResidueActual` **MISSING**（RETIRED） | **条件式；F7Sep RETIRED 且已删** |
| phantom / retracted | `Mzk1P1ProperAssemblyActual`（15:02 为 446 B）与 `Mzk1F7SeparableResidueActual` 现已 **MISSING**；`Mzk1P1SeparatedActual` 仍 MISSING（其 log 三条 sorryAx） | **全部禁引** |

### 2o-2 删除 / 清理核对（本批）
- **新观察到两个删除**：`Mzk1P1ProperAssemblyActual.lean`（§2m 15:02 仍为 446 B 注释草稿）与 `Mzk1F7SeparableResidueActual.lean`（§2l #272 记 RETIRED）在 15:45 快照均 **不存在**（`Test-Path` false；目录 glob 0）。删除发生在 15:02–15:45 之间（可能即 alan 清理）；**无 olean、无新事件，仍禁引/禁排队**。
- `Mzk1P1SeparatedActual.lean` 仍 MISSING（batch 15 已记录）；其 log 中 `p1GluedToBase_isProper` 带 sorryAx，永不可引。
- 本批新增文件：`Mzk1P1PointSeparationActual`、`Mzk1UCHCor312FromP5Actual`、`Mzk1D1D3DonorProbeActual`、`Mzk1G1PsiCoverActual`、`_ProbeBatch16Actual`、`_ProbeBatch16bActual`；未观察到其它 paper 文件被删除。

## 3n. Probe 16 / 16b（本批 batch 16）

- `_ProbeBatch16Actual.lean`：`wd_add` 15:37:12 → **DONE 15:37:48（36s）**；log 859 B，**0 error / 0 sorryAx**；6 条全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | gate |
|---|---|---|
| `G1FermatCurveSmoothActual.chartRing_smooth` | [propext, Classical.choice, Quot.sound] | #286（只对 23:32:15 olean） |
| `G1FermatCurveSmoothActual.chartRing_exists_standardSmooth_localized` | [propext, Classical.choice, Quot.sound] | #286（只对 23:32:15 olean） |
| `G1FermatCurveSmoothActual.chartR_span_eq_top` | [propext, Classical.choice, Quot.sound] | #286 |
| `G1FermatCurveSmoothActual.loc_isSmooth` | [propext, Classical.choice, Quot.sound] | #286 |
| `ULPacketBPerLabelBridgeActual.packetB_eq_perLabelBound` | [propext, Classical.choice, Quot.sound] | #287 |
| `ULPacketBPerLabelBridgeActual.avg_packetB_eq_processionAverage` | [propext, Classical.choice, Quot.sound] | #287 |

- `_ProbeBatch16bActual.lean`：`wd_add` 15:39:01 → **DONE 15:39:41（29s）**；log 325 B；2 条全部三公理：`P1ValuativeUniquenessActual.chartMorphismInf_zero_ne_chartMorphism0_zero`、`…lift_eq_chartMorphism0_of_closedPoint_mem`（#289，只对 23:37:44 olean）。
- **版本纪律**：Probe16 的 CurveSmooth 四条在 23:43:17 源改写后已 **STALE**（当前源 15:43:58 红）；它们只证明 23:32:15 olean 的 5 声明版。Bridge 两条仍 fresh（23:35:14）。合计 8 条全部三公理、0 sorryAx；**未运行** `lake env lean`、未自起 watchdog。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 16 续）

### 4.116 【高·纪律】CurveSmooth：15:32:15 DONE 已被 23:43:17 改写作废，当前红
- 15:32:15 DONE 的 5 声明版（`chartRing_smooth` + `chartRing_exists_standardSmooth_localized` 均三公理，Probe16）**只对 23:32:15 olean 有效**。23:43:17 源追加 scheme 层输入 `chartRing_locally_standardSmooth`，15:43:58 首错 127/130 `.mpr`（`isStandardSmoothOfRelativeDimension_algebraMap` 是 `∀ n, …`，需 `(... 1).mpr`）。**当前源无 olean，不得说 G-A smooth 现在 DONE，也不得引新声明**；修法只是一行显式 `1`。

### 4.117 【高·U-R/C2】URThetaHullUpper：15:32:16 DONE 是旧内容；literal sorry 已被覆盖；≤ 路线仍 WIP
- 15:32:16 的 olean 23:32:15 **不含** `padicFractionalLattice_eq_ceil`（二进制符号检查；含 `BallCeilEqualityAt`/`le_ceilExp`），所以它是旧 81 行版，不能当新主定理的证据。15:33:46 / 15:35:13 / 15:36:57 三次 FAIL 的 log 对 `padicFractionalLattice_eq_ceil` 报 **sorryAx**，均为失败证明的错误恢复；Lead 所指 literal sorry 120/125 的中间版本已被 23:44:06 源覆盖，**当前源无 literal sorry**。15:40:24 DONE 是 98 行回退壳（三条三公理）；23:44:06 又加 `padicFractionalLattice_eq_intCeil` → 15:44:42 FAIL 113:2 `ext`。**htheta≤ 主定理仍未交付；无 olean 可引。**
- **白名单事实**：`dag/watchdog/extra-targets.txt` 第 144 行仍有该文件；§38 移出没有停止 watchdog（15:32–15:44 仍不断 DONE/FAIL）。若 Lead 要真正停编，需从 `extra-targets.txt` 移除。

### 4.118 【高·G-A】Uniqueness 首次有最终定理语句，但差两个 `Inv S.R` 实例；IsProper 仍无 producer
- #289 的 15:40:02 版（23831 B）写出 `valuativeCriterion_uniqueness : ValuativeCriterion.Uniqueness p1GluedToBase`（207 行），15:41:07 首错 327:28 / 444:28：`r0⁻¹` 在 `S.R` 上需要 `Inv S.R`，而 `S.R` 只是一般交换环/整环。这是**真实 near-miss**：修法是不在 `R` 上取逆（用 `r * r0 = 1` 的 unit 形式，或先在 `S.K` 取逆再取整代表）。15:43:58 再 FAIL（log 0 B），当前源 23:44:19 又被改。**在重编译绿 + olean fresh 前，不得写 uniqueness/IsSeparated/IsProper 已证**；`p1GluedToBase_isProper` grep 仍 0。

### 4.119 【高·C4/P5】UCHCor312FromP5 的 “no htheta” 是证书重编码，不是无条件 C4
- `S2953CThetaUpperCertificate`（S2953CThetaFromCertificateActual:17）字段 `hupper : thetaLogVolume ≤ CThetaPaper * |log q|` 就是目标上界；构造器 `certificateOfFloorData`（Mzk1IVThm110HCor312FloorActual:38）还需 `htheta`、`hCTheta` 与 floor data。因此 `uc_c4_of_P5_certificate` 只是把 htheta 换成证书字段，**不能据此说 θ 侧已绕过或 C4 闭合**。当前文件 15:43:05 仍红在末段 `rw [heStarMod]`，无 olean，禁引。

### 4.120 【中·D3】D1D3 只给 rational ABC 供体；D3 接口仍无 inhabitant
- #293 `d3_rat_of_abcTriple` 三公理，真实消费 accepted Legendre j-height bounds，但只对 `IsABCTriple` 的 rational point 给出 `|jHeight−6λ|≤log 256`；`HeightDictionaryInterface` 仍是 def、无实例。**不得写 D3 已交或 j 高度下界已证。**

### 4.121 【中·G-A/π】PointSep 与 PiPreimage 仍红；π⁻¹ 仍无陈述
- PointSep 15:43:56 首错 30:6（`mem_basicOpen` 重写）与 54:4（类型不匹配），无 olean；仍是 R。PiPreimage 15:43:56 首错 39:6 carrier motive、51:6 rewrite、60/71 unknown `Chart0Ring`/`ChartInfRing`；新 helper 未编译。**`π⁻¹(D_+(X0)) = D(x0^n)` 仍无任何陈述**。

### 4.122 【中·删除/纪律】P1ProperAssembly 与 F7Sep 已被删除；引用纪律再收紧
- 15:02 仍存在的 `Mzk1P1ProperAssemblyActual`（446 B）与 RETIRED 的 `Mzk1F7SeparableResidueActual` 在 15:45 快照均 MISSING；P1Separated 仍 MISSING。三者均无 olean，**永禁引/禁排队**。任何 “P¹ proper 已证” 或 “F7Sep 可用” 的说法都不成立。

## 5l. batch 16 立即动作（快照 15:45 UTC）

1. **CurveSmooth（最高优先，一行修）**：把 127/130 改成 `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr …`；重编 DONE 后才可引 `chartRing_locally_standardSmooth`。`chartRing_smooth`/`chartRing_exists...` 仍只引 23:32:15 olean（Probe16），当前源 23:43:17 已 STALE。
2. **P¹_glued proper（david/alan，最高优先）**：保持 15:40:02 的 `valuativeCriterion_uniqueness` 语句；修 327/444 的 `Inv S.R`（不要在 `S.R` 上 `⁻¹`；用 `r * r0 = 1` 或 `S.K` 内逆 + 整代表），重编绿后再做 `IsSeparated.of_valuativeCriterion`，最后与 existence/UC/QC/QS/LFT 组装 IsProper。**在 `p1GluedToBase_isProper` 真实存在前不建/不排队 P1ProperAssembly、不引其名**（该文件已删）。
3. **C2 θ ≤ 路线（kurt）**：修 HullUpper 113:2 的 `ext`（先 `SetLike.ext`/`Set.ext` 或 `funext x`；`padicFractionalLattice` 是 Set），再证 `padicFractionalLattice_eq_intCeil`；在 `actualLocalHullLog ≤ −thetaCoefficientContribution` 出来前**不写 htheta 已证**。若要真正停编，先把 `extra-targets.txt` 第 144 行移除。
4. **C4/P5（kurt/alan）**：UCHCor312 末段 `rw [heStarMod]` 改为展开 `paperEar` 后 `simp [paperEar, heStarMod]` 或先 `change`；**即使转绿，也只能记“条件于 S2953 证书”**，不得写 C4 无条件闭合或 htheta 已绕过。
5. **PointSep（grace）**：30 行改用正确的 `mem_basicOpen` 方向（先 `change` 到 `PrimeSpectrum` 的 Set）；54 行把 `↥chart0Scheme` 与 `PrimeSpectrum ℚ[X]` 的 Membership 统一。该文件是 uniqueness 的混合点输入，转绿才有用。
6. **π⁻¹（henry）**：先修 39/51 的 carrier（`change` 到 `PrimeSpectrum` 的 Opens）并把 `Chart0Ring`/`ChartInfRing` 限定到 `Mzk1G1FermatOverlapActual`；`specMap_preimage_primeBasicOpen` 转绿后再写 `π⁻¹(D_+(X0)) = D(x0^n)` 与 Inf 侧。
7. **D3（andrew）**：D1D3 的 rational 供体已 DONE（三公理），下一步是把它接进 `HeightDictionaryInterface` 的实例，或明确 D3 只需 rational ABC 分支；**当前仍不得写 D3 已交**。
8. **引用纪律（batch 16 版，强制）**：#286 CurveSmooth 只引 23:32:15 版（当前源红、新声明禁引）；#287 Bridge 条件于 `hlam`；#288 HullUpper 无 olean/无主定理，禁引；#289 Uniqueness 只有 8 helper（23:37:44）可引，最终定理未编译；#290/#291/#292 红、禁引；#293 D1D3 只作 rational 供体；P1ProperAssembly/F7Sep/P1Separated 已删且禁引。F7 条件式、D3 NO INHABITANT、P¹ 三模型无 iso、IsFinite π 差 h0/h1、IsProper 无 producer 不变。

## 6m. batch 16 更新（快照 **15:45 UTC = 23:45 CST**；覆盖 §6–§6l 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_add.mjs`（Probe16/16b）；`node tools/wd_status.mjs`；`Get-Content watchdog.log -Tail` 多次（15:31–15:45 全量按 attempt 抽取）；`Get-Item` src/olean/log 对照（15+ 文件，含二进制 olean 符号检查 `padicFractionalLattice_eq_ceil`/`sorryAx`）；per-file log 逐个读取（CurveSmooth 1928 B、HullUpper 6091/799 B、Bridge、Uniqueness 2367/1117 B、PointSep 1890/2029 B、PiPreimage 3798 B、UCHCor312 1612 B、D1D3 1767 B）；源码阅读（CurveSmooth 108–138、HullUpper 当前 98 行、Uniqueness 145–204/300–454、PiPreimageChart 全文 88 行、UCHCor312 全文 85 行、D1D3 全文 64 行、S2953 证书/Floor 构造器、HCor312Supply、Mzk1IVThm110HCor312、P8ProducerMissingExact）；grep（`p1GluedToBase_isProper`/`p1GluedToBase_valuativeCriterion` Lean 0、`ValuativeCriterion.Uniqueness` 仅 probe 注释 + #289 新语句、`HeightDictionaryInterface` 1、`projectiveLine` 3、`DistinguishedScalarData` 16 处无实例）。
- **Probe 16/16b**：8 条全部三公理、0 error / 0 sorryAx；Probe16 DONE 15:37:48（36 s），Probe16b DONE 15:39:41（29 s）。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**；仅写本表与两个 probe 文件。
- **未覆盖 / 未运行（如实标注）**：15:44:56 起的一波（G1PsiCover 新文件、PointSep、ULStepVIII、Uniqueness、PiPreimage）结果未取；Uniqueness 15:43:58 的首错（log 0 B）未取；PiPreimageChart 15:32:13 的 log 已消失，首错未取；CurveSmooth 当前新声明的后续错误只取首错；UCHCor312 末段后续未展开；G1PsiCover 未读；U-R 其余 θ 侧、G-K、H-T F1–F4/F8、P8-P 端到端仍未做语义审计。
- **15:45 之后**：watchdog 仍在跑（15:44:56 波 + 后续），之后的任何 DONE/FAIL 本表未审计。
- 本批写入范围：本表 + **新建** `_ProbeBatch16Actual.lean`、`_ProbeBatch16bActual.lean`；未改其它 Lean 文件；未 spawn_teammate、未 `lake env lean`、未自起 watchdog、未写 sorry/axiom。

### 2o-3 快照后补记（15:45:28–15:51:41；**覆盖 §2o 对应状态**；旧行保留）

- **15:45:28–15:45:58**：PiPreimage FAIL 15:45:28；G1PsiCover 首 FAIL 15:45:28；PointSep FAIL 15:45:28；Uniqueness FAIL 15:45:30（log 0 B）；ULStepVIII DONE 15:45:58。
- **15:46:44 双 DONE**：CurveSmooth DONE（src 23:45:23 / 7165 B，olean 23:46:44）；Uniqueness DONE（src 23:46:11 / 23965 B，olean 23:46:43）。**HullUpper 15:46:46 仍 FAIL**。
- **15:47–15:49**：15:47:35 PointSep / G1PsiCover 再 FAIL；15:47:37 G1JHeightD3Probe DONE（仅多项式恒等式）；15:48:24 HullUpper FAIL；15:48:44 ULStepVI 新文件 FAIL（24:0 import 顺序）；15:49:09 G1PsiCover DONE；15:49:11 Uniqueness 再 DONE；15:49:40 ULStepVIII DONE。
- **15:50–15:51**：15:50:27 PiPreimage FAIL；15:50:27 **Probe16d DONE**；15:50:30 G1JHeightD3Actual FAIL；15:50:31 HullUpper FAIL；15:51:13 SchemeOpensRangeInterface FAIL；15:51:14 **P1ProperFinal FAIL**；15:51:41 **ULStepVI DONE**。

| # | 文件 | 最新状态 | 时间 (UTC) | 判定（覆盖 §2o） |
|---|---|---|---|---|
| 286 | Mzk1G1FermatCurveSmoothActual | **DONE（ring-level）/ 新 scheme 声明 WIP** | 15:46:44 | `chartRing_locally_standardSmooth` 已编译，**三公理（P16c）**；`chartSpec_smoothOfRelativeDimension` 不在 23:46:44 olean，23:47:32 新源在 **142:6** `HasRingHomProperty.Spec_iff` rewrite 失败并 sorryAx。`chartRing_smooth`/`chartRing_exists...` 仍只对 23:32:15 版（P16）；**当前源 7877 B 已 STALE，scheme 层未交付**。 |
| 289 | Mzk1P1ValuativeUniquenessActual | **DONE（重大）** | 15:46:44 / 15:49:11 | `valuativeCriterion_uniqueness : ValuativeCriterion.Uniqueness p1GluedToBase`（207 行）**三公理（P16c）**；`p1GluedToBase_valuativeCriterion : ValuativeCriterion p1GluedToBase`（476 行，Existence ∧ Uniqueness）**三公理（P16d）**。**P¹ ValuativeCriterion 现已真实闭合**；但 `p1GluedToBase_isProper` 仍未编译（见 #300）。 |
| 295 | Mzk1G1PsiCoverActual | **DONE** | 15:49:09 | `qPiece_isOpenImmersion`、`mem_range_localization_iff` 均**三公理**（P16d）；G1-B 局部开浸入，非全局 ψ/Ω。 |
| 297 | Mzk1ULStepVIPacketAggregationActual（**新文件**） | **DONE（import 修复后）** | 15:51:41 | 三条三公理（自身 `#print`）：`processionVolume_le_s3014`、`weighted_bad_sum_le`、`bad_sum_eq_weighted_aggregate`；U-C Step VIII part (alpha) 的真聚合。**未独立 probe**。 |
| 298 | Mzk1G1JHeightD3ProbeActual（**新文件**） | **DONE** | 15:47:37 | 只有 `probe_left`/`probe_right` 两条多项式恒等式（`Q··N * jNumN + … = 256 X^10`），**不陈述 D3**；不是 D3 证据。 |
| 299 | Mzk1G1JHeightD3Actual（**新文件**） | **FAIL** | 15:50:30 | log 8869 B：`Q00N_isHomogeneous`、`QK_isHomogeneous`、`jBezN_relation`、`logHeight_jHeight_ge`、`jHeight_relation` 均 **sorryAx**（错误恢复）；D3 仍 open。 |
| 300 | Mzk1P1ProperFinalActual（**新文件**） | **FAIL（near-miss）** | 15:51:14 | `p1GluedToBase_isSeparated : IsSeparated p1GluedToBase` **三公理**（自身 #print，未 probe）；`p1GluedToBase_isProper` 在 **19:2** 用 `⟨separated, universallyClosed, inferInstance⟩` 喂 `IsProper.mk`，报 “Insufficient number of fields … does not have explicit fields” ⇒ sorryAx。**这是 IsProper 最后一步，修构造器即可。** |
| 301 | Mzk1SchemeOpensRangeInterfaceActual | **FAIL** | 15:51:13 | 旧文件被改后红（旧 DONE 14:19:56）；细节未取。 |
| 302 | Mzk1URThetaHullUpperActual | **FAIL（仍 WIP）** | 15:50:31 | 当前源 8364/更大；仍无 htheta≤ 主定理；无 olean（最后 23:40:24 壳已 STALE）；literal sorry 0（120/125 版本已覆盖）。 |

**更新后的缺口表（本补记优先）**：
| 缺口 | 最新证据（15:52） | 状态 |
|---|---|---|
| IsProper p1GluedToBase | `ValuativeCriterion` ✓（P16d 三公理）+ UC ✓（#258）+ QC/QS/LFT；`p1GluedToBase_isSeparated` ✓ 三公理；**只差 `p1GluedToBase_isProper` 的构造器组装**（P1ProperFinal 19 行 `IsProper.mk` 字段 arity） | **near-miss；仍无编译版 producer** |
| CurveSmooth scheme 层 | ring-level `chartRing_locally_standardSmooth` ✓（P16c 三公理）；`chartSpec_smoothOfRelativeDimension` 142:6 红、olean 无此名 | **ring-level ✓ / scheme-level WIP** |
| D3 | D1D3 rational ABC donor DONE（三公理）；D3Actual multiple sorryAx；`HeightDictionaryInterface` 无实例 | **open（有 rational 供体）** |
| C2 θ / task-13 | HullUpper 15:50:31 仍 FAIL；15:40:24 只是回退壳；无 htheta producer | **WIP，未交付** |
| 其余（P¹ 三模型 / IsFinite π / π⁻¹ / J3 / F7 / 删除件） | 同 §2o-1：P¹ 无 iso；IsFinite π 差 h0/h1；π⁻¹ 无陈述（PiPreimage 15:50:27 又 FAIL）；J3 条件；F7 条件；P1ProperAssembly/F7Sep/P1Separated 均 MISSING | 不变 |

**Probe 16c / 16d（补记）**：
- `_ProbeBatch16cActual.lean`：15:48:38 排队 → **FAIL 15:49:09**，仅因 `chartSpec_smoothOfRelativeDimension` 在 23:46:44 olean 中 unknown；其余 4 条全部三公理：`valuativeCriterion_uniqueness`、`chartMorphismInf_zero_ne_chartMorphism0_zero`、`chartRing_locally_standardSmooth`、`chartRing_exists_standardSmooth_localized`。
- `_ProbeBatch16dActual.lean`：15:49:55 排队 → **DONE 15:50:27（32s）**；log 418 B；3 条全部三公理：`p1GluedToBase_valuativeCriterion`、`G1PsiCoverActual.qPiece_isOpenImmersion`、`…mem_range_localization_iff`。
- 合计独立 probe **15 条确认三公理**（16:6 + 16b:2 + 16c:4 + 16d:3），0 error/0 sorryAx；`chartSpec` 因不在 olean 未确认。

**立即动作追加（高于 §5l 旧文）**：
1. **P1ProperFinal（最高，一行级）**：把 19–21 行的 `⟨…⟩` 改成 Mathlib 的 `IsProper.of_valuativeCriterion`（或先给 `[QuasiCompact] [QuasiSeparated] [LocallyOfFiniteType]` 实例再用 `inferInstance`）；`p1GluedToBase_isSeparated` 已三公理，重编后 `p1GluedToBase_isProper` 即可 producer；随后 probe 该定理。**在此之前仍不得写“P¹ proper 已证”。**
2. **CurveSmooth scheme 层**：142:6 `HasRingHomProperty.Spec_iff` 的 rewrite 参数需显式（或直接用 `RingHom.PropertyIsLocal.Spec_iff` 的实例形式）；ring-level 已绿可引（`chartRing_locally_standardSmooth`，P16c）。
3. **D3Actual**：修 `Q00N_isHomogeneous`/`QK_isHomogeneous`/`jBezN_relation`/`logHeight_jHeight_ge`/`jHeight_relation` 的 sorryAx；若只做 rational 分支，明确写“仅 D1D3 rational donor”，不冒充 `HeightDictionaryInterface` 实例。
4. **C2 θ**：HullUpper 仍 WIP（15:50:31）；先修 `padicFractionalLattice_eq_intCeil` 的 `ext`/rewrite，再谈主定理；**htheta 未证**。
5. **C4/P5**：UCHCor312 仍红（末段 `heStarMod`）；即使转绿也只记“条件于 S2953 证书”（`hupper` 字段就是目标不等式），不得写无条件 C4/绕开 htheta。
6. **import 顺序纪律**：ULStepVI 已通过移 import 修复；UCHCor312 也已修；新文件仍须 imports 第一行，`/-!` 不能写在 imports 前。

**15:52 之后**：watchdog 仍在跑（HullUpper、PiPreimage、ULStepVI、SchemeOpensRange 等），之后的 DONE/FAIL 未审计。

### 2o-4 终局补记（15:52:02–15:54:29；**覆盖 §2o-1/§2o-3 的 IsProper 与 ≤ 路线状态**）

- **15:52:30 HullUpper DONE**：src 23:50:58 / 8426 B，olean 23:52:30；`padicFractionalLattice_eq_intCeil` **四声明全部三公理**（自身 #print；P16e 独立复算 `padicFractionalLattice_eq_intCeil` 三公理）。这是 ≤ 路线的核心 ball-ceil 等式，**但文件仍没有 `actualLocalHullLog b ≤ −thetaCoefficientContribution b` 或 htheta 主定理**，故 htheta producer 仍未交付。
- **15:53:12 P1ProperFinal DONE（重大）**：src 23:52:02 / 1231 B，olean 23:53:12；`p1GluedToBase_isSeparated` 与 `p1GluedToBase_isProper : IsProper p1GluedToBase` **均三公理**（自身 #print；P16e 独立复算两条均三公理）。`p1GluedToBase_isProper` 由 `IsProper.of_valuativeCriterion` + P16d 的 `p1GluedToBase_valuativeCriterion` 构造，**P¹_glued proper 的 producer 首次真实存在**。
- 15:53:11 SchemeOpensRangeInterface DONE（恢复旧内容）；15:53:39 ULStepVI 再 DONE；15:54:25/15:54:28 G1PsiCover / G1JHeightD3Actual 仍 FAIL。

| # | 文件 | 最新状态 | 时间 (UTC) | 判定 |
|---|---|---|---|---|
| 303 | Mzk1P1ProperFinalActual | **DONE** | 15:53:12 | **A（G-A 出口）**：`p1GluedToBase_isProper : IsProper p1GluedToBase` 三公理（P16e）；`p1GluedToBase_isSeparated` 三公理；依赖 `p1GluedToBase_valuativeCriterion`（P16d 三公理）+ UC（#258）+ QC/QS/LFT。**IsProper 缺口闭合**；但 `Mzk1P1ProperAssemblyActual` 仍是已删幻影，禁引其名，引用请用 `Mzk1P1ProperFinalActual.p1GluedToBase_isProper`。 |
| 304 | Mzk1URThetaHullUpperActual | **DONE（核心引理）/ htheta 主定理未交** | 15:52:30 | `padicFractionalLattice_eq_intCeil` 三公理（P16e）；四声明全部三公理；≤ 路线的 ball-ceil 数值核心已证。**无 htheta 主定理、无 `actualLocalHullLog ≤ −thetaCoeff` 陈述**，不得写 θ 侧已闭合。 |

**更新后的缺口表（15:54，最终口径）**：
| 缺口 | 最新证据 | 状态 |
|---|---|---|
| IsProper p1GluedToBase | `P1ProperFinalActual.p1GluedToBase_isProper` 三公理（P16e，23:53:12 olean）；isSeparated 三公理；ValuativeCriterion（P16d）、UC（#258）、QC/QS/LFT 齐 | **CLOSED（producer 存在）** |
| Y_n proper / IsFinite π | `PiProper.fermatCurveToSpec_isProper (hfin : IsFinite (pi n)) (hP1 : IsProper p1GluedToBase)`；**hP1 现已可 discharge**，只剩 `hfin`；`isFinite_pi_of_chart_restrict` 仍要 h0/h1 两条 chart restriction | 条件式，**只差 h0/h1** |
| P¹ 三模型 | 两份 `projectiveLine` + `projectiveLineGlued`；iso grep 0 | **无 iso，禁复合**（proper 只对 glued 模型） |
| D3 | D1D3 rational ABC donor 三公理；D3Actual 15:54:28 仍 FAIL（`Q00N_isHomogeneous` 等 sorryAx）；`HeightDictionaryInterface` 无实例 | **open（有 rational 供体）** |
| π⁻¹(D_+(X0)) | PiPreimageChart 15:52:26 仍 FAIL；无具体 chart 等式陈述 | **无陈述** |
| C2 θ / task-13 | `padicFractionalLattice_eq_intCeil` 已证（P16e），但无 htheta 主定理/`actualLocalHullLog ≤ −thetaCoeff`；HullUpper 仍无 producer | **≤ 路线核心引理 ✓ / htheta WIP** |
| J3 / F7 / F7Sep / 删除件 | J3 仍只 j≠1 条件；F7 条件于 hdiv/hpn；F7Sep/P1Separated/P1ProperAssembly 均 MISSING | 不变 |

**Probe 16e（补记）**：`_ProbeBatch16eActual.lean` 15:53:53 排队 → **DONE 15:54:29（36s）**；log 419 B；3 条全部三公理：`P1ProperFinalActual.p1GluedToBase_isProper`、`P1ProperFinalActual.p1GluedToBase_isSeparated`、`URThetaHullUpperActual.padicFractionalLattice_eq_intCeil`。连同 16/16b/16c/16d，独立 probe 共 **18 条确认三公理**、0 error/0 sorryAx（P16c 的 `chartSpec` 因不在 olean 未确认）。

**立即动作（最终口径，高于 §5l 旧文）**：
1. **G-A 收尾**：直接用 `Mzk1P1ProperFinalActual.p1GluedToBase_isProper` discharge `PiProper.fermatCurveToSpec_isProper` 的 hP1；只剩 `hfin : IsFinite (pi n)`（h0/h1 两条 chart restriction）与 π⁻¹ 具体等式。**不得再引 P1ProperAssembly 的旧幻影名。**
2. **CurveSmooth scheme 层**：ring-level `chartRing_locally_standardSmooth` 已三公理（P16c）；`chartSpec_smoothOfRelativeDimension` 当前源 142:6 红（`HasRingHomProperty.Spec_iff` rewrite 参数），修好后 scheme 层 λ-chart smooth 才闭合。
3. **C2 θ**：ball-ceil 核心（`padicFractionalLattice_eq_intCeil`）已三公理（P16e），下一步必须写出并证明 `actualLocalHullLog b ≤ −thetaCoefficientContribution b`（或按 docstring 接 old-corpus `qVFamLocalQPilotLogVolume_le_thetaHull`）；**htheta 仍未证**。
4. **D3**：D1D3 rational donor 已三公理；D3Actual 的 5 条 sorryAx 需修，或明确 D3 仅需 rational 分支；不得写 D3 已交。
5. **π⁻¹**：PiPreimageChart 15:52:26 仍红（39/51/60/71），先修 carrier/namespace，再写具体 chart 等式。
6. **C4/P5**：UCHCor312 仍红（末段 `heStarMod`），且 `S2953CThetaUpperCertificate.hupper` 是目标不等式重编码，不得写无条件 C4/绕开 htheta。
7. **引用纪律（batch 16 终版）**：`P1ProperFinalActual.p1GluedToBase_isProper`/`p1GluedToBase_valuativeCriterion`/`valuativeCriterion_uniqueness` 可引（均三公理，P16c/d/e）；`P1ValuativeUniquenessActual` 当前源 23:46:11 与其 olean 23:46:43 一致；`CurveSmooth` 只引 23:46:44 olean 的 ring-level 声明；`HullUpper` 只引 23:52:30 olean 的四声明；P1ProperAssembly/F7Sep/P1Separated 已删禁引。

**15:54:29 之后**：watchdog 仍在跑（G1PsiCover、D3Actual、ULHviTable 等），之后的 DONE/FAIL 未审计。

## 2p. 本批 batch 17 gate 表（快照 **16:29 UTC = 2026-11-17 00:29 CST**；**#305–327**，覆盖 15:54:29–16:25:04 的全部 DONE/FAIL + Lead 指定 10 项复核）

- 证据版本：src / olean 均按 `Get-Item` 实测；`(P17)` = 本批独立 probe 复算（§3o）。**15:31:30–15:54:29 已由 §2o/#286–304 覆盖**；本批不重复，只对 Lead 指定的 CurveSmooth（15:55:41 终版）与 P1ProperFinal（15:53:12）做终版复核。**16:25:04 之后未审计**（16:24:24 起的文件波：URBadWeightSum、ULHviTableFinal、URSmallPrime、ProjectiveLineChartPreimage 在飞；ULStepVIII 16:25:37、OmegaRamificationLocal 16:25:02 只作尾注）。
- **15:54:54–16:25:04 全量事件（按 attempt 计）**：15:54:54 ULHviTable FAIL；15:55:39 PiProper DONE；15:55:41 OmegaLineBundle FAIL / CurveSmooth DONE；15:56:00 UCHthetaWiring FAIL；15:56:48 ULHviTable DONE；15:57:32 PiPreimageChart DONE；15:57:33 PsiCover DONE；15:57:35 JHeightD3 DONE / OmegaLineBundle FAIL；15:58:44 UCHthetaWiring FAIL；15:59:27 PiPreimageFinal FAIL；15:59:28 FermSmoothGAttempt DONE / PsiCover DONE / OmegaLineBundle FAIL；16:00:11 Probe16c DONE；16:00:39 ULHviTableLetters DONE；16:01:24 PiPreimageFinal FAIL / PsiCover FAIL；16:01:27 OmegaLineBundle DONE；16:01:51 UCHthetaWiring FAIL；16:02:33 CurveSmooth2 FAIL；16:02:34 D2Interface DONE；16:02:54 DisplayIdentity FAIL；16:03:19 PiPreimageFinal FAIL / PsiCover FAIL；16:03:48 UCHthetaWiring DONE；16:04:32 PsiCover FAIL；16:04:33 CurveSmooth2 DONE；16:04:35 OmegaLineBundle FAIL；16:05:01 ULHviTable FAIL；16:05:46 PiPreimageFinal FAIL；16:06:15 DisplayIdentity FAIL；16:06:20 ULStepVIII DONE；16:06:33 CollectionLayer FAIL；16:07:18 PiPreimageFinal FAIL / PsiCover FAIL / CurveSmooth2 FAIL / OmegaLineBundle FAIL；16:07:47 ULHviTable DONE；16:08:33 PiPreimageFinal FAIL；16:08:34 PsiCover DONE / OmegaLineBundle DONE；16:09:01 DisplayIdentity FAIL；16:09:18 CollectionLayer FAIL；16:10:03 PsiCover FAIL / CurveSmooth2 FAIL / CollectionLayer FAIL；16:11:16 PiPreimageFinal FAIL / OmegaLineBundleData FAIL / CurveSmooth2 FAIL；16:11:45 DisplayIdentity FAIL；16:11:47 ULHviTable FAIL；16:11:49 ULStepVIII DONE；16:12:33 PsiCover FAIL / JHeightUniformProbe FAIL / JHeightUniform FAIL / CollectionLayer FAIL；16:13:17 DisplayIdentity FAIL；16:13:41 PiPreimageFinal FAIL / PsiCover FAIL；16:13:43 CurveSmooth2 DONE / OmegaLineBundleData DONE；16:14:53 ULHviTable FAIL；16:15:44 PsiCover DONE；16:15:45 JHeightUniform DONE / JHeightUniformProbe FAIL；16:15:47 CurveSmooth2 FAIL；16:16:12 CollectionLayer FAIL / DisplayIdentity FAIL；16:16:56 ProjectiveLineChartPreimage FAIL / OmegaRamificationLocal FAIL；16:16:57 JHeightUniformProbe DONE；16:17:24 ULHviTable DONE；16:18:10 CurveSmooth2 FAIL；16:18:34 CollectionLayer FAIL / DisplayIdentity FAIL；16:19:17 OmegaRamificationLocal FAIL / CurveSmooth2 FAIL；16:19:46 ULHviTable DONE；16:20:40 ProjectiveLineChartPreimage FAIL；16:20:53 CollectionLayer DONE；16:21:37 OmegaRamificationLocal FAIL / CurveSmooth2 FAIL；16:22:03 DisplayIdentity DONE；16:22:06 ULHviTable DONE；16:24:09 ProjectiveLineChartPreimage FAIL；16:25:00 PiPreimageFinal FAIL；16:25:02 OmegaRamificationLocal DONE；16:25:04 CurveSmooth2 FAIL。

| # | 文件（`tmp/sheaf/xif/paper/`） | 节点 | 最新状态 | 时间 (UTC) | olean | grep | axioms | 判定 |
|---|---|---|---|---|---|---|---|---|
| 305 | Mzk1G1FermatCurveSmoothActual | G-A R n smooth | **DONE（终版）** | **15:55:41** | fresh（src 23:54:15 / 7993 B；olean 23:55:41） | clean | 7 条全部三公理（自身 log；P17 `chartSpec_smoothOfRelativeDimension`） | **A-局部（affine chart scheme 层）**。含 `chartRing_smooth`、`chartRing_exists_standardSmooth_localized`、`chartRing_locally_standardSmooth`、`chartSpec_smoothOfRelativeDimension : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Chart n))))`，另有 `chartX_chartR_add`/`chartR_span_eq_top`/`loc_isSmooth`。**Lead 指定 1 满足：15:55:41 DONE 内容含 chartSpec**；15:32:15/15:46:44 旧 attempt 只到 ring-level，不得当当前。仍非 R2 chart scheme / glued smooth。 |
| 306 | Mzk1P1ProperFinalActual | G-A IsProper 出口 | **DONE（producer）** | **15:53:12** | fresh（src 23:52:02 / 1231 B；olean 23:53:12） | clean | `p1GluedToBase_isProper`、`p1GluedToBase_isSeparated` 均三公理（log 271 B + P17） | **A（G-A 出口）**。`p1GluedToBase_isProper := IsProper.of_valuativeCriterion (Mzk1P1ValuativeUniquenessActual.p1GluedToBase_valuativeCriterion)`；后者（476 行）与 `valuativeCriterion_uniqueness`（207 行）在 fresh olean 23:49:11 中。**producer 首次真实存在**；`Mzk1P1ProperAssemblyActual` 仍 MISSING，禁引旧名。 |
| 307 | Mzk1G1FermatPiProperActual | G-A Y_n proper 装配 | **DONE** | **15:55:39** | fresh（src 23:54:15 / 5207 B；olean 23:55:39） | clean | 8 条三公理（log 1723 B；P17 `_cond`） | **A/consumer**。`fermatCurveToSpec_isProper_cond (hfin)` 消费 #306 的 producer，故 **Y_n proper 现只条件于 `IsFinite (pi n)`**；`fermatCurveToBase_isProper` 仍取 hfin + hP1。装配本身是 `rw [← eq]` + `inferInstance`（with hfin/hP1 instances），非新假设。 |
| 308 | Mzk1G1FermatPiPreimageChartActual | G-A π⁻¹ chart | **DONE** | **15:57:32** | fresh（src 23:56:15 / 3311 B；olean 23:57:32） | clean（无 #print） | P17 `overlapToChart0_opensRange` 三公理；另两条同日志未取（无 #print） | **A-局部（opensRange carrier 桥）**。仅 3 条：P¹ `overlapToChart0.opensRange = basicOpen X`；Y 侧 `overlapToChart0_opensRange = Spec(Chart0Ring).basicOpen (secOf x0)`；Y 侧 `overlapToChartInf_opensRange = basicOpen (secOf r1)`。**仍无 `π⁻¹(D_+(X0)) = D(x0^n)` 陈述**（见 #325）。 |
| 309 | Mzk1G1JHeightD3Actual | L-H D3 j-height | **DONE（重大修正）** | **15:57:35** | fresh（src 23:56:01 / 16485 B；olean 23:57:35） | clean | 9 条三公理（log 3875 B；P17 `jHeight_relation`） | **A-局部（D3 j-height 比较）**。`jHeight_relation : ∃ B, ∀ lam, abs (jHeight lam − 6·lambdaHeight lam) ≤ B`；证明用 `Height.logHeight_eval_le'/ge'` + `jBezN_relation`（Bezout）+ 齐次性，真实。**纠正 #299（15:50:30 的 5 条 sorryAx）**。但 `HeightDictionaryInterface`（qHeight 接口）仍无 inhabitant（见 §4.124）。 |
| 310 | Mzk1G1FermatSmoothGAttemptActual | G-A ∞-chart smooth 代数核 | **DONE** | **15:59:28** | fresh（src 23:58:30 / 7485 B；olean 23:59:28） | clean | 8 条三公理（log 1185 B） | **A-局部**。`fermatModelRing = ℚ[x,y,z]/(1+x^n−y^n, (n x^{n−1})z−1)` 的 submersive presentation，jacobian = (n x^{n−1})² 由关系式成 unit，rel dim 1；`fermatModel_isStandardSmooth` 三公理。**未证它与 `Localization.Away (coordX) (B n)` 同构**。 |
| 311 | Mzk1ULHviTableLettersActual | U-C Step VIII (beta) 字典 | **DONE** | **16:00:39** | fresh（src 23:59:19 / 3102 B；olean 16:00:39） | clean | 2 条三公理（log 288 B） | **A-局部**。`S3014PerLabelBound_eq_paperLetters` 是 `unfold`+`push_cast`+`ring` 的精确字母恒等式；`S3014Exceptional_le_R4` 转调 donor `exceptionalSum_le_r4`。非 Step VIII 整体。 |
| 312 | Mzk1G1OmegaLineBundleActual | G1-B (iii) 线丛数据 | **DONE（多 attempt）** | **16:08:36** | fresh（src 00:07:33 / 7064 B；olean 16:08:36） | clean | 10 条三公理（log 1375 B；P17 `canonicalLineBundle_data`） | **A-局部（两 chart 数据）**。`canonicalLineBundle_data` 是三重合取：trivial0(omegaForm)=1、trivial1(omegaInfForm)=1、omegaInfRaw = transitionUnit·omega0O（unit = u0^(n−3)）；另有 `pi_pullback_lambda/one_sub/infinity`、`a5_transition_unit`、`lambda_eq_x_pow`。**不是 sheaf 同构 Ω ≅ O(n−3)，不是全局 Ω**（见 §4.123）。 |
| 313 | Mzk1G1D2InterfaceActual | G-B D2 接口 | **DONE** | **16:02:34** | fresh（src 00:01:28 / 3522 B；olean 16:02:34） | clean | 2 条三公理（log 281 B，均为字段投影） | **C（定义自反 / NO INHABITANT）**。`TripodalDictionary` 结构 10 字段 + 4 条 law；`relations` 是 `⟨T.logDiff_eq, …⟩`，`fFtpd_conductor_le` 是字段访问。三公理 ≠ 内容；**不得当 D2 进展**。 |
| 314 | Mzk1UCHthetaWiringActual | U-C C4 θ 接线 | **DONE** | **16:03:48** | fresh（src 00:02:46 / 8124 B；olean 16:03:48） | clean | 3 条三公理（log 383 B） | **B− 条件接线**。`htheta_of_hperB` = #273 wrapper；`HthetaInput` 命名 Prop（字段 htheta，PENDING，无 inhabitant）；`uc_c4_of_htheta`/`uc_c4_of_hperB` 把 htheta（或 hperB）+ hstepVIII 作显式假设。**hperB/hscale/hpacket 均无 producer；θ 未闭合**。 |
| 315 | Mzk1G1FermatCurveSmooth2Actual | G-A R2 chart smooth | **DONE（16:13:43）→ 当前源红** | 16:13:43 / **16:25:04** | **STALE**（src 00:22:53 / 9351 B；olean 16:13:42 / 283608 B） | clean | `preR2_jacobian` 三公理（P17）；olean 另含 pderiv zero/one、span_range、preR2、naive_jacobian | **A-局部（pre-submersive presentation）/ 当前 R**。二进制 olean **不含 `loc_u2_standardSmooth`**；当前源已加 loc_u2 段并红（log 0 B，首错未取）。**Lead 指定 5 的括号条件“loc_u2 若绿”不成立**；不得写 R2 chart standard smooth 已证。 |
| 316 | Mzk1ULHviTableActual | U-C Step VIII (beta) accounting | **DONE** | **16:22:06** | fresh（src 00:21:02 / 13278 B；olean 16:22:05） | clean | 9 条三公理（log 1787 B） | **A-局部（求和记账）**。`badWeighted_le_commonBound(_gen)`、`processionAverage_le_of_perLabel`、`hviTable_of_packetBounds/perLabelBounds/badSum_perLabel/collectionLayer(_logp)`、`badWeighted_collectionBound`。依赖 `collectionBound` 线性性；**具体字母实例化在 #311**。 |
| 317 | Mzk1URCollectionLayerActual | U-C collection 层 | **DONE** | **16:20:53** | fresh（src 00:19:29 / 3989 B；olean 16:20:52） | clean | 无定理；log 660 B 只有 4 条 `#print` 定义 | **C（定义层）**。只有 `urCollHullLog`、`urCollLocalNormOrder`、`urCollIndex`、`urCollLogp`、`urCollLam := fun _ => 1`、`urCollOq`、`urCollIotaL`；文件自述 definitions only。**不是 Step VIII 证据**。 |
| 318 | Mzk1ULStepVDisplayIdentityActual | U-C Step V display 系数 | **DONE** | **16:22:03** | fresh（src 00:20:26 / 4064 B；olean 16:22:02） | clean | 8 条三公理（log 1130 B） | **A-局部（初等算术）**。`sum_Icc_one_add/sq/four_one_add/const` + `paperDisplay_coefficient_D/Q/T/S`（(l+5)/4、(l+1)/24、l+5、S）。**不是完整 Step V display identity**。 |
| 319 | Mzk1G1JHeightUniformActual | G-B uniform height | **占位更正 / 空模块** | 16:15:45 | olean 00:15:45 / 3448 B（空模块）；src **MISSING** | — | — | **C / 非证据**。磁盘只有 `_PlaceholderJHeightUniformActual.lean`（13 行 import + namespace，mtime 00:14:07）；`Mzk1G1JHeightUniformActual.lean` 不存在。16:15:45 DONE 是空模块编译；**不得写 uniform height 已交**。 |
| 320 | Mzk1G1JHeightUniformProbeActual | G-B height infra probe | **DONE** | **16:16:57** | fresh（src 00:15:54 / 913 B；olean 16:16:57） | clean | 2 条三公理（log 740 B） | **B infra**。`infPlace_intCast`、`finPlace_intCast_le_one` 是 intCast 的绝对值/≤1 事实；不是 uniform height comparison。 |
| 321 | Mzk1ULStepVIIIActual | U-C Step VIII 装配 | **DONE（16:11:49 / 16:25:37）** | 16:25:37 | olean 00:25:36 / 1396920 B；src 00:24:43 / 18667 B | clean | `hstepVIII_of_retained`/`uc_c4_of_retained` 三公理（P15）；新记录未编译 | **B（retained）**。olean 含 `hviProcession`、`hstepVIII_of_retained`、`uc_c4_of_retained`；**不含** 16:24:43 新加的 `nativeWeightsSum_eq_invDegreeSum`/`NativeVsPaperWeightsRecord`。三字段（hiii/hviPacket/hvii）仍 NO INHABITANT；`uc_c4_of_retained` 条件于 hscale/hpacket/hstepVIII。见 §4.125 内容-mtime 陷阱。 |
| 322 | Mzk1G1OmegaLineBundleDataActual | G1-B 命名数据 | **DONE** | **16:13:43** | fresh（src 00:12:30 / 5969 B；olean 16:13:43） | clean | 3 条三公理（log 456 B） | **A-局部数据 / B**。`CanonicalLineBundleData` 结构 + `canonicalLineBundleData` 由 #312 实例化；`canonicalLineBundleData_a5` 等是同一恒等式搬运；`boundaryRamificationAlgebraData` 把 6 条事实重装为 Prop；`BoundaryRamificationIndexObligation` **NO INHABITANT**；`RelativeDifferentialInterface`/`ArithmeticDifferentInterface` **NO INHABITANT**（仅接口）。 |
| 323 | Mzk1G1OmegaRamificationLocalActual | G1-B λ=0/1 ramification | **DONE（窗口外尾注）** | **16:25:02** | fresh（src 00:22:37 / 8512 B；olean 16:25:01） | clean | 2 条三公理（log 307 B；P17 `boundary_zero_uniformizer_power`） | **A-局部（真实 e=n 核心）**。`boundary_zero_uniformizer_power`：在 (0,1) 局部环 `x^n = unit·(1−y)`；`boundary_one_uniformizer_power`：在 (1,0) 局部环 `y^n = unit·(1−x)`。用 geometric sum + AtPrime 局部化 unit 判据。**∞ 侧 r 不在此文件**。 |
| 324 | Mzk1G1ProjectiveLineChartPreimageActual | G-A P¹ chart preimage | **FAIL / WIP** | 16:24:09 | olean 旧 21:37:11（STALE）；src 00:25:23 / 2916 B | clean（未编译） | — | **R（当前源）**。当前源是 4 定理重写（`preimage_opensRange_ι`、`localChartInf_preimage_localChart0`、`localChart0_preimage_localChartInf`、`localChart0_opensRange_sup_localChartInf`）；16:16:56/16:20:40/16:24:09 FAIL、16:25:51 START；log 0 B。**PiPreimageChart 15:57:32 的 DONE 用的是旧 olean**，不得把当前源当已证。 |
| 325 | Mzk1G1FermatPiPreimageFinalActual | G-A π⁻¹ 具体等式 | **FAIL** | **16:25:00** | none（src 00:12:45 / 4924 B） | clean（未编译） | — | **R**。首错 **29:6**（`overlapToChartInf = invAuto ≫ overlapToChart0` 的 rewrite motive 依赖 `IsOpenImmersion`，type-correct 失败）、**75:29** `end` 语法、**64:2** unknown `rw`；后段 62:5/66:6 `basicOpen` 与 `ΓSpecIso` coercion 不一致。**π⁻¹(D_+(X0)) = D(x0^n) 仍无陈述**。 |
| 326 | Mzk1SchemeOpensRangeInterfaceActual / Mzk1ULStepVIPacketAggregationActual | G-A opensRange 接口 / U-C Step VIII (alpha) | **DONE / DONE** | 15:53:11 / 15:53:39 | fresh（各自） | clean | SchemeOpensRange 6 条三公理（log 883 B）；ULStepVIPacket 4 条三公理（log 601 B） | **A-局部 infra / B**。SchemeOpensRange 给 `opensRange_coe_eq_range`、`mem_opensRange_iff`、`opens_eq_of_forall_mem`、`opensRange_localizationAway'`、`primeBasicOpen_opensRange_coe`；ULStepVIPacket 的 `processionVolume_le_s3014_actual` 无条件转调 donor，`bad_sum_eq_weighted_aggregate` 是 `rfl`（C），其余 3 条真。 |
| 327 | Mzk1G1PsiCoverActual | G1-B ψ cover | **DONE** | **16:15:44** | fresh（src 00:14:55 / 6027 B；olean 16:15:44） | clean | P16d 已独立确认 2 条三公理；`cover_point`/`opensRange_sup_top` 未独立 probe（源内 #print 存在，log 未留） | **A-局部 cover**。`cover_point`（每点落在 U0 或 D(q)）与 `opensRange_sup_top`（`U0.opensRange ⊔ (qPiece).opensRange = ⊤`）用 glue data 的 `ι_jointly_surjective` + overlap opensRange 证；`qPiece_isOpenImmersion` 实例。非全局 ψ。 |


### 2p-1 缺口表（快照 16:29 UTC，逐项核对；旧 §2n-1/§2o-1 保留）

| 缺口 | 当前证据（16:29） | 状态 |
|---|---|---|
| P¹ 三模型 | 两份 `projectiveLine` + `projectiveLineGlued`；`projectiveLineIso`/`≅` grep **0** | **无 iso，禁复合** |
| D3 | `G1JHeightD3Actual.jHeight_relation` 三公理（P17，23:57:35 olean）：`∃ B, ∀ lam, |jHeight lam − 6·lambdaHeight lam| ≤ B`；`HeightDictionaryInterface` 仍只有 `Mzk1G1QHeightActual:40` 一处 def、无实例（grep 1） | **j-height 比较 ✓ / interface NO INHABITANT** |
| IsFinite π | `isFinite_pi_of_chart_restrict`（`Mzk1G1FermatPiFiniteAssemblyActual:40`）仍要 h0/h1 两条 chart restriction | 条件式，**差 h0/h1** |
| π⁻¹(D_+(X0)) | `PiPreimageChart` 15:57:32 DONE 只给 P¹/Y 两侧 `overlapToChart*_opensRange`（P17 一条）；`PiPreimageFinal` 16:25:00 仍红（29:6 / 75:29） | **无具体等式陈述** |
| IsProper p1GluedToBase | `Mzk1P1ProperFinalActual.p1GluedToBase_isProper` 三公理（P17，23:53:12）；`p1GluedToBase_isSeparated` 三公理；依赖 `Mzk1P1ValuativeUniquenessActual.valuativeCriterion_uniqueness` + `p1GluedToBase_valuativeCriterion`（207/476 行，src 23:48:01 / olean 23:49:11 fresh） | **CLOSED（producer 存在）** |
| Y_n proper | `Mzk1G1FermatPiProperActual.fermatCurveToSpec_isProper_cond (hfin)` 三公理（P17，23:55:39）只差 `IsFinite (pi n)` | **条件式，只差 hfin** |
| C2 θ / task-13 | `UCHthetaWiring` 全部条件式（`HthetaInput` 命名 Prop、无 inhabitant；`uc_c4_of_htheta`/`_of_hperB` 显式假设）；`URThetaHullUpper` 15:52:30 只有 ball-ceil 核心（`padicFractionalLattice_eq_intCeil`），**无 `actualLocalHullLog ≤ −thetaCoeff` 主不等式**；hperB/hscale/hpacket 均无 producer | **无 θ producer** |
| J3 | 仍只 j≠1 条件备选；`DistinguishedScalarData` 全 paper 无实际实例（结构在 `Mzk1BoxDistinguishedScalarActual:43`，出现全是 binder） | 条件性备选 |
| F7 htame | `tameCount_of_div_ramification` 仍假设 hdiv/hpn；`RadicalSupport` 仍假设 htame/hbad；F7Sep RETIRED 且 MISSING | 条件式 |
| 删除/占位 | `Mzk1P1ProperAssemblyActual` / `Mzk1F7SeparableResidueActual` / `Mzk1P1SeparatedActual` 均 MISSING；`Mzk1G1JHeightUniformActual` MISSING（只余 `_Placeholder...` 空模块） | **禁引 / 非证据** |

### 2p-2 删除 / 占位 / 新增核对（本批）

- **三件删除维持**：`Mzk1P1ProperAssemblyActual`、`Mzk1F7SeparableResidueActual`、`Mzk1P1SeparatedActual` 在 16:29 仍 `Test-Path = False`；均无 olean/事件，**永禁引**。
- **JHeightUniform 占位更正（Lead 指定 4）**：`tmp/sheaf/xif/paper/Mzk1G1JHeightUniformActual.lean` **不存在**；磁盘只有 `_PlaceholderJHeightUniformActual.lean`（13 行：两条 import + namespace，mtime 00:14:07）与 olean `Mzk1G1JHeightUniformActual.olean`（3448 B，mtime 00:15:45，对应 16:15:45 DONE）。即 16:12:34 FAIL 后文件被替换成**空模块**，DONE 16:15:45 是空模块编译成功，随后改名为下划线占位。**不构成任何高度比较证据**；`JHeightUniformProbe`（2 条 intCast 引理，三公理）是另一件、仅为 infra。
- **本窗口新增文件**：`Mzk1G1OmegaLineBundleActual`、`Mzk1G1OmegaLineBundleDataActual`、`Mzk1G1D2InterfaceActual`、`Mzk1UCHthetaWiringActual`、`Mzk1ULHviTableActual`、`Mzk1ULHviTableLettersActual`、`Mzk1ULStepVDisplayIdentityActual`、`Mzk1URCollectionLayerActual`、`Mzk1G1FermatCurveSmooth2Actual`、`Mzk1G1FermatSmoothGAttemptActual`、`Mzk1G1FermatPiPreimageFinalActual`、`Mzk1G1ProjectiveLineChartPreimageActual`（重写）、`Mzk1G1JHeightUniformProbeActual`、`_PlaceholderJHeightUniformActual`、`Mzk1G1OmegaRamificationLocalActual`；16:24:24 波新增 `Mzk1URBadWeightSumActual`、`Mzk1URSmallPrimeActual`、`Mzk1ULHviTableFinalActual`（在飞）。本批只新建 `_ProbeBatch17Actual.lean`。
- **未观察到其它删除**；`Mzk1G1FermatCurveSmoothActual`、`Mzk1P1ProperFinalActual` 等保持原位。

### 2p-3 版本陷阱（本批最重要，必须与 §0 四层一起用）

- **ULStepVIII 内容-mtime 陷阱**：当前源 `Mzk1ULStepVIIIActual.lean` mtime **00:24:43 / 18667 B** 晚于 16:24:24 START、早于 olean 00:25:36；但二进制 olean 只含 `hviProcession`/`hstepVIII_of_retained`/`uc_c4_of_retained`/`log_pi_le_two`，**不含** `nativeWeightsSum_eq_invDegreeSum`、`NativeVsPaperWeightsRecord`（这两条是 16:24:43 编辑加入的、对应 Lead 2026-11-17 ruling (c) 的审计记录块）。**因此 16:25:37 DONE 只覆盖 16:24:24 START 时读到的旧内容；mtime 检查通过但内容不对应当前源。** 不得引当前源的新记录；也不得据 mtime 说当前源已 DONE。
- **CurveSmooth2 的 olean 是子集**：16:13:42 olean 含 `pderiv_secondEquation_zero/one`、`span_range_secondEquation`、`preR2`、`naive_jacobian`、`preR2_jacobian`，**不含** `loc_u2_standardSmooth`（二进制核验）。故 P17 的 `preR2_jacobian` 三公理只覆盖 pre-submersive presentation；当前源 00:22:53 已加入 loc_u2 段并在 16:25:04 红（log 0 B，首错未取）。
- **ProjectiveLineChartPreimage 旧 olean / 新红源**：当前源 00:25:23 / 2916 B 是 4 定理重写，但 olean 仍是 **21:37:11**（旧版本），16:16:56/16:20:40/16:24:09 三次 FAIL、16:25:51 START；**PiPreimageChart 15:57:32 的 DONE 用的是旧 olean，不是当前源**。
- **DONE→改写→FAIL 循环（本窗口重复 4 例）**：OmegaLineBundle 16:01:27 DONE → 16:04:35/16:07:22 FAIL → 16:08:36 DONE；ULHviTable 16:07:47 DONE → 16:11:47/16:14:53 FAIL → 16:17:24/16:19:46/16:22:06 DONE；CurveSmooth2 16:13:43 DONE → 16:15:47 起全红；PsiCover 16:08:34 DONE → 16:10:03/16:13:42 FAIL → 16:15:44 DONE。**引用一律写 olean 时间，不写文件名。**

## 3o. Probe 17（本批 batch 17）：`tmp/sheaf/xif/paper/_ProbeBatch17Actual.lean`

- `node tools/wd_add.mjs` 16:26 排队（NO-EVENT 后进入）→ **DONE 16:29:30**；log 1128 B，**0 error / 0 sorryAx**。8 条全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | 证据版本 / gate |
|---|---|---|
| `Mzk1G1FermatCurveSmoothActual.chartSpec_smoothOfRelativeDimension` | [propext, Classical.choice, Quot.sound] | 23:55:41 olean（#305） |
| `Mzk1P1ProperFinalActual.p1GluedToBase_isProper` | [propext, Classical.choice, Quot.sound] | 23:53:12 olean（#306） |
| `G1JHeightD3Actual.jHeight_relation` | [propext, Classical.choice, Quot.sound] | 23:57:35 olean（#309） |
| `Mzk1G1FermatCurveSmooth2Actual.preR2_jacobian` | [propext, Classical.choice, Quot.sound] | 16:13:42 olean（#315；**不含 loc_u2**） |
| `Mzk1G1FermatPiPreimageChartActual.overlapToChart0_opensRange` | [propext, Classical.choice, Quot.sound] | 23:57:32 olean（#308） |
| `Mzk1G1FermatPiProperActual.fermatCurveToSpec_isProper_cond` | [propext, Classical.choice, Quot.sound] | 23:55:39 olean（#307） |
| `Mzk1G1OmegaLineBundleActual.canonicalLineBundle_data` | [propext, Classical.choice, Quot.sound] | 16:08:36 olean（#312） |
| `Mzk1G1OmegaRamificationLocalActual.boundary_zero_uniformizer_power` | [propext, Classical.choice, Quot.sound] | 16:25:01 olean（#323；窗口外尾注） |

- **版本纪律**：8 条均按磁盘 olean 复算；`preR2_jacobian` 只证明 16:13:42 版（当前源已红）；`overlapToChart0_opensRange` 只证明 15:57:32 版（当前源未改，fresh）；`boundary_zero_uniformizer_power` 是 16:25:02 DONE（晚于 16:20 窗口，作尾注）。probe **未运行** `lake env lean`、未自起 watchdog。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 17 续）

### 4.123 【高·G-B】Omega 线丛：两 chart 数据真实，但不是全局 Ω，也不是层同构
- `Mzk1G1OmegaLineBundleActual.canonicalLineBundle_data`（P17 三公理）是**三重合取**：`trivial0(omegaForm)=1 ∧ trivial1(omegaInfForm)=1 ∧ omegaInfRaw = transitionUnit·omega0O`，其中 transitionUnit = u0^(n−3)。另有 `pi_pullback_lambda`（d(x^n)=n x^{n−1}dx）、`pi_pullback_one_sub_lambda`、`pi_pullback_infinity`、`a5_transition_unit`。
- 这些是**两 chart 局部化数据 + 边界微分**的真实计算；但**没有 sheaf 层同构 Ω ≅ O(n−3)**、没有 transition cocycle 的层粘合、也没有 Omega 与 OmegaInf 的整体比较。`Mzk1G1OmegaLineBundleDataActual` 只是把上述对象装进 `CanonicalLineBundleData` 结构并逐字段重述（`canonicalLineBundleData_a5` 等仍是同一恒等式的搬运）。**不得写“Ω 线丛已构造 / Ω≅O(n−3) 已证”。**

### 4.124 【高·D3】D3Actual 已 DONE 且是真证明，但仍不是 `HeightDictionaryInterface` 的 inhabitant
- `Mzk1G1JHeightD3Actual` 15:57:35 DONE（src 23:56:01 / olean 23:57:35，fresh）。log 3875 B 列出 `Q00N_isHomogeneous`、`QK_isHomogeneous`、`pN_isHomogeneous`、`jBezN_left/right/relation`、`logHeight_jHeight_ge`、`jHeight_relation` 等**全部三公理**；P17 `jHeight_relation` 三公理。这**纠正了 #299 / §2o-3（15:50:30 FAIL，5 条 sorryAx）**：那些定理现在有真实证明（`ring` + `Height.logHeight_eval_le'/ge'` + Bezout 关系）。
- 但 `jHeight_relation` 的陈述是 `abs (jHeight − 6·lambdaHeight) ≤ B`（j-映射的高度比较）；`HeightDictionaryInterface` 要的是 `abs (lambdaHeight − qHeight/6) ≤ B`，其中 qHeight 来自 U-R 的 Tate 参数。**qHeight 仍无构造**，故 D3 接口仍 NO INHABITANT。不得把 `jHeight_relation` 当 D3 接口实例，也不得写“D3 已闭合”。

### 4.125 【高·纪律】ULStepVIII：mtime 通过但内容不对应当前源（新增记录未编译）
- 事实见 §2p-3：16:24:43 编辑加入 `nativeWeightsSum_eq_invDegreeSum` 与 `NativeVsPaperWeightsRecord`（Lead ruling (c) 审计记录），但 16:24:24 START 的编译读的是旧内容，olean 00:25:36 不含这两条；16:25:37 DONE 只覆盖旧内容。**当前源 mtime 00:24:43 < olean 00:25:36，按 §0 第 2 层的 mtime 规则会误判 fresh。** 本批据此把当前源标“内容 STALE”；引用 `uc_c4_of_retained`/`hstepVIII_of_retained` 只能按 00:25:36 olean 的旧内容，且三字段仍无 inhabitant。

### 4.126 【高·纪律】JHeightUniform 是空模块占位，16:15:45 DONE 无数学内容
- 见 §2p-2：`Mzk1G1JHeightUniformActual.lean` 已不存在，`_PlaceholderJHeightUniformActual.lean` 13 行只有 import 和 namespace；olean 3448 B 是空模块。**任何“uniform height 已 DONE”的说法都不成立**；`JHeightUniformProbe` 只是两条 intCast 引理（B infra）。

### 4.127 【中·G-A/π】π⁻¹：15:57:32 只到 overlap opensRange，仍无目标等式；PiPreimageFinal 红
- `Mzk1G1FermatPiPreimageChartActual` DONE 15:57:32（src 23:56:15 / olean 23:57:32）含 3 条：P¹ `overlapToChart0.opensRange = basicOpen X`；Y 侧 `overlapToChart0_opensRange = Spec(Chart0Ring).basicOpen (secOf x0)`；Y 侧 `overlapToChartInf_opensRange = basicOpen (secOf r1)`。P17 只确认第一条三公理。**这些是 carrier/opensRange 桥，不是 `π⁻¹(D_+(X0)) = D(x0^n)`。**
- `Mzk1G1FermatPiPreimageFinalActual` 16:25:00 仍红：首错 **29:6**（`overlapToChartInf = invAuto ≫ overlapToChart0` 的 rewrite motive 依赖 `IsOpenImmersion`，type-correct 失败）、**75:29** 语法 `end`、**64:2** unknown `rw`；后段 62:5/66:6 仍是 `basicOpen` 与 `ΓSpecIso` coercion 不一致。无 olean；**π⁻¹ 具体等式仍无陈述**。

### 4.128 【中·U-R/C2】UCHthetaWiring 是条件接线，不是 θ producer
- `Mzk1UCHthetaWiringActual` DONE 16:03:48（三公理）：`htheta_of_hperB` 就是 #273 `thetaHullLog_le_ucHpkt` 的实例化；`HthetaInput` 是命名 Prop（字段 `htheta`，docstring 明确 PENDING，无 inhabitant）；`uc_c4_of_htheta`/`uc_c4_of_hperB` 把 htheta（或 hperB）+ hstepVIII 作显式假设。**hperB 仍无 producer；不得写“htheta 已接入/θ 已闭合”。**

### 4.129 【中·D2】D2Interface 是接口 + 字段投影，NO INHABITANT
- `Mzk1G1D2InterfaceActual` DONE 16:02:34：`TripodalDictionary` 结构 10 字段（logDiff/dFtpd/fFtpd/dmod/eStar/Cd + 4 条 law），`TripodalDictionary.relations` 只是 `⟨T.logDiff_eq, T.fFtpd_le_conductor, T.dmod_le, T.eStar_le⟩`，`fFtpd_conductor_le` 是字段投影。文件自述 NO INHABITANT。**三公理 ≠ 数学内容**：这是定义自反式搬运，判 **C**，不得当 D2 进展。

### 4.130 【中·G-A】CurveSmooth2：16:13:43 DONE 只覆盖 pderiv/preR2，loc_u2 从未进 olean
- 事实见 §2p-3：olean 含 `pderiv_secondEquation_zero/one`、`span_range_secondEquation`、`preR2`、`naive_jacobian`、`preR2_jacobian`，**不含 `loc_u2_standardSmooth`**；P17 `preR2_jacobian` 三公理。故 16:13:43 DONE 是 **A-局部**（∞ chart 的 pre-submersive presentation + jacobian，及 `u2_v2_span_eq_top` 等），**不是 `(R2 n)[1/u]` standard smooth**。当前源已加 loc_u2 段并红（16:25:04，log 0 B）。**Lead 指定 5 的括号条件“loc_u2 若绿”不成立。**

### 4.131 【中·G-A】CurveSmooth chartSpec 是 affine chart 的 scheme 层 smooth，不是 glued/R2 整体
- 15:55:41 DONE 的 `chartSpec_smoothOfRelativeDimension : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Chart n))))`（P17 三公理）覆盖 **U0 的 affine chart**；`chartRing_locally_standardSmooth` 只给 `algebraMap ℚ (Chart n)` 的 `RingHom.Locally`。**没有 R2 n chart 的 scheme 层 smooth（CurveSmooth2 未交），也没有 Y_n/P¹ glued 的整体 smooth。** 引用时限定“affine λ-chart”。

### 4.132 【低】本窗口其余 DONE 的真实内容与边界
- `Mzk1G1FermatSmoothGAttemptActual`（15:59:28，8 条三公理）：`fermatModelRing = ℚ[x,y,z]/(1+x^n−y^n, (n x^{n−1})z−1)` 是 rel dim 1 standard smooth；**未证它与 `Localization.Away (coordX) (B n)` 同构**，是代数核心。
- `Mzk1ULHviTableLettersActual`（16:00:39，2 条三公理）：`S3014PerLabelBound_eq_paperLetters` 是 `unfold`+`ring` 的字典恒等式；`S3014Exceptional_le_R4` 转调 donor。A-局部。
- `Mzk1ULHviTableActual`（16:22:06，9 条三公理）：`hviTable_of_*`/`badWeighted_*` 是求和/线性记账，依赖 `collectionBound` 的线性性；A-局部 accounting，**不是具体字母实例化**（后者在 Letters）。
- `Mzk1ULStepVDisplayIdentityActual`（16:22:03，8 条三公理）：`sum_Icc_*` 与 `paperDisplay_coefficient_D/Q/T/S` 是初等系数恒等式；**不是完整 Step V display identity**。
- `Mzk1URCollectionLayerActual`（16:20:53）：只有定义（`urCollHullLog`、`urCollLam := fun _ => 1`、`urCollOq`、`urCollLogp`、`urCollIotaL`），log 660 B 也只含 `#print` 定义；**C（定义层）**，无定理。
- `Mzk1G1OmegaRamificationLocalActual`（16:25:02，P17 三公理）：`boundary_zero_uniformizer_power`/`boundary_one_uniformizer_power` 在 (0,1)/(1,0) 局部环证 `x^n = unit·(1−y)`、`y^n = unit·(1−x)`；**A-局部真实 e=n 核心**，∞ 侧 r 未在此文件。
- `Mzk1G1PsiCoverActual`（16:15:44，三公理）：`cover_point`/`opensRange_sup_top` 用 glue data 证 Y_n = U0 ∪ D(q)；A-局部 cover，非全局 ψ。
- `Mzk1SchemeOpensRangeInterfaceActual`（15:53:11，6 条三公理）：`opensRange_coe_eq_range`、`mem_opensRange_iff`、`opens_eq_of_forall_mem`、`opensRange_localizationAway'`、`primeBasicOpen_opensRange_coe` 等 carrier 桥；A-局部 infra。
- `Mzk1ULStepVIPacketAggregationActual`（15:53:39，4 条）：`processionVolume_le_s3014_actual` 无条件转调 donor；`weighted_bad_sum_le` 是 `Finset.sum_le_sum`；`bad_sum_eq_weighted_aggregate` 是 `rfl`（C）。B。

### 4.133 【低·纪律】DONE→改写→FAIL 循环本窗口 4 例，均须按 olean 引用
- 见 §2p-3。另：`Mzk1G1FermatPiPreimageFinalActual` 与 `Mzk1G1ProjectiveLineChartPreimageActual` 当前源均红、无当前 olean；`Mzk1G1FermatCurveSmooth2Actual` 当前源红；`ULStepVIII` 当前源内容未编译。**引用纪律：文件名 + DONE 时间 + olean 时间三者齐备才算证据。**

## 5m. batch 17 立即动作（快照 16:29 UTC）

1. **G-A 收尾（最高）**：直接用 `Mzk1P1ProperFinalActual.p1GluedToBase_isProper` discharge `PiProper.fermatCurveToSpec_isProper_cond` 的 hP1（已做，P17 三公理）；**只剩 `IsFinite (pi n)`**（`isFinite_pi_of_chart_restrict` 的 h0/h1 两条 chart restriction）与 π⁻¹ 具体等式。不得再引 P1ProperAssembly 旧名。
2. **CurveSmooth scheme 层**：15:55:41 的 `chartSpec_smoothOfRelativeDimension`（affine λ-chart）已绿可引；R2 n chart 需修 `CurveSmooth2.loc_u2_standardSmooth`（当前源 16:25:04 红、log 已清；先重编取首错，再按 `comp_jacobian`/`localizationAway_jacobian` 的 `IsUnit` 链检查）。**在 loc_u2 进 olean 前，不得写“R2 chart smooth 已证”。**
3. **D3**：`jHeight_relation` 已是真三公理；下一步必须构造 `HeightDictionaryInterface` 的 `qHeight`（U-R Tate 参数）并证 `abs (lambdaHeight − qHeight/6) ≤ B`；**不得把 j-height 比较当接口实例**。
4. **C2 θ**：UCHthetaWiring 仅接线；`HthetaInput`/`hperB`/`hscale`/`hpacket` 均无 producer。`URThetaHullUpper` 15:52:30 的 `padicFractionalLattice_eq_intCeil` 是 ≤ 路线数值核心，但**主不等式 `actualLocalHullLog b ≤ −thetaCoefficientContribution b` 仍未写/未证**；先写陈述再证。
5. **π⁻¹（henry）**：PiPreimageChart 三条 opensRange 已绿；下一步用 `SchemeOpensRangeInterfaceActual.opensRange_localizationAway'` + `basicOpen_eq_of_affine` 写 `π⁻¹(D_+(X0)) = D(x0^n)`；PiPreimageFinal 的 **29:6** 不要再 `rw` bridge（用 `Scheme.Hom.opensRange_comp_of_isIso`/`change` 到 `Spec (Polynomial ℚ)` 的 Opens），先修 75:29 的 `end` 语法。
6. **G-B**：Omega 两 chart 数据已真；仍需 (a) sheaf 层 `Ω ≅ O(n−3)` 的 transition cocycle，(b) ∞ 侧 ramification 的 `boundary_infinity_uniformizer_power`（本窗口只有 λ=0/1），(c) `BoundaryRamificationIndexObligation` 的 inhabitant（当前 NO INHABITANT）。**不得把 `canonicalLineBundle_data` 当 Ω 整体。**
7. **引用纪律（batch 17 版，强制）**：
   - CurveSmooth 只引 23:55:41 olean（`chartRing_*` + `chartSpec_*`，P17）；PiProper 只引 23:55:39 olean 的 `_cond`；P1ProperFinal 只引 23:53:12（P17）；PiPreimageChart 只引 23:57:32 的 opensRange（非 π⁻¹ 等式）；JHeightD3 只引 23:57:35 的 `jHeight_relation`（非 interface）；CurveSmooth2 只引 16:13:42 olean 的 pderiv/preR2（**无 loc_u2**）；OmegaLineBundle 只引 16:08:36（局部数据）；OmegaLineBundleData 只引 16:13:43（结构与搬运；obligation 无 inhabitant）；OmegaRamificationLocal 只引 16:25:01（λ=0/1）；ULStepVIII 只引 00:25:36 olean 的旧内容（新记录未编译）。
   - D2Interface 是 C；CollectionLayer 是 C（定义层）；JHeightUniform 是空占位（禁引），JHeightUniformProbe 仅 infra；UCHthetaWiring 条件式；HviTable/HviTableLetters/DisplayIdentity 是本地 accounting/初等恒等式；F7 条件式；J3 条件备选；P¹ 无 iso；IsFinite π 差 h0/h1；PiPreimageFinal / ProjectiveLineChartPreimage / CurveSmooth2 当前源红、禁引。

## 6n. batch 17 更新（快照 **16:29 UTC = 2026-11-17 00:29 CST**；覆盖 §6–§6m 的旧结论，旧文保留）

- **已运行（本批）**：`node tools/wd_status.mjs`（24+ 文件）；`node tools/wd_add.mjs`（Probe 17）；watchdog.log 时间窗过滤（15:54:54–16:25:04 全量 + 16:24:24 波尾）；`Get-Item` src/olean/log 对照（30+ 文件）；per-file log 逐个读取（CurveSmooth 997 B、P1ProperFinal 271 B、JHeightD3 3875 B、PiPreimageChart、PiProper 1723 B、OmegaLineBundle 1375 B、OmegaLineBundleData 456 B、D2 281 B、UCHthetaWiring 383 B、HviTableLetters 288 B、ULHviTable 1787 B、CollectionLayer 660 B、DisplayIdentity 1130 B、CurveSmooth2（一度 3211 B 后被清 0）、JHeightUniformProbe 740 B、OmegaRamificationLocal 307 B、FermSmoothGAttempt 1185 B、SchemeOpensRange 883 B、ULStepVIPacket 601 B、PiPreimageFinal 13503 B）；源码阅读（CurveSmooth 152 行、P1ProperFinal 24 行、OmegaLineBundle 156 行、OmegaLineBundleData 119 行、D2 79 行、UCHthetaWiring 144 行、HviTableLetters 61 行、CollectionLayer 98 行、DisplayIdentity 107 行、Placeholder 13 行、JHeightUniformProbe 26 行、JHeightD3 324 行、QHeight 145 行、PsiCover 135 行、PiProper 107 行、PiPreimageChart 54 行、CurveSmooth2 195 行、ULStepVIII 130–378 行、FermSmoothGAttempt 165 行、OmegaRamificationLocal 182 行、ULHviTable 237 行、SchemeOpensRange 55 行、ULStepVIPacket 85 行、ProjectiveLineChartPreimage 61 行）；二进制 olean 名核验（CurveSmooth chartSpec、CurveSmooth2 的 loc_u2 缺失、ULStepVIII 的 nativeWeights 缺失、PiPreimageChart、OmegaRamificationLocal）；grep（`p1GluedToBase_isProper` 仅 P1ProperFinal:18 + PiProper:101 + probes、`HeightDictionaryInterface` 1、`projectiveLineIso` 0、`isFinite_pi_of_chart_restrict` 1、`pi_preimage_eq` 一般式、`DistinguishedScalarData` 无实例）。
- **Probe 17**：8 条 DONE 16:29:30，**全部三公理、0 sorryAx**。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**；仅写本表与 `_ProbeBatch17Actual.lean`。
- **未覆盖 / 未运行（如实标注）**：16:25:04 之后（ULStepVIII 16:25:37、OmegaRamificationLocal 16:25:02 只作尾注；URBadWeightSum/URSmallPrime/ULHviTableFinal 在飞）；CurveSmooth2 当前源首错（log 0 B）；ProjectiveLineChartPreimage 当前源首错（log 0 B）；ULStepVIII 16:24:43 新记录块的编译结果；`Mzk1P1ValuativeUniquenessActual` 207/476 行之外的其余证明未逐行重读；G-K/H-T/P8-P 端到端与 F1–F4/F8 仍未做语义审计。
- **16:25:04 之后**：watchdog 仍在跑；之后的任何 DONE/FAIL 本表未审计。
- 本批写入范围：本表 + **新建** `_ProbeBatch17Actual.lean`；未改其它 Lean 文件。

## 2q. batch 18 gate 表（**评估口径批**；快照 **16:45 UTC = 2026-11-17 00:45 CST**；覆盖 16:25:04–16:42:34，旧行保留）

- 本批只做 Lead 指定 7 项**评估口径**复核 + 新 DONE/FAIL 取证。证据版本一律写 olean 时间；`(P18)` = 本批独立 probe（§3p）。**16:42:34 之后未审计**（`Mzk1G1FermatPiPreimageCloseActual` 仍在重试；`OmegaLineBundleData`、`PsiCover` 仍在飞）。
- 关键新事实：`Mzk1ULStepVIIIActual` **16:41:23 DONE** 已把 16:24:43 的审计记录/等式编进 olean（内容-mtime 陷阱在该 attempt 已解除）；`CurveSmooth2` **16:42:12 DONE** 含 `loc_u2`+`loc_v2`；`PiPreimageFinal` 16:29:27 的 DONE 是**退缩到两条平凡引理**；`PiPreimageClose` 16:42:06 **FAIL**，M-b 仍红。

### 2q-1 Lead 指定 7 项评估口径表

| # | 评估项 | 结论 | 证据（版本/行号） | 处置 |
|---|---|---|---|---|
| 1 | **hγsum 撤回** | **RETRACTED（撤回正确）；PASS** | 全 paper Lean `hγsum`/`gammaSum` grep **0**；决策记录仅存文档：GOAL-PROGRESS 5891/5911/5922/5928/5935、ROUTE-COMPLIANCE §50（301）/314/326；**无活动 consumer**。残留的是旧 `Mzk1ULHviTableActual` 的 `hγ1 : (∑γ)=1`（22–23/51–52/92–93/159–160/218–219），仅文件内使用，Final 已改无归一路线。 | 维持撤回。旧 `badWeighted_le_commonBound`/`hviTable_of_collectionLayer(_logp)` 标 **SUPERSEDED / 不可作 C4 证据**；不要在 Lean 中复活 `hγsum` 名。 |
| 2 | **聚合字母口径** | **PASS（内部会计）/ CONDITIONAL（对 paper）** | `uc_c4_of_retained` LHS = `∑ i, nativeBadLocalWeight T i * B i`（ULStepVIII:386–387）；`PaperStepVIIIRetained.s3014` 同义（105–120）；**无 Σγ=1**。`hstepVIII_of_retained` 现把 `hlogP_le_logSQ` 作显式假设（170–172）。HviTableFinal 16:35:55 `hviTable_final`（P18 三公理）无归一；旧 HviTable 16:22:06 的 5 条 hγ1 定理已由 Final 取代；HviTableLetters 16:00:39 只给 `S3014PerLabelBound_eq_paperLetters`/`S3014Exceptional_le_R4` 字典恒等式。 | 维持聚合字母；**只能写“内部 γ-聚合会计”**，不得写“等价于 paper λ_e/Σλ=d_mod 加权”。paper LHS 若需要严格 λ 权重，另立 conversion task。 |
| 3 | **nativeVsPaperWeights 字段语义** | **CONDITIONAL（named record，NO INHABITANT）** | `Mzk1ULStepVIIIActual:338–354`：`lam`（doc=paper λ_e，IUT IV L1715–1716）、`d_mod`、`paper_lambda_sum : Σλ=d_mod`（L1736–1741）、`hlam_pos`、`c`、`hc_def`。全 paper 仅此 1 处，无实例/构造器。`c` 的精确式由 `urBadWeightSum_eq_invDegree`（16:32:13，P18 三公理）支撑；`d_mod` 在树中只是 opaque 参数（`ExplicitConstantObject.dmod`/`ActualThm110Data.dmod`），**没有 `d_mod=[F_mod:Q]` 的证明**。 | 保留为 audit record；把字段 doc 的 `d_mod = [F_mod:Q]` 改为“paper parameter, unproved”；不得当证明用，不得由它推出 `c=d_mod` 或 `c=1`。 |
| 4 | **s^Q 无定义问题** | **CONDITIONAL（已有实际代理定义；仍非 paper s^Q）** | `Mzk1URSmallPrimeActual` 16:35:52 DONE（olean 16:35:51）：`urSQ X := max 1 ((primes ≤ X).sup id)`（44–45）；`ur_prime_le_sQ`/`ur_log_prime_le_logSQ`/`ur_hlogp_le_logSQ`（67–87）；`ur_badWeightedLogP_le`（95–115，P18 三公理）。**但** `urSQ` 是“最大小素数”代理，不是 paper 的 `s^Q` 常数；`hX : p_b ≤ X` 仍是显式假设；`logP_aggregate_le_logSQ`（ULStepVIII 16:41:23，三公理）只给 `Σγ log p ≤ (Σγ)·log(urSQ X)`。 | 引用一律写 `Mzk1URSmallPrimeActual.urSQ`，不得写“paper s^Q 已定义/已证”。若把 `logSQ` 取 `(Σγ)·log(urSQ X)`，必须同步重述 hiii/hvi；否则退回 paper 单字母 `log s^Q`（仍 retained）。 |
| 5 | **hlogP_le_logSQ retained** | **RETAINED（NO INHABITANT）；未证** | 16:25:37 旧 olean：作 `PaperStepVIIIRetained` 字段（旧源 148 行），`hstepVIII_of_retained` 内 `hmono` 消费；**16:41:23 新 olean**已把它移出结构、作 `hstepVIII_of_retained` 的显式参数（170–172）；`PaperStepVIIIRetained` 仍无 inhabitant。`logP_aggregate_le_logSQ` 只在 `logSQ := (Σγ)·log(urSQ X)` 下给桥，**不是 paper 的 `logSQ`**。 | 维持 RETAINED；`logP_aggregate_le_logSQ` 只能记“rescaled-logSQ 条件桥”；不得写 C4 已闭合/hlogP 已证。 |
| 6 | **uniform D3 占位更正** | **FAIL / NO INHABITANT** | `Mzk1G1JHeightUniformActual.lean` **MISSING**；只有 `_PlaceholderJHeightUniformActual.lean`（436 B / 13 行：2 import + namespace，**0 声明**；16:15:45 DONE 是空模块）。`HeightDictionaryInterface`（`Mzk1G1QHeightActual:40–42`）仍只 1 处 `def Prop`、**无实例**。另有 `Mzk1G1D1ProducerActual:116–137` 的 `D1AnalyticInput.height_dictionary`：`qHeight : ∀ K, K→ℝ`、单一 `B`、`∀ K lam, InKv D lam → |logHeight₁ lam − qHeight K lam/6| ≤ B`——这是**唯一 uniform-in-K D3 形状**，但只是结构字段（NO INHABITANT），`d1_of_analyticInput` 条件消费。`JHeightD3Actual.jHeight_relation`（294–311）是 per-K `∃ B, ∀ lam`（B 由该 K 的 `Cu/Cl` 给出），docstring “over every number field” 不等于 uniform B。 | 更正口径：磁盘无 `Mzk1G1JHeightUniformActual` 内容；只有空占位；`D1AnalyticInput.height_dictionary` 是 uniform D3 的**接口字段**而非交付；`HeightDictionaryInterface` 与 uniform D3 均 **NO INHABITANT**。 |
| 7 | **PiPreimageFinal / M-b** | **FAIL（目标仍红；P¹ 侧已绿）** | `Mzk1G1FermatPiPreimageFinalActual` 16:29:27 DONE（src 00:27:52 / 1697 B / 31 行；olean 00:29:26 / 59776 B）：只有 `piChart0_preimage_chart0`、`piChartInf_preimage_chartInf`（16–30），即“本 chart 的 opensRange 原像 = ⊤”的两条**平凡**引理（P18 三公理）。16:25:00 的 29:6/75:29 是旧 4924 B 版日志，**不是当前文件**。`PiBridge2` 16:32:54 DONE 给 P¹ t-overlap composite；`ProjectiveLineChartPreimage` 16:26:17 DONE 给 P¹ 两侧 cross-chart `localChartInf_preimage_localChart0`/`localChart0_preimage_localChartInf`（P18 一条三公理）。**Y 侧 `pi_preimage_localChart0/Inf` 仍红**：`PiPreimageClose` 16:42:06 FAIL，首错 35:2（ΓSpecIso naturality）/44:6（`evalAt` rewrite）/52:6（basicOpen coercion）/83:36 unknown `image_top_eq_opensRange`/90:12 rewrite。 | M-b = **等 henry 的 π⁻¹ 等式**；P¹ 侧输入可用，Y 侧目标未交。引用 `PiPreimageFinal` 只能写“own-chart preimage=⊤”，不得写 `π⁻¹(D_+(X0))=U0`。 |

### 2q-2 本窗口新增 DONE/FAIL（16:25:04–16:42:34，按 attempt 计）

| # | 文件 | 事件 | 证据 | 判定 |
|---|---|---|---|---|
| 328 | Mzk1G1ProjectiveLineChartPreimageActual | **DONE 16:26:17** | src 00:25:23 / 2916 B；olean 00:26:17 / 124352 B；4 定理：`preimage_opensRange_ι`、`localChartInf_preimage_localChart0`、`localChart0_preimage_localChartInf`、`localChart0_opensRange_sup_localChartInf` | **A-局部（P¹ cross-chart preimage）**。P18 只 probe 第二条（三公理）；另两条源内 #print 未独立取。**P¹ 侧已绿，Y 侧仍缺**。 |
| 329 | Mzk1URSmallPrimeActual | **DONE 16:27:26 → 16:35:52** | src 00:34:09 / 5631 B；olean 00:35:51 / 89584 B | **A-局部（s^Q 代理 + 聚合桥）**。定义 `urSQ`（最大小素数）与 `ur_badWeightedLogP_le`（P18 三公理）；**不是 paper s^Q**（见 §4.137）。 |
| 330 | Mzk1G1FermatPiPreimageFinalActual | **DONE 16:29:27** | src 00:27:52 / 1697 B；olean 00:29:26 / 59776 B | **C（换题/退缩）**：两条 own-chart preimage=⊤ 平凡引理，**非 π⁻¹ 等式**（见 §4.140）。 |
| 331 | Mzk1G1FermatCurveSmooth2Actual | **DONE 16:29:29 → 16:37:59 → 16:42:12** | 终版 src 00:40:23 / 15177 B；olean 16:42:12 / 477776 B；二进制含 `loc_u2_standardSmooth`、`loc_v2_standardSmooth`、`preR2_jacobian` | **A-局部（R2 chart smooth 终版）**：`loc_u2_standardSmooth`/`loc_v2_standardSmooth : Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away (u2/v2 n))`（164–165/222–223）。P18 只 probe `loc_u2`（三公理）；`loc_v2` 仅源内 #print。**更新 #315/#130：R2 chart smooth 现已真实进 olean**。 |
| 332 | Mzk1URBadWeightSumActual | **DONE 16:32:13** | src 00:30:28 / 3463 B；olean 00:32:12 / 31352 B | **A-局部**：`urBadWeightSum_eq_invDegree`（P18 三公理）、`urBadWeightSum_nonneg`；`BadWeightTotalEqDmod`/`BadWeightedLogPBridge` 是命名 Prop，**NO INHABITANT**。 |
| 333 | Mzk1G1FermatPiBridge2Actual | **DONE 16:32:54** | src 00:31:27 / 1690 B；olean 00:32:54 / 20704 B；`p1_overlapToChartInf_composite` | **B（P¹ 侧桥）**：composite opensRange = basicOpen X；未独立 probe；无 π⁻¹ 目标。 |
| 334 | Mzk1ULHviTableFinalActual | **DONE 16:33:23 → 16:35:55** | src 00:34:05 / 7316 B；olean 00:35:54 / 165688 B | **A-局部（无归一聚合会计）**：`hviTable_final`（P18 三公理）、`hV_of_collectionLayer`、`hviTable_of_collectionLayer'`；纯会计，不证明 paper λ 权重。 |
| 335 | Mzk1G1OmegaRamificationInfinityActual | **DONE 16:36:37** | src 00:33:09 / 8076 B；log 含 `boundary_infinity_uniformizer_power` 三公理 | **A-局部（G1-B ∞ 侧）**：`boundary_infinity_uniformizer_power` 三公理（自身 #print）；补 λ=0/1 之外的 ∞ 侧 ramification 幂。未独立 probe。**不是 `BoundaryRamificationIndexObligation` 的 inhabitant**。 |
| 336 | Mzk1ULStepVIIIActual | **DONE 16:41:23** | src 00:40:15 / 20695 B；olean 00:41:22 / 1540328 B；二进制含 `nativeWeightsSum_eq_invDegreeSum`、`NativeVsPaperWeightsRecord`、`logP_aggregate_le_logSQ`；log 7 条全三公理 | **B（retained 装配 + 新审计记录）**。16:25:37 旧 olean 的“新记录未编译”已被 16:41:23 取代；`hstepVIII_of_retained` 现多一个显式 `hlogP_le_logSQ` 假设（170–172）；三字段仍 NO INHABITANT；C4 仍条件式。 |
| 337 | Mzk1G1FermatPiPreimageCloseActual | **FAIL 16:40:51 / 16:42:06** | src 00:41:33 / 5189 B；**无 olean**；首错 35:2/44:6/52:6/83:36/90:12 | **R（M-b 近失）**：目标 `pi_preimage_localChart0`（78–96）未编译；`pi_preimage_localChartInf` 尚未写。修 83 的限定名/35–52 的 coercion 后再谈 DONE。 |
| 338 | Mzk1G1ProjectiveLineGluedActual | **DONE 16:36:37** | olean 00:36:37 / 158400 B；新增 `overlapToChartInf_opensRange_eq_composite` | **A-局部 infra**。注意：`ProjectiveLineChartPreimage` 的 olean 16:26:17 早于该次重建；若只新增引理则无碍，**但下游引用须按名核**。 |
| 339 | Mzk1G1PsiCoverActual | 反复 FAIL（16:34:07 等） | 旧 DONE olean 16:15:44；当前源仍改 | **R（当前源）**：旧 `cover_point`/`opensRange_sup_top` 仅对 16:15:44 olean 可引；当前源红。 |

### 2q-3 缺口表（16:45 口径；旧 §2p-1 保留）

| 缺口 | 当前证据 | 状态 |
|---|---|---|
| hγsum / Σγ=1 | 决策撤回；Lean 无 `hγsum`；旧 HviTable 仍有 5 条 hγ1 定理，无外部 consumer | **RETRACTED；残留代码 SUPERSEDED** |
| U-C Step VIII LHS | `uc_c4_of_retained` LHS = `∑ nativeBadLocalWeight·B`；`hstepVIII_of_retained` 显式要 `hlogP_le_logSQ`；三字段（hiii/hviTable/hvii）无 inhabitant | **γ-聚合口径 ✓；hlogP retained；C4 条件式** |
| paper λ/d_mod 加权 | `NativeVsPaperWeightsRecord` 仅结构，无 inhabitant；`d_mod=[F_mod:Q]` 未证；`c=d_mod`/`c=1` 均未证 | **仅 named record；CONDITIONAL** |
| s^Q | `urSQ` 已定义（最大小素数代理）；`ur_badWeightedLogP_le` 三公理；`logP_aggregate` 给 `(Σγ)·log(urSQ)` | **代理 ✓；paper s^Q 无定义/无识别** |
| hlogP_le_logSQ | 16:41:23 起为 `hstepVIII_of_retained` 显式参数；无 producer；rescaled 版才有桥 | **RETAINED（NO INHABITANT）** |
| uniform D3 / HeightDictionaryInterface | `G1JHeightUniformActual` MISSING；`_Placeholder` 空；`HeightDictionaryInterface` 1 def 无实例；`D1AnalyticInput.height_dictionary` 仅字段 | **NO INHABITANT / 未交付** |
| π⁻¹(D_+(X0)) / M-b | P¹ 侧 ChartPreimage 16:26:17 ✓；Y 侧 `PiPreimageFinal` 仅平凡；`PiPreimageClose` 16:42:06 FAIL | **P¹ ✓ / Y 侧 R；M-b open** |
| R2 chart smooth | `CurveSmooth2` 16:42:12 `loc_u2`/`loc_v2` 进 olean；`loc_u2` P18 三公理 | **A-局部 CLOSED（两 chart）** |
| IsProper / Y_n proper / IsFinite π | `p1GluedToBase_isProper` 三公理；`fermatCurveToSpec_isProper_cond (hfin)`；h0/h1 仍缺 | **IsProper CLOSED；Y_n 只差 hfin** |
| G-B Ω / boundary obligation | Ω 两 chart 数据；`BoundaryRamificationIndexObligation` NO INHABITANT；Ω 全局/`Ω≅O(n−3)` 未证 | **局部 / NO INHABITANT** |
| P¹ 三模型 | 无 iso | **禁复合（不变）** |
| 删除件 | P1ProperAssembly / F7Sep / P1Separated MISSING | **禁引（不变）** |

### 2q-4 内容-mtime / 版本陷阱（本批更正）

- **ULStepVIII 的“内容 STALE”已解除（16:41:23）**：16:25:37 旧 olean（00:25:36 / 1396920 B）确实不含 16:24:43 加入的 `nativeWeightsSum_eq_invDegreeSum`/`NativeVsPaperWeightsRecord`；16:34:38、16:37:08 两次 FAIL；**16:41:23 DONE 的新 olean（00:41:22 / 1540328 B）二进制含全部新名**，log 7 条三公理。**此前的“新记录未编译”只适用于 16:25:37 attempt，不得再引旧结论。**
- **但签名变了**：16:41:23 版 `hstepVIII_of_retained` 多一个显式 `(hlogP_le_logSQ : P.logP ≤ P.logSQ)`（170–172），且 `PaperStepVIIIRetained` 已无该字段。引用必须写“16:41:23 版”；16:25:37 的 3 字段+字段版不可混用。
- **CurveSmooth2 终版**：16:37:59 olean 已含 `loc_u2_standardSmooth`；16:42:12 再重建为 477776 B，二进制含 `loc_u2`+`loc_v2`。P18 的 `loc_u2` 三公理是 16:42:12 olean（probe DONE 16:42:34），不是 16:13:42 的 preR2 子集。
- **PiPreimageFinal 旧日志陷阱**：16:25:00 的 13503 B 日志（29:6/75:29）属于旧 4924 B 版；当前 31 行版 16:29:27 DONE，ole 00:29:26，二进制含 `piChart0_preimage_chart0`/`piChartInf_preimage_chartInf`。**不得把 29:6/75:29 当当前文件首错。**
- **PiPreimageClose 无 olean**：16:42:06 FAIL 的日志是当前 attempt；修前不得引 `pi_preimage_localChart0`。
- **PsiCover 当前源红**：旧 16:15:44 DONE 只对旧 olean；当前源 16:34:07 FAIL，引用须写 olean 时间。

## 3p. Probe 18（本批 batch 18）：`tmp/sheaf/xif/paper/_ProbeBatch18Actual.lean`

- `node tools/wd_add.mjs` 16:41 排队（total 177）→ **START 16:41:37 → DONE 16:42:34（57 s）**；log 6 条，**0 error / 0 sorryAx**，全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | 证据版本（olean） / gate |
|---|---|---|
| `Mzk1ULHviTableFinalActual.hviTable_final` | [propext, Classical.choice, Quot.sound] | 16:35:54（#334；无 Σγ=1） |
| `Mzk1URSmallPrimeActual.ur_badWeightedLogP_le` | [propext, Classical.choice, Quot.sound] | 16:35:51（#329；s^Q 聚合） |
| `Mzk1URBadWeightSumActual.urBadWeightSum_eq_invDegree` | [propext, Classical.choice, Quot.sound] | 16:32:12（#332；Σγ=逆次数） |
| `Mzk1G1ProjectiveLineChartPreimageActual.localChartInf_preimage_localChart0` | [propext, Classical.choice, Quot.sound] | 16:26:17（#328；P¹ cross-chart） |
| `Mzk1G1FermatPiPreimageFinalActual.piChart0_preimage_chart0` | [propext, Classical.choice, Quot.sound] | 16:29:26（#330；平凡 own-chart） |
| `Mzk1G1FermatCurveSmooth2Actual.loc_u2_standardSmooth` | [propext, Classical.choice, Quot.sound] | 16:42:12（#331；R2 chart） |

- 版本纪律：6 条均按 probe 时刻磁盘 olean 复算；`loc_u2_standardSmooth` 是 16:42:12 版，`piChart0_preimage_chart0` 是 16:29:26 平凡版；**未运行** `lake env lean`、未自起 watchdog、未写 sorry/axiom、未 spawn_teammate。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 18 续）

### 4.134 【高·纪律】hγsum 撤回正确；残留 Σγ=1 代码必须标 SUPERSEDED
- 决策层已撤回（ROUTE-COMPLIANCE §50）；Lean 全仓无 `hγsum`/`gammaSum` 声明，**无活动 consumer**。但 `Mzk1ULHviTableActual`（16:22:06 olean）仍导出 5 条带 `hγ1 : (∑γ)=1` 的定理（22–23/51–52/92–93/159–160/218–219），包括 `badWeighted_le_commonBound`、`hviTable_of_collectionLayer(_logp)`。它们**不是** C4 活动路线（Final 用无归一的 `hviTable_final`），但代码未删/未 deprecate，易被误引。**不得把这些定理当 hγsum 的替代证据，也不得再要求 Σγ=1。**

### 4.135 【高·口径】聚合字母路线是内部会计，不是 paper λ_e/d_mod 加权
- `hviTable_final`（P18 三公理）与 `hstepVIII_of_retained` 的 LHS 是 `Σ_b nativeBadLocalWeight b · V_b`（`uc_c4_of_retained`:386–387），无归一化；`s3014` doc 明确 no sum_gamma=1。**内部一致**。
- 但 paper 的 Step (viii) 用 `λ_e := [(F_mod)_v : Q_{vQ}]`、`Σ_e λ_e = d_mod`（IUT IV L1715–1741），本路线用 `γ_b = 1/[K_w:F_v]`，两者一般不同；**没有定理说 γ-聚合等于 paper λ-加权**。`NativeVsPaperWeightsRecord` 只是并排放两个族。**引用时只能写“γ-聚合会计”，不得写“Step (viii) paper display 已证”。**

### 4.136 【中·接口】NativeVsPaperWeightsRecord 无 inhabitant，`d_mod` 注释越界
- 结构 6 字段（`lam/d_mod/paper_lambda_sum/hlam_pos/c/hc_def`）在 16:41:23 olean 中；全 paper 仅 1 处、无实例。`c = Σ nativeBadLocalWeight` 由 `urBadWeightSum_eq_invDegree`（P18 三公理）支撑；`d_mod` 在树中只是 opaque 参数（`ExplicitConstantObject.dmod` / `ActualThm110Data.dmod : Nat`），**没有 `d_mod = [F_mod:Q]` 的证明**；`c=d_mod`、`c=1` 也都未证（`BadWeightTotalEqDmod` 是命名 Prop，NO INHABITANT）。
- 结构 `lam` 只索引 `Bad`（若 paper e 范围更大，则 index 可能不匹配）；`paper_lambda_sum` 是字段约束而非定理。**保留为 record；修正 doc 的过度断言；不得当证明。**

### 4.137 【高·s^Q】`urSQ` 是“最大小素数”代理，不是 paper s^Q；logSQ 出现两种缩放
- `urSQ X = max 1 (sup (primes ≤ X))`（44–45），故 `ur_prime_le_sQ` 本质是 `p ≤ max`；`ur_hlogp_le_logSQ` 只把 `p_b ≤ X` 转成 `log p_b ≤ log(urSQ X)`；`ur_badWeightedLogP_le` 只给 `Σγ log p ≤ (Σγ)·log(urSQ X)`。**paper 的 `log s^Q` 仍只是抽象 `logSQ`。**
- **冲突点**：ULStepVIII 的 `hiii` 用单字母 `logSQ`（`(4/l)·logSQ`），而 `hlogP` 桥需要 `(Σγ)·log(urSQ X)`。若把 `logSQ` 取后者，hiii/hvi 的 paper 系数含义被改；若取前者，`logP_aggregate_le_logSQ` 不能给 `hlogP_le_logSQ`（除非 Σγ=1，已撤回）。**这是 C4 仍未闭合的真实口径缺口，不得用“s^Q 已落地”掩盖。**

### 4.138 【中·retained】hlogP_le_logSQ 从结构字段变为显式假设，仍无 producer
- 16:25:37 版：`PaperStepVIIIRetained.hlogP_le_logSQ` 字段；16:41:23 版：移出结构，作 `hstepVIII_of_retained` 的参数（170–172），`hmono` 消费（186–197）。两版都**没有 inhabitant/producer**；`PaperStepVIIIRetained` 本身也无实例。`logP_aggregate_le_logSQ` 只对 rescaled `logSQ` 成立。**维持 RETAINED；C4 仍是条件式。**

### 4.139 【高·D3】uniform D3 是空占位 + 接口字段，不是交付
- `Mzk1G1JHeightUniformActual.lean` MISSING；`_PlaceholderJHeightUniformActual.lean` 436 B 只有 import/namespace，**0 声明**；16:15:45 DONE 是空模块。
- 唯一 uniform-in-K 形状是 `D1AnalyticInput.height_dictionary`（D1Producer 116–137，单一 B），但它只是结构字段，`d1_of_analyticInput` 条件消费，**NO INHABITANT**。`HeightDictionaryInterface`（G1QHeight 40–42）仍是 per-K `def Prop`、无实例。`jHeight_relation`（D3Actual 294–311）是 per-K `∃ B`（B 由 `Cu/Cl` 定），docstring “over every number field” 不可读成 uniform B。
- **更正口径**：不能说“uniform D3 只有占位所以完全没形状”；准确说法是“无 uniform 定理/无 inhabitant；只有 D1AnalyticInput 的接口字段和空占位”。

### 4.140 【高·换题】PiPreimageFinal 16:29:27 是退缩，不是 π⁻¹ 等式
- 当前 31 行文件只证 `(piChart0 n) ⁻¹ᵁ localChart0.opensRange = ⊤` 与 `(piChartInf n) ⁻¹ᵁ localChartInf.opensRange = ⊤`（16–30）；证明用 `image_top_eq_opensRange` + `preimage_image_eq`，本质是 `f⁻¹(f(⊤))=⊤`。**没有 `π⁻¹(D_+(X0)) = U0`，没有 `π⁻¹(A¹_t)=U1`，也没有 cross-chart Y 侧原像。**
- 16:25:00 旧 4924 B 版的 29:6/75:29 是另一 attempt，当前文件已绕过；**不得把 16:29:27 DONE 写成 G-A π⁻¹ 已交。**

### 4.141 【高·M-b】PiPreimageClose 是真实近失：目标已写出，但 5 处红
- `PiPreimageClose` 78–96 的 `pi_preimage_localChart0` 是正确目标（λ chart 原像 = U0），用 `pi_preimage_eq` + `piChart0_preimage_chart0` + `piChartInf_preimage_chart0` + `overlapImage_le_chart0`。但 16:42:06 FAIL：35:2 ΓSpecIso naturality 类型不匹配、44:6 `evalAt` rewrite 不匹配、52:6 `basicOpen` 与 `Spec` carrier coercion 不一致、83:36 unknown `image_top_eq_opensRange`（应为 `...localChart0.image_top_eq_opensRange` 的限定名）、90:12 rewrite 找不到 `overlapToChartInf.opensRange`。**无 olean；M-b 仍 open。**
- P¹ 侧 `localChartInf_preimage_localChart0`/`localChart0_preimage_localChartInf` 已 DONE（16:26:17，P18 一条三公理），所以 M-b 现在只差 Y 侧 cross-chart/union 的 coercion 收尾；`pi_preimage_localChartInf`（t 侧）尚未写。

### 4.142 【中·新 DONE 边界】CurveSmooth2 / OmegaRamificationInfinity / ProjectiveLineChartPreimage
- `CurveSmooth2` 16:42:12：`loc_u2_standardSmooth`/`loc_v2_standardSmooth` 均进 olean（二进制），`loc_u2` P18 三公理；**R2 chart smooth 两 chart 已真实可引**。`loc_v2` 未独立 probe（仅源内 #print）。更新 #315/#130 的“loc_u2 从未进 olean”。
- `OmegaRamificationInfinity` 16:36:37：`boundary_infinity_uniformizer_power` 三公理（自身 #print），补 ∞ 侧 ramification；**不是 `BoundaryRamificationIndexObligation` 的 inhabitant，也不是 Ω 全局。**
- `ProjectiveLineChartPreimage` 16:26:17：P¹ 两 chart cross-preimage + cover；P18 一条三公理。**这是 M-b 的可用输入，不是 M-b 本身。**

### 4.143 【低·纪律】旧 attempt 日志/旧 olean 仍是本窗口最大误引源
- `PiPreimageFinal` 旧 13503 B 日志、`ULStepVIII` 16:25:37 旧 1396920 B olean、`CurveSmooth2` 16:13:42 子集 olean、`PsiCover` 16:15:44 旧 DONE、`ProjectiveLineGlued` 16:36:37 重建，均已不是当前内容。**引用必须“文件名 + DONE 时间 + olean 时间”三者齐备**；本表新增的 16:41:23/16:42:12 是当前口径。

## 5n. batch 18 立即动作（快照 16:45 UTC）

1. **hγsum（纪律）**：维持 RETRACTED；不要新增/复活 `hγsum`。旧 `Mzk1ULHviTableActual` 的 5 条 `hγ1` 定理标 SUPERSEDED；若 Lead 要彻底防误引，下一步可把它们改名为 `*_of_sumGammaEqOne` 并加 doc“仅历史，不在 C4 路线”。
2. **聚合字母口径**：保持 γ-聚合/无归一；所有报告写“内部会计”，不写“paper λ/d_mod 加权已证”。若 H-T 需要严格 paper LHS，另立 `nativeVsPaperWeights` conversion task（不是本批）。
3. **NativeVsPaperWeightsRecord**：保留为 audit record；把 `d_mod = [F_mod:Q]` 的 doc 改为“paper 参数，树中未证”；`c=d_mod`/`c=1` 保持命名 Prop；**不构造假 inhabitant**。
4. **s^Q**：把 `urSQ` 明确标为“模型代理（最大小素数）”，不是 paper `s^Q`；先决定 `logSQ` 用 paper 单字母还是 `(Σγ)·log(urSQ X)`，再重述 hiii/hvi。`ur_badWeightedLogP_le` 只作聚合桥；**不得写“s^Q 已定义 ⇒ hlogP 已证”**。
5. **hlogP_le_logSQ**：保持显式 retained 假设；`logP_aggregate_le_logSQ` 只对 rescaled `logSQ` 有效；C4 仍条件于 hiii/hvi/hvii/hlogP + htheta。
6. **uniform D3**：不要引 `Mzk1G1JHeightUniformActual`；`_Placeholder` 是空模块。若要做 uniform D3，需构造 `D1AnalyticInput.qHeight` + 单一 `B` 的 inhabitant（或 `HeightDictionaryInterface` 实例）；`jHeight_relation` 只是 per-K。
7. **PiPreimage / M-b（henry，最高优先）**：`PiPreimageClose` 先修 35:2（`ΓSpecIso_inv_naturality` 的 coercion）、44:6（`evalAt` 用 `show`/`change` 而非 `rw`）、52:6（`basicOpen_eq_of_affine` 统一 carrier）、83:36（限定 `Mzk1G1ProjectiveLineGluedActual.localChart0.image_top_eq_opensRange`）、90:12（先 `rw [← overlapToChartInf_opensRange]` 或 `change`）。**`pi_preimage_localChart0` 转绿后再写 `pi_preimage_localChartInf`；在 olean 出现前 M-b 仍 open。**
8. **CurveSmooth2**：`loc_u2`/`loc_v2` 16:42:12 已可引（loc_u2 P18）；若需 scheme 层/glued smooth，另做 `Spec`/glue 装配，不要从 ring-level 直接跳。
9. **ULStepVIII**：引用一律 16:41:23 版（1540328 B olean）；`hstepVIII_of_retained` 多 `hlogP` 参数；`nativeWeightsSum_eq_invDegreeSum`/`logP_aggregate_le_logSQ` 三公理可引，但 `NativeVsPaperWeightsRecord` 仍只是 record。
10. **版本纪律（强制）**：旧 16:25:37/16:29:29/16:13:42/16:15:44 的 DONE 不再代表当前内容；`PiPreimageClose`、`PsiCover` 当前源红；`ProjectiveLineChartPreimage` 16:26:17 的 olean 早于 `ProjectiveLineGlued` 16:36:37 重建，引用时按声明名核（新增 composite 引理不影响旧声明）。

## 6o. batch 18 更新（快照 **16:45 UTC = 2026-11-17 00:45 CST**；覆盖 §6–§6n 的旧结论，旧文保留）

- **已运行（本批）**：`Get-Item` src/olean 对照（15+ 文件）；二进制 olean 符号核验（ULStepVIII 新记录、CurveSmooth2 loc_u2/loc_v2、PiPreimageFinal、ChartPreimage、HviTableFinal、URSmallPrime、URBadWeightSum）；`node tools/wd_add.mjs`（Probe18，total 177）；watchdog.log 按 attempt 过滤（16:25–16:42）；per-file log 读取（Probe18 6 条、ULStepVIII 7 条、PiPreimageClose 5 错、PiBridge2、URSmallPrime、ULHviTableFinal、PiPreimageFinal 旧日志、OmegaRamificationInfinity）；源码阅读（ULStepVIII 全文、ULHviTableFinal、ULHviTable、HviTableLetters、URSmallPrime、URBadWeightSum、PiPreimageFinal、PiPreimageClose、PiPreimageChart、PiPreimageActual、ProjectiveLineChartPreimage、CurveSmooth2 关键段、QHeight、D1Producer、JHeightD3、Placeholder、Probe）；grep/Select-String（`hγsum` 0、`hγ1` 5 处、`HeightDictionaryInterface` 1、`NativeVsPaperWeightsRecord` 1、`PaperStepVIIIRetained` 无构造、`hlogP_le_logSQ` 位置）。
- **Probe 18**：6 条 DONE 16:42:34，全部三公理、0 error/0 sorryAx。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**。
- **未覆盖 / 未运行（如实标注）**：16:42:34 后的新事件（PiPreimageClose 重试、OmegaLineBundleData、PsiCover、ULStepVIII 再改）；`loc_v2_standardSmooth` 未独立 probe；`PiBridge2`、`OmegaRamificationInfinity`、`ChartPreimage` 其余定理未独立 probe；`ProjectiveLineGlued` 16:36:37 的 diff 未逐行审；G-K/H-T/P8-P 端到端与 F1–F4/F8 仍未做语义审计；未重读 paper 原文（行号 provenance 沿用既有记录）。
- 本批写入范围：本表 + **新建** `_ProbeBatch18Actual.lean`；未改其它 Lean 文件；未删旧行。

### 2q-5 快照后补记（**16:44:16–16:46:18**；**覆盖 §2q-1 第 7 行、#337、§4.140–§4.141 的“M-b open”结论**；旧行保留）

- **16:44:16 PiPreimageClose DONE（重大）**：src 00:43:37 / 5226 B；olean 00:44:16 / 169696 B。二进制含 `pi_preimage_localChart0`、`piChartInf_preimage_chart0`、`overlapImage_le_chart0`；**不含** `pi_preimage_localChartInf`。16:42:06 的 FAIL 日志（35:2/44:6/52:6/83:36/90:12）是**上一 attempt 的旧日志**（DONE 不覆盖 FAIL 日志），不得再当当前首错。
- **Probe 18b（本批补）**：`_ProbeBatch18bActual.lean` 16:45:50 排队 → **DONE 16:46:18（27 s）**；2 条均 **[propext, Classical.choice, Quot.sound]**：`Mzk1G1FermatPiPreimageCloseActual.pi_preimage_localChart0`、`…piChartInf_preimage_chart0`。
- **M-b 更正口径**：`pi_preimage_localChart0 : (pi n) ⁻¹ᵁ localChart0.opensRange = (fermatChart0ToCurve n).opensRange`（Close 78–80）已真实编译、三公理；**π⁻¹(A¹_λ)=U0 的 λ 侧闭合**。但 t 侧 `pi_preimage_localChartInf` **尚未写/未编译**（二进制 false），所以 M-b 不是“全开”，也**不是“全闭”**：**λ 侧 CLOSED / t 侧 open**。不得写“M-b 已全交”，也不得再写“M-b 全红”。
- **对 §2q-1 第 7 行的覆盖**：PiPreimageFinal 16:29:27 仍只是两条平凡引理（不是目标）；真正目标是 Close 16:44:16 的 `pi_preimage_localChart0`。P¹ 侧（ChartPreimage 16:26:17）+ Y 侧 λ 半（Close 16:44:16）现已齐；t 侧仍等 henry。
- **对 §4.141 的覆盖**：35/44/52/83/90 五处红已被 16:44:16 的源码修过并 DONE；下一步不是修 λ 侧，而是写 `pi_preimage_localChartInf`（对称地用 `pi_preimage_eq` + `piChartInf_preimage_chartInf` + `piChart0_preimage_chart0` + `overlapImage_le_chartInf` 一类引理），并核 `Chart0Ring/ChartInfRing` 的 symmetric coercion。
- **新事件编号**：#340 `Mzk1G1FermatPiPreimageCloseActual` **DONE 16:44:16**（A-局部/λ 侧；P18b 三公理）；#341 `Mzk1G1PsiGlobalActual` DONE 16:44:16（未审，G1-B 全局 ψ 候选，另行取证）。
- **立即动作追加（高于 §5n 第 7 条）**：henry 只需写 t 侧 `pi_preimage_localChartInf`；λ 侧可引 `Mzk1G1FermatPiPreimageCloseActual.pi_preimage_localChart0`（16:44:16，三公理）。引用 Close 时不要用 16:42:06 的旧 FAIL 日志。

## 6p. batch 18 最终口径（16:46 UTC = 00:46 CST；覆盖 §6o 的“16:42:34 后未审计”）

- 本批最终证据截止 **16:46:18**（Probe18b DONE）。新增已审事件：Probe18 16:42:34、OmegaRamificationInfinity 16:36:37、ULStepVIII 16:41:23、CurveSmooth2 16:42:12、PiPreimageClose 16:44:16、Probe18b 16:46:18。
- 7 项最终判定：1 hγsum **RETRACTED/PASS**；2 聚合字母 **PASS 内部 / CONDITIONAL paper**；3 NativeVsPaperWeights **CONDITIONAL/no inhabitant**；4 s^Q **CONDITIONAL（urSQ 代理）**；5 hlogP **RETAINED**；6 uniform D3 **FAIL/no inhabitant**；7 M-b **λ 侧 PASS（Close 16:44:16 三公理）/ t 侧 open**。
- 16:46:18 之后未审计；`Mzk1G1PsiGlobalActual`、`Mzk1HT81InterfaceActual`、`Mzk1G1ConductorDifferentCancellationActual` 等新事件留待 batch 19。

### 2q-6 t 侧补记（**16:46:18 Close2 FAIL，sorryAx**；覆盖 §2q-5 的“t 侧 open”细节）

- **新文件 `Mzk1G1FermatPiPreimageClose2Actual`**（src 00:45:27 / 4647 B；**无 olean**）试图对称给出 `pi_preimage_localChartInf : (pi n) ⁻¹ᵁ localChartInf.opensRange = (fermatChartInfToCurve n).opensRange`；**16:46:18 FAIL**。
- 首错：**30:35 unknown identifier `preimage_specMap_basicOpen`**（该 helper 在 `Mzk1G1FermatPiPreimageCloseActual` 命名空间内，Close2 未 `open` 也未限定）；**27:77 unsolved goals**（`Spec.map (evalAt (x0^n)) ⁻¹ᵁ basicOpen X` 仍是未闭合目标）；**85:14 unknown constant `pi_preimage_localChart0`**（#print 未限定命名空间）。
- **关键风险**：log 末行 `'…pi_preimage_localChartInf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]`——即该定理在错误恢复下带 **sorryAx**，**不是有效证明**，永不可引。t 侧仍 open；M-b 仍是 **λ 侧 CLOSED / t 侧 open**。
- 修法（henry）：在 Close2 中 `open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageCloseActual`（或把 `preimage_specMap_basicOpen` 限定为 `…CloseActual.preimage_specMap_basicOpen`）；27 行先 `rw [preimage_specMap_basicOpen]` 再 `simp only [CommRingCat.hom_ofHom, evalAt_X]` 消除 unsolved；#print 用全限定名。**重编 DONE 且 #print axioms 无 sorryAx 前，不得写 t 侧已交。**
- 本补记后最终口径不变：7 项中第 7 项 = **λ 侧 PASS（Close 16:44:16，P18b 三公理）/ t 侧 open（Close2 16:46:18，sorryAx）**；其它 6 项同 §6p。

## 2r. batch 19 gate 表（快照 **16:58 UTC = 2026-11-17 00:58 CST**；覆盖 16:46:18–16:57:38；旧行全保留）

- 证据版本：src/olean 均 `Get-Item` 实测；`(P19)` = §3q 独立 probe 复算；每文件日志按 attempt 读取。**16:57:38 之后未审计**（watchdog 仍在跑）。
- 本窗口全量事件（按 attempt）：16:46:18 Close2 FAIL（旧 attempt，末行 sorryAx）；16:46:59 PsiGlobal FAIL；16:47:01 ConductorDifferentCancellation DONE；16:47:43 Close2 DONE；16:49:23 ULStepVIII FAIL（旧 attempt，`hstepVIII_of_collectionLayer` 带 sorryAx）；16:50:10/11/12 PsiGlobal / Close2 / PiFiniteChart / ConductorDifferentCancellation 四 DONE；16:51:31 ULStepVIII DONE；16:51:43 HviTableInstance FAIL（isDefEq timeout + 临时 sorry）；16:52:27 PiFiniteChart FAIL；16:52:29 ConductorCore FAIL；16:52:53 ThetaHullTensor FAIL；16:52:56 **Probe19 DONE**；16:53:40 GlueCocycle DONE；16:53:41 JHeightUniform FAIL（log 0）；16:54:16 ULStepVIII 再 DONE；16:55:06 PsiGlobal FAIL / PiRestrictFinite FAIL；16:55:08 JHeightUniform DONE；16:55:09 Core FAIL；16:55:36 ThetaHullTensor FAIL；16:55:38 HviTableInstance DONE；16:56:23 HT81Interface DONE；16:56:25 PsiGlobal / PiRestrictFinite / PiFiniteChart FAIL；16:56:52 ThetaHullTensor DONE；16:57:36 PiFiniteChart FAIL；16:57:38 Core FAIL。

### 2r-1 Lead 指定 10 项复核（判定按当前 olean，不按旧日志）

| # | 指定项 | 最新证据（src / olean / log） | 判定 / 处置 |
|---|---|---|---|
| 1 | **PiPreimageClose λ 侧** | src 00:43:37 / 5226 B；olean **00:44:16** / 169696 B；P18b 两条打印均三公理（`pi_preimage_localChart0`、`piChartInf_preimage_chart0`）；P19 未重复（同一 olean） | **A-局部 CLOSED（λ 侧）**。可引 `Mzk1G1FermatPiPreimageCloseActual.pi_preimage_localChart0`；不得引 16:42:06 旧 FAIL 日志。 |
| 2 | **Close2 t 侧（关键翻转）** | 16:46:18 FAIL 的末行 `pi_preimage_localChartInf ⇒ [propext, sorryAx, …]` 是**旧 attempt**；源码修后 **16:47:43 DONE、16:50:10 再 DONE**；src 00:49:15 / 4765 B；olean **00:50:10** / 133800 B；log 293 B：`pi_preimage_localChart0` 与 `pi_preimage_localChartInf` **均三公理**；二进制无 `sorryAx`；**P19 三公理** | **A-局部 CLOSED（t 侧）**。任务前提「16:46:18 t 侧 sorryAx、禁引」**已被 16:50:10 覆盖**：**不得再写 t 侧带 sorryAx/禁引**；引用写 `Mzk1G1FermatPiPreimageClose2Actual.pi_preimage_localChartInf`（16:50:10 olean）。 |
| 3 | **CurveSmooth2** | src 00:40:23 / 15177 B；olean **16:42:12** / 477776 B；log 3400 B 八条打印**全部三公理**：`loc_u2_standardSmooth`、`loc_v2_standardSmooth`、`chartRing2_locally_standardSmooth`、`chartSpec2_smoothOfRelativeDimension`、`preR2_jacobian` 等；P18 `loc_u2`、**P19 `loc_v2`** | **A-局部 CLOSED（R2 两 chart）**。attempt 序列：16:13:43（仅 preR2 子集）→ 16:29:29 → 16:37:59 → 16:40:07 → **16:42:12 终版**（`loc_u2`/`loc_v2` 均进 olean）。引用写 16:42:12 olean。 |
| 4 | **OmegaRamificationInfinity** | src 00:35:22 / 8151 B；olean **16:36:37** / 439136 B；**P19 `boundary_infinity_uniformizer_power` 三公理**；源内另有 `≤` 侧 | **A-局部（G1-B ∞ 侧 e=n）**。一般 K 上 `r^n = unit·(s−ζ)`；**不是 `BoundaryRamificationIndexObligation` 的 inhabitant，也不是 Ω 全局**。 |
| 5 | **URSmallPrime** | src 00:34:09 / 5631 B；olean **16:35:51** / 89584 B；P18 `ur_badWeightedLogP_le` 三公理；`urSQ X = max 1 (sup primes≤X)` | **A-局部（s^Q 代理）**。`urSQ` 是「最大小素数」模型代理，**不是 paper 的 s^Q 常数**；`hX : p_b ≤ X` 仍是显式假设；`logP_aggregate_le_logSQ` 只在 rescaled `logSQ := (Σγ)·log(urSQ X)` 下给桥。 |
| 6 | **URBadWeightSum** | src 00:30:28 / 3463 B；olean **16:32:12** / 31352 B；P18 `urBadWeightSum_eq_invDegree` 三公理 | **A-局部**：Σγ = Σ 逆完成次数；`BadWeightTotalEqDmod` / `BadWeightedLogPBridge` 是命名 Prop，**NO INHABITANT**；`c=d_mod`、`c=1` 均未证。 |
| 7 | **ULHviTableFinal** | src 00:34:05 / 7316 B；olean **16:35:54** / 165688 B；P18 `hviTable_final` 三公理 | **A-局部（无归一聚合会计）**：`hV_of_collectionLayer`、`hviTable_of_collectionLayer'`、`hviTable_final`；**无 Σγ=1**；纯会计，不证明 paper λ 权重。 |
| 8 | **ULStepVIII** | src 00:53:09 / 28274 B；olean **16:54:15** / 1586264 B；log 1032 B **八条打印全部三公理**；二进制含 `hstepVIII_of_collectionLayer`、`logP_aggregate_le_logSQ`、`NativeVsPaperWeightsRecord`，**无 `sorryAx`**；P19 `logP_aggregate_le_logSQ` / `uc_c4_of_retained` 三公理 | **B（retained 装配 + 条件式 collection 实例）**。16:41:23 → 16:51:31 → **16:54:16 终版**；16:48/16:49 attempt 的 `hstepVIII_of_collectionLayer sorryAx` **已被 16:54:16 覆盖**。C4 仍条件于 hiii/hX/hlogSQ（+htheta/hscale/hpacket），**不得写 C4 已闭合**。 |
| 9 | **ChartPreimage（P¹）** | src 00:25:23 / 2916 B；olean **16:26:17** / 124352 B；P18 `localChartInf_preimage_localChart0`、**P19 `localChart0_preimage_localChartInf`** 均三公理 | **A-局部（P¹ 两 chart cross-preimage + cover）**。这是 M-b 的 P¹ 侧输入，不是 M-b 本身。 |
| 10 | **16:46 后其它文件** | 见 §2r-2 #342–356：PsiGlobal、HT81Interface、ConductorDifferentCancellation、PiFiniteChart、HviTableInstance、ThetaHullTensor、GlueCocycle、JHeightUniform、ConductorCore、PiRestrictFinite | 除条件式/局部外，**无新的路线出口**；详见下表。 |

### 2r-2 本窗口新增 DONE / FAIL（#342–356，按 attempt 计）

| # | 文件 | 事件（UTC） | 证据 | 判定 |
|---|---|---|---|---|
| 342 | Mzk1G1FermatPiPreimageClose2Actual | **DONE 16:47:43 / 16:50:10**（16:46:18 FAIL） | src 00:49:15 / 4765 B；olean 00:50:10 / 133800 B；log 293 B 两打印三公理 | **A-局部（t 侧 CLOSED）**；覆盖 §2q-6/#337。 |
| 343 | Mzk1G1PsiGlobalActual | **DONE 16:44:16 / 16:50:10**；**FAIL 16:55:06 / 16:56:25** | 16:50:10 olean 20496 B 只含 `psiChart0`、`psiChart1`（P19 三公理）；当前 src 00:55:51 / 3812 B 新增 `overlapToCurve_condition`，16:56:25 FAIL：`glue_condition` 的 `glued` 端点与 `fermatCurveScheme` 类型不匹配，末行 **sorryAx** | **R（当前源）/ 非全局 ψ**：只有两个 chart def；cocycle 目标写出但红；`psiChart0/1` 仅在 16:50:10 olean 可用。 |
| 344 | Mzk1HT81InterfaceActual | **DONE 16:45:36 / 16:56:23** | src 00:55:13 / 3126 B；olean 16:56:23；结构 `HT81Interface`（I/E/hO1/Ei/phi/y/L/K/KintoL）+ `HT81LineBundleHeights`；0 定理 | **C（接口，NO INHABITANT）**：命名 paper 8.1 对象，无构造；不得当 8.1 已交。 |
| 345 | Mzk1G1ConductorDifferentCancellationActual | **DONE 16:47:01 / 16:50:12** | src 00:48:29 / 3290 B；olean 00:50:12 / 136008 B；log 321 B 两打印三公理；P19 `discriminant_tower_formula_ringOfIntegers` 三公理 | **A-局部/B**：`f2_f3_cancellation` 是 `linarith`（F2+F3 直接相加）；tower 公式转调 Mathlib donor；**不是 8.1 构造**。 |
| 346 | Mzk1G1FermatPiFiniteChartActual | **DONE 16:50:10**（3 条平凡引理）；**FAIL 16:52:27 / 16:56:26 / 16:57:36**（finite restriction） | 旧 olean 16:50:10 / 38512 B 只含 `piChart0_eq_lamSpec`（rfl）+ 两条 `Set.range` 引理（三公理）；当前 src 00:56:45 / 5544 B 加 `isFinite_pi_of_chart0_restrict`/`..._chartInf_restrict`，16:57:36 首错 `Arrow.isoMk` 的 `hcomm` 方向（应为 `q ≫ eU.symm` 侧），两条均 **sorryAx** | **R/STALE（当前源）**：旧 olean 的 3 条平凡引理不能用来说 `IsFinite π|U0` 已证；**`isFinite_pi_of_chart0_restrict` 未进 olean，禁引**。 |
| 347 | Mzk1ULHviTableInstanceActual | **FAIL 16:51:43 → DONE 16:55:38** | src 00:53:24 / 4775 B；olean 00:55:37 / 67928 B；log 134 B `hviTable_instance` 三公理（16:51:43 旧日志是 timeout+临时 sorry） | **B-条件（C4 的 collection 实例）**：`hVh` 为显式 retained（possible-images hull，无 producer）；实例本身是 `hviTable_final` 的 `simpa`。**不得写 C4 已闭合**。 |
| 348 | Mzk1ULStepVIIIActual | **DONE 16:51:31 → 16:54:16** | 见 §2r-1 第 8 行；16:54:15 olean 1586264 B；八打印三公理；`hstepVIII_of_collectionLayer` 已进 olean | **B（条件式装配）**：`hstepVIII_of_collectionLayer` 消费 `hviTable_final` + `logP_aggregate_le_logSQ`，但 hiii/hX/hlogSQ 仍显式；C4 条件式。 |
| 349 | Mzk1URThetaHullTensorActual | **FAIL 16:52:53 / 16:55:36 → DONE 16:56:52** | src 00:55:44 / 5422 B；olean 16:56:52；log 718 B 五打印三公理：`arithmeticTupleFractionalLattice_congr`、`..._const_eq_single`、`urRootCoeff_nonneg`、`urCeilCoeff_ge`、`urLocal_ball_eq_ceil` | **A-局部（C2 θ 的 tensor-lattice stage 1 定义/引理）**：congruence + subsingleton + ball-ceil 应用；**无 `actualLocalHullLog ≤ −thetaCoeff` 主不等式**。 |
| 350 | Mzk1GlueCocycleActual | **DONE 16:53:40** | src 00:52:14 / 1256 B；log 264 B 两打印三公理：`glue_condition_eqToHom`、`glue_condition_of_v_eq` | **A-局部 infra**：把 `Scheme.GlueData.glue_condition` 写成带 `hV`/`eqToHom` 的泛型形式；这是 ψ cocycle 的候选工具，不是 cocycle 本身。 |
| 351 | Mzk1G1JHeightUniformActual | **FAIL 16:53:41（log 0）→ DONE 16:55:08** | 新文件（00:52:05 重建，00:53:54 / 4184 B）；olean 00:55:08 / 75576 B；log 391 B 三打印三公理：`coeffAbsSum_coeff_le`、`_add_le`、`_C_mul_le` | **B infra（非 uniform D3）**：只有整系数 `coeffAbsSum` 的初等界；**无 uniform-in-K 高度比较、无 `HeightDictionaryInterface` 实例**。更正 §4.126「磁盘只有空占位」：现在有 84 行文件，但内容仍不是 uniform D3。 |
| 352 | Mzk1G1ConductorDifferentCancellationCoreActual | **FAIL 16:52:29 / 16:55:09 / 16:57:38** | src 00:55:54 / 4879 B；**无 olean**；首错 `ring` 未闭合、`Ideal.absNorm … = 0` rewrite 失败、`Function.ne'` 不存在 | **R**：H-T 8.2 core 未编译；`conductorDifference_le_differentTerm` 的 hdelta 本身是假设，`log_natAbs_discr_tower` 仍未绿。 |
| 353 | Mzk1G1FermatPiRestrictFiniteActual | **FAIL 16:55:06 / 16:56:25** | src 00:55:33 / 2770 B；`Arrow.mk` 陈述处类型错误、`Set.range` rewrite 失败、`Scheme.morphismRestrict` unknown、`isFinite_pi_restrict_chart0` sorryAx | **R/WIP**：与 #346 同一 goal 的拆分尝试；未产生可用声明。 |
| 354 | PsiGlobal 的 `overlapToCurve_condition` | **FAIL 16:56:25** | log 1752 B：期望 `Overlap0 n ⟶ fermatCurveScheme n`，实际 `glue_condition` 给 `… ⟶ glued`；需经 glue iso 传输 | **R**：B1 step 4 的 cocycle 仍开；不得写 ψ 全局已交。 |
| 355 | `_ProbeBatch19Actual.lean` | **DONE 16:52:56（60 s）** | log 1158 B；8 条全部三公理、0 error/0 sorryAx | 见 §3q（P19）。 |
| 356 | Mzk1G1FermatCurveSmooth2Actual | **DONE 16:42:12**（本窗口尾注） | 见 §2r-1 第 3 行 | A-局部 CLOSED（R2 两 chart）。 |

### 2r-3 audit18 评估口径收录（Lead 已收入 RC §59；写入本 gate/风险区）

| 评估项 | 最终口径（batch 19 复核） | 强制引用纪律 |
|---|---|---|
| **hγsum 撤回** | **RETRACTED / PASS**：全 paper `hγsum`/`gammaSum` 仅 ULStepVIII 文档 2 处；无 Lean 声明、无活动 consumer；旧 `Mzk1ULHviTableActual` 的 5 条 `hγ1 : (∑γ)=1` 定理仍存在但 **SUPERSEDED**，Final 已改无归一路线 | 不得复活 `hγsum`；不得要求 Σγ=1；旧 hγ1 定理不得作 C4 证据 |
| **聚合字母** | **PASS（内部会计）/ CONDITIONAL（对 paper）**：`hviTable_final`（P18）与 `hviTable_instance`（16:55:38，三公理）的 LHS = `Σ_b γ_b·(1/n)Σ_label V`，字母 `ΣγD/ΣγQ/ΣγlogP/ΣγT`；**无归一**；**无定理说 γ-聚合等于 paper λ_e/Σλ=d_mod 加权** | 只能写「内部 γ-聚合会计」；paper LHS 若需严格 λ 权重，另立 conversion task |
| **NativeVsPaperWeightsRecord** | **CONDITIONAL（named record，NO INHABITANT）**：ULStepVIII 16:54:15 olean 含结构（`lam/d_mod/paper_lambda_sum/hlam_pos/c/hc_def`），无实例；`c = Σ nativeBadLocalWeight` 由 `urBadWeightSum_eq_invDegree` 支撑；`d_mod` 在树中只是 opaque paper 参数（`ExplicitConstantObject.dmod` / `ActualThm110Data.dmod`），**无 `d_mod=[F_mod:Q]` 证明**；`c=d_mod`/`c=1` 未证 | 保留为 audit record；doc 的 `d_mod=[F_mod:Q]` 应标「paper parameter, unproved」；不得由它推出 `c=d_mod` 或 `c=1` |
| **s^Q** | **CONDITIONAL（代理）**：`Mzk1URSmallPrimeActual.urSQ`（最大小素数）已定义；`ur_badWeightedLogP_le` 三公理；`logP_aggregate_le_logSQ`（16:54:15，三公理）只给 `Σγ log p ≤ (Σγ)·log(urSQ X)`；**paper 的单字母 `log s^Q` 仍只是抽象 `logSQ`** | 引用写 `urSQ`/「代理」；不得写 paper s^Q 已定义/已识别；`logSQ` 两种缩放冲突未解（见 §4.137） |
| **hlogP_le_logSQ** | **RETAINED（NO INHABITANT）**：16:41:23 起是 `hstepVIII_of_retained` 显式参数；16:54:15 版仍如此，`hmono` 消费；`PaperStepVIIIRetained` 无 inhabitant；`logP_aggregate_le_logSQ` 只对 rescaled `logSQ` 有效 | 维持 retained；不得写 C4 闭合/hlogP 已证 |
| **uniform D3** | **FAIL / NO INHABITANT**：`Mzk1G1JHeightUniformActual` 现存在（16:55:08 DONE）但只有 `coeffAbsSum` 三条初等引理；`HeightDictionaryInterface` 1 处 `def Prop` 无实例；`D1AnalyticInput.height_dictionary` 仅结构字段（单一 B）；`jHeight_relation` 是 per-K `∃ B` | 不得写 uniform D3 已交；`jHeight_relation` 不是 interface 实例；JHeightUniform 只算 infra |
| **Close2 t 侧** | **更新：CLOSED（16:50:10，P19 三公理）**；16:46:18 的 sorryAx 是旧 attempt，已被 16:47:43/16:50:10 修复覆盖 | 可引 `Close2.pi_preimage_localChartInf`（16:50:10）；**不得再写 t 侧 sorryAx/禁引** |

### 2r-4 缺口表（16:58 口径；旧 §2q-3 保留）

| 缺口 | 当前证据 | 状态 |
|---|---|---|
| **M-b / π⁻¹** | λ 侧 `CloseActual.pi_preimage_localChart0`（00:44:16，P18b）；t 侧 `Close2.pi_preimage_localChartInf`（00:50:10，P19）；P¹ 侧 ChartPreimage 00:26:17（P18/P19） | **两侧 CLOSED**（本批修正 §2q-5/§2q-6 的「t 侧 open」）；不再有红侧 |
| **IsFinite π** | `isFinite_pi_of_chart_restrict`（PiFiniteAssembly）仍需 h0/h1；h0 的 `isFinite_pi_of_chart0_restrict` 当前源 16:57:36 红（旧 olean 只有 3 条平凡引理）；h1 的 t 侧限制有限未写 | **条件式；h0 未交、h1 未写** |
| **C4 / Step VIII** | `hstepVIII_of_collectionLayer`（16:54:16，三公理）消费 `hviTable_final` + `logP_aggregate_le_logSQ`；`hviTable_instance`（16:55:38，三公理）条件于 hVh；htheta/hscale/hpacket/hiii/hX/hlogSQ 均无 producer | **C4 仍条件式** |
| **hlogP / s^Q / paper 权重** | 见 §2r-3：hlogP RETAINED；urSQ 代理；NativeVsPaper 无 inhabitant；d_mod paper 参数 | 口径不变（batch 18 收录） |
| **uniform D3 / HeightDictionaryInterface** | JHeightUniform 16:55:08 只有 coeffAbsSum 三条；接口 1 def 无实例；D1AnalyticInput 字段无 inhabitant | **NO INHABITANT / 未交付** |
| **R2 chart smooth** | CurveSmooth2 16:42:12：`loc_u2`（P18）、`loc_v2`（P19）、`chartRing2`、`chartSpec2` 全部三公理 | **A-局部 CLOSED（两 chart）** |
| **G-B Ω / boundary** | 两 chart 数据（16:08:36）；λ=0/1（16:25:01）；∞ 侧 16:36:37（P19）；`BoundaryRamificationIndexObligation` NO INHABITANT；Ω 全局/`Ω≅O(n−3)` 未证 | 局部 / NO INHABITANT |
| **ψ 全局** | GlueCocycle 16:53:40 给泛型 `glue_condition_eqToHom`；PsiGlobal 只有 `psiChart0/1` def；`overlapToCurve_condition` 16:56:25 red（sorryAx） | **未交**（B1 step 4 仍开） |
| **H-T 8.1/8.2** | HT81Interface 只有结构（NO INHABITANT）；ConductorDifferent `f2_f3_cancellation` 是 linarith、tower 是 donor；Core 16:57:38 red | **接口/局部；无 8.1 构造** |
| **P¹ 三模型 / 删除件** | `projectiveLineIso` grep 0；P1ProperAssembly / F7Sep / P1Separated 仍 MISSING | 禁复合 / 禁引（不变） |

### 2r-5 版本/内容陷阱（本批）

- **Close2 旧日志陷阱**：16:46:18 的 log 末行确实带 `sorryAx`，但那是**旧 attempt**；16:47:43/16:50:10 的 log 只有两条三公理打印，源码 00:49:15 与 olean 00:50:10 对齐。**引用只认 16:50:10。**
- **ULStepVIII 旧 attempt 陷阱**：16:49:23 的 log 有 `hstepVIII_of_collectionLayer depends on … sorryAx`（当时源码 00:48:03 版）；16:54:16 的 log 八条全三公理、二进制无 `sorryAx`。**引用只认 16:54:15 olean。**
- **PiFiniteChart 旧 olean 陷阱**：16:50:10 的 38512 B olean 只含 3 条平凡引理；当前源 00:56:45 / 5544 B 的 `isFinite_pi_of_chart0_restrict` 从未进 olean（16:52:27/16:56:26/16:57:36 三次红）。**不得按 mtime 说 h0 已证。**
- **PsiGlobal 旧 olean 陷阱**：16:50:10 olean 只有 `psiChart0/1`；`overlapToCurve_condition` 从未进 olean（16:56:25 红）。
- **HviTableInstance 旧日志陷阱**：16:51:43 的 log 有 timeout + `declaration uses sorry`；16:55:38 的 log 只有一条三公理打印。
- **JHeightUniform 已非空占位**：00:52:05 重建、16:55:08 DONE；但内容仅 `coeffAbsSum` 三条，仍无 uniform D3。此前 §4.126/§4.139 的「MISSING/空模块」只适用于 16:15:45 事件。
- **新文件**：`Mzk1ULHviTableInstanceActual`、`Mzk1URThetaHullTensorActual`、`Mzk1GlueCocycleActual`、`Mzk1G1JHeightUniformActual`（重建）、`Mzk1G1ConductorDifferentCancellationCoreActual`、`Mzk1G1FermatPiRestrictFiniteActual`；本批只新建 `_ProbeBatch19Actual.lean`。

## 3q. Probe 19（本批 batch 19）：`tmp/sheaf/xif/paper/_ProbeBatch19Actual.lean`

- `node tools/wd_add.mjs` 16:51 排队（total 186）→ **START 16:51:57 → DONE 16:52:56（60 s）**；log 1158 B，**0 error / 0 sorryAx**，8 条全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | 证据版本（probe 时磁盘 olean） |
|---|---|---|
| `Mzk1G1FermatPiPreimageClose2Actual.pi_preimage_localChartInf` | [propext, Classical.choice, Quot.sound] | **16:50:10**（#342；t 侧 M-b，本批关键） |
| `Mzk1G1FermatCurveSmooth2Actual.loc_v2_standardSmooth` | [propext, Classical.choice, Quot.sound] | 16:42:12（#331/#346；R2 v-chart） |
| `Mzk1G1OmegaRamificationInfinityActual.boundary_infinity_uniformizer_power` | [propext, Classical.choice, Quot.sound] | 16:36:37（#335；∞ 侧 e=n） |
| `Mzk1ULStepVIIIActual.logP_aggregate_le_logSQ` | [propext, Classical.choice, Quot.sound] | 16:51:31（probe 时；16:54:15 同声明仍三公理） |
| `Mzk1ULStepVIIIActual.uc_c4_of_retained` | [propext, Classical.choice, Quot.sound] | 16:51:31（C4 条件式） |
| `Mzk1G1ProjectiveLineChartPreimageActual.localChart0_preimage_localChartInf` | [propext, Classical.choice, Quot.sound] | 16:26:17（#328；P¹ 另一方向） |
| `Mzk1G1PsiGlobalActual.psiChart0` | [propext, Classical.choice, Quot.sound] | 16:50:10（#343；def，非全局 ψ） |
| `Mzk1G1ConductorDifferentCancellationActual.discriminant_tower_formula_ringOfIntegers` | [propext, Classical.choice, Quot.sound] | 16:50:12（#345；Mathlib donor） |

- 版本纪律：8 条均按 probe 时刻磁盘 olean 复算；`pi_preimage_localChartInf` 是 16:50:10 版（不是 16:46:18 的 sorryAx 版）；`logP_aggregate_le_logSQ`/`uc_c4_of_retained` 是 16:51:31 版（16:54:15 重建后声明不变）。probe **未运行** `lake env lean`、未自起 watchdog、未写 sorry/axiom、未 spawn_teammate。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 19 续）

### 4.144 【高·纪律】Close2 t 侧已翻转：16:46:18 的 sorryAx 是旧 attempt，16:50:10 三公理
- 16:46:18 的 log 末行确实是 `pi_preimage_localChartInf depends on [propext, sorryAx, …]`，当时源码 4647 B；随后源码修到 4765 B（00:49:15），16:47:43 DONE、16:50:10 再 DONE（olean 133800 B），log 只有 `pi_preimage_localChart0` 与 `pi_preimage_localChartInf` 两条三公理打印，二进制无 `sorryAx`，P19 独立复算三公理。
- **结论**：M-b 的 t 侧 `(pi n) ⁻¹ᵁ localChartInf.opensRange = (fermatChartInfToCurve n).opensRange` 已真实编译；配合 λ 侧（Close 00:44:16，P18b）两目标等式均 CLOSED。**不得再写「t 侧 sorryAx/禁引」；也不得把 16:46:18 当当前首错。**

### 4.145 【高·C4】HviTableInstance 是条件式 collection 实例，不是 C4 闭合
- 16:55:38 DONE 的 `hviTable_instance`（P19 未 probe，log 三公理）把 `hviTable_final` 实例化到 `b := Bad`、`γ := nativeBadLocalWeight`、`V := urPacketHullLog`；但 `hVh` 是显式 retained（route §5.4 possible-images hull 几何识别 + L814/L524 donor），**无 producer**。
- 16:51:43 的旧 attempt 是 `isDefEq` timeout + `unknown identifier urPacketHullLog` 恢复出的 `sorryAx`，**以 16:55:38 为准**。即便如此，C4 仍条件于 hiii/hX/hlogSQ + htheta/hscale/hpacket；`hstepVIII_of_collectionLayer`（16:54:16）只是把这些条件装进 `PaperStepVIIIRetained`。**不得写「C4 已闭合/θ 已接入」。**

### 4.146 【高·G-A】PiFiniteChart 的 finite restriction 三次红，旧 olean 只有平凡引理
- 16:50:10 的 olean（38512 B）只含 `piChart0_eq_lamSpec`（rfl）、`chart0_toCurve_range_eq`、`localChart0_range_eq`；当前源 00:56:45 / 5544 B 新加 `isFinite_pi_of_chart0_restrict`/`isFinite_pi_of_chartInf_restrict`，16:52:27/16:56:26/16:57:36 三次 FAIL；16:57:36 的首错是 `Arrow.isoMk` 的 `hcomm` 方向（期望 `q ≫ eU.symm`，给的是 `(eA ≪≫ eW.symm).hom ≫ q`），两条定理都落 `sorryAx`。
- 因此 **`IsFinite (pi ∣_ U0)` 仍未交**；不得按 mtime 说 h0 已证，也不得引 `isFinite_pi_of_chart0_restrict`。`isFinite_pi_of_chartInf_restrict` 本身只是把 h1 当假设转调 PiFiniteAssembly 的装配，若引用须写明 h1。

### 4.147 【中·纪律】ULStepVIII 16:54:16 是当前口径；hstepVIII_of_collectionLayer 仍条件式
- 16:49:23 的旧 attempt 中 `hstepVIII_of_collectionLayer` 带 `sorryAx`（源码 00:48:03）；16:54:16 的 olean（1586264 B）八条打印全三公理、二进制无 `sorryAx`，`hstepVIII_of_collectionLayer` 已进 olean。
- 但它的输入 hiii（Step (iii) display）、hX（小素数 cutoff）、hlogSQ（rescaled 聚合界）都是显式假设；`hstepVIII_of_retained` 仍需 `hlogP_le_logSQ`。**C4 仍条件式；16:41:23/16:51:31 的旧 olean 不再代表当前内容。**

### 4.148 【高·ψ】PsiGlobal 只有两个 chart def；cocycle 尝试带 sorryAx
- 16:50:10 的 olean 只有 `psiChart0`、`psiChart1`（P19 三公理，但都是 `noncomputable def`，不是全局 ψ）；当前源 00:55:51 新增 `overlapToCurve_condition`，16:56:25 FAIL：`glue_condition` 给 `… ⟶ glued`，目标要 `Overlap0 n ⟶ fermatCurveScheme n`（缺 glue iso 传输），末行 sorryAx。
- GlueCocycle 16:53:40 只给泛型 `glue_condition_eqToHom`（三公理），可用于改写，但**没有实例化到 fermat 两 chart**。**不得写 ψ 全局已构造；B1 step 4 仍开。**

### 4.149 【中·H-T】HT81/Conductor 系列是接口/平凡推导，不是 8.1/8.2 进展
- `HT81Interface`（16:56:23）是结构 + `HT81LineBundleHeights`，0 定理、NO INHABITANT；`ConductorDifferentCancellation`（16:50:12）的 `f2_f3_cancellation` 只是 F2+F3 的 `linarith`，`discriminant_tower_formula_ringOfIntegers` 是 Mathlib donor；`ConductorDifferentCancellationCore`（16:57:38 红）尚未编译。
- H-T 的 8.1 实际构造（E_i、phi_i、y、K、L、h_{O(1)}）仍**没有任何 inhabitant**；不得把接口/结构或 linarith 当 8.1/8.2 已交。

### 4.150 【高·D3】JHeightUniform 现在是 coeffAbsSum infra，仍不是 uniform D3
- 文件 00:52:05 重建、16:55:08 DONE（olean 75576 B），但只有 `coeffAbsSum_coeff_le`、`coeffAbsSum_add_le`、`coeffAbsSum_C_mul_le` 三条初等整系数界（三公理）。
- `HeightDictionaryInterface` 仍 1 处 `def Prop`、无实例；`D1AnalyticInput.height_dictionary` 仍是单一 B 的结构字段；`jHeight_relation` 是 per-K `∃ B`。**uniform D3 仍 FAIL/NO INHABITANT；§4.126/§4.139 的「占位缺失」只适用于旧事件，现行表述改为「只有 coeff-size infra」。**

### 4.151 【中·口径】audit18 评估口径已收录（详见 §2r-3）；旧 §4.134–§4.143 除第 7 项外维持
- hγsum RETRACTED；聚合 PASS（内部）/CONDITIONAL（对 paper）；NativeVsPaperWeightsRecord NO INHABITANT + d_mod paper parameter；s^Q = urSQ 代理；hlogP RETAINED；uniform D3 FAIL；Close2 t 侧 CLOSED（本批翻转）。

### 4.152 【低·纪律】16:46–16:57 的版本陷阱清单
- Close2 旧 sorryAx log（16:46:18）；ULStepVIII 旧 sorryAx log（16:49:23）；PiFiniteChart 旧 olean（16:50:10，仅 3 平凡引理）；PsiGlobal 旧 olean（16:50:10，仅 2 def）；HviTableInstance 旧 log（16:51:43，timeout+sorry）；JHeightUniform 16:53:41 的 log 为 0（文件被改）。**引用一律「文件 + DONE 时间 + olean 时间」三者齐备。**

## 5o. batch 19 立即动作（快照 16:59 UTC）

1. **M-b（henry，最高优先，口径已变）**：λ 侧 `CloseActual.pi_preimage_localChart0`（00:44:16，P18b）与 t 侧 `Close2.pi_preimage_localChartInf`（00:50:10，P19）**两侧都三公理 CLOSED**。下一步不是修 Close2，而是把这两个等式喂给 `IsFinite π` 的 h0/h1；**不得再引 16:46:18 的 sorryAx 日志**。
2. **PiFiniteChart / h0**：当前源 16:57:36 红，唯一首错是 `Arrow.isoMk` 的 `hcomm` 方向；把 `hcomm` 改成 `(eA ≪≫ eW.symm).hom ≫ q = (pi n ∣_ U0) ≫ eU.inv` 的期望方向（或直接 `exact Arrow.isoMk … (by …)`），再重编。**在 DONE 且 print 无 sorryAx 前，不得写 h0 已证**；`PiRestrictFinite` 是同一 goal 的拆分尝试，当前陈述本身有类型错误（`Arrow.mk`/`Scheme.morphismRestrict`），先别引。
3. **C4**：`hviTable_instance`（16:55:38，三公理）给条件式 collection 实例，`hVh` 无 producer；`hstepVIII_of_collectionLayer`（16:54:16，三公理）把 hiii/hX/hlogSQ 装进 retained。下一步只做 hVh 的 possible-images hull 几何识别（或明确记为 retained），**不得写 C4 闭合**。
4. **audit18 口径冻结**（详见 §2r-3）：hγsum RETRACTED；聚合只写「内部 γ-聚合会计」；`NativeVsPaperWeightsRecord` 保持 named record、`d_mod` 标 paper parameter；`urSQ` 只作代理；`hlogP_le_logSQ` 保持 retained；uniform D3 不引 JHeightUniform。
5. **ψ 全局**：`GlueCocycle.glue_condition_eqToHom`（16:53:40，三公理）可用；`PsiGlobal.overlapToCurve_condition` 需把 `glue_condition` 的 `glued` 端点经 glue iso 传输到 `fermatCurveScheme`（或对 `glue_condition` 与 `D.ι` 复合后用 `IsOpenImmersion` 消去），**在 DONE 前不得写全局 ψ**。
6. **H-T（sophie/alan）**：HT81Interface 只是结构（NO INHABITANT）；ConductorDifferent 的 `f2_f3_cancellation` 是 linarith、tower 是 donor；Core 16:57:38 red。**不得把接口/linarith 报成 8.1/8.2 进展**。
7. **D3**：JHeightUniform 的 `coeffAbsSum` 三条只是 infra；真 uniform D3 仍需 `D1AnalyticInput.qHeight` + 单一 B（或 `HeightDictionaryInterface` 实例）。`jHeight_relation` 只是 per-K。
8. **版本纪律（强制）**：Close2 只引 16:50:10；ULStepVIII 只引 16:54:15（或 16:58:55 同声明）；PiFiniteChart 只引 16:50:10 的 3 条平凡引理（不得引 finite restriction）；PsiGlobal 只引 16:50:10 的 `psiChart0/1`；HviTableInstance 只引 16:55:37；CurveSmooth2 只引 16:42:12；OmegaRamificationInfinity 只引 16:36:37。

## 6q. batch 19 更新（快照 **16:59 UTC = 00:59 CST**；覆盖 §6–§6p 的旧结论，旧文保留）

- **已运行（本批）**：`Get-Item` src/olean/log 对照（30+ 文件）；watchdog.log 按 attempt 过滤（16:46–16:59）；per-file log 逐个读取（Close2 293 B、ULStepVIII 1032 B、CurveSmooth2 3400 B、HviTableInstance 134/1524 B、PiFiniteChart 3101/3717 B、PiRestrictFinite 1825/3551 B、PsiGlobal 1752 B、JHeightUniform 391 B、ThetaHullTensor 718/4964 B、GlueCocycle 264 B、Core 2140 B、Probe19 1158 B）；二进制 olean 名核验（Close2/ULStepVIII/CurveSmooth2/OmegaRamificationInfinity/ChartPreimage/PsiGlobal/Conductor/HviTableInstance）；源码阅读（Close2 89 行、PsiGlobal 67、HT81 73、Conductor 71、ConductorCore 107、PiFiniteChart 103、PiRestrictFinite 49、HviTableInstance 83、ThetaHullTensor 116、GlueCocycle 27、JHeightUniform 84、OmegaRamificationInfinity 176、CurveSmooth2 关键段、SmallPrime/BadWeightSum/HviTableFinal/ChartPreimage/Close 全文）；grep（`hγsum` 仅 2 处文档、`HeightDictionaryInterface` 1、`NativeVsPaperWeightsRecord` 1、`PaperStepVIIIRetained` 7、`projectiveLineIso` 0、`pi_preimage_localChartInf` 4、`pi_preimage_localChart0` 7）。
- **Probe 19**：8 条 DONE 16:52:56，全部三公理、0 error/0 sorryAx。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**；仅写本表与 `_ProbeBatch19Actual.lean`。
- **未覆盖 / 未运行（如实标注）**：16:59:10 起的 Core/PiFiniteChart 波在飞；16:58:22 PsiGlobal/PiRestrictFinite 再 FAIL；16:58:56 ULStepVIII 再 DONE；`hstepVIII_of_collectionLayer` 证明未逐行重读；`CurveSmooth2` 的 chartSpec2 只按源内 print（未独立 probe）；`ThetaHullTensor` 的五条只按自身 log；G-K/H-T/P8-P 端到端与 F1–F4/F8 仍未做语义审计；未重读 paper 原文（行号 provenance 沿用既有记录）。
- 本批写入范围：本表 + **新建** `_ProbeBatch19Actual.lean`；未改其它 Lean 文件；未删旧行。

### 6r. 快照后补记（**16:58:22–16:58:56**；不改变 §2r 结论）

- **16:58:22 PsiGlobal FAIL / PiRestrictFinite FAIL**：与 16:56:25 同一源码（00:55:51 / 00:55:33），错误相同（cocycle 端点类型不匹配 / `Arrow.mk` 陈述类型错误）。仍 R。
- **16:58:56 ULStepVIII DONE**：src 00:53:09 / 28274 B；新 olean **00:58:55 / 1620816 B**；log 1032 B 仍八条三公理（`hstepVIII_of_collectionLayer`、`uc_c4_of_retained` 等）。声明集与 16:54:15 版相同，引用写 16:58:55 olean 亦可；C4 仍条件式。
- **16:59:10 起**：Core / PiFiniteChart 重新编译；之后的 DONE/FAIL 未审计。
- **16:59:39 PiFiniteChart FAIL / 16:59:41 Core FAIL**：PiFiniteChart 源码 00:58:44 / 5474 B，错误仍有 75:8 rewrite 未命中 + 88:84 `Arrow.isoMk` 类型不匹配，`isFinite_pi_of_chart0_restrict`/`..._chartInf_restrict` 仍带 sorryAx；**h0 仍未交**。Core 仍红。此后的 DONE/FAIL 未审计。

## 2s. batch 20 gate 表（快照 **2026-11-16 17:32 UTC = 2026-11-17 01:32 CST**；覆盖 16:59:41–17:32:23；旧行全保留）

- 证据版本：src/olean/log 均 `Get-Item` 实测；`(P20)` = §3r 独立 probe；`(P20b)/(P20c)` = 本批补充 probe。**17:32:23 之后见 §6s 补记（到 17:34:40）**；更晚未审计（watchdog 仍在跑；`CurveSmoothFinal` 当前源只剩 cover、`PsiGlobal` 17:34:36 已 DONE、`HviTableInstance` 17:33:43 已 DONE）。
- 本窗口关键翻转：**G-A proper CLOSED**；**IsFinite π 两条路线 CLOSED**；**G-A glued smooth 仍 OPEN**（原 smooth 主定理在 17:32:21 源码中已被删成 cover-only）；**(h) 两 chart cover CLOSED** 但几何整性/连通未做；`PsiGlobal` 的 cocycle condition CLOSED 但 global ψ 仍红；`HviTableInstance/URLabelData/ULStepVHullPaper` 把 hVh 桥到 `LabelStepVHullData`（NO INHABITANT），C4 仍条件式。
- batch19 尾注确认（不计新事件）：`PiPreimageClose2` 16:50:10（olean 133800 B）仍为当前；`OmegaRamificationInfinity` 16:36:37、`ULStepVIII` 16:58:55 未再改；`ThetaHullTensor` 16:56:52 旧版已由 17:10:28/17:32:23 取代；`HviTableInstance` 16:55:38 旧版已由 17:16:01/17:28:12 取代；`PiRestrictFinite` 16:58:22 红为旧 attempt，17:16:42 已 DONE。

### 2s-1 Lead 指定 G-A 出口逐项

| # | 指定项 | 证据（src / olean / log） | 判定 |
|---|---|---|---|
| 1 | **PiFiniteChart 17:17:53** | src 17:16:51 / 8300 B；olean 17:17:53 / 141768 B；log 847 B，6 条打印**全部三公理**：`piChartInf_eq_lamSpec2`、`piChart0_eq_lamSpec`、`chart0_toCurve_range_eq`、`localChart0_range_eq`、`isFinite_pi_of_chartInf_restrict`、`isFinite_pi`。`isFinite_pi_of_chart0_restrict` 源内**无自己的 #print**，但 P20 独立复算三公理；`isFinite_pi` 消费两条 chart restriction + `PiFiniteAssembly.isFinite_pi_of_chart_restrict`。 | **G-A IsFinite π CLOSED（grace 路线）**。引用写 17:17:53 olean；特别可引 `isFinite_pi_of_chart0_restrict`（P20）与 `isFinite_pi`。 |
| 2 | **PiProper 17:19:19** | src 17:18:49 / 5762 B；olean 17:19:18 / 45432 B；log 1870 B，9 条打印**全部三公理**（`subsingleton_hom_spec_rat`、两条 chart/base 交换、`fermatCurveToBase_eq_pi_comp`、`fermatCurveToBase_eq_fermatCurveToSpec`、`fermatCurveToSpec_isProper`、`_cond`、`_final`、`fermatCurveToBase_isProper`）。`_final (n) (hn) : IsProper (fermatCurveToSpec n)` 逐字见源 107–110；`_cond` 用 `Mzk1P1ProperFinalActual.p1GluedToBase_isProper`，`_final` 再喂 `Mzk1G1FermatPiRestrictFiniteActual.isFinite_pi n hn`。P20 `_final` 三公理。 | **G-A proper CLOSED（真实出口）**：结构态射 `fermatCurveToSpec n : fermatCurveScheme n ⟶ Spec ℚ` 已 proper；消费 henry `isFinite_pi` + alan `p1GluedToBase_isProper`（均三公理）。引用写 17:19:18 olean（声明名 `fermatCurveToSpec_isProper_final`）。**不得由此推出 smooth/整性**。 |
| 3 | **PiRestrictFinite 17:16:42** | src 17:15:44 / 7825 B；olean 17:16:42 / 139384 B；log 134 B 只含 `isFinite_pi` 一条三公理；源内另有 `restrict_eq_chart0/Inf`、`isFinite_pi_restrict_chart0/Inf`。P20 复算 `isFinite_pi` 与 `isFinite_pi_restrict_chart0`（三公理）；P20b 复算 `isFinite_pi_restrict_chartInf`、`restrict_eq_chart0`、`restrict_eq_chartInf`（均三公理）。 | **henry 路线 CLOSED**：`isFinite_pi` 与两条 chart restriction、两条 restriction 等式均无 sorryAx。`PiProper._final` 消费的正是本文件 17:16:42 版 `isFinite_pi`。 |
| 4 | **CurveSmoothFinal** | **不是 DONE**。当前 src 17:32:21 / 2438 B **只剩** `chartOpenFamily`、`chartOpenFamily_zero/one`、`chartOpenFamily_iSup_eq_top`，**smooth 主定理已被删除**；无 olean。此前 17:24:51 / 3378 B、17:30:20 / 2510 B 版曾写 `fermatCurveToSpec_smoothOfRelativeDimension`，17:04:49、17:07:22、17:10:01、17:12:15、17:14:06、17:15:33、17:21:07、17:24:13、17:25:26、17:28:56、17:31:54 全部 FAIL；19118 B 日志含 32/35/36/56/62 行错误、universe metavariable，末段该定理 **sorryAx**。 | **G-A glued smooth OPEN / 禁引**。当前源码连目标定理都不存在；不得写“glued Y_n smooth 已交”。chart-level 输入仍可引：`CurveSmooth.chartSpec_smoothOfRelativeDimension`（15:55:41，U0）与 `CurveSmooth2.chartSpec2_smoothOfRelativeDimension`（16:42:12，U1）。 |
| 5 | **`SmoothOfRelativeDimension 1 (fermatCurveToSpec n)`** | 当前 paper 源 grep **0 处**（只在旧 attempt 日志）；P19 的 `loc_v2`、P18 的 `loc_u2` 与 `chartSpec2` 均只是 chart 层。 | **未陈述/未证明**；G-A §2.4 的 scheme 层 smooth 出口仍缺。 |

### 2s-2 本窗口新增 DONE / FAIL（#357–#371，按 attempt 计）

| # | 文件 | 事件（UTC） | 证据 | 判定 |
|---|---|---|---|---|
| 357 | Mzk1G1FermatPiFiniteChartActual | **DONE 17:13:00 → 17:17:53** | src 17:16:51 / 8300 B；olean 17:17:53 / 141768 B；log 847 B 6 打印三公理 | **A-局部 CLOSED（IsFinite π grace 路线）**；见 §2s-1#1。 |
| 358 | Mzk1G1FermatPiRestrictFiniteActual | **DONE 17:14:50 → 17:16:42**（16:58:22 旧 red） | src 17:15:44 / 7825 B；olean 17:16:42 / 139384 B；P20/P20b 覆盖 5 条三公理 | **A-局部 CLOSED（IsFinite π henry 路线）**；见 §2s-1#3。 |
| 359 | Mzk1G1FermatPiProperActual | **DONE 17:19:19** | src 17:18:49 / 5762 B；olean 17:19:18 / 45432 B；log 9 打印三公理 | **A-局部/G-A 出口（proper）**；见 §2s-1#2。 |
| 360 | Mzk1G1PsiGlobalActual | **DONE 17:00:24**（16:58:22 旧 red）；**当前 17:30:46 源 17:32:21 FAIL** | 17:00:24 olean 36544 B；log 710 B：`psiChart0`、`psiChart1`、`overlapToCurve_condition` 均三公理（P20 复算 condition）；当前源 4619 B 新增 `hcomp_left_eq`，17:32:21 红：unsolved goals + **sorryAx** | **B1④ cocycle condition CLOSED；global ψ 仍未交**。引用只写 17:00:24 的三条；**不得引当前源的 `hcomp_left_eq`**。 |
| 361 | Mzk1G1ConductorDifferentCancellationCoreActual | **DONE 17:08:52 / 17:10:03**（16:59:41 旧 red） | src 17:09:24 / 5611 B；olean 17:10:03 / 235504 B；log 492 B：`conductorDifference_le_differentTerm`、`log_natAbs_discr_tower`、`log_absNorm_differentIdeal_eq` 均三公理（P20 tower） | **B（H-T 8.2 core 编译）**：tower 公式真证；`conductorDifference_le_differentTerm` 仍以 `hdelta` 为假设。 |
| 362 | Mzk1URThetaHullTensorActual | **DONE 17:10:28 → FAIL 17:29:39 → DONE 17:32:23** | 17:32:22 olean 91136 B；log 718 B 五条三公理（`arithmeticTupleFractionalLattice_congr/const_eq_single`、`urRootCoeff_nonneg`、`urCeilCoeff_ge`、`urLocal_ball_eq_ceil`）；17:28:22 加的新 target 段在 17:29:39 红（timeout + `urNonzeroLabelHullLog` unknown + sorryAx），17:30:05 源回退 | **A-局部（tensor-lattice stage 1）**；主不等式 `actualLocalHullLog ≤ −thetaCoeff` 仍无。引用写 17:32:22 olean 的五条。 |
| 363 | Mzk1ULHviTableInstanceActual | **DONE 17:01:52 / 17:09:17 / 17:16:01 / 17:28:12**；**当前 17:28:37 源 17:31:07 FAIL** | 17:28:11 olean 240000 B；P20c 三公理：`hVh_of_labelData`、`hVh_of_paperBound_letters'`、`hviTable_instance`、`labelDifferentSum_nonneg`；17:16:00 olean 202016 B 四条三公理；当前源 17494 B 新增 `hviTable_instance_of_labelData`，17:31:07 因 244:6 isDefEq timeout + 285:14 unknown 红 | **B 条件式（C4 hVh 桥）**：`hVh_of_labelData` 把 hVh 归约到 `LabelStepVHullData` + paper/exceptional 界；T-side `hviTable_instance_of_labelData` 当前红、禁引。 |
| 364 | Mzk1URLabelDataActual | **DONE 17:06:39 / 17:13:24 / 17:20:26 / 17:22:44** | src 17:21:40 / 5013 B；olean 17:22:44 / 764216 B；log 0 B（无 #print）；结构 `LabelStepVHullData`（varpi/Phi/hullSet/small_outside/hexc/hpaper）**NO INHABITANT** | **B 接口**：标签定义 + retained 结构；不得当 hVh 已交。 |
| 365 | Mzk1ULStepVHullPaperActual（新） | **DONE 17:24:40** | src 17:22:42 / 3783 B；olean 17:24:39 / 96416 B；log 130 B：`hV_of_L814_data` 三公理 | **A-局部（hpaper 从 L814 donor 产出）**；配合 `LabelStepVHullData` 仍差 inhabitant。 |
| 366 | Mzk1URThetaHullGenericActual（新） | **DONE 17:27:00**（17:14:09/17:17:09/17:24:41 曾 FAIL） | src 17:25:38 / 6001 B；olean 17:26:59 / 134240 B；log 597 B 四条**全部三公理**：`fractionalLattice_mul_holomorphic_le`、`thetaRegion_zero_eq_holomorphic`、`thetaRegion_subset_holomorphic`、`thetaImageSet_subset_holomorphic` | **A-局部（U-R C2 upper stage）**：非负系数 scaled region ⊆ O_hol；zero-label region = O_hol；不是主不等式。 |
| 367 | Mzk1G1PsiHcompRightActual（新） | **DONE 17:30:23**（17:20:11/17:23:29/17:25:26/17:27:44 曾 FAIL） | src 17:28:38 / 3749 B；olean 17:30:23 / 77760 B；log 四条打印三公理：`qToOverlap_lift`、`infToOverlap_lift`、`overlapSpecMap10_comp_overlapToChartInf`、`hcomp_right_eq` | **B1④ hcomp right leg CLOSED**；不是 global ψ。 |
| 368 | Mzk1G1ChartCoverActual（新） | **DONE 17:31:53**（17:28:55/17:30:22 曾 FAIL） | src 17:30:27 / 1777 B；olean 17:31:53 / 59776 B；log 28 行，末段 `chartOpenFamily_iSup_eq_top` 三公理（旧段有 sorryAx，已过） | **A-局部（G-A (h) 两 chart cover）**；两 chart `opensRange` 并 = ⊤。 |
| 369 | Mzk1G1FermatCurveSmoothFinalActual（新） | **FAIL 17:04:49–17:31:54**（多次）；当前 src 17:32:21 只 cover | 无 olean；19118 B 日志含 sorryAx/类型错误；当前源 2438 B 无 smooth 定理 | **R（当前源）/ G-A glued smooth OPEN**；见 §2s-1#4。 |
| 370 | Probe 20 / 20b / 20c | **DONE 17:24:16 / 17:27:44 / 17:30:52** | log 1155 B / 436 B / 551 B；8 / 3 / 4 条全部三公理、0 error/0 sorryAx | 见 §3r。 |
| 371 | _ProbeCoverApi | **DONE 17:19:19** | 非 audit 文件（lane probe）；log 含 API #check 与若干 error | 仅记录，不当作 audit 证据。 |

### 2s-3 缺口表（17:32 口径；旧 §2r-4 保留）

| 缺口 | 当前证据 | 状态 |
|---|---|---|
| **G-A proper** | `PiProper.fermatCurveToSpec_isProper_final`（17:19:18，P20 三公理） | **CLOSED** |
| **IsFinite π** | `PiFiniteChart.isFinite_pi`（17:17:53，P20）+ `PiRestrictFinite.isFinite_pi`（17:16:42，P20） | **CLOSED（两条独立路线）** |
| **M-b / π⁻¹** | Close 16:44:16（P18b）+ Close2 16:50:10（P19） | **两侧 CLOSED**（batch19 已收录，本批确认未改） |
| **U0/U1 chart smooth** | `chartSpec_smoothOfRelativeDimension` 15:55:41；`chartSpec2_smoothOfRelativeDimension` 16:42:12 | **A-局部 CLOSED（两 chart）** |
| **G-A glued smooth** | `CurveSmoothFinal` 当前源只有 two-chart cover；smooth 主定理已删；旧 attempts 均 sorryAx | **OPEN / 禁引** |
| **(h) 几何整性/连通** | `ChartCover.chartOpenFamily_iSup_eq_top`（17:31:53，三公理）；环层 `SmoothIntegral.fermatCurveRing_isDomain`（00:37:00）；**无** scheme 层 `IsIntegral (fermatCurveScheme n)` / 几何连通定理 | **OPEN**（cover 已交，整性/连通未做） |
| **B1 ψ** | `overlapToCurve_condition`（17:00:24，P20）；`hcomp_right_eq`（17:30:23，三公理）；当前 `hcomp_left_eq` 17:32:21 红 | **cocycle/right leg 局部 CLOSED；global ψ 未交** |
| **C4 / Step VIII** | `hVh_of_labelData`（17:28:11，P20c）；`hV_of_L814_data`（17:24:39）；`LabelStepVHullData` NO INHABITANT；T-side `hviTable_instance_of_labelData` 红 | **C4 仍条件式**（htheta/hiii/hvii/hX/hVh） |
| **H-T 8.1/8.2** | Core 17:10:03 编译；8.1 `HT81Interface` 仍结构 NO INHABITANT；`hdelta` 仍是假设 | **8.2 core 局部；8.1 未做** |
| **U-R C2** | `URThetaHullGeneric` 17:27:00 四条三公理；`URThetaHullTensor` 17:32:23 stage-1 五条 | **stage 1 CLOSED；主不等式仍缺** |
| **R2/U0 smooth；D3；P¹ 三模型** | 同 batch19 | D3 NO INHABITANT；P¹ 无 iso；不重复 |

## 3r. Probe 20 / 20b / 20c（本批 batch 20）

- **Probe 20**（`tmp/sheaf/xif/paper/_ProbeBatch20Actual.lean`）：`node tools/wd_add.mjs` 17:23 排队（total 197）→ **START 17:23:43 → DONE 17:24:16（33 s）**；log 1155 B，**0 error / 0 sorryAx**，8 条全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | 证据版本（probe 时磁盘 olean） |
|---|---|---|
| `Mzk1G1FermatPiFiniteChartActual.isFinite_pi_of_chart0_restrict` | [propext, Classical.choice, Quot.sound] | **17:17:53**（源内无 #print；P20 独立复算） |
| `Mzk1G1FermatPiFiniteChartActual.isFinite_pi_of_chartInf_restrict` | [propext, Classical.choice, Quot.sound] | 17:17:53 |
| `Mzk1G1FermatPiFiniteChartActual.isFinite_pi` | [propext, Classical.choice, Quot.sound] | 17:17:53（消费两条 restriction） |
| `Mzk1G1FermatPiRestrictFiniteActual.isFinite_pi` | [propext, Classical.choice, Quot.sound] | **17:16:42**（`PiProper._final` 消费的版本） |
| `Mzk1G1FermatPiRestrictFiniteActual.isFinite_pi_restrict_chart0` | [propext, Classical.choice, Quot.sound] | 17:16:42 |
| `Mzk1G1FermatPiProperActual.fermatCurveToSpec_isProper_final` | [propext, Classical.choice, Quot.sound] | **17:19:18**（G-A proper 出口） |
| `Mzk1G1PsiGlobalActual.overlapToCurve_condition` | [propext, Classical.choice, Quot.sound] | **17:00:24**（B1④ cocycle condition） |
| `Mzk1G1ConductorDifferentCancellationCoreActual.log_natAbs_discr_tower` | [propext, Classical.choice, Quot.sound] | **17:10:03**（H-T 8.2 tower） |

- **Probe 20b**（`_ProbeBatch20bActual.lean`）：17:27 排队（total 198）→ **DONE 17:27:44（29 s）**；log 436 B，3 条全部三公理：`PiRestrictFinite.isFinite_pi_restrict_chartInf`、`restrict_eq_chart0`、`restrict_eq_chartInf`（均 17:16:42 olean）。补足 §2s-1#3 的源内无 #print 项。
- **Probe 20c**（`_ProbeBatch20cActual.lean`）：17:29 排队（total 200）→ **DONE 17:30:52（59 s）**；log 551 B，4 条全部三公理：`Mzk1ULHviTableInstanceActual.hVh_of_labelData`、`hVh_of_paperBound_letters'`、`hviTable_instance`、`labelDifferentSum_nonneg`（均 **17:28:11** olean；当前源 17:28:37 已红，不能混用）。
- 版本纪律：8+3+4 条均按 probe 时刻磁盘 olean 复算；`CurveSmoothFinal` 无 olean/无当前定理，**不在 probe 内**；`hV_of_L814_data`、`chartOpenFamily_iSup_eq_top`、`hcomp_right_eq`、`thetaRegion_zero_eq_holomorphic` 只按各自当前 attempt 日志末段三公理记录（未单独 probe）。三个 probe **均未运行** `lake env lean`、未自起 watchdog、未写 sorry/axiom、未 spawn_teammate。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 20 续）

### 4.153 【高·G-A 正结论】proper 出口真实 CLOSED，但只能冻结在 proper
- `Mzk1G1FermatPiProperActual.fermatCurveToSpec_isProper_final (n) (hn) : IsProper (fermatCurveToSpec n)`（src 107–110）17:19:19 DONE；P20 三公理，无 sorryAx。证明链：`fermatCurveToSpec_isProper_cond` 消费 `Mzk1G1FermatPiRestrictFiniteActual.isFinite_pi n hn`（17:16:42，P20）与 `Mzk1P1ProperFinalActual.p1GluedToBase_isProper`（15:53:12，P17）；`fermatCurveToBase_isProper` 再用 `pi ≫ p1GluedToBase` 的 finite⇒proper 复合作 proper；两条“到 Spec ℚ 的态射唯一”用 `Subsingleton.elim` / `subsingleton_hom_spec_rat`。
- 因此 **G-A 的 proper 出口可正式记为 CLOSED**；引用写 17:19:18 olean + 声明名 `fermatCurveToSpec_isProper_final`。**不得据此写 Y_n smooth/几何整性/degree**；proper 的证明不经过 smooth 或整性。

### 4.154 【高·G-A】glued smooth 仍 OPEN，且当前源已删掉主定理
- `Mzk1G1FermatCurveSmoothFinalActual` 从未 DONE；17:04:49–17:31:54 的多次 attempt 全部 FAIL，19118 B 日志含 32/35/36/56/62 行错误、universe metavariable，末段 `fermatCurveToSpec_smoothOfRelativeDimension` 带 **sorryAx**。
- 17:32:21 的当前源（2438 B）已把该定理删除，只剩 `chartOpenFamily` / `chartOpenFamily_zero/one` / `chartOpenFamily_iSup_eq_top`；当前 paper 源 grep `fermatCurveToSpec_smoothOfRelativeDimension` 为 **0**。故“当前源红”更准确说是“**当前源没有 smooth 主定理**”，旧 attempts 的 sorryAx 只作历史。
- 不得把 `ChartCover.chartOpenFamily_iSup_eq_top`（17:31:53）或 chart-level `chartSpec(_2)_smoothOfRelativeDimension`（15:55:41 / 16:42:12）写成 **glued** smooth；后者只覆盖 U0/U1。

### 4.155 【高·G-A (h)】两 chart cover 已交，几何整性/连通仍无陈述
- `Mzk1G1ChartCoverActual.chartOpenFamily_iSup_eq_top` **DONE 17:31:53**（src 17:30:27 / 1777 B；olean 17:31:53 / 59776 B；log 末段三公理；旧段 34:36/35:6 的 sorryAx 已过）。它给出 `iSup (chartOpenFamily n) = ⊤`，是 route §2.4 (h) 的 cover 输入。
- 但 scheme 层 **`IsIntegral (fermatCurveScheme n)` / 几何连通**仍无任何定理（grep 0）；只有环层 `Mzk1G1FermatSmoothIntegralActual.fermatCurveRing_isDomain`（00:37:00，A-局部）与 chart 层有限性。route §2.4 要求“两 chart 整 + 重叠非空稠密 ⇒ glue 整/几何连通”，**该步未写**。不得把 ChartCover 当 (h) 已交。

### 4.156 【中·B1】cocycle condition 与 right leg 已 CLOSED，global ψ 仍被 hcomp_left 卡住
- `Mzk1G1PsiGlobalActual.overlapToCurve_condition` 17:00:24 DONE（P20 三公理）：两 overlap 包含到 Y_n 的复合相等，即 glue condition 的用户级等式；`Mzk1G1PsiHcompRightActual.hcomp_right_eq` 17:30:23 DONE（4 条三公理）。这是 B1④ 的两个真实组件。
- 但当前 `PsiGlobal` 源（17:30:46 / 4619 B）在 17:32:21 FAIL：`hcomp_left_eq` 有 **unsolved goals + sorryAx**（目标只是 `Category.assoc` 方向的复合等式）。**global ψ 未组装**；不得写“ψ 全局已交”。下一步用 `glueMorphisms` + 两条 condition/leg 装配，并修 hcomp_left。

### 4.157 【中·C4】hVh 已桥到 LabelStepVHullData（NO INHABITANT），T-side 实例当前红
- `Mzk1ULHviTableInstanceActual` 17:28:11 olean（P20c 三公理）：`hVh_of_labelData` 由 `LabelStepVHullData` 的 `hpaper`（L814 输出）与 `hexc` 直接得 donor `collectionBound` 上界；`Mzk1ULStepVHullPaperActual.hV_of_L814_data`（17:24:39，P20 未含，日志三公理）提供 `hpaper` 的 L814 形状；`hVh_of_paperBound_letters'` 把 hVh 化为 paper/exceptional 两条不等式。
- 但 `Mzk1URLabelDataActual.LabelStepVHullData`（17:22:44，764216 B）是 **structure，NO INHABITANT**；`hviTable_instance_of_labelData` 在 17:28:37 源中新增，17:31:07 因 244:6 isDefEq timeout + 285:14 unknown 红。**C4 仍条件于 htheta/hiii/hvii/hX + LabelStepVHullData 的 varpi/Phi/hexc 几何识别**；引用只写 17:28:11 的 `hVh_of_labelData` / `hviTable_instance`，不要引当前源的新定理。

### 4.158 【中·H-T】8.2 core 已编译，8.1 仍接口；hdelta 仍是假设
- `Mzk1G1ConductorDifferentCancellationCoreActual` 17:10:03 DONE（src 5611 B，olean 235504 B）：`log_natAbs_discr_tower`（P20 三公理）是真证明（`discriminant_tower_formula_ringOfIntegers` + log 乘法），`log_absNorm_differentIdeal_eq` 由它 linarith；`conductorDifference_le_differentTerm` 仍以 `hdelta : ∀ w, e w − 1 ≤ differentExponent w` 为假设，不是无条件下界。
- `Mzk1HT81InterfaceActual`（16:56:23）仍是结构 + `HT81LineBundleHeights`，0 定理、NO INHABITANT。**不得把 Core 编译写成 8.1/8.2 已交**。

### 4.159 【低·U-R】stage 1 两件 CLOSED，C2 主不等式仍缺
- `Mzk1URThetaHullGenericActual` 17:27:00 DONE（4 条三公理）：非负系数 scaled region ⊆ O_hol、zero-label region = O_hol、theta image set ⊆ O_hol；`Mzk1URThetaHullTensorActual` 17:32:23 DONE（5 条三公理）是 tensor-lattice congruence / ball-ceil stage 1。17:28:22–17:29:39 的中间尝试（`urNonzeroLabelHullLog` / timeout / sorryAx）已被 17:30:05 回退，**不是当前内容**。
- 这些都**不是** `actualLocalHullLog b ≤ −thetaCoefficientContribution b`；C2 主不等式仍未写/未证。不得把 stage 1 当 C2 闭合。

### 4.160 【低·纪律】本窗口版本陷阱清单
- `PiFiniteChart`：16:50:10 旧 olean（38512 B）只有 `piChart0_eq_lamSpec` + 两条 range 平凡引理；17:17:53 才是 finite restriction + `isFinite_pi`。`PiRestrictFinite`：16:58:22 旧 red，17:16:42 才是当前。
- `PsiGlobal`：16:50:10/17:00:24 只有 `psiChart0/1` + condition；17:30:46 源新增 `hcomp_left_eq` 且 17:32:21 红；引用必须写 17:00:24。
- `HviTableInstance`：17:16:00（无 `hVh_of_labelData`）→ 17:28:11（有，P20c）→ 17:28:37 源（新增 T-side，红）；三个版本不可混用。
- `CurveSmoothFinal`：旧 attempts 的 sorryAx、17:32:21 的 cover-only 源、无 olean 三者必须分开；`URThetaHullTensor` 17:10:28 / 17:29:39 红 / 17:32:23 stage-1 三个 attempt 分开；`ChartCover` 日志前段 sorryAx 是旧 attempt，末段三公理才是当前。
- `URLabelData` 17:22:44 DONE 但 log 0 B（无 #print）；`LabelStepVHullData` 的存在不等于 inhabitant。

### 4.161 【低·probe 覆盖】未独立 probe 的新 DONE 定理
- `ChartCover.chartOpenFamily_iSup_eq_top`、`ULStepVHullPaper.hV_of_L814_data`、`PsiHcompRight.hcomp_right_eq`、`URThetaHullGeneric.thetaRegion_zero_eq_holomorphic` 目前只按各自当前 attempt 日志末段三公理记录；若下批要作正式出口，建议各加一条 probe。`CurveSmoothFinal` 无 olean，不能 probe。

## 5p. batch 20 立即动作（快照 17:32 UTC）

1. **G-A proper（冻结）**：`fermatCurveToSpec_isProper_final` 17:19:18 已三公理 CLOSED；不要再改 PiProper / PiRestrictFinite / PiFiniteChart 的 proper 链。下游引用写“Y_n ⟶ Spec ℚ proper（17:19:18）”。
2. **G-A smooth（最高优先，当前 OPEN）**：当前 `CurveSmoothFinal` 只剩 cover。恢复 `fermatCurveToSpec_smoothOfRelativeDimension` 时，直接用 `Mzk1G1ChartCoverActual.chartOpenFamily_iSup_eq_top`（17:31:53）作 cover，改用 `IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)`；上一轮 35:36/36:6/56:8/62:8 的 motive/universe 错误要按 `change … ((opensRange).ι ≫ f)` 统一 carrier，再 `rw [fermatCurveToSpec_ι0/ι1]`。**在 DONE 且 #print 无 sorryAx 前，不得写 glued smooth 已交。**
3. **(h) 几何整性/连通（G-A §2.4 出口）**：用 ChartCover + 两 chart 环层整性（`fermatCurveRing_isDomain` 00:37:00、R2 侧同）与重叠非空稠密，写 scheme 层 `IsIntegral (fermatCurveScheme n)` / 几何连通；**当前无陈述**，先写陈述再证。不得用 ChartCover 冒充。
4. **B1 ψ**：用 `overlapToCurve_condition`（17:00:24）+ `hcomp_right_eq`（17:30:23）经 `glueMorphisms` 组装 global ψ；先修当前 `hcomp_left_eq`（17:30:46 源，17:32:21 红，复合 assoc 方向）。在 DONE 前不写“ψ 全局”。
5. **C4**：`hVh_of_labelData`（17:28:11，P20c）已把 hVh 缩到 `LabelStepVHullData`；下一步构造该结构的 inhabitant（varpi/Phi/hexc/`hpaper` 的几何识别），并修 `hviTable_instance_of_labelData` 的 244:6 timeout / 285:14 unknown。C4 仍条件式，不得写闭合。
6. **H-T**：8.2 Core 已编译；8.1 `HT81Interface` 仍 NO INHABITANT，继续按 8.1 构造；`hdelta` 保持显式假设。
7. **U-R / D3**：C2 主不等式 `actualLocalHullLog ≤ −thetaCoeff` 仍未写；D3 仍无 `HeightDictionaryInterface` 实例（同 batch19）。
8. **版本纪律（强制）**：PiFiniteChart 只引 17:17:53；PiRestrictFinite 只引 17:16:42；PiProper 只引 17:19:18；Close/Close2 只引 16:44:16/16:50:10；PsiGlobal 只引 17:00:24（当前源红）；HviTableInstance 只引 17:28:11（当前源红）；URLabelData 只引 17:22:44；ULStepVHullPaper 只引 17:24:39；URThetaHullGeneric 只引 17:26:59；ChartCover 只引 17:31:53；URThetaHullTensor 只引 17:32:22（stage-1 五条）；CurveSmoothFinal 无 olean/禁引。

## 6r. batch 20 更新（快照 **17:32 UTC = 2026-11-17 01:32 CST**；覆盖 §6–§6q 的旧结论，旧文保留）

- **已运行（本批）**：`Get-Item` src/olean/log 对照（30+ 文件）；`watchdog.log` 按 attempt 过滤（16:59:41–17:32:23）；per-file log 逐个读取（PiFiniteChart 847 B、PiRestrictFinite 134 B、PiProper 1870 B、PsiGlobal 710 B、ConductorCore 492 B、URThetaHullTensor 718 B、URThetaHullGeneric 597 B、ULStepVHullPaper 130 B、ChartCover 28 行（末段）、CurveSmoothFinal 19118 B、Probe20/20b/20c）；源码阅读（PiFiniteChart 143 行、PiRestrictFinite 133 行、PiProper 117 行、CurveSmoothFinal 50 行、PsiGlobal 66+ 行、ConductorCore 118 行、HviTableInstance 202+ 行、URLabelData 107 行、ULStepVHullPaper 77 行、URThetaHullGeneric 128 行、URThetaHullTensor 125 行、ChartCover 54 行、PsiHcompRight 67 行）；grep（`fermatCurveToSpec_smoothOfRelativeDimension` 0、`SmoothOfRelativeDimension 1 (fermatCurveToSpec` 0、`IsIntegral (fermatCurveScheme` 0、`ConnectedSpace (fermatCurveScheme` 0、`fermatCurveRing_isDomain`、`LabelStepVHullData`、`hVh_of_labelData`）。
- **Probe 20 / 20b / 20c**：8 / 3 / 4 条全部三公理、0 error/0 sorryAx；DONE 17:24:16 / 17:27:44 / 17:30:52。**未运行** `lake env lean`、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**；仅写本表与三个 probe 文件（未改其它 Lean 文件）。
- **未覆盖 / 未运行（如实标注）**：17:32:23 之后（`CurveSmoothFinal` 当前 cover-only、`PsiGlobal` 17:32:21 红、`HviTableInstance` 17:31:07 红、`URThetaHullTensor` 17:32:23 之后的再改）；`ChartCover`/`URThetaHullGeneric`/`URThetaHullTensor`/`ULStepVHullPaper`/`PsiHcompRight` 只按日志末段，未独立 probe；G-A (h) 的 scheme 层整性/连通无陈述；G-K/H-T/P8-P 端到端与 F1–F4/F8 仍未做语义审计；未重读 paper 原文（行号 provenance 沿用既有记录）。

### 6s. 快照后补记（**17:32:23–17:34:40**；覆盖 §2s-2 #360/#363、§4.156/§4.157、§5p 第 4/5 条的当前状态；旧行保留）

- **PsiGlobal 17:34:36 DONE（关键翻转）**：src 17:32:41 / 4635 B；olean 17:34:36 / 71800 B；log 13 行，四条打印**全部三公理**：`hcomp_left_eq`、`psiChart0`、`psiChart1`、`overlapToCurve_condition`。`hcomp_left_eq` 的证明是 `chart0ToOverlap ≫ fermatChart0ToCurve = … ≫ overlapToChart0 ≫ fermatChart0ToCurve`，用 `rToOverlap`/`alpha_comp_algebraMap` 与 `simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]` 收尾。**B1④ 的 hcomp left leg 现已 CLOSED**；但源内仍**只有两个 chart def + condition/left leg**，**没有 global ψ 的 def**（无 `psiGlobal`/`glueMorphisms` 装配）。所以：**B1④ 两 leg + cocycle condition 组件齐；global ψ 仍未组装**。§2s-2 #360 与 §4.156 的“当前源红”**已被 17:34:36 覆盖**；引用 hcomp_left 只写 17:34:36 olean。
- **HviTableInstance 17:33:43 DONE（C4 hVh 桥稳定）**：src 17:31:55 / 13465 B；olean 17:33:43 / 240000 B；log 8 行只含 `hVh_of_labelData` 一条三公理。当前源已**删除** 17:28:37 版里失败的 `hviTable_instance_of_labelData`（T-side），只保留 `hVh_of_labelData`/`hviTable_instance`/`hVh_of_paperBound_letters'`。P20c 对 17:28:11 olean 的 `hVh_of_labelData` 三公理仍成立、声明名未变。**§2s-2 #363 的“17:28:37 源红”仍适用于 T-side 失败 attempt，但 17:33:43 的源已回到“只到 hVh 桥”的稳定状态**；C4 仍差 `LabelStepVHullData` 的 inhabitant。
- **ULStepVIII 17:33:50 FAIL（当前源未重编）**：src 17:34:08 / 29504 B，**当前源晚于最后一次 FAIL**；无当前 attempt 日志（0 B/被清）。最后有效 olean 仍是 **16:58:55 / 1620816 B**（8 条三公理，含 `hstepVIII_of_collectionLayer`/`uc_c4_of_retained`）。**不得把 17:34:08 源的新内容当已编译**；C4 引用仍写 16:58:55。
- **ConductorDifferentCancellationAssembly（新文件）17:33:14 / 17:34:38 FAIL**：src 17:33:45 / 3466 B；无 olean；log 只 50:77 `unexpected identifier; expected '}'` + `f2_of_witness` 带 **sorryAx**。H-T 8.1 的 assembly 尝试仍红，未产生可用声明。
- **CurveSmoothFinal 仍无 olean**：src 17:34:35 / 2308 B，当前源仍只含 `chartOpenFamily` 与 `chartOpenFamily_iSup_eq_top`（无 smooth 主定理）；§2s-1#4/§4.154 的 G-A glued smooth OPEN 不变。
- **URThetaHullTensor 17:34:06 起重试 → 17:35:21 FAIL**：src 17:33:12 / 7529 B，ole 仍 17:32:22（stage-1 五条）；**当前源红**（新 attempt 失败），**17:32:23 的 stage-1 证据仍为最后有效**，主不等式不变；不得引 17:33:12 源的新内容。

## 2t. batch 21 gate 表（快照 **17:44:18 UTC = 2026-11-17 01:44 CST**；覆盖 **17:34:40–17:44:18**；旧行全保留）

- 证据版本：src/olean/log 均 Get-Item 实测；**(P21)** = §3s 独立 probe；log 只取当前 attempt（单文件日志跨 attempt 追加/清空）。**17:44:18 之后未审计**（PsiGlobal src 17:44:18、JHeightUniform src 17:43:24、URThetaHullNonzero src 17:42:53、HT84F4F5 src 17:43:35 在飞或已改写，见 §6t）。
- 本窗口全量事件（按 attempt）：17:34:36 PsiGlobal DONE；17:34:38 ConductorAssembly FAIL；17:35:21 URThetaHullTensor FAIL；17:36:09 SmoothFinal DONE（cover-only）；17:36:10 JHeightUniform FAIL；17:36:45 ULStepVIII FAIL；17:37:24/37:44/38:04 HT84 重试；17:37:31 PsiGlobal FAIL / SmoothFinal FAIL；17:37:33 ConductorAssembly FAIL；17:38:23 HT84 FAIL；17:39:08 PsiHcompMain FAIL；17:39:09 PsiGlobal DONE；17:39:10 JHeightUniform FAIL；17:39:43 ULStepVIII DONE；17:40:31 SmoothFinal DONE；17:40:32 JHeightUniform DONE；17:40:33 ConductorAssembly DONE；17:40:59 HT84 FAIL；17:42:03 URThetaHullNonzero FAIL；17:42:52 PsiGlobal FAIL；17:42:54 RelativeDifferentNorm DONE；17:42:58 PsiGlueCompat FAIL；17:43:19 HT84 FAIL；17:43:21 ULStepVIIIInstances DONE；17:44:09 Probe 21 DONE。

### 2t-1 Lead 指定项复核（判定按当前 olean/当前源，不按旧日志）

| # | 指定项 | 证据（src / olean / log） | 判定 / 处置 |
|---|---|---|---|
| 1 | **SmoothFinal 17:40:31** | src 17:38:39 / 5890 B；olean **17:40:31 / 125912 B**；log 652 B 四条打印**全部三公理**（chartOpenFamily_iSup_eq_top、chart0_restrict、chartInf_restrict、主定理）；**P21 独立复算主定理 + 两 restriction + 本文件 cover 均三公理**；源 96–105 行 | **G-A smooth 出口 CLOSED**：fermatCurveToSpec_smoothOfRelativeDimension (n) (hn) : SmoothOfRelativeDimension 1 (fermatCurveToSpec n)。证明 = IsZariskiLocalAtSource.iff_of_iSup_eq_top + 两条 chart restriction（IsOpenImmersion.isoOfRangeEq + MorphismProperty.arrow_mk_iso_iff），chart 腿引 15:55:41 U0 / 16:42:12 U1。引用写 **17:40:31 olean**；结论只对 hn : 0 < n。 |
| 2 | **17:36:09 cover-only 中间版** | 17:36:09 DONE 时 src 17:34:35 / 2308 B，只含 chartOpenFamily / chartOpenFamily_iSup_eq_top，**无 smooth 主定理**；17:37:31 FAIL；17:04:49–17:37 的旧 attempt 全红（19118 B 日志含 sorryAx/类型错误） | **不是出口、禁引**；只作历史。当前源（17:38:39）与 17:40:31 olean 才含主定理。 |
| 3 | **PiProper（G-A proper）** | src 17:18:49 / 5762 B；olean **17:19:18 / 45432 B**；P20 + **P21 三公理**；未再改 | **G-A proper CLOSED**；与 smooth **同一** fermatCurveToSpec : fermatCurveScheme n ⟶ Spec ℚ。引用 fermatCurveToSpec_isProper_final（17:19:18）。 |
| 4 | **G-A 两出口并列 + 两 chart smooth** | proper 17:19:18；smooth 17:40:31；chart 层 chartSpec_smoothOfRelativeDimension（src 15:54:15 / olean **15:55:41** / 245472 B）与 chartSpec2_smoothOfRelativeDimension（src 16:40:23 / olean **16:42:12** / 477776 B）均未改 | **G-A = proper + smooth 双出口 CLOSED**；chart 层只覆盖 U0/U1，不得替代 glued smooth（本批已不需要替代）。 |
| 5 | **(h) 几何整性/连通** | ChartCover 17:31:53 / 59776 B（P21 三公理）；paper 目录 grep IsIntegral (fermatCurveScheme / ConnectedSpace (fermatCurveScheme = **0**；S2611CurveSkeleton 只是带 geomConn 字段的通用 skeleton | **cover CLOSED；(h) 仍 OPEN**：scheme 层 IsIntegral/几何连通无陈述。不得用 ChartCover 冒充 (h) 已交。 |
| 6 | **ULStepVIII 当前源** | src 17:37:58 / 29468 B；olean **17:39:42 / 1819960 B**；log 1032 B **八条打印全部三公理**；二进制含 hiii_of_stepII_and_sQ、**无 sorryAx**；源 538–557 是新标量 narrowing（hii+hsQ ⇒ hiii） | **B（C4 条件式）**：17:39:42 是当前口径；C4 仍条件于 htheta/hiii/hX/hlogSQ，不得写闭合。16:58:55 旧版已被取代。 |
| 7 | **ConductorAssembly 17:34:38 parse error** | 已翻绿：src 17:39:04 / 2782 B；olean **17:40:32 / 121072 B**；log 152 B **f2_of_witness 三公理**；结构 F2PlaceWitness（places/constant/hdelta/hdifferent，自注 NO INHABITANT） | **B 条件式（H-T 8.2 assembly）**：17:34:38 的 unexpected identifier 已修；不是 8.1/8.2 闭合。 |
| 8 | **URThetaHullTensor current** | src 17:36:00 / 5885 B；olean **17:37:57 / 91136 B**；log 718 B **五条三公理**（congr/const_eq_single/urRootCoeff_nonneg/urCeilCoeff_ge/urLocal_ball_eq_ceil） | **A-局部 stage-1**：17:37:57 是当前最后好版本；主不等式 actualLocalHullLog ≤ −thetaCoeff 仍无。 |
| 9 | **PsiGlobal 17:34:36 hcomp_left_eq** | 17:39:09 olean 77144 B（src 当时更早）含 hcomp / hcomp_left_eq；17:42:52 FAIL：91:6 **pullback unknown**（缺 open CategoryTheory.Limits），该 attempt log 中 **hcomp / hcomp_left_eq 均三公理**；二进制无 wToPullback；当前 src 17:44:18 / 6033 B 又改 | **hcomp CLOSED（17:39:09 olean；17:42:52 log 三公理）；wToPullback 红；全局 ψ 未组装**。wToPullback 的修法是补 open CategoryTheory.Limits（或 open Limits）。 |
| 10 | **PsiHcompRight / HviTableInstance** | PsiHcompRight src 17:28:38 / 3749 B，olean 17:30:23 / 77760 B；HviTableInstance src 17:31:55 / 13465 B，olean 17:33:43 / 240000 B | 两者均未改；维持 B（hcomp right leg；hVh 桥）。 |
| 11 | **新文件（17:40Z 后）** | PsiGlueCompat 17:42:58 红；URThetaHullNonzero 17:42:03 红；RelativeDifferentNorm 17:42:54 DONE；ULStepVIIIInstances 17:43:21 DONE；HT84F4F5 17:40:59/17:43:19 红；PsiHcompMain 17:39:08 红后文件被删 | 详见 §2t-2；均不改变 G-A/C4 主判定。 |

### 2t-2 本窗口新增 DONE / FAIL（#372–#387，按 attempt 计）

| # | 文件 | 事件（UTC） | 证据 | 判定 |
|---|---|---|---|---|
| 372 | Mzk1G1FermatCurveSmoothFinalActual | **DONE 17:40:31**（17:36:09 cover-only DONE；17:37:31 FAIL） | src 17:38:39 / 5890 B；olean 125912 B；log 652 B 四打印三公理；P21 三公理 | **A（G-A smooth 出口）**；见 §2t-1#1/#2。 |
| 373 | Mzk1G1FermatPiProperActual | DONE 17:19:19（未改） | src 17:18:49 / 5762 B；olean 17:19:18 / 45432 B；P20+P21 | **A（G-A proper 出口）**；见 §2t-1#3。 |
| 374 | Mzk1ULStepVIIIActual | **DONE 17:39:42** | src 17:37:58 / 29468 B；olean 1819960 B；log 1032 B 八打印三公理；二进制含 hiii_of_stepII_and_sQ、无 sorryAx | **B（C4 条件式）**；见 §2t-1#6 / §4.166。 |
| 375 | Mzk1G1ConductorDifferentCancellationAssemblyActual | **DONE 17:40:33**（17:34:38/17:37:33 曾 FAIL） | src 17:39:04 / 2782 B；olean 121072 B；log 152 B f2_of_witness 三公理 | **B 条件式（H-T 8.2）**；F2PlaceWitness NO INHABITANT；见 §2t-1#7 / §4.167。 |
| 376 | Mzk1G1JHeightUniformActual | **DONE 17:40:32** | src 17:39:43 / 9385 B；olean 187288 B；log 961 B 五打印三公理（coeffAbsSum_coeff_le/add_le/C_mul_le、support_card_le、coeffAbsSum_mul_le）；源内无 HeightDictionaryInterface | **B infra（非 uniform D3）**；见 §4.168。 |
| 377 | Mzk1URThetaHullTensorActual | **DONE 17:37:57**（17:35:21 曾 FAIL） | src 17:36:00 / 5885 B；olean 91136 B；log 718 B 五打印三公理 | **A-局部 stage-1**；见 §4.169。 |
| 378 | Mzk1G1PsiGlobalActual | **DONE 17:39:09**（17:37:31 旧红）；**17:42:52 FAIL**；src 17:44:18 又改 | 17:39:09 olean 77144 B；二进制有 hcomp/hcomp_left_eq、无 wToPullback；17:42:52 首错 91:6 pullback unknown；该 log 中 hcomp/hcomp_left_eq 三公理 | **B−（hcomp CLOSED；wToPullback 红）**；见 §4.164。 |
| 379 | Mzk1G1PsiGlueCompatActual（新） | **FAIL 17:42:58** | src 17:42:13 / 4531 B；无 olean；首错 wToPullback unknown（PsiGlobal olean 17:39:09 无该声明）；psi 定义条件于 [IsIso (wToPullback n T)] | **R / 条件式（全局 ψ 未交）**；见 §4.165。 |
| 380 | Mzk1G1PsiHcompRightActual | DONE 17:30:23（未改） | src 17:28:38 / 3749 B；olean 77760 B | **B（hcomp right leg）**。 |
| 381 | Mzk1ULHviTableInstanceActual | DONE 17:33:43（未改） | src 17:31:55 / 13465 B；olean 240000 B | **B 条件（hVh 桥）**。 |
| 382 | Mzk1URThetaHullNonzeroActual（新） | **FAIL 17:42:03** | src 17:39:15 / 7778 B；无 olean；log 2947 B；首错 148:4 rewrite actualRootThetaHull 未命中；4 条定理落 sorryAx（urRootThetaImageSet_subset_holomorphic、urRootThetaHull_eq_holomorphic、urActualLocalHullLog_eq_zero、urActualThetaHullLogRoot_eq_zero） | **R**；见 §4.169。 |
| 383 | Mzk1G1RelativeDifferentNormActual（新） | **DONE 17:42:54** | src 17:41:38 / 2321 B；olean 216416 B；log 1 打印三公理（differentTerm_le_log_absNorm） | **B（H-T 8.2 helper）**；结构 RelativeDifferentNormData 无 inhabitant。 |
| 384 | Mzk1ULStepVIIIInstancesActual（新） | **DONE 17:43:21** | src 17:41:02 / 3340 B；olean 24120 B；log 0 B（无 #print）；二进制无 sorryAx；hviTable_instance_letters 条件于 hVh | **B 条件（C4 letters-level glue）**；不改变 C4 条件。 |
| 385 | Mzk1HT84F4F5InterfaceActual（新） | **FAIL 17:40:59 / 17:43:19** | src 17:43:35 / 5899 B；无 olean；首错 111:9 unfold F5Statement 失败；f5Statement_of_labelTl 带 sorryAx；f4_two 两条三公理 | **R（H-T 8.4/8.5 接口未编译）**；见 §4.170。 |
| 386 | Mzk1G1PsiHcompMainActual（新，已删） | **FAIL 17:39:08** | log 864 B：overlapToCurve_condition 被当函数应用；hcomp 带 sorryAx；之后 src 消失 | **不采**（文件已删；同名功能由 PsiGlobal 的 hcomp 承担）。 |
| 387 | _ProbeBatch21Actual | **DONE 17:44:09（33 s）** | log 937 B；6 条全部三公理、0 error/0 sorryAx | 见 §3s。 |

### 2t-3 缺口表（17:44 口径；旧 §2s-3 保留）

| 缺口 | 当前证据 | 状态 |
|---|---|---|
| **G-A proper** | PiProper.fermatCurveToSpec_isProper_final（17:19:18，P20+P21） | **CLOSED** |
| **G-A smooth** | SmoothFinal.fermatCurveToSpec_smoothOfRelativeDimension（17:40:31，P21） | **CLOSED** |
| **(h) 几何整性/连通** | ChartCover 17:31:53（P21）；paper 目录 scheme 层 IsIntegral/ConnectedSpace 陈述 = 0 | **cover CLOSED；(h) OPEN** |
| **B1 ψ** | hcomp 17:39:09（17:42:52 log 三公理）；wToPullback 红；PsiGlueCompat psi 条件于 IsIso wToPullback（无 provider） | **组件齐、组装条件式；global ψ 未交** |
| **C4 / Step VIII** | ULStepVIII 17:39:42（8 条三公理，新增 hiii narrowing）；ULStepVIIIInstances 17:43:21；ConductorAssembly 17:40:33 | **C4 仍条件式**（htheta/hiii/hX/hlogSQ/hVh） |
| **U-R C2** | URThetaHullTensor 17:37:57 stage-1；URThetaHullNonzero 17:42:03 红/sorryAx | **stage-1 CLOSED；主不等式未交** |
| **H-T 8.1/8.2** | ConductorAssembly 条件式；RelativeDifferentNorm 17:42:54；HT84F4F5 红；HT81Interface NO INHABITANT | **8.2 局部/条件式；8.1 未交** |
| **uniform D3** | JHeightUniform 17:40:32（5 条 coeffAbsSum infra）；无 HeightDictionaryInterface 实例 | **NO INHABITANT / 未交付** |

## 3s. Probe 21（本批 batch 21）：tmp/sheaf/xif/paper/_ProbeBatch21Actual.lean

- node tools/wd_add.mjs 17:44 前排队（**total 208**）→ START 17:43:36 → **DONE 17:44:09（33 s）**；log **937 B**，0 error / 0 sorryAx，6 条全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | 证据版本（probe 时磁盘 olean） |
|---|---|---|
| SmoothFinal.fermatCurveToSpec_smoothOfRelativeDimension | [propext, Classical.choice, Quot.sound] | **17:40:31**（G-A smooth 出口） |
| SmoothFinal.smoothOfRelativeDimension_of_chart0_restrict | [propext, Classical.choice, Quot.sound] | 17:40:31 |
| SmoothFinal.smoothOfRelativeDimension_of_chartInf_restrict | [propext, Classical.choice, Quot.sound] | 17:40:31 |
| SmoothFinal.chartOpenFamily_iSup_eq_top | [propext, Classical.choice, Quot.sound] | 17:40:31（文件内重新证明的 cover） |
| ChartCover.chartOpenFamily_iSup_eq_top | [propext, Classical.choice, Quot.sound] | **17:31:53**（Lead 的 cover 文件，未改） |
| PiProper.fermatCurveToSpec_isProper_final | [propext, Classical.choice, Quot.sound] | **17:19:18**（G-A proper 出口） |

- 版本纪律：6 条均按 probe 时刻磁盘 olean 复算；**probe 未运行** lake env lean、未自起 watchdog、未写 sorry/axiom、未 spawn_teammate。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 21 续）

### 4.162 【高·G-A 正结论】smooth 出口真实 CLOSED，与 proper 并列
- SmoothFinal 17:40:31（src 17:38:39 / 5890 B；olean 125912 B）的 fermatCurveToSpec_smoothOfRelativeDimension (n) (hn) : SmoothOfRelativeDimension 1 (fermatCurveToSpec n) 由 IsZariskiLocalAtSource.iff_of_iSup_eq_top 归约到两条 chart restriction；chart restriction 用 IsOpenImmersion.isoOfRangeEq 得到 eW，再用 MorphismProperty.arrow_mk_iso_iff 把 (opensRange.ι ≫ f) 的 smooth 换回 (chartToCurve ≫ f)；chart 腿用 fermatCurveToSpec_ι0/ι1 与 15:55:41 / 16:42:12 的 chart smooth。log 四条与 P21 六条全部三公理。
- **结论**：G-A 的 §2.4 两个出口（proper 17:19:18、smooth 17:40:31）均为真实结构态射 fermatCurveToSpec : fermatCurveScheme n ⟶ Spec ℚ 的已证性质。**不得**由 smooth/proper 推出 (h)（整性/连通）或 degree；二者的证明互不依赖。

### 4.163 【高·纪律】SmoothFinal 的 17:36:09 DONE 是 cover-only，不是 smooth 出口
- 17:36:09 的 DONE 对应 src 17:34:35 / 2308 B，只含 chartOpenFamily + cover；17:37:31 又 FAIL；17:04:49–17:37 的旧 attempt 19118 B 日志含 sorryAx/类型错误。只有 17:40:31 的 olean（125912 B）含 smooth 主定理。
- **引用只写 17:40:31；不得用 17:36:09 的 DONE 说 smooth 已交，也不得引旧 attempt 的 sorryAx 当当前状态。**

### 4.164 【高·ψ】PsiGlobal：hcomp 已三公理，wToPullback 因缺 open CategoryTheory.Limits 红
- 17:39:09 olean（77144 B）含 hcomp、hcomp_left_eq、psiChart0/1、overlapToCurve_condition；二进制不含 wToPullback。17:42:52 的 attempt（src 17:40:46）在 91:6 报 **pullback unknown**（pullback.fst/snd/lift 随后全 unknown），错误恢复给 wToPullback 挂 **sorryAx**；但同一 attempt log 末尾 hcomp/hcomp_left_eq 仍三公理。
- 修法（emmy）：在 PsiGlobal 顶部补 open CategoryTheory.Limits（与 PsiGlueCompat 第 10 行一致），并把 wToPullback 的 pullback 端点写全；DONE 后再重编 PsiGlueCompat。**在 wToPullback 进 olean 前，不得用 PsiGlueCompat 的 psi。**

### 4.165 【高·ψ】PsiGlueCompat 是条件式全局 ψ，IsIso wToPullback 无 provider
- PsiGlueCompat（src 17:42:13 / 4531 B）用 (psiOpenCover n T).glueMorphisms 组装 psi : fermatCurveScheme n ⟶ projectiveLineGlued，并给 psi_ι_false/true；但 **psi 与 glueMorphisms_compat 都带 [IsIso (wToPullback n T)]**。所谓 emmy 的 isIso_wToPullback 在 paper 目录 grep **只出现在注释**，无声明。
- 17:42:58 FAIL 的直接原因是 import 的 PsiGlobal olean（17:39:09）没有 wToPullback（不是 ψ 本身数学错）。因此当前状态是：**B1④ 的 hcomp 组件 CLOSED、global ψ 组装代码存在但未编译、且 IsIso wToPullback 未证**。不得写“ψ 全局已交”。

### 4.166 【中·C4】ULStepVIII 17:39:42 为当前版，新增 hiii narrowing；C4 仍条件式
- src 17:37:58 / 29468 B，olean 17:39:42 / 1819960 B；log 八条三公理；二进制含新定理 hiii_of_stepII_and_sQ（源 538–557：hii+hsQ ⇒ (1+4/l)logDK+(4/l)logSQ ≤ (1+12d_mod/l)S_ar+2log l+52），是真标量证明、无 sorryAx。
- 但 uc_c4_of_retained 仍显式消费 htheta/hstepVIII；hstepVIII_of_collectionLayer 仍消费 hiii/hX/hlogSQ；ULStepVIIIInstances 17:43:21 只做 letters-level 实例（条件于 hVh）。**C4 仍条件式，不得写闭合**；16:58:55 旧版不再引用。

### 4.167 【中·H-T】ConductorAssembly 翻绿但只是条件式 F2；8.1/8.2 未交
- 17:40:33 DONE（src 17:39:04 / 2782 B；olean 121072 B）的 f2_of_witness : F2PlaceWitness H i Hh → F2 H i …；F2PlaceWitness 的 hdelta（∀w, e w −1 ≤ differentExponent w）与 hdifferent（differentTerm ≤ D(L)−D(K_i)）都是结构字段，自注 **NO INHABITANT**；实际证明只是 conductorDifference_le_differentTerm + hdifferent + linarith。
- 17:34:38 的 parse error 已修，但 HT81Interface 仍是结构、无 inhabitant；**不得把 f2_of_witness 当 8.1/8.2 闭合**。

### 4.168 【中·D3】JHeightUniform 17:40:32 仍是 coeffAbsSum infra
- src 17:39:43 / 9385 B；olean 187288 B；log 五条三公理：coeffAbsSum_coeff_le/add_le/C_mul_le、support_card_le、coeffAbsSum_mul_le。文件内无 HeightDictionaryInterface、无 uniform-in-K 高度比较。
- **uniform D3 仍 NO INHABITANT**；JHeightUniform 只算 infra。17:36:10/17:39:10 的 FAIL 是旧 attempt。

### 4.169 【中·U-R】URThetaHullNonzero 新文件红（sorryAx）；Tensor stage-1 不变
- URThetaHullNonzero（src 17:39:15 / 7778 B，无 olean）17:42:03 FAIL：148:4 rewrite actualRootThetaHull 在目标（含 closure actualRootThetaImageSet）中未命中；urRootThetaImageSet_subset_holomorphic、urRootThetaHull_eq_holomorphic、urActualLocalHullLog_eq_zero、urActualThetaHullLogRoot_eq_zero 四条带 **sorryAx**。该文件标题声称 theta=0 观察 + nonzero-label 路线，**不得引用其任何 sorryAx 定理**。
- URThetaHullTensor 17:37:57（src 17:36:00 / 5885 B）五条三公理，仍只是 tensor-lattice stage-1；C2 主不等式 actualLocalHullLog ≤ −thetaCoeff 未写。

### 4.170 【中·H-T】HT84F4F5 17:43:19 红后 17:44:35 翻绿（F4/F5 仍 NO INHABITANT；覆盖见 §6u）
- HT84F4F5Interface（src 17:43:35 / 5899 B，无 olean）17:43:19 FAIL：111:9 unfold F5Statement 在 hEi i ≤ hO1 y + 20/3*lstar + C_height 上失败；f5Statement_of_labelTl 带 **sorryAx**；f4Statement_of_f2_f3、f4_f5_combined 两条三公理。H-T 8.4/8.5 无可用结果。

### 4.171 【低·纪律】batch 21 版本/内容陷阱清单
- SmoothFinal：17:36:09 cover-only（src 17:34:35）、17:37:31 FAIL、**17:40:31 才是出口**；三者不可混用。
- PsiGlobal：17:39:09 olean（有 hcomp、无 wToPullback）≠ 当前 src 17:44:18（6033 B）；17:42:52 的 FAIL 日志里 wToPullback 带 sorryAx，但 hcomp 三公理；不要用当前 src 说 wToPullback 已交。
- PsiGlueCompat 17:42:58 的错误是 **stale import**（PsiGlobal olean 17:39:09 无 wToPullback），不是 psi 的数学错；但 psi 本身条件于 IsIso wToPullback。
- 单文件日志会在下一次 START 时被清空：URThetaHullNonzero/HT84 的 17:42–17:43 日志在 17:43:36 重启后已为 0；引用必须以已保存的 attempt 输出/olean 为准。
- PsiHcompMain 17:39:08 红后文件被删除；不要把它当现存文件或现有接口。
- 二进制检查：SmoothFinal/ULStepVIII/ConductorAssembly/URThetaHullTensor/ChartCover/PiProper/RelativeDifferentNorm/ULStepVIIIInstances/JHeightUniform 的当前 olean 均无 sorryAx；PsiGlobal 17:39:09 无 sorryAx。

## 5q. batch 21 立即动作（快照 17:44 UTC）

1. **G-A 双出口冻结（最高优先，已完成）**：proper 写 fermatCurveToSpec_isProper_final（17:19:18，P20+P21）；smooth 写 fermatCurveToSpec_smoothOfRelativeDimension（17:40:31，P21）。下游引用写“Y_n ⟶ Spec ℚ proper / rel-dim-1 smooth”。**不要**再改 SmoothFinal/PiProper 的证明链；**不得**由此推出 (h)/degree。
2. **(h)（G-A §2.4 剩余口）**：用 ChartCover.chartOpenFamily_iSup_eq_top（17:31:53）作 cover，配合环层 fermatCurveRing_isDomain（00:37:00，A-局部）与重叠非空/稠密，写 scheme 层 IsIntegral (fermatCurveScheme n) / 几何连通。**当前无陈述**，先陈述再证；不得用 ChartCover 冒充。
3. **PsiGlobal（emmy，最快修复）**：顶部补 open CategoryTheory.Limits（或 open Limits），使 91–104 行的 pullback/pullback.fst/snd/lift 可解析；重编到 DONE 后再重编 PsiGlueCompat。**随后**才谈 global ψ；注意 psi 仍条件于 [IsIso (wToPullback n T)]，isIso_wToPullback 只有注释、无声明，需另证（几何识别 overlap→pullback）。
4. **C4**：ULStepVIII 只引 17:39:42（8 条三公理），hiii_of_stepII_and_sQ 可用于 narrowing；hstepVIII_of_collectionLayer 仍条件于 hiii/hX/hlogSQ；ULStepVIIIInstances 17:43:21 只做 letters-level 条件 glue。**C4 仍条件式**。
5. **H-T**：ConductorAssembly 17:40:33 只给条件式 F2（F2PlaceWitness NO INHABITANT）；RelativeDifferentNorm 17:42:54 是 8.2 helper；HT84F4F5 17:43:19 红（f5Statement_of_labelTl sorryAx）。8.1 仍 HT81Interface NO INHABITANT；**不得写 8.1/8.2 已交**。
6. **U-R**：URThetaHullNonzero 17:42:03 红，先修 148:4 的 rewrite（目标用 closure (actualRootThetaImageSet …)，不是 actualRootThetaHull；改用 imageSet/closure 形式）并清掉四条 sorryAx；URThetaHullTensor 仍只到 stage-1，C2 主不等式未写。
7. **D3**：JHeightUniform 17:40:32 的 5 条只是 coeffAbsSum infra；真 uniform D3 仍需 HeightDictionaryInterface 实例或 D1AnalyticInput.qHeight + 单一 B。
8. **版本纪律（强制）**：SmoothFinal 只引 17:40:31；PiProper 只引 17:19:18；ULStepVIII 只引 17:39:42；ConductorAssembly 只引 17:40:32；URThetaHullTensor 只引 17:37:57；ChartCover 只引 17:31:53；PsiGlobal 的 hcomp 只引 17:39:09（wToPullback 禁引）；PsiGlueCompat 无 olean/禁引；URThetaHullNonzero/HT84F4F5 无 olean/禁引；JHeightUniform 只引 17:40:32。

## 6t. batch 21 更新（快照 **17:44:18 UTC = 2026-11-17 01:44 CST**；覆盖 §6–§6s 的旧结论，旧文保留）

- **已运行（本批）**：Get-Item src/olean/log 对照（15 个关键文件 + 新文件）；watchdog.log 按 attempt 过滤（17:34–17:44）；per-file log 读取（SmoothFinal 652 B、ULStepVIII 1032 B、ConductorAssembly 152 B、URThetaHullTensor 718 B、JHeightUniform 961 B、PsiGlobal 17:42:52 段、PsiGlueCompat、URThetaHullNonzero 2947 B、HT84、RelativeDifferentNorm、Probe 21 937 B）；二进制 olean 符号核验（SmoothFinal/ULStepVIII/ConductorAssembly/URThetaHullTensor/ChartCover/PiProper/JHeightUniform/PsiGlobal 的 hcomp 与 sorryAx）；源码阅读（SmoothFinal 112 行全文、PsiGlobal 114 行全文、PsiGlueCompat 89 行全文、ChartCover 54 行全文、ConductorAssembly 53 行全文、CurveToSpec 54 行、ULStepVIII 480–558、URThetaHullNonzero 头部、ULStepVIIIInstances 全文、PsiGlueCompat 全文）；grep（IsIntegral/ConnectedSpace fermatCurveScheme = 0、isIso_wToPullback 仅注释、wToPullback 全仓分布、HeightDictionaryInterface）。
- **Probe 21**：6 条 DONE 17:44:09，全部三公理、0 error/0 sorryAx。**未运行** lake env lean、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**；仅写本表与 _ProbeBatch21Actual.lean（未改其它 Lean 文件）。
- **未覆盖 / 未运行（如实标注）**：**17:44:18 之后**（PsiGlobal/JHeightUniform/URThetaHullNonzero/HT84 的下一 attempt、PsiGlueCompat 重编、新文件 ULStepVIIIInstances 之后的再改）；PsiGlobal 当前 src 17:44:18 的 wToPullback 是否已补 open Limits 未编译；PsiGlueCompat 的 IsIso 供给未做；G-A (h) 的 scheme 层整性/连通仍无陈述；G-K/P8-P 端到端与 F1–F4/F8 仍未做语义审计；未重读 paper 原文（行号 provenance 沿用既有记录）。
- 本批写入范围：本表 + **新建** _ProbeBatch21Actual.lean；未改其它 Lean 文件；未删旧行。

### 6u. 快照后补记（**17:44:18–17:45:57**；覆盖 §2t-2 #385、§4.170 的 HT84 “R” 判定；旧行保留）

- **HT84F4F5Interface 17:44:35 DONE（翻转）**：src 17:43:35 / 5899 B；olean **17:44:35 / 212336 B**；log 三条打印**全部三公理**：f4Statement_of_f2_f3、f4_f5_combined、f5Statement_of_labelTl；二进制含三条、**无 sorryAx**。**§2t-2 #385 的 17:40:59/17:43:19 FAIL 是旧 attempt**；17:44:35 后该文件可引。但语义仍是 H-T §8.4 的**命名陈述 + 结构引理**：F4Statement/F5Statement 是 Prop def、自注 **NO INHABITANT**；f4Statement_of_f2_f3 是 F2+F3 ⇒ F4；f4_f5_combined 是 F4+F5 的组合；f5Statement_of_labelTl 在 hstar 下把 F5 重述。**不是 8.4 已交**，只是接口层。
- **JHeightUniform 17:44:26 FAIL**：src 17:43:24 的 attempt 失败；随后 src 17:45:35 又改、**未编译**。最后有效仍是 **17:40:32 DONE**（5 条三公理，coeffAbsSum/support infra）；不得引 17:43:24/17:45:35 源。
- **17:45:57 之后未审计**：PsiGlobal src 17:44:18 尚未重编（olean 仍 17:39:09，wToPullback 不在）；PsiGlueCompat 仍无 olean；URThetaHullNonzero 17:42:03 后未再 DONE。
- 本补记不改变 §2t-3 的主判定：G-A proper+smooth **双出口 CLOSED**；(h) **OPEN**；B1 global ψ **未组装**；C4 **条件式**；H-T 8.1/8.2 **未交**。

## 2u. batch 22 gate 表（快照 **17:57 UTC = 2026-11-17 01:57 CST**；覆盖 **17:44:18–17:57**；旧行全保留）

- 证据版本：src/olean/log 均 Get-Item 实测；**(P22)** = §3t 独立 probe。**引用纪律**：olean+log 三件齐备才可引；本批 HT84、PsiGlueCompat（17:47/17:52 两次）、ULStepVIIIInstances 的单文件 log 多次缺失/为 0（17:43:36 重启清空的前例再次出现），这些只认 olean+watchdog.log；**无 olean 一律禁引**。**17:57 之后未审计**（URThetaHullNonzero 17:56:34 起的 attempt 在飞；ChartKbar/PsiGlueCompat/HT84/JHeight 在 17:56–17:57 仍被改写）。
- 本窗口全量事件（按 attempt）：17:44:26 JHeight FAIL；17:44:35 HT84 DONE；17:46:27 URThetaHullNonzero FAIL；17:47:13 PsiGlobal DONE；17:47:21 PsiGlueCompat FAIL；17:47:39 _ProbeQVFamApi FAIL（scratch，不计）；17:48:20 JHeight FAIL；17:49:06 ChartKbar FAIL；17:49:07 PsiCover DONE；17:49:50 ULStepVIIIInstances FAIL；17:51:21 URThetaHullNonzero FAIL；17:52:14 ChartKbar FAIL；17:52:16 PlaceData FAIL、JHeight DONE；17:52:23 PsiGlueCompat FAIL；17:52:46 HT84 FAIL；17:52:47 Probe 22 DONE、ULStepVIIIInstances DONE；17:53:31 PlaceData DONE；17:54:53 URThetaHullNonzero FAIL；17:55:42 PsiOverlapIso FAIL、ChartKbar FAIL；17:55:51 PsiGlueCompat FAIL；17:56:10 HT84 FAIL；17:56:13 ULStepVIIIInstances DONE；17:56:20 ULStepVIII FAIL；17:57:02 PsiOverlapIso DONE。

### 2u-1 Lead 指定项复核（判定按当前 olean/当前源，不按旧日志）

| # | 指定项 | 证据（src / olean / log） | 判定 / 处置 |
|---|---|---|---|
| 1 | **PsiGlobal**（wToPullback 曾禁引） | src 17:44:18 / 6033 B；olean **17:47:12 / 85472 B**；log 1313 B **八条打印全三公理**、0 error、无 sorryAx；二进制含 wToPullback + hcomp | **hcomp / hcomp_left_eq 仍 CLOSED（17:47:12 版）；wToPullback / wToPullback_fst / wToPullback_snd 首次进 olean（同版三公理）→ batch21 的 wToPullback 禁引解除**。但 IsIso (wToPullback n T) 仍未证，global ψ 未组装。 |
| 2 | **PsiGlueCompat**（psi 条件式） | src 17:54:45 / 4313 B；无 olean；17:55:51 log 1863 B：32:10 unsolved goals（两个 case）、33:4 unexpected identifier、77:2/80:2 ι_glueMorphisms 类型不符；**psi / glueMorphisms_compat = sorryAx** | **R 禁引**。已改用 PsiGlobal.wToPullback（inst✝ : IsIso (wToPullback n T)），但证明未收、IsIso 无 provider；17:47:21 / 17:52:23 两次 FAIL 无 log（当时 PsiCover/PsiGlobal 为 stale import，未单独定因）。 |
| 3 | **JHeightUniform 17:44:26 后源** | 17:44:26 / 17:48:20 FAIL 是旧 attempt；**17:52:16 DONE**：src 17:49:05 / 11815 B；olean 256712 B；log 1485 B **九条打印全三公理** | **B infra（新版本可引 17:52:16）**：coeffAbsSum、support_card、polyZ、numeral 等；**仍无 HeightDictionaryInterface 实例，D3 未交**。 |
| 4 | **ULStepVIII 17:39:42** | src 17:54:24 / 29971 B；olean **17:39:42 / 1819960 B（已 stale）**；17:56:20 log 1187 B：182:4 unknown identifier hiii_of_stepII_and_sQ（定义在 547 行，先用后定义）；六条三公理 + hstepVIII_of_retained / hstepVIII_of_collectionLayer 带 sorryAx | **17:39:42 仍是唯一可引版（八条三公理，含 hiii_of_stepII_and_sQ）；当前源 R**。C4 仍条件式；修复=把 hiii 定理块移到 182 行之前。 |
| 5 | **ConductorAssembly 17:40:33** | 未改：src 17:39:04 / 2782 B；olean 17:40:32 / 121072 B；log 152 B f2_of_witness 三公理 | **B 条件式（H-T 8.2）**：F2PlaceWitness 自注 NO INHABITANT；不是 8.2 闭合。 |
| 6 | **URThetaHullTensor 17:37:57** | 未改：src 17:36:00 / 5885 B；olean 17:37:57 / 91136 B；log 718 B 五条三公理 | **A-局部 stage-1**；C2 主不等式 actualLocalHullLog ≤ −thetaCoeff 仍未写。 |
| 7 | **HT84F4F5 17:44:35** | 17:44:35 olean 212336 B（三条三公理，§6u）；**src 17:56:35 / 10910 B 已顶成 stale**；17:52:46 / 17:56:10 FAIL，per-file log 缺失；新增 F4DifferentForm / differentTerm_le_normalizedLogDisc_sub / f4Bound_of_f4DifferentFormAt 段**未编译** | **只可历史引 17:44:35；当前源 R/未编译**。F4/F5 仍 NO INHABITANT；8.4 未交。 |
| 8 | **ChartKbar**（(h) step1，grace） | src 17:53:18 / 1445 B；无 olean；17:55:42 log 436 B：25:2 **K ⊗[ℚ] MvPolynomial ℚ ≠ A ⊗[ℚ] K**；ambientEquiv 带 **sorryAx** | **R：k̄ base-change step1 未交**。17:49:06/17:52:14 亦红（早期 toAddEquiv 字段记法错）。 |

### 2u-2 本窗口新增 DONE / FAIL（#388–#402，按 attempt 计）

| # | 文件 | 事件（UTC） | 证据 | 判定 |
|---|---|---|---|---|
| 388 | Mzk1HT84F4F5InterfaceActual | DONE 17:44:35；FAIL 17:52:46 / 17:56:10（新源） | src 17:56:35 / 10910 B（stale）；olean 17:44:35 / 212336 B | **STALE（8.4 接口）**；见 §2u-1#7。 |
| 389 | Mzk1G1JHeightUniformActual | **DONE 17:52:16**（17:44:26/17:48:20 旧 attempt 红） | src 17:49:05 / 11815 B；olean 256712 B；log 1485 B 九条三公理 | **B infra**；D3 未交。 |
| 390 | Mzk1URThetaHullNonzeroActual | **FAIL 17:51:21**（8329 B）；**FAIL 17:54:53**（8051 B）；src 17:56:11 / 8004 B 未编译 | 17:51:21 log：157:4 isDefEq 心跳 1e6 超时；两条 sorryAx。17:54:53 log：**五条三公理、无 sorryAx**，唯一错误 165:14 unknown urActualThetaHullLogRoot_eq_zero（悬空 #print，该定理已删） | **R（接近绿）**；当前版无 sorry 文本但无 olean，**禁引**；语义只是 theta=0 观察。 |
| 391 | Mzk1G1PsiGlobalActual | **DONE 17:47:13** | src 17:44:18 / 6033 B；olean 17:47:12 / 85472 B；log 八条三公理 | **B+（hcomp + w 组件 CLOSED）**；IsIso 未证。 |
| 392 | Mzk1G1PsiCoverActual | **DONE 17:49:07** | src 17:47:16 / 7561 B；olean 270488 B；log 八条三公理 | **A-局部**：真 Scheme.OpenCover（U0 ∪ D(q)），cover_point / opensRange_sup_top 真证；非 ψ 本身。 |
| 393 | Mzk1G1PsiGlueCompatActual | **FAIL 17:55:51（真错）**；17:47:21/17:52:23 亦红 | src 17:54:45 / 4313 B；无 olean；log 1863 B（32:10、33:4、77:2、80:2） | **R 禁引**；psi/glueMorphisms_compat sorryAx。 |
| 394 | Mzk1G1PsiOverlapIsoActual（新） | FAIL 17:55:42 → **DONE 17:57:02** | src 17:56:26 / 2634 B；olean 新；log 1 打印三公理（isOpenImmersion_r2ToOverlap_away） | **B− step (a) only**；(b)(c)(2)(3)(4) 未写。 |
| 395 | Mzk1G1ChartKbarActual（新） | FAIL 17:49:06 / 17:52:14 / **17:55:42** | src 17:53:18 / 1445 B；无 olean；ambientEquiv sorryAx | **R；(h) step1 未交**。 |
| 396 | Mzk1ULStepVIIIActual | **FAIL 17:56:20（回归）** | src 17:54:24 / 29971 B；olean 17:39:42 stale；log 182:4 unknown hiii…；两条 sorryAx | **R 当前源；17:39:42 唯一可引**。 |
| 397 | Mzk1ULStepVIIIInstancesActual | FAIL 17:49:50 → **DONE 17:56:13** | src 17:54:24 / 3516 B；olean 24368 B；log 0 B（无 #print）；二进制无 sorryAx | **B 条件（hVh）**：letters-level glue。 |
| 398 | Mzk1G1PlaceDataActual（新） | FAIL 17:52:16 → **DONE 17:53:31** | src 17:52:57 / 2626 B；olean 110184 B；log 401 B：placeData 三公理 | **B（真 place data）**：primesOver/ramificationIdx/inertiaDeg/absNorm 真；delta 输入、NO INHABITANT。 |
| 399 | Mzk1G1FermatCurveSmoothFinalActual | 未改（复核） | src 17:38:39；olean 17:40:31；P22 三公理 | **A（G-A smooth 出口）**。 |
| 400 | Mzk1G1FermatPiProperActual | 未改（复核） | src 17:18:49；olean 17:19:18；P22 三公理 | **A（G-A proper 出口）**。 |
| 401 | _ProbeBatch22Actual | **DONE 17:52:47（72 s）** | log 16 行、6 条全三公理、0 error | 见 §3t。 |
| 402 | _ProbeQVFamApi（scratch） | FAIL 17:47:39 | 非 paper 交付件、无 olean | **不计入 gate**（scratch）。 |

### 2u-3 缺口表（17:57 口径；旧 §2t-3 保留）

| 缺口 | 当前证据 | 状态 |
|---|---|---|
| **G-A proper** | PiProper.fermatCurveToSpec_isProper_final（17:19:18，P20+P21+P22） | **CLOSED** |
| **G-A smooth** | SmoothFinal.fermatCurveToSpec_smoothOfRelativeDimension（17:40:31，P21+P22） | **CLOSED** |
| **(h) 几何整性/连通** | cover：ChartCover 17:31:53（P21）/ PsiCover 17:49:07 是 ψ 的 cover，不是 (h)；(h) 链第 1 步 ChartKbar **17:55:42 红**；paper 目录 scheme 层 IsIntegral / ConnectedSpace (fermatCurveScheme) 仍 = 0 | **cover CLOSED；(h) OPEN（step1 红）** |
| **B1 ψ** | PsiGlobal 17:47:12（hcomp + wToPullback 三公理）；PsiCover 17:49:07（真开覆盖）；PsiGlueCompat 17:55:51 红/psi sorryAx；PsiOverlapIso 17:57:02 仅 step(a) | **组件齐；IsIso w 未证；global ψ 未交（禁引）** |
| **C4 / Step VIII** | ULStepVIII 只可引 17:39:42（8 条三公理）；当前源 17:56:20 红；ULStepVIIIInstances 17:56:13；ConductorAssembly 17:40:32 | **C4 仍条件式；ULStepVIII 引用钉死 17:39:42** |
| **U-R C2** | URThetaHullTensor 17:37:57 stage-1；URThetaHullNonzero 17:54:53 近绿但无 olean | **stage-1 CLOSED；主不等式未交** |
| **H-T 8.1/8.2** | ConductorAssembly 17:40:32（F2 条件式）；RelativeDifferentNorm 17:42:53；PlaceData 17:53:31（delta NO INHABITANT）；HT84 17:44:35 stale；HT81Interface NO INHABITANT | **8.2 局部/条件式；8.1 未交** |
| **uniform D3** | JHeightUniform 17:52:16（9 条 infra） | **NO INHABITANT / 未交付** |

## 3t. Probe 22（本批 batch 22）：tmp/sheaf/xif/paper/_ProbeBatch22Actual.lean

- node tools/wd_add.mjs 17:51 前排队（total 210）→ START 17:51:35 → **DONE 17:52:47（72 s）**；log 16 行，0 error / 0 sorryAx，6 条全部 **[propext, Classical.choice, Quot.sound]**：

| 定理 | axioms | 证据版本（probe 编译时磁盘 olean） |
|---|---|---|
| SmoothFinal.fermatCurveToSpec_smoothOfRelativeDimension | [propext, Classical.choice, Quot.sound] | **17:40:31**（G-A smooth 出口） |
| PiProper.fermatCurveToSpec_isProper_final | [propext, Classical.choice, Quot.sound] | **17:19:18**（G-A proper 出口） |
| Close2.pi_preimage_localChartInf | [propext, Classical.choice, Quot.sound] | **16:50:10**（t 侧 M−b；未改） |
| CurveSmooth2.loc_v2_standardSmooth | [propext, Classical.choice, Quot.sound] | **16:42:12**（未改） |
| ULStepVIII.hiii_of_stepII_and_sQ | [propext, Classical.choice, Quot.sound] | **17:39:42**（probe 后该源 17:54:24 改动并红，olean 现 stale；本行只证明 17:39:42 版） |
| PsiGlobal.wToPullback | [propext, Classical.choice, Quot.sound] | **17:47:12**（新 DONE 17:47:13；batch22 第 6 条） |

- **ChartKbar 替代说明**：任务原定第 6 条在 ChartKbar DONE 时取其主定理；ChartKbar 17:49:06/17:52:14/17:55:42 全红、无 olean，**无法 probe**，故第 6 条改用本窗口新 DONE 的 PsiGlobal.wToPullback。**不对 ChartKbar 作任何 CLOSED 声明**。
- 版本纪律：6 条均按 probe 时刻磁盘 olean 复算；probe 未运行 lake env lean、未自起 watchdog、未写 sorry/axiom、未 spawn_teammate。

## 4. 本 round 发现的伪证 / 换题 / 空 card 风险（batch 22 续）

### 4.172 【高·(h)】ChartKbar 三红：k̄ base-change step1 未交，且即便绿也不够
- 17:55:42 的 attempt（src 17:53:18 / 1445 B）错在 25:2：右侧是 K ⊗[ℚ] MvPolynomial (Fin 2) ℚ，目标却是 A ⊗[ℚ] K（A = MvPolynomial (Fin 2) ℚ）。TensorProduct.comm / algebraTensorAlgEquiv 的方向与 AlgEquiv/RingEquiv 记法先后错配，错误恢复给 ambientEquiv 挂 **sorryAx**；17:49:06/17:52:14 的早期 attempt 还出现 toAddEquiv 字段记法错误。
- 更关键：该文件当前只声明 ambientEquiv : A ⊗[ℚ] K ≃ₐ[ℚ] MvPolynomial (Fin 2) K，**没有 chart 商环、没有 ℚ[X0,X1]/(F) 的 k̄ 基变换识别、没有 IsDomain 运输、没有 ∞-chart**。所以 (h) 链的第 1 步（k̄ base-change）**未交**；不得写“(h) 有进展”。

### 4.173 【高·Lead 裁决】URThetaHullNonzero：旧 attempt 禁引；当前版已无 sorry 文本但两次 attempt 均未绿
- batch21 记的 4 条 sorryAx（urRootThetaImageSet_subset_holomorphic、urRootThetaHull_eq_holomorphic、urActualLocalHullLog_eq_zero、urActualThetaHullLogRoot_eq_zero）属于 **17:42 旧 attempt（7778 B）**——**禁引**。
- 当前演进：8329 B（17:47:34）attempt 17:51:21 因 157:4 isDefEq 心跳 1e6 超时失败，错误恢复让 urActualLocalHullLog_eq_zero / urActualThetaHullLogRoot_eq_zero 带 **sorryAx**（前四条三公理）；8051 B（17:52:26）attempt 17:54:53 **五条打印全三公理、无 sorryAx**，唯一错误是 165:14 unknown urActualThetaHullLogRoot_eq_zero（悬空 #print，定理已删）。8004 B（17:56:11）尚未编译。
- 结论：**旧 attempt 禁引；当前版待绿后评审**（删 165 行悬空 #print 即可望绿，删后重编到 DONE 才可引）。文件语义仍只是“all-label theta hull = O_hol、log = 0”的观察，**不是 C2 的 nonzero-label 主不等式**；即便绿也只是 B/语义观察，不得写 C2 交。

### 4.174 【高·正结论】PsiGlobal 17:47:13：wToPullback 首次进 olean，解除禁引
- src 17:44:18 / 6033 B；olean 17:47:12 / 85472 B；log 八条打印全三公理（wToPullback、wToPullback_fst、wToPullback_snd、hcomp、hcomp_left_eq、psiChart0、psiChart1、overlapToCurve_condition），0 error；二进制含 wToPullback/hcomp、无 sorryAx。
- 修法已落地：顶部 open CategoryTheory.Limits 后，pullback / pullback.fst / snd / lift 全部可解析；wToPullback := pullback.lift chart0ToOverlap chartInfPieceToOverlap (hcomp n T)。
- **引用纪律更新**：batch21 §5q#8 的“wToPullback 禁引”**作废**；可引 17:47:12 olean。但 **IsIso (wToPullback n T) 没有证明**（PsiOverlapIso 只完成 step (a)）；PsiGlueCompat 的 psi 仍条件于此实例，且其自身 17:55:51 红。**不得写 global ψ 已交**。

### 4.175 【中·B1】PsiCover 17:49:07：真开覆盖，但不是 ψ
- src 17:47:16 / 7561 B；olean 17:49:07 / 270488 B；log 八条三公理。内容：qPiece : Spec(Away(q)) → Y_n；psiOpenCover : Y_n.OpenCover，两片 X false = U0、X true = Spec(Away(q))；cover_point 用 fermatTwoChartGlueData.ι_jointly_surjective + “q 与 r 不能同时为零”（span{q,r}=⊤）+ 局部化 range 引理证明；opensRange_sup_top 由 cover_point 得。
- 这是 B1④ 的真覆盖输入（不是空壳）；但它是 **cover**，不是 scheme 层整性/连通（(h)），也不是 ψ 本身。

### 4.176 【高·ψ】PsiGlueCompat 17:55:51 真错：psi/glueMorphisms_compat 带 sorryAx
- src 17:54:45 / 4313 B；无 olean。log 1863 B：32:10 unsolved goals（两个 case 的 pullback.fst/snd 等式）、33:4 unexpected identifier（case 结构被写坏）、77:2/80:2 ι_glueMorphisms 期望 (psiOpenCover n T).f … 但实际是 (Precoverage.ZeroHypercover.toPreZeroHypercover …).f（需先 simp/change 展开）；psi 与 glueMorphisms_compat 均带 sorryAx。
- 与 batch21 不同：这次不是 stale import（PsiGlobal 17:47:12 已有 wToPullback，PsiCover 17:49:07 已有 olean），是**真证明错误**。**psi 禁引**；IsIso w 仍无 provider。

### 4.177 【中·(h)/ψ】PsiOverlapIso 17:57:02 只完成 step (a)
- 新文件 src 17:56:26 / 2634 B；olean 新；log 1 打印三公理：isOpenImmersion_r2ToOverlap_away（R2 → Away(q*r) 的局部化是开浸入，infer_instance）。文件头列出 (b)(c)(2)(3)(4) 计划：chartInfPieceToOverlap / chart0ToOverlap 的开浸入、IsOpenImmersion.of_comp、opensRange=⊤、isIso_of_isOpenImmersion_of_opensRange_eq_top。
- **只可引 step (a)**；IsIso (wToPullback n T) **仍未证**，不可写“IsIso 已交”。

### 4.178 【高·回归】ULStepVIII 17:56:20：先用后定义，17:39:42 olean 变 stale
- src 17:54:24 / 29971 B；olean 17:39:42 / 1819960 B（stale）。17:56:20 log：182:4 unknown identifier hiii_of_stepII_and_sQ——hstepVIII_of_retained 在 180–182 行调用该定理，但其定义在 547 行；Lean 不允许前向引用，错误恢复让 hstepVIII_of_retained / hstepVIII_of_collectionLayer 带 sorryAx（其余六条三公理）。
- **C4 引用只可指 17:39:42 olean**（P21+P22 八条三公理，hiii_of_stepII_and_sQ 在 538 行）；当前源禁引。修复=把 547 行的 hiii 块整体移到 hstepVIII_of_retained（165 行）之前，或把 182 行改 inline。

### 4.179 【中·H-T】HT84 17:44:35 已 stale；当前 F4-different 段未编译
- 17:44:35 olean（212336 B）三条三公理，但 src 17:56:35 / 10910 B 已晚于它；17:52:46 与 17:56:10 两次 FAIL，**per-file log 均缺失**（无法定因）。新段新增 HT84HeightData.toLineBundleHeights、F4DifferentFormAt、differentTerm_le_normalizedLogDisc_sub（differentTerm ≤ D(L)−D(K)，用 RelativeDifferentNorm + 判别式塔）、f4Bound_of_f4DifferentFormAt；这些**尚未编译**。
- 只可历史引 17:44:35；F4/F5 仍 NO INHABITANT，**8.4 未交**。

### 4.180 【中·H-T】PlaceData 17:53:31：真 place data，delta 仍 NO INHABITANT
- src 17:52:57 / 2626 B；olean 17:53:31 / 110184 B；log 401 B：placeData 三公理。字段 W = p.primesOver(O_L)、e = ramificationIdx、f = inertiaDeg、logNv = log|N(p)|、Ldim = [L:ℚ] 均为实际数域对象；**differentExponent := delta P.1 是输入函数**，文件自注 delta 的实际构造（relative different 的重数）未证、NO INHABITANT。
- **B（8.2 局部数据）**；不得写 8.2 已交。

### 4.181 【中·D3】JHeightUniform 17:52:16：新 olean 仍只是 coeffAbsSum infra
- src 17:49:05 / 11815 B；olean 256712 B；log 九条三公理：coeffAbsSum_coeff_le/add_le/C_mul_le、support_card_le、coeffAbsSum_mul_le/X_pow/X_pow_mul_X_pow/polyZ_le、numeral_eq_C_int。文件 import JHeightD3，但**无 HeightDictionaryInterface 实例、无 uniform-in-K 高度比较**。
- **D3 仍 NO INHABITANT**；17:44:26 / 17:48:20 的 FAIL 是旧 attempt（17:43:24 / 17:47:xx 源），不得与 17:52:16 混用。

### 4.182 【中·纪律】本窗口 log 缺失/清空清单（引用前必须核对三件）
- HT84：17:44:35 之后 per-file log 被清空/缺失；17:52:46、17:56:10 的 FAIL 只剩 watchdog.log 的 FAIL 行。
- PsiGlueCompat：17:47:21 / 17:52:23 无 log；17:55:51 的 log 才有内容（1863 B）。
- ULStepVIIIInstances：17:49:50 与 17:56:13 两次 attempt 的 log 为 0 B（源内无 #print）。
- URThetaHullNonzero：17:48:35 的 log 在 17:51:21 前为 0；17:54:53 的 log 是当前 8051 B 版。
- **共同规则**：log 缺失时只认 olean 二进制 + watchdog.log；**无 olean = 禁引**（PsiGlueCompat、ChartKbar、URThetaHullNonzero、PsiOverlapIso 之前的状态、HT84 当前源）。

## 5r. batch 22 立即动作（快照 17:57 UTC）

1. **(h) 链（grace，最高优先）**：ChartKbar 当前错在基变换方向/记法——TensorProduct.comm ℚ A K 给 A ⊗ K ≃ K ⊗ A，而 algebraTensorAlgEquiv 给 K ⊗ MvPolynomial ℚ ≃ MvPolynomial K；用 AlgEquiv 组合（comm 是 AlgEquiv，勿再走 toAddEquiv/toRingEquiv 字段记法）并去掉 AlgEquiv.ofRingEquiv 的 sorry。绿后才写 **chart 商环的 k̄ 基变换 ≃ k̄[X0,X1]/(F)** → **IsDomain 运输**（fermatCurveRing_isDomain）→ **∞-chart 同构** → **overlap 相容/几何连通**。**当前 (h) 无任何可引进展**。
2. **ψ（henry/emmy）**：可引 PsiGlobal 17:47:12（wToPullback/fst/snd/hcomp/hcomp_left_eq）、PsiCover 17:49:07；**PsiGlueCompat 17:55:51 禁引**（psi sorryAx）。先修 32/33 的 case 结构与 77/80 的 ι_glueMorphisms 展开，再谈 global ψ；IsIso (wToPullback n T) 由 PsiOverlapIso 的 (b)(c)(2)(3)(4) 完成（step (a) 已绿）。
3. **C4（david）**：ULStepVIII 只引 **17:39:42**（八条三公理）；把 547 行的 hiii_of_stepII_and_sQ 移到 165 行之前（或 inline 到 182 行），重编到 DONE 后才更新引用。ULStepVIIIInstances 17:56:13 只是 hVh 条件 glue；C4 仍条件式。
4. **U-R（kurt）**：URThetaHullNonzero 删 165 行悬空 #print axioms urActualThetaHullLogRoot_eq_zero（该定理已删），或补回该定理；绿后重审。当前 8051 B attempt 五条三公理、无 sorryAx，是本窗口最接近绿的红件；但语义只是 theta=0 观察，**不得写 C2 交**。
5. **H-T（alan/henry）**：PlaceData 17:53:31 可引（delta 供给仍未构造）；ConductorAssembly 17:40:32 不变（F2 条件式）；HT84 17:44:35 已 stale，修好 F4-different 段（differentTerm_le_normalizedLogDisc_sub）再引；8.1/8.2/8.4 均未交。
6. **D3**：JHeightUniform 17:52:16 只算 infra；真 uniform D3 仍需 HeightDictionaryInterface 实例或单一 B。
7. **版本纪律（强制）**：SmoothFinal 只引 17:40:31；PiProper 只引 17:19:18；Close2 只引 16:50:10；CurveSmooth2 只引 16:42:12；ULStepVIII 只引 17:39:42；ConductorAssembly 只引 17:40:32；URThetaHullTensor 只引 17:37:57；ChartCover 只引 17:31:53；PsiGlobal 只引 17:47:12；PsiCover 只引 17:49:07；JHeightUniform 只引 17:52:16；PlaceData 只引 17:53:31；ULStepVIIIInstances 只引 17:56:13；PsiOverlapIso 只引 17:57:02 的 step (a)。**禁引**：PsiGlueCompat、ChartKbar、URThetaHullNonzero、HT84 当前源、18:00 后任何再改源。

## 6v. batch 22 更新（快照 **17:57 UTC = 2026-11-17 01:57 CST**；覆盖 §6–§6u 的旧结论，旧文保留）

- **已运行（本批）**：Get-Item src/olean/log 对照（20+ 文件）；watchdog.log 按 attempt 过滤（17:44–17:57）；per-file log 读取（PsiGlobal 1313 B、PsiCover 1051 B、ChartKbar 436 B、PlaceData 401 B、JHeightUniform 1485 B、URLThetaHullNonzero 两次、PsiGlueCompat 1863 B、ULStepVIII 1187 B、ULStepVIIIInstances 0 B、Probe 22 16 行）；二进制 olean 符号核验（PsiGlobal 的 wToPullback/hcomp、SmoothFinal/PiProper/Close2/CurveSmooth2/ULStepVIII/ChartCover/JHeight/ULStepVIIIInstances/PlaceData 的 sorryAx = false）；源码阅读（ChartKbar 全文、URThetaHullNonzero 130–178、PsiGlobal 全文、PsiGlueCompat 全文、PsiCover 全文、PlaceData 全文、PsiOverlapIso 全文、ULStepVIII 160–204、HT84 100–194、JHeight 1–63）。
- **Probe 22**：6 条 DONE 17:52:47，全部三公理、0 error/0 sorryAx。**未运行** lake env lean、**未自起** watchdog、**未写** sorry/axiom、**未 spawn_teammate**；仅写本表与 _ProbeBatch22Actual.lean（未改其它 Lean 文件）。
- **未覆盖 / 未运行（如实标注）**：**17:57 之后**（URThetaHullNonzero 17:56:34 起的 attempt、ChartKbar 17:56 后重试、PsiGlueCompat/HT84/JHeight 的后续改写、PsiOverlapIso 的下一步）；PsiGlueCompat 17:47:21/17:52:23 与 HT84 17:52:46/17:56:10 的具体错误因 log 缺失**未定因**；G-A (h) 的 scheme 层整性/连通仍无陈述；G-K/P8-P 端到端与 F1–F4/F8 仍未做语义审计；未重读 paper 原文。
- 本批写入范围：本表 + 新建 _ProbeBatch22Actual.lean；未改其它 Lean 文件；未删旧行。

### 6w. 快照后补记（**17:57–18:05**；覆盖 §2u-1#4/#7/#8、§2u-2 #388/#390/#395/#396、§4.172/§4.173/§4.178/§4.179 的红/stale 判定；旧行保留）

- **ChartKbar 17:59:05 DONE（ambient 半）**：src 17:56:54 / 1560 B；olean **17:59:05 / 33552 B**；log 1 打印三公理；P22b 独立三公理。内容只有 ambientEquiv : A ⊗[ℚ] K ≃ₐ[ℚ] MvPolynomial (Fin 2) K（A = MvPolynomial (Fin 2) ℚ，用 Algebra.TensorProduct.comm + MvPolynomial.algebraTensorAlgEquiv 组合）。**§2u-1#8、§2u-2#395、§4.172 的“R”对 17:59:05 版作废**，但 **chart 商环 A₀/D 的 k̄ 基变换与 IsDomain 运输未写**：18:01:39 新源（3544 B）18:03:49 FAIL（36:2 p : ℚ 类型不符；46:4 无 Algebra A (MvPolynomial (Fin 2) K) 实例；47 unsolved goals，sorry）。**(h) 仍 OPEN；只可引 17:59:05 的 ambientEquiv，当前源红。**
- **URThetaHullNonzero 17:58:18 DONE**：src 17:56:11 / 8004 B；olean **17:58:18 / 113224 B**；log 5 打印**全三公理**、0 error、二进制无 sorryAx；P22b 独立复算 2 条三公理。**§4.173 的“旧 attempt 禁引”仍成立；§2u-2#390 的“R/待绿”对 17:58:18 版作废**。但 18:00:33 新源（10635 B，加 nonzero-label 段）18:03:12 FAIL（181:42 oneLabel unknown；gaussExponent 期望 ℤ 参数；one_le_gaussExponent_of_ne_zero unknown）→ **当前源红、ole 已 stale；只可引 17:58:18 版，语义仍是 theta=0 观察（all-label hull=O_hol），nonzero-label 主不等式未写，C2 未交。**
- **HT84 18:00:47 DONE（新版本）**：src 17:59:51 / 10998 B；olean **18:00:47 / 375440 B**；log 5 打印全三公理：differentTerm_le_normalizedLogDisc_sub、f4Bound_of_f4DifferentFormAt、f4Statement_of_f2_f3、f4_f5_combined、f5Statement_of_labelTl；P22c 独立复算两条新定理三公理。**§2u-1#7、#388、§4.179 的 stale 判定作废**；F4/F5 仍 NO INHABITANT，**8.4 仍只是接口层**。
- **ULStepVIII 18:02:12 DONE（新版本）**：src 18:00:35 / 29973 B；olean **18:02:12 / 1837320 B**；log 8 打印**全三公理**（含 hstepVIII_of_retained、hstepVIII_of_collectionLayer，无 sorryAx）；二进制无 sorryAx；hiii_of_stepII_and_sQ 移到 173 行、hstepVIII_of_retained 在 198 行；P22c 复算 hstepVIII_of_retained + hiii 三公理。**§2u-1#4、#396、§4.178 的 R/stale 判定作废；C4 引用从 17:39:42 更新为 18:02:12**。C4 仍条件式（消费 htheta/hX/hlogSQ/hVh），不得写闭合。
- **PsiGlueCompat 17:59:06 / 18:01:34 仍 FAIL**：src 17:56:55 / 4414 B；无 olean；两次 per-file log 缺失。**仍禁引**；psi 与 IsIso 均未交。
- **RelativeDifferentFactorization（新，H-T）翻绿**：17:59:08 FAIL → **18:03:51 DONE**：src 18:02:16 / 2424 B；olean 54336 B；log 2 打印三公理（absNorm_differentIdeal_eq_prod、absNorm_prime_eq_pow_inertiaDeg）。**B（8.2 因子化 helper）**；此前 normalizedFactors unknown / ne_bot 参数错已修。
- **PsiOverlapIso 状态**：17:57:02 DONE 只覆盖 step (a)；18:02:41 新源（4281 B）18:03:49 / 18:05:00 FAIL → 当前源红；IsIso (wToPullback n T) **仍未证**，只可历史引 17:57:02 的 isOpenImmersion_r2ToOverlap_away。
- **HT86F6Interface（新，H-T 8.6）**：src 18:04:08 / 5087 B，18:04:59 FAIL，无 olean；仅登记为 R/未审（不属本批 8.1–8.4 判定）。
- **Probe 22b**：DONE 18:02:04（62 s），5/5 三公理：ChartKbar.ambientEquiv、URThetaHullNonzero.urRootThetaHull_eq_holomorphic / urActualLocalHullRegion_eq_holomorphic、PsiOverlapIso.isOpenImmersion_r2ToOverlap_away、ULStepVIIIInstances.hviTable_instance_letters。**Probe 22c**：DONE 18:04:17（59 s），4/4 三公理：ULStepVIII.hstepVIII_of_retained / hiii_of_stepII_and_sQ、HT84.differentTerm_le_normalizedLogDisc_sub / f4Bound_of_f4DifferentFormAt。
- **版本纪律（18:05 口径）**：G-A smooth 17:40:31、proper 17:19:18 不变；**ULStepVIII 改引 18:02:12**（17:39:42 作废）；**HT84 引 18:00:47**（17:44:35 作废）；**URTheta 只引 17:58:18**（当前 src 已改红）；**ChartKbar 只引 17:59:05 的 ambientEquiv**；PsiGlobal 17:47:12、PsiCover 17:49:07 不变；PsiGlueCompat/HT86F6/Current ChartKbar 源**禁引**。
- **18:05 之后未审计**（UCHthetaWiring 在飞；HT86F6 / PsiOverlapIso 在改；URTheta 的 nonzero-label 段、ChartKbar 的商环段均未绿）。















