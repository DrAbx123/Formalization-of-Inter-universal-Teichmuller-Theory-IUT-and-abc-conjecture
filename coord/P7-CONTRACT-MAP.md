# P7 #8 CONTRACT — reconciliation 12 rows / 7 missing ↔ 10 GAP codes

日期：2026-11-13；owner：mainline；Status：**CONDITIONAL ASSEMBLY（装配定理 green，缺口状态机器化）**；watchdog **DONE 89s@11:18:55Z，olean=True**。

机器文件：`tmp/sheaf/xif/paper/Mzk1P7ContractMapActual.lean`（待 watchdog 名单）。

## 1. 12 行 reconciliation → GAP 映射（`recon12ToGap`）

| # | obligation | 映射 |
|---|---|---|
| 1 | WallObligation.holomorphicHull | GAP-P7-CONTRACT |
| 2 | WallObligation.determinantNormalization | GAP-P7-OB33-SRC |
| 3 | WallObligation.logVolumeComparison | GAP-P7-GENERAL-CMP |
| 4 | S3137 q reading | DISCHARGED |
| 5 | S3137 theta reading | GAP-P7-THETA-V |
| 6 | HullVolumeReuse comparison | DISCHARGED |
| 7 | GapNormalization sufficient reductions | GAP-P7-GENERAL-CMP（conditional） |
| 8 | S3137 → Cor312 assembly | DISCHARGED（conditional on comparison） |
| 9 | N3 SharedContainer bridge | DISCHARGED |
| 10 | strength upgrade | DISCHARGED（shape；comparison pending） |
| 11 | HullDeterminantLogVolumeReduction | GAP-P7-THETA-D / THETA-DEG / OB33-SRC |
| 12 | final boundary Szpiro | GAP-P7-HULL-UB |

## 2. 7 missing → GAP + interface（`missing7ToGap`）

| # | missing item | GAP code | interface 文件 |
|---|---|---|---|
| 1 | general qThetaPilotLogVolumeComparison | GAP-P7-GENERAL-CMP | Mzk1GeneralComparisonInterfaceActual.lean |
| 2 | paper carrier IQ realization | GAP-P7-IQ-LITERAL | Mzk1PaperIQCarrierInterfaceActual.lean:16/23 |
| 3 | (Ob3-3) source identification | GAP-P7-OB33-SRC | Mzk1Ob33InterfaceActual.lean |
| 4 | multiradial (xi-e)/(xi-f) production | GAP-P7-MULTIRADIAL | Mzk1ComparisonDataStatusActual.lean |
| 5 | theta raw Haar vs paper normalized V | THETA-V / THETA-D / THETA-DEG | Mzk1C3S1902BridgeActual / ThetaVFactorInterface |
| 6 | StepXIContract fields/linkage | GAP-P7-CONTRACT | Mzk1StepXIContractLinkageActual.lean:15/16 |
| 7 | exact hull volume upper bound | GAP-P7-HULL-UB | Mzk1HullUpperBoundInterfaceActual.lean |

跨切：GAP-NORM-ARCH-C-K（#10）服务于 #1/#7 的归一化因子；10 个 GAP code 全部被覆盖
（`gapCodesCovered_length = 10 = gapRegister.length`，rfl）。

## 3. 条件装配定理（`p7_conditional_contract`）

```
qThetaPilotLogVolumeComparison C3 P
  ├─(assembly green)→ contractOfS3137Comparison C3 P h
  └─(XiF formal step)→ Cor312Conclusion ...
```

**条件装配形式**：唯一数学输入是 actual comparison；12 行表说明哪些行 DISCHARGED、
哪些是 7 missing 项（各自映射到 10 GAP code 的 interface）。`ContractFieldsLinked = false`
（`contract_fields_not_linked`）证明 #6 目前确为真缺口（contract 无 evidence 字段）。

## 4. 状态

- GAP-P7-CONTRACT：**CONDITIONAL（装配定理 green）**，不再是纯 INTERFACE；
- 其余 9 个 GAP code 状态不变（见 `coord/P7-GAP-ATTACK-PLAN.md`）；
- 本文件与 `Mzk1P7ContractMapActual` 是 P7 最终条件形态的单一映射来源。


## 5. Route B #3 进展（2026-11-13 后续）

- **B4.4/B5 全局形式已构造并证明**：`tmp/sheaf/xif/paper/Mzk1DetLineConstructionActual.lean`
  （DONE 57s@11:47:36Z，olean=True）：
  `relativeDetLine H O = det(H) * det(O)^{-1}`（实际 fractional-ideal line bundle）、
  `globalLogVolume_relativeDetLine : log D(H,O) = log H - log O`、
  `relativeDetLog_eq_ratio`。
- **逐位 B5 接口**：`tmp/sheaf/xif/paper/Mzk1DetLinePlaceB5Actual.lean`
  （DONE 45s@11:57:04Z，olean=True）：`LocalGeneratorData`、`LocalPrincipalGenerator`、
  `LocalHaarScalingLaw`、`placeLogVolume`、`PlaceB5Target`（named inputs，未硬 assert）。
  下一步：DVR 主理想生成元（`adicCompletion.exists_uniformizer K v` +
  FractionalIdeal num/den 的 Associates.count 指数）+ Haar scaling law。
- **第 4 步 arch 入口**：`Mzk1NormArchCHArcActual`（hTerm/toricTerm over InfinitePlace）、
  `Mzk1NormArchDegreeActual`（arch-normalized explicit-divisor degree）、
  `Mzk1NormArchCKActual`（archCK）、`Mzk1NormArchConsumerActual`（NormArchConsumer，green）。
- **第 5 步**：等 shehdd 的 `Ob33DetLine`（qPilotDetLine/DetMap/ActualDetDegree）green 后，
  用 `globalLogVolume_relativeDetLine` 替换 `Mzk1Ob33SourceIdentificationActual:67`
  的命名 identification。


## 6. Route B #3 第 4/5 步（2026-11-13 后续）

- **第 4 步 archCK hookup**：`tmp/sheaf/xif/paper/Mzk1DetLinePlaceB5ArchActual.lean`（待名单）：
  `archCKForK = archCK T.arithmetic.K`、`archCKForK_eq_heightWeight`、
  `hArc_nonneg_for_K`（复用 green `hArc_nonneg_via_archCK`）、
  `mergedLogDegree finitePart archSum = finitePart + archCK*archSum`、
  `mergedLogDegree_nonneg`。接入 `Mzk1NormArchCKActual`/`Mzk1NormArchConsumerActual`。
- **第 5 步 Ob33 桥**：`tmp/sheaf/xif/paper/Mzk1Ob33DetLineBridgeActual.lean`（待名单）：
  qpilot 的实际 bad-prime source (`Mzk1PaperQPilotLineBundleSourceActual`/`Mzk1Ob33DetLineFromBadPrimeSourceActual`)
  + 我们的 `globalLogVolume_relativeDetLine`：
  `qPilotDetArithmeticDegreeOfBadPrimes = relativeDetLog(H,O) + globalLogVolume O`；
  `RouteBArithmeticDegreeReadingGap ⇔ 相对行列式形式`；
  `BadPrimeSourceReadingIdentification ⇔ relativeDetLog 形式`。
  参照线丛 O 与非零见证 hH/hO 为显式内容输入（bad-prime 理想乘积 ≠ paper q-除子的语义仍待识别）。

### 6.1 第 4/5 步状态（2026-11-13 后续 2）

- Mzk1DetLinePlaceB5ArchActual — DONE 64s@12:58:34Z，olean=True（archCKForK / hArc_nonneg_for_K / mergedLogDegree / mergedLogDegree_nonneg）。
- Mzk1Ob33DetLineBridgeActual — DONE 58s@12:41:14Z，olean=True：
  qPilotDetArithmeticDegreeOfBadPrimes = relativeDetLog(H,O) + globalLogVolume O；
  RouteBArithmeticDegreeReadingGap ⇔ 相对行列式形式；
  BadPrimeSourceReadingIdentification ⇔ relativeDetLog 形式。
- Mzk1DetLinePlaceB5MergedActual（待名单）：finiteB5Part = -(vH-vO)logp、
  finiteB5Part_eq_placeLogVolume_sub（PlaceB5Target ⇒ finite part = placeLogVolume 差）、
  mergedLogDegree_B5 / mergedLogDegree_B5_nonneg（finite+arch 合并声明接上 PlaceB5Target）。
- 剩余内容输入：LocalHaarScalingLaw（Haar scaling）、LocalPrincipalGenerator/CountLocalizationBridge
  （DVR 主理想生成元）、参照线丛 O 与非零见证 hH/hO（paper 除子识别后消去）。

补充：Mzk1DetLinePlaceB5MergedActual — DONE 60s@13:03:49Z，olean=True。

### 6.2 B5 展开与 arch 汇总（2026-11-13 后续 3）

- Mzk1B5RelativeDetLogExpansionActual — DONE 55s@13:25:05Z，olean=True：
  - FractionalLogVolumeExpansion（named input：fractional ideal log 展开）；
  - relativeDetLog_eq_finsum_sub_of_expansions：log D(H,O) 写成两个有限位和的差；
  - relativeDetLog_eq_single_finsum：给定 hsub（finsum 次可分配性）得单和形式；
  - relativeDetLog_add_archMetricWeight_eq：+ archDetMetricWeight_eq_neg_archimedeanLogNorm 得 B5 arch 汇总（条件）。
- Mzk1B5CountLocalValuationBridgeActual — DONE 33s@13:24:42Z，olean=True：
  LocalNormGeneratorBridge、CountValuationBridge、placeLogVolume_eq_count_mul_log_residueNormBase、
  placeLogVolume_eq_localLogVolume（含 residue-degree-one 等式 hchar）。
- 剩余可关闭项：FractionalLogVolumeExpansion（等 qpilot Mzk1B5FractionalAbsNormFormulaActual +
  Mzk1B5FractionalCountNumDenActual/count_eq_count_num_sub_count_den green 后替换）；
  hsub（用 Summable + finsum_sub_distrib，支撑有限性来自 FractionalIdeal.finite_factors）；
  LocalNormGeneratorBridge/CountValuationBridge 与 residue-one（GAP-PC-RESDEG）。

## 7. #8 集成核对：margin7Rows vs missing7ToGap（2026-11-13 13:30Z）

- 逐行比对 `Mzk1P7ContractMapActual.missing7ToGap`（7 行）与 `Mzk1P7ContractMarginConsumerActual.margin7Rows`：**item 名称、顺序完全一致**；gap code 仅第 5 行原不一致（margin7Rows 缺 `GAP-` 前缀/空格），已修正为 `"GAP-P7-THETA-V / GAP-P7-THETA-D / GAP-P7-THETA-DEG"`。
- **Bridge green**：`tmp/sheaf/xif/paper/Mzk1P7ContractRowsBridgeActual.lean` **DONE 13:29:25Z（54s，olean=True）**：`margin7Rows_items_eq_missing7ToGap`、`margin7Rows_codes_eq_missing7ToGap`、`margin7Rows_length_eq_missing7ToGap`（全 rfl）。
- **mainline 消费入口（green）**：`Mzk1P7ContractMarginConsumerActual`（DONE 13:14:31Z）：`comparison_of_margin_one`、`margin_one_theta_sub`、`p7_conditional_contract_of_margin_one`、`p7_conditional_contract_of_hullQDictionary`；用法示例：给 `hmargin : qPilotLogVolumeReading P + 1 ≤ thetaPilotHullLogVolumeReal C3`，调用 `p7_conditional_contract_of_margin_one C3 P hmargin` 得 `Cor312Conclusion (contractOfS3137Comparison C3 P (comparison_of_margin_one C3 P hmargin))`。
- 状态：GAP-P7-CONTRACT 仍 **CONDITIONAL**；本次仅确认 7 行行码/顺序覆盖一致，rows 2–7 内容未变。
### 6.3 FractionalLogVolumeExpansion 已由 qpilot 定理推导（2026-11-13 后续 4）

- Mzk1B5FractionalExpansionBridgeActual — DONE 56s@13:37:39Z，olean=True：
  `fractionalLogVolumeExpansion_of_qpilot` 用 qpilot 的
  `log_absNorm_fractional_eq_sum_diff`（num/den count 和之差）与
  `count_eq_count_num_sub_count_den`（fractional count = num − den）
  证明 `FractionalLogVolumeExpansion`。
  条件只剩 `hsumH/hsumO : Function.HasFiniteSupport`（num/den count 加权和），
  可由 `Ideal.finite_factors`/`Associates.finite_factors` 关闭（下一步）。
  carrier 对齐用 `NumberField.FinitePlace.equivHeightOneSpectrum` 的 `finsum_comp_equiv`，
  `residueNormBase v = Ideal.absNorm v.maximalIdeal.asIdeal` 为定义（rfl）。
- ⇒ B5 汇总 ① 不再需要 named `FractionalLogVolumeExpansion`（改用该定理 + 两 finite-support）；
  ③ arch 已证；剩余为 ② 的 `LocalNormGeneratorBridge`/`CountValuationBridge` 与
  residue-one（GAP-PC-RESDEG/tame）。
