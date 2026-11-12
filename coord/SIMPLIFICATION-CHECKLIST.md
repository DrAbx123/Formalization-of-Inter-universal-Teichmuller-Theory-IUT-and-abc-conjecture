# SIMPLIFICATION-CHECKLIST — 可空泛满足/任意数据/Prop 占位审计 (A1128)

| field | value |
|---|---|
| Status | READ-ONLY AUDIT（no compile）；判定 = ACTUAL / ARBITRARY / SIMPLIFIED |
| 范围 | S919/S917/S970/S976/S989/S994/S1004 + PaperXiFSourceLink 链（Concrete*） |

## 1. S919GlobalWeightedInequalityActual（olean=True）

| 位置 | 内容 | 判定 |
|---|---|---|
| L33-34 | `mu : ∀ b, Measure (qVFamTensorBlock T b)` + `[IsAddHaarMeasure (mu b)]` | **ARBITRARY**：任意 additive Haar（归一化未固定）；per-b log 依赖此归一化 |
| L37-39 | `weightedPaperV := Σ_b nativeBadLocalWeight T b * V b` | **ACTUAL**（权重来自 nativeBadLocalWeight；L49 用其非负性） |
| L52-57 | `perBVR := qPilotPaperRegionLog T b (mu b)`；`perBVS := paperRootThetaHullLogNonzero T b (mu b)` | **ARBITRARY**（inherits mu 归一化） |
| L61-66 | `globalWeightedInequality_of_perB`（per-b ⇒ 全局） | **ACTUAL**（纯加权单调） |
| L69-71 | `PerBGlobalWeightedHypothesis : Prop`（per-b 不等式本身） | **SIMPLIFIED / GAP**（把目标侧当假设；未证） |
| L73-77 | `globalWeightedInequality_actual (h : PerB...)` | **ACTUAL conditional**（条件版，不空泛） |

## 2. S917IndImageUnionActual（olean=True）

| 位置 | 内容 | 判定 |
|---|---|---|
| L37-39 | `currentMultiradialImageUnion_eq_theta : paperRootThetaImageNZ = paperRootThetaImageNZ` | **SIMPLIFIED/TRIVIAL**（rfl 自等；**不包含 Ind1/2/3 像**；文件注释自认） |
| L42-50 | `qPilotPaperRegion_subset_thetaImageNZ` | **ACTUAL**（j=1 包含，真证） |
| L53-60 | `indAugmentedImageUnion (IndImages) := paperRootThetaImageNZ ∪ IndImages`；`indAugmentedHull := closure ...` | **ARBITRARY**：`IndImages : Set (qVFamTensorBlock T b)` 是**任意参数**，未由 Ind1/2/3 作用构造 |
| L64-69 | `qPilot_subset_indAugmentedHull (IndImages)` | **SIMPLIFIED**（对任意 IndImages 都成立；无实际 Ind 数据即空泛） |
| L72-74 | `IndStrictEnlargement` | Prop 条件（GAP marker） |
| L90-95 | `indAugmentedHull_empty`（空 IndImages ⇒ hull = closure θ image） | **ACTUAL equality，但退化**（enlargement=0，正是隐含的 iv/单像情形） |

## 3. S970FiniteLogShellCarrierActual（olean=True）

| 位置 | 内容 | 判定 |
|---|---|---|
| L25-26 | `FiniteLogShellCarrier p d := Fin d → ℚ_[p]` | **ACTUAL**（有限维模型；d 此处为参数） |
| L39-47 | `FiniteLogShellHaarData` 字段：`[LocallyCompactSpace]`/`[MeasurableSpace]`/`[BorelSpace]`/`measure`/`[IsAddHaar]`/`unitRegion`/`unit_pos`/`unit_lt_top` | **ARBITRARY**（结构层允许任意 Haar + 任意 unitRegion；不是 canonical） |
| L50-51 | `FiniteLogShellHaarRequired := Nonempty (FiniteLogShellHaarData d)` | **SIMPLIFIED**（存在 Prop；已被 S976 实际构造超越） |
| L55-57 | `FiniteQuotientBridge Packet := ∃ d, Nonempty (Packet ≃ₗ Fin d → Qp)` | **SIMPLIFIED/GAP**（存在性 Prop；S996 对 qVFamTensorBlock 提供实际线性化） |

## 4. S976FiniteLogShellHaarActual（olean=True）

| 位置 | 内容 | 判定 |
|---|---|---|
| L36-48 | `finiteLogShellHaarData d`：`Measure.addHaar`、`unitRegion := Metric.closedBall 0 1`、pos/lt_top 证明 | **ACTUAL**（canonical Haar + 单位球；d 任意但构造实际） |
| L51-53 | `finiteLogShellHaarRequired d` | **ACTUAL**（已证） |
| L62 | `finiteQuotientBridge_of_finiteDimensional` | **ACTUAL conditional**（需有限维假设；对本项目 qVFamTensorBlock 由 S996 提供） |

## 5. S989FiniteCarrierDirectActual（olean=True）

| 位置 | 内容 | 判定 |
|---|---|---|
| L46-48 | `finitePaperTensorData d := finiteLogShellHaarData d` | **ACTUAL** |
| L51-54 | `finiteQPilotImage L := L.e '' qPilotPaperImageInLValued` | **ACTUAL**（但依赖 `L : S965CarrierLinearization`；需 S996 型实际线性化） |
| L57-60 | `finitePaperHull L := finitePaperTensorHull`（S978） | **ACTUAL**（S978 实际） |
| L62-65 | `finiteQPilotImage ⊆ finitePaperHull` | **ACTUAL**（S978） |
| L68-71 | `finiteNormalizedLog := log μS − log μ unitRegion` | **ACTUAL**（与 S962 同型；单位归一化） |
| L74-82 | `FiniteCarrierPaperComparisonInterface`：`qPilotLog hullLog : Real`、`logComparison : Prop` | **SIMPLIFIED**（任意 Real/Prop 字段；由 L84-90 用实际数据填充，但接口本身允许空泛） |

## 6. S994FiniteCarrierCor312Actual（olean=True）

| 位置 | 内容 | 判定 |
|---|---|---|
| L47-53 | `S994FiniteLinearization`（d/e）+ `s994ActualLinearization`（d := finrank, e := s996QVFamLinearization） | **ACTUAL**（d 由 finrank 给出） |
| L54-61 | `s994H := finiteLogShellHaarData L.d`；`s994QPilotImage/s994Hull := L.e '' (paper regions)` | **ACTUAL** |
| L62-64 | `s994Containment` | **ACTUAL**（image_mono） |
| L65-70 | `S994PerBInput` 字段 `qPilot_pos`、`hull_finite` | **ARBITRARY/条件**（显式假设 `0 < μ(qPilotImage)`、`μ(hull) < ⊤`；positivity 未自动得） |
| L71-85 | `s994PerBLogComparison` | **ACTUAL conditional**（由 containment+pos/fin 真证） |
| L86-91 | `S994FiniteInput`（每 b 的 pos/fin） | 条件（同上） |
| L92-98 | `s994VR/s994VS/s994GlobalWeightedInequality` | **ACTUAL conditional**（log 公式 + S919 加权单调） |

## 7. S1004QVFamFiniteLinearizationActual（olean=True）

| 位置 | 内容 | 判定 |
|---|---|---|
| L47-51 | `s1004E := s996QVFamLinearization`（`qVFamTensorBlock ≃ₗ Fin d → Qp`） | **ACTUAL**（d = finrank） |
| L52-61 | `s1004QPilotImage/s1004Hull := s1004E '' (qPilotPaperRegion / paperRootThetaImageNZ)` | **ACTUAL** |
| L62-64 | `s1004Containment` | **ACTUAL** |
| L65-77 | `finiteNormalizedLog_mono_qvfam`（log 单调，pos/fin 显式条件） | **ACTUAL conditional** |
| L79-85 | `s1004PerB`（per-b log 比较） | **ACTUAL conditional**（pos/fin） |

## 8. PaperXiFSourceLink 链（Concrete*，olean=True）

| 位置 | 内容 | 判定 |
|---|---|---|
| `ConcretePaperUnconditionalDataActual` L92-124 | `concretePaperUnconditionalData (hnormal) (hq) (hcomp)`：`link_identification := concreteSourceComparison`（真 Prop，非 True）；`link_implies_inclusion := concreteMembership_of_sourceComparison` | **ACTUAL 结构 + GAP 输入**（`hnormal`/`hq`/`hcomp` 三个显式假设；`hq` 是 q-pilot log 归一化，`hcomp` 是 source comparison） |
| `ConcretePaperXiFInclusionActual` L16-30 | 文件头声明：link_identification 从不是 True；inclusion 只在 comparison 证明下成立；“remaining q-pilot log normalization equality is an explicit input” | **ACTUAL**（无 True/PUnit/axiom/sorry；但 hq 为输入） |
| `PaperFinalLValuedTensorCarrierActual` L34-46 | `finalLGeometry` 用 `PUnit` 作为 place index；`FinalL := RootExtension := AlgebraicClosure`；`FinalLValuedCarrier := TensorProduct ... FinalL` | **SIMPLIFIED/ARBITRARY**：PUnit 指标（单点几何）折叠 place 结构；AlgebraicClosure 非有限维无 canonical Haar（见 MODEL-FIX） |
| `ConcreteSignedHullUnconditionalActual` L74/93/111 | `unconditionalPaperSignedHull` + `hull_logVolume_eq` + `signedHnormal` | **ACTUAL**（由 concrete signed hull + normalized Haar 构造） |

## 9. 汇总

```
ACTUAL（实际数据/真证）：
  - S976 finiteLogShellHaarData（canonical addHaar + closedBall）；
  - S994/S1004 的 d := finrank、e := s996QVFamLinearization、containment、log 单调、global weighted；
  - S919 weights、weightedPaperV、globalWeightedInequality_of_perB；
  - Concrete* 链的 link_identification（真 Prop）与 unconditionalPaperSignedHull；
  - S917 qPilotPaperRegion_subset_thetaImageNZ。
ARBITRARY：
  - S919 `mu`（任意 additive Haar 归一化）；
  - S917 `IndImages`（任意 Set，未由 Ind1/2/3 构造）；
  - S970 `FiniteLogShellHaarData`（结构层任意 measure/unitRegion；但 S976 提供 canonical 实例）；
  - S994 `S994PerBInput.qPilot_pos/hull_finite`（显式条件）；
  - `finalLGeometry` 的 PUnit index。
SIMPLIFIED/TRIVIAL/GAP：
  - S917 `currentMultiradialImageUnion_eq_theta`（rfl 自等，不含 Ind 像）；
  - S917 `qPilot_subset_indAugmentedHull`（对任意 IndImages 空泛成立）；
  - S970 `FiniteLogShellHaarRequired`/`FiniteQuotientBridge`（存在性 Prop）；
  - S919 `PerBGlobalWeightedHypothesis`（目标侧当假设）；
  - S989 `FiniteCarrierPaperComparisonInterface` 的 `qPilotLog/hullLog/logComparison` 字段（任意 Real/Prop）；
  - Concrete* 的 `hq`/`hcomp`/`hnormal` 输入（显式 GAP）；
  - `FinalL := AlgebraicClosure`（无限维、无 canonical Haar）。
```

## 10. 对 target 的影响

1. 模型应统一到 **S1004/S994 有限维链**（canonical Haar、d 实际、containment 真证）；
2. S919 的 `mu` 归一化需固定为 S976 的 `Measure.addHaar`（否则 per-b log 不唯一）；
3. S917 的 `IndImages` 必须由实际 Ind1/2/3 作用构造，否则 enlargement 是任意/空泛的；
4. Concrete* 链的 `hq`/`hcomp` 是 GAP（目标侧），不能作已证输入；
5. FinalL 载体（S971/S979/S981）应迁到方案 A（见 MODEL-FIX）；
6. S989/S994 的接口中 `qPilotLog/hullLog/logComparison` 是简化字段，实际使用时应直接取 S1004/S994 的 `s994VR/s994VS` 定义。