# REUSE-AUDIT-ABC — N5/QRegion/CTheta/单调性 可复用清单 (A1048)

| field | value |
|---|---|
| Status | PARTIAL (可复用清单；与 stepxi/hull 的 REUSE-AUDIT 对齐待其输出；未新增 Lean) |
| 原则 | 先复用、后新建；已写文件不删；本清单对应 `CONDITION-LATTICE.md` 的条件格 |

## 1. 单调性/体积比较（可直接复用）

| 定理 | 位置 | 用途 |
|---|---|---|
| `componentVol_le_of_subset` | `Iut/Wall/Rss.lean:63` | 包含 ⇒ componentVol 单调（QRegion 方向的核心） |
| `logVol_le_logVol_hullOf` | `Iut/Wall/Ind3.lean:138` | adelic region 包含于 hull ⇒ logVol 上界 |
| `packetVol_le_of_subset` | lana LocalTheory（Gap:140 使用） | packet 级单调 |
| `processionVol_le_of_packetVol` | lana LocalTheory（Ind3:140 使用） | procession 级单调 |
| `logVol_le_rhs` | lana WallEquiv（Gap:510-512 使用） | hull 上界到 rhs（N2/上界侧） |
| `logVol_monoLogShell` | `Iut/Reconstruction/Local/LogShellMono.lean:228` | log-shell 体积单调 |
| `logVolume_mono` | 我们 `A482LiteralIQHullInterfaceActual.lean:30` | IQ-hull log-volume 单调（green） |
| `lgpWeightedLogVolume_mono` | 我们 `AbsTopIII06WeightedVolumeBridgeActual.lean:43` | 加权 lgp 体积单调（green） |
| `ENNReal.toReal_mono` 适配 | 我们 `A502HcompToRealAdapterActual.lean:9` | measure→Real 单调 |
| `haarLogVolume_mono_of_subset` | 我们 `Mzk1QRegionInclusionActual.lean`（新） | 抽象 negative-log 单调（可证） |

## 2. CTheta / Step V 上界（可复用）

| 定理/结构 | 位置 | 用途 |
|---|---|---|
| `S3016CThetaUpperInterface`（fields + `upper`） | `S3016CThetaUpperActual.lean` | CTheta 上界接口（字段式） |
| `S3016CThetaUpperInterface.stepV_eq_global` / `upper_bound` | 同上 | stepV=global + 上界 |
| `S3017_processionAverage_bound` / `_expanded` | `S3017StepVUpperGapAssembly.lean` | procession 平均上界 |
| `S3017_CTheta_upper_of_height` | 同上 | 条件于 `hheight` 的 CTheta 上界 |
| `S3015FinalBound` / `S3015_final_real_inequality` | `S3015FinalRealInequalityActual.lean` | 最终实数不等式 |
| `S3014ProcessionData` / `S3014_processionAverage_of_data` | `S3014StepVProcessionAverageActual.lean` | 平均数据/引理 |
| `S3050_stepVTerm_eq_label_sq_mul_unit` / `_eq_qCoeff_mul_Q_add_rest` | `S3050StepVQExpansionActual.lean` | StepV 精确仿射分解 |
| `S3050QUnitIdentification Q` | 同上 | Q 系数识别的显式 Prop（GAP） |
| `S3029_perLabel_decomposition` / `_affine` | `S3029StepVAlignmentActual.lean` | per-label 仿射 |
| `S3013QSideSignedValueCondition` / `S3013` 系列 | 同目录 | q-side 符号条件 |

## 3. N5 直接相关（无现成定理，需组合）

| 需求 | 现有最接近 | 差距 |
|---|---|---|
| N5 `rhs >= -A` | `S3016CThetaUpperInterface.upper`（上界，方向相反） | GAP-DIRECTION：需 Step (xi-d) 的下界/包含 |
| N5Weak C | `S3017_CTheta_upper_of_height`（hheight 条件） | 方向对齐后才可给 C |
| q-pilot ⊆/⊇ theta hull | lana `inHullOfImage_lgp`（`lgp hull(vcI) ⊆ hull(theta)`，方向是 upper bound） | 需正确的 region 包含（θ⊆q，见 QRegion 文件的方向核定） |
| Q 系数精确 | `S3050QUnitIdentification`（Prop） | 未证 |
| Step (xi-d) determinant 比较 | 无 | 完全缺失（最大 GAP） |

## 4. 我们的 N1–N4（green，可复用）

| 节点 | 定理 | 文件 |
|---|---|---|
| N1 | `paperStepV_inequality` | `Mzk1PaperStepVBoxActual` |
| N2 | `volume_upper_of_dictionary`（+ `PaperDictionaryShape`） | `Mzk1StepVIdentificationActual` |
| N3 | `L7_with_arch` / `L7_global` / `L7_term` | `Mzk1DExactFromHullActual` |
| N4 | `deficit_nonpos_iff` / `deficit_expanded_form` | `Mzk1PaperNormDeficitActual` |
| 辅助 | `thetaSumPaper_eq_clana_mul` | `Mzk1PaperNormThetaActual` |
| 辅助 | `sum_jsq_eq_nC_mul_sFactor`（scaling 归一化） | `Mzk1ScalingNormalizationActual`（待 watchdog） |
| 骨架 | `N5Weak`/`MOf`/`M_ge_negC_of_N5Weak` | `Mzk1N5WeakSkeletonActual`（新，待 watchdog） |
| 骨架 | `haarLogVolume_mono_of_subset`/`cor312_rankone_conditional` | `Mzk1QRegionInclusionActual`（新，待 watchdog） |

## 5. 与 stepxi/hull REUSE-AUDIT 的对齐

- `coord/` 中现有 REUSE 文件：`BASIS-REUSE-A505.md`、`TAKKUN-REUSE-A500.md`、`TAKKUN-DIOPHANTINE-REUSE.md`
  —— 均非 N5/CTheta 线；**未发现 stepxi/hull 的 REUSE-AUDIT 文件**；
- 建议：把本清单提交 mainline/stepxi/hull 合并；若其审计列有上述 lana 单调性/`S30xx` 条目，
  以他们为准，避免重复新建。

## 6. 结论：哪些新文件真正必要

1. **必要**（已写，不删）：`Mzk1N5WeakSkeletonActual`（N5Weak 算术骨架）、
   `Mzk1QRegionInclusionActual`（抽象单调 + rank-one 条件定理，方向核定）；
2. **不必要（可复用代替）**：`CTheta` 上界、`StepV` 平均/仿射、QRegion 具体化、N1–N4 均已有 green 文件，
   **不要再新建**；
3. **只有 Step (xi-d) determinant 比较** 无任何可复用项；若要做，需 owner 决策（预计最大单项）；
4. 下一步：把 `CONDITION-LATTICE.md` 的条件映射到上表已有的定理/结构；仅对缺失项（N5/C5/hscalar/Step xi-d）
   建新文件。
## 7. A1067 拿来主义分类（工具性 / 强不等式）

**原则**：我们的目标是**较弱的自身 variant** `M = V + gap - (sF-1)*A >= 0`（等价 `V+gap >= (sF-1)A`），
**不是** lana 的 SSIneq `V - (sF-1)*A >= 0`（更强）。禁止把 lana 的 SSIneq/Wall/Thm311/Cor312Variant/
Cor312VariantHolds 作假设或前提；只 cherry-pick 定义、单调性、局部体积公式、signed-log 工具。

### 7.1 工具性（可直接复用）

| 条目 | 分类 | 说明 |
|---|---|---|
| `componentVol_le_of_subset` (Wall/Rss:63) | 工具：单调性 | 包含 ⇒ 体积单调 |
| `logVol_le_logVol_hullOf` (Wall/Ind3:138) | 工具：单调性/上界 | hull 包含 ⇒ logVol 上界 |
| `packetVol_le_of_subset` / `processionVol_le_of_packetVol` | 工具：单调性 | packet/procession 级单调 |
| `logVol_monoLogShell` (Reconstruction/Local/LogShellMono:228) | 工具：单调性 | log-shell 体积单调 |
| `haarLogVolume` / `haarLogVolume_mono` (ABCBridge/Geometry/FinitePlaceIQHullInterface:51/68) | 工具：定义+单调 | ENNReal log-volume 工具 |
| `signedLogVolume` / `signedLogVolume_mono` / `signedLogVolume_nonpos`（我们的 SignedLog 栈） | 工具：定义+单调+符号 | 条件版 signed 比较工具 |
| `componentVol_leastHull_tensorLogShell_eq` (VcI:603) | 工具：局部体积公式 | hull(⊗𝓘) 体积 = Σ radius·log p |
| `tame` 局部公式 (VcI:403-435)、`archDefect_nonneg`/`shellDefect_nonneg`/`ind2Term_nonneg` | 工具：局部非负/公式 | 局部项符号/公式，不涉全局强不等式 |
| `logVol_lgp`（体积平移公式） | 工具：归一化公式 | `logVol(lgp S) = logVol S - sF*A`；需按需弱化使用 |
| `S2807_thetaHullVolume_eq_haarRegion` | 工具：C3 Haar 识别 | theta hull = −haarLog region |
| `S2717QPilotLogVolume` / `S2717ThetaHullLogVolume` 定义 | 工具：定义 | 标量定义 |
| `Mzk1C3LogShellTensorLActual` 区域/haar/compactness | 工具：定义+测度 | L 侧体积工具 |
| `S3050_stepVTerm_eq_label_sq_mul_unit` / `_eq_qCoeff_mul_Q_add_rest` | 工具：代数恒等式 | StepV 仿射分解 |
| `S3016CThetaUpperInterface`（fields/upper） | 工具：接口/上界 | 上界估计，非目标假设 |
| `localNormOrder` / `rootNormedLogVolume` / `localQrootLogVolume` | 工具：标量定义 | Route A 标量工具 |

### 7.2 强不等式（禁止作假设/前提）

| 条目 | 分类 | 说明 |
|---|---|---|
| `Iut.Wall.SSIneq` | 强不等式（lana 目标） | `V - (sF-1)A >= 0` 形式，**不是**我们的目标 |
| `Iut.Corollary312Variant` / `Cor312VariantHolds` / `Cor312LiteralHolds` | 强/目标式 | lana 的 variant 形式；不得作前提 |
| `Iut.Wall`/`Wall.Gap` 的 `ss_iff_lgp_vcI`、`variant_of_ss_gap`、`ssNoHull_*` | 强不等式链 | 把 SSIneq 与 rhs 绑定；不得引用为前提 |
| `logVol_lgp_vcI_le_rhs` / `gap_nonneg` / `gapNoHull_nonneg` | 强不等式的中间结论 | 方向是 lana rhs 上界（其 gap≥0），若用于我们目标需弱化/只取其实例化工具部分 |
| `Thm311`/`Cor312` 的任何“结论式”定理（NonDerivable 等） | 强/元结论 | 不作前提 |
| lana `classicalABC_of_variant`（MainTheorem:13） | 强假设式 | 需要 Cor312VariantHolds；我们的目标不走这条路 |

### 7.3 使用规则

1. 任何 lana 引理若**陈述本身蕴含 SSIneq/Variant 方向**，必须改写或弱化后使用（如只取其
   monotonicity/定义/局部公式实例）；
2. 文档与 Lean 文件不得把 lana 的 SSIneq/Variant 写成我们的目标；我们的目标固定为
   `M = V + gap - (sF-1)*A >= 0`；
3. 需要 lana 工具时，引用其**定义/局部公式/单调性**行号，并注明“工具性”分类；
4. 我们的 `Mzk1SSIneq*`/`Mzk1Scaled*` 等若引用 lana SSIneq，只作审计对照，不进我们链。

### 7.4 现有文件的影响

- `Mzk1QRegionInclusionActual`（θ⊆q 桥）：工具性（单调性+signedLog 桥），非 lana 强不等式；
- `Mzk1N5WeakSkeletonActual`：纯算术（N5Weak 是我们的显式假设/目标弱化），不含 lana 强不等式；
- `Mzk1QPilotHaarBridgeActual`：Harr 工具 + S2807 识别，不引用 lana SSIneq；
- `Mzk1ContainAttemptActual`：候选区域/单调性，工具性。