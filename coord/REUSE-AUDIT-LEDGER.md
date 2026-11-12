# REUSE-AUDIT-LEDGER — 六主题历史结论/文件复用清单

日期：2026-11-13（A1048）。**Status: READ-ONLY inventory；不是证据/不是编译结果。** 所有 Lean 状态只到“源码/olean/gate 记录”层级；未重编。

口径：`A编号` 为 AUDIT_LEDGER/历史任务号；无 A 编号的条目保留日期。`PENDING-WATCHDOG` 表示尚未有 watchdog trio/#print axioms/probe 结果；`data-only` 不可当 Lean 证明。

## 1. Σj²/nC·sF/qScaling 恒等式

| 条目 | 历史 A/日期 | 文件 | 状态 | 可复用 |
|---|---|---|---|---|
| `sum_jsq_eq_nC_mul_sFactor`：`Σ_{j=1}^{nC} j² = nC·sFactor nC` | A777–A787（paper normalization 阶段）/ A1043 巡检 | `tmp/sheaf/xif/paper/Mzk1ScalingNormalizationActual.lean` | 源码/olean 存在；A1043 巡检/编译记录；非 N5 gate | **可直接复用**：纯算术恒等式，接 `sFactor`/`jsqSum`；不依赖 N5 |
| `M = logp·[(1−sF)x1 + mean(frac)] + Kbar'` 分解 | A1018/A1022/A1030（见 `DECOMP-ALGEBRAIC.md`） | `coord/DECOMP-ALGEBRAIC.md`；`tmp/sheaf/xif/paper/Mzk1MDecompositionActual.lean` | `Mzk1MDecompositionActual` green（A1043，olean 244,848B fresh）；文档为 MODEL 推导 | 可复用代数重排/`mean_frac_bound`；**不能**给目标不等式 |
| qScaling 归一化（`qScale`/`jsqSum` 与 A 系数） | A1043 巡检 / A777–A787 | `Mzk1ScalingNormalizationActual.lean` 的 `sum_jsq_eq_nC_mul_sFactor`/后续两式 | 源码/olean；未列入 N5 gate | 可复用为归一化恒等式；先核 `qOrder`/2ℓ 口径（A1029） |

## 2. Signed log volume

| 条目 | 历史 A/日期 | 文件 | 状态 | 可复用 |
|---|---|---|---|---|
| `sourceLogVolumeSigned_eq`、`sourceLogVolumeSigned_upper`、`globalThetaHullLogVolumeSigned_eq` | A1043 巡检（2026-11-13） | `tmp/sheaf/xif/paper/Mzk1SignedLogVolumeActual.lean` | 源码/olean（0:12:59 落盘）；PENDING-WATCHDOG | 可复用 signed readout/等式；`PaperRIdentification` 是 def，不含目标 |
| `signedHullLogVolume`/`signedHull_le` 历史读法 | 未标 A（2026-11-06/07） | `S2714`/`S2715`、`S660RootPaperSignedHullActual`、`S665PaperSignedHullXiFInterfaceActual` | 部分 ACTUAL/部分条件；见 `AUDIT_LEDGER` 约 L8300/L11600 | 可复用 signed 定义/上界接口；**方向**须按 A1050：`logVol=−log μ`，不混用旧读法 |
| `sourceSignedHullLogVolume = 0` 的模型限制 | 见 `SUBAGENT_C_REPORT.md` | `tmp/sheaf/xif/paper/...` | MODEL/限制记录 | 只可作反例/范围提醒；不能当 paper signed hull |

## 3. Log-volume 单调性/包含

| 条目 | 历史 A/日期 | 文件 | 状态 | 可复用 |
|---|---|---|---|---|
| `componentVol_mono`（`a·O ⊆ b·O ⇒ V(a)≤V(b)`） | lana 源级（无 A；见 `Iut/Concrete/LocalConstruct/Volume.lean`） | lana `Iut/...` | 源级；本地 olean 未必产 | 可复用公式/证明骨架；不可当本地 green |
| `leastHull_subset`/`leastHull_mono`/`componentVol_le_leastHull` | lana 源级（Gap.lean/VcI） | lana `Iut/WallEquiv/Gap.lean`/`VcI.lean` | 源级 | 可复用 hull 单调性/包含；R 仍不可数值 |
| `actualRegion_subset_hull`、`actualHolomorphicHull_monotone` | 未标 A（2026-11-10 task-18） | `tmp/sheaf/xif/paper/Mzk1S3132PaperHullSetPropertiesActual.lean` | 源码/olean（待 watchdog 复核） | 可直接复用 hull 包含/单调 API |
| `actualHolomorphicHull_monotone` 与 `haarLogVolume_mono_of_subset` 组合 | A1049/A1050（方向核定） | `Mzk1QRegionInclusionActual.lean` | 源码待 watchdog；方向 VERIFIED | 可复用 measure 单调骨架；正确方向 `theta⊆q` |

## 4. CTheta/CThetaPaper scale/bridge

| 条目 | 历史 A/日期 | 文件 | 状态 | 可复用 |
|---|---|---|---|---|
| `CThetaPaper` 定义、`CThetaPaper_def_eq`、`cThetaPaperFactor_pos`、`CThetaPaper_ge_neg_one_iff`、lowerBound 转换 | 未标 A（2026-11-06） | `tmp/sheaf/xif/paper/S2715CThetaPaperScaleActual.lean` | ACTUAL（历史）；olean/source 存在；非 gate | 可复用**定义/scale 转换**；`lowerBound` 仍需 theta hull upper+q 归一化 |
| `CThetaPaper = thetaSigned/|log q|`、upper bound | 未标 A（2026-11-07） | `S2953CThetaFromCertificateActual`、`S2956CThetaPaperUpperActual` | ACTUAL/条件；S2953 被记录为定义循环 | 只可复用定义/条件接口；**不能**当独立 CTheta 上界 |
| `S3016CThetaUpperInterface`/`upper_bound` | 未标 A（2026-11-07） | `S3016CThetaUpperActual.lean` | 接口字段式；无 construction | 可复用接口形状；`upper` 是字段，不是定理 |
| `S3034PacketScalarBoundActual` | 未标 A（2026-11-07） | `S3034PacketScalarBoundActual.lean` | target Prop `S3034Hscalar`；无 theorem | 只有 hscalar 接口；不能给 rhs 下界 |

## 5. N5/rhs 下界/variant 条件版

| 条目 | 历史 A/日期 | 文件 | 状态 | 可复用 |
|---|---|---|---|---|
| N5 精确陈述 `rhs = V+gap−sF·A`、`N5 ⇔ M≥0` | A1041（N5-STATEMENT）/ A1045 修符 | `coord/N5-STATEMENT.md` | PARTIAL；N1–N4 PENDING-WATCHDOG | 可复用陈述/符号；**无 determinant comparison** |
| N5 assembly feasibility：S3016/S3017/S3034 只给 upper bound，不能给下界 | A1042（N5-ASSEMBLY-FEASIBILITY） | `coord/N5-ASSEMBLY-FEASIBILITY.md` | READ-ONLY audit | **直接复用结论**：上界栈不能证 `rhs≥−A`；`hheight` 非 green |
| `N5Weak(C)`/`CPaper` 陈述 | A1042（N5-WEAK-PLAN） | `coord/N5-WEAK-PLAN.md` | PARTIAL/草案 | 可复用目标形状；C 的候选仍需 `hheight`/det 输入 |
| `Cor312VariantHolds` 是未证假设；ABC 桥纯蕴含 | A1029/stepxi | `coord/LANA-VARIANT-STATUS.md` | READ-ONLY audit | 可复用于“不得把 variant 当定理”的口径 |

## 6. 区域包含 / Haar 单调（含正确方向）

| 条目 | 历史 A/日期 | 文件 | 状态 | 可复用 |
|---|---|---|---|---|
| `haarLogVolume_mono_of_subset`；`thetaRegion⊆qRegion ⇒ variant` | A1049/A1050 | `tmp/sheaf/xif/paper/Mzk1QRegionInclusionActual.lean` | 源码待 watchdog；DIRECTION-SUFFICIENT（非等价）；反向反例保留 | **直接复用** measure 单调骨架；只接受 `theta⊆q`，反向只给相反不等式 |
| `prime_smul_closedBall`、`rootExtensionHaar_ball_strict`（1D p-scaling） | A587 | `tmp/sheaf/xif/paper/Mzk1HaarScalingOneDimActual.lean` | GREEN（历史 95s）；olean fresh | 可复用 1D 球严格测度 |
| `rpRegion_subset_hull`、`rpVolume_strict`、`rp_cor312`（乘积严格性/strict_measure） | A588 | `tmp/sheaf/xif/paper/Mzk1HaarStrictScalingProductActual.lean` | GREEN（历史 99s）；olean fresh | **直接复用** region 包含/严格测度/Cor312 要求；注意与 N5 下界不同 |
| `componentVol_mono`/`leastHull_mono`/`actualHolomorphicHull_monotone` | A587–A588 + 2026-11-10 task-18 | lana `Gap.lean`/`VcI.lean` + `Mzk1S3132PaperHullSetPropertiesActual` | 部分源级/部分源码 | 可复用 monotonicity API；不替代 determinant comparison |

## 7. 结论

- 可直接复用的核心：`sum_jsq_eq_nC_mul_sFactor`、`Mzk1SignedLogVolumeActual` 的 signed 读数、`Mzk1HaarStrictScalingProductActual` 的 region inclusion/Haar strictness、`Mzk1QRegionInclusionActual` 的 measure 单调（方向 `theta⊆q`）、N5 feasibility 的“upper-bound 不能给下界”结论。
- 只能复用接口/定义、不能当证明：`CThetaPaper` 定义/scale、`S3016CThetaUpperInterface` 字段、`S3034Hscalar` target、N1–N4（PENDING-WATCHDOG）。
- 不可复用/需修正：任何 q⊆θ 方向（A1048b 作废）；`Olean TRUE` 当 gate；`S2953` 定义循环的 upper certificate。

**指针**：`AUDIT_LEDGER.md`（A587/A588/A777–A787/A1029/A1041–A1045/A1049–A1050）、`coord/DECOMP-ALGEBRAIC.md`、`coord/N5-ASSEMBLY-FEASIBILITY.md`、`coord/XID-DETERMINANT-PLAN.md`、`coord/CTHETA-RETARGET-IMPL.md`、`coord/REUSE-AUDIT-ABC.md`。

## 8. A1051 signed-stack 约定说明（不要混）

两种写法**在 `vol = exp(-·)` 下等价**，但字面方向/变量名不同：

| 约定 | 单调量 | 包含字段的字面 | 结论 | 对应 |
|---|---|---|---|---|
| **我们的 logVol 约定** | `logVol S = −log μ(S)` | `thetaRegion ⊆ qRegion` | `−A ≤ −R`（variant） | `Mzk1QRegionInclusionActual` / `haarLogVolume_mono_of_subset` |
| **signed-stack 约定** | `signedLogVolume vol S = log(vol S)` | `XiEContainment.subset : qRegion ⊆ hullRegion` | `signedQ ≤ signedTheta`，即 `−A ≤ −R` | `Mzk1SignedLogVolumeCor312Actual` / `signed_cor312_inequality` |

- 对应关系：令 `vol qRegion = exp(−A)`、`vol hullRegion = exp(−R)`，则 `signedQ = −A`、`signedTheta = −R`；`qRegion⊆hullRegion` + `vol` 单调 ⇒ `−A≤−R`，与 logVol 约定的 `thetaRegion⊆qRegion` 是**同一充分条件**（只是 set 命名/vol 映射不同；反向 measure 不等式不反推包含）。
- **禁止混用**：在 logVol 约定下写 `q⊆θ` 会得到 `−A≥−R`（反向）；在 signed-stack 约定下不要把包含字段改写成 `θ⊆q`，除非同时换 `vol` 映射。引用时写明约定。
- `Mzk1QRegionInclusionActual` 已标 `SUPERSEDED-PARTIAL`，新增 adapter 复用 signed 栈；`variant_rankone_conditional_rev` 保留为反向反例。指针：`coord/REUSE-SIGNEDLOG-INTEGRATION.md`、`tmp/sheaf/xif/paper/Mzk1SignedLogVolumeCor312Actual.lean`。

## 9. A1067 工具性/强不等式分类（拿来主义）

**目标口径**：我们的目标 = `M := V+gap−(sF−1)A ≥ 0`（我们的 variant，较弱），**不是** lana `SSIneq`（`V−(sF−1)A≥0`，更强）。只取 lana 工具，不取强不等式。

| 历史条目/文件 | 分类 | 用法 |
|---|---|---|
| `sum_jsq_eq_nC_mul_sFactor`（ScalingNormalization） | **TOOL** | 纯代数恒等式，可直接用 |
| `sourceLogVolumeSigned*`、`signedLogVolume*`、`signedLogVolume_mono` | **TOOL** | signed-log/单调性工具；不假设 lana variant |
| `haarLogVolume_mono`、`componentVol_mono`、`actualHolomorphicHull_monotone` | **TOOL** | Haar/volume 单调；配我们自己区域 |
| `Mzk1HaarStrictScalingProductActual`/`Mzk1HaarScalingOneDimActual` | **TOOL** | region inclusion/strict Haar 工具 |
| `CThetaPaper` 定义/scale/lower-bound 转换（S2715） | **TOOL（条件）** | 只取定义/scale；`lowerBound` 仍是接口，不是 lana 强不等式 |
| `S3016CThetaUpperInterface.upper`/`S3034Hscalar` | **TOOL（上界/接口）** | 上界不是我们目标；不能给 rhs 下界 |
| `signed_cor312_inequality` / `signedLogVolume_mono` | **TOOL（抽象条件）** | 需 `q⊆hull` + `vol=exp(-·)` 实例化；不是 lana SSIneq |
| `Mzk1SSIneqVolumeActual.ssIneq_iff_volume` / lana `Wall.SSIneq` / `Cor312Variant*` | **LANA-STRONG / NO** | 只可对照/工具化片段；**禁止当目标/假设**；若引用必须弱化 |
| `final_cTheta_ge_neg_one` | **TOOL（cTheta 下界）** | 只作 cTheta 标量工具；不推出我们的 `M≥0` |
| HDD S1476/S1418/S1422 det/tensor assets | **TOOL（部分）** | det/tensor-power/one-sided theta；不提供 N5 `theta⊆q` |
| N5Weak/N5 陈述 | **OURS** | 我们的弱目标；N5Weak 常数/误差需自行接 |

- **禁止**：把 `SSIneq`/`Wall`/`Thm311`/`Cor312Variant(Holds)` 当输入或目标；若某工具引理陈述本身 = 强不等式，只能取其实例化/弱化片段。
- 旧 `REUSE-AUDIT-LEDGER` 条目若无分类，按本表/目标口径处理；历史“target=SSIneq”表述以 A1067 为准。
