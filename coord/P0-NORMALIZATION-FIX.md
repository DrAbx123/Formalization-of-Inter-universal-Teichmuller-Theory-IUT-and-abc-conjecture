# P0-NORMALIZATION-FIX — q-pilot c_norm=m vs paper c_root=m/(2l)

日期：2026-11-13；qpilot（R29e / task-85，P0-fix）。**Status: source-level target correction + read-only impact audit**；未编辑既有 green 文件；新接口已 watchdog **DONE EXIT=0**（olean 85,984B，2026-11-12T20:23:15Z）。

## 0. 结论先行

**Paper 系数判定：paper 的 q-pilot/Theta-pilot 读数使用 `q_v := q^(1/2l)`，即 `c_root = order(q)/(2l) = m/(2l)`；`c_norm=m` 只是 green 链的建模归一化，不是 paper 的 q-pilot 读数。**

因此 `Ind3OutputHullQPilotActual:97` 的 `actualQPilotLog_le_ind3OutputHullLog` 是 **c_norm q-region vs c_root hull**，**不是** paper 的 `−|log q| ≤ −|log Θ|`。

## 1. 原文定位（paper 系数）

文本文件：`D:/lean/tmp/iut1.txt`、`iut2.txt`、`iut3.txt`（审计用文本副本；行号为该文件行号）。

| 事实 | 原文位置 | 引文/说明 |
|---|---|---|
| q_v 是 q 的 2l 次根 | `tmp/iut1.txt:3703-3712` | `Write q_v for the q-parameter ... q_v admits a 2l-th root` |
| **q_v := q^{1/2l}** | `tmp/iut1.txt:3713-3726` | `the value of Θ_v at √−q_v is equal to q_v := q^{1/2l}`（原文记号 `q^{1/2l}_v`） |
| theta 值是 `q_v^{j²}` | `tmp/iut2.txt:4273-4289`（Rem 2.5.1(i)） | `θ_j(Π...) consists of ... q_v^{j²}`，引 `[IUTchI], Example 3.2, (iv)` |
| q_v 是 2l-th root | `tmp/iut2.txt:96-100` | `q_v denotes ... Let q_v be a 2l-th root of q_v.` |
| q-pilot object 由 q_v 决定 | `tmp/iut3.txt:6506-6544`（Def 3.8(i)） | `determined by the 'q_v', for v∈V_bad [cf. ... Example 3.2, (iv)] — as a q-pilot object` |
| Cor 3.12 目标 | `tmp/iut3.txt:10152-10180` | `−|log Θ| ≥ −|log q|`（10178-10180） |

**判定**：q-pilot 对象的读数是 `q_v=q^{1/2l}`，所以 `−|log q_v| = −(m/(2l))logp`；Theta 侧 `q_v^{j²}` 的系数也是 `j² m/(2l)`。
`c_norm=m` 对应的是 `−|log q|`（q 本身）的模型 qRegion，不是 paper 的 q-pilot。

## 2. 修正后的 paper-faithful 目标（块级）

在固定实际 block `qVFamTensorBlock T b`（one-factor）、paper 系数 `c_root` 下：
```
qPilotPaperRegion := thetaTensorScaledRegion (c_root)
paperPossibleImages := rootThetaImageSet (c_root)
paperQLog := arithmeticTupleNormalizedLogVolume (qPilotPaperRegion)
paperThetaLog := arithmeticTupleNormalizedLogVolume (leastLambdaOHull paperPossibleImages)
PaperTargetNormalization := paperQLog <= paperThetaLog
```
等价正量（Cor 3.12 的 signed 形式）：
```
A_paper := -paperQLog;   R_paper := -paperThetaLog;
M_paper := A_paper - R_paper;
PaperTargetNormalization <=> 0 <= M_paper
```
注意：这是**单 block 的 component 目标**，不是全局 Cor 3.12；仍缺全局权重、arch、Ind1/Ind2/Ind3 和 procession 归一化。不得把它当完整目标 closure。

### 2.1 新 Lean 接口

文件：`tmp/sheaf/xif/paper/Mzk1PaperTargetNormalizationActual.lean`

- `cNorm i := rootNormCoefficient T b i`（green c_norm）；
- `cRoot i := rootHalfCoefficient T b i`（paper c_root）；
- `cNorm_eq_twoL_mul_cRoot : cNorm i = (2*l) * cRoot i` —— deviation 的精确形式；
- `paperQLog := qPilotPaperRegionLog`；`paperThetaLog := paperHullLog`；
- `PaperTargetNormalization : paperQLog <= paperThetaLog`；
- `paperTargetNormalization_of_pos_fin`：直接复用 `S800LeastLambdaOHullActual.qPilotPaperRegionLog_le_paperHullLog`，posit/finit 是显式假设；
- `paperA/paperR/paperM` 与 `paperM_nonneg_iff_target`；watchdog DONE EXIT=0，olean 85,984B；
- 不删除、不覆盖任何旧 c_norm 定理。


## 2.2 与既有 S3050/S3029 StepV 接口的对齐

文件：tmp/sheaf/xif/paper/S3050StepVQExpansionActual.lean

- S3050Unit p jValue l := -((-localNormOrder p jValue)/(2*l))*log p
  = (ord J)/(2l) * log p（因为 localNormOrder J = ord J，而 paper 的 qOrder = -ord J）；
  即 S3050Unit = -c_root(q) * log p，其中 c_root(q)=qOrder/(2l)。
- S3050_stepVTerm_eq_label_sq_mul_unit：S3029StepVTerm = label^2 * S3050Unit；
  所以 StepV 的 j^2 结构自动是 paper 的 j^2 * c_root，不是 c_norm。
- S3050QUnitIdentification Q := ∃ c, S3050Unit = c * Q。

真值判定：

| 命题 | 判定 | 理由 |
|---|---|---|
| S3050QUnitIdentification Q，Q != 0 | 真（平凡） | 取 c = S3050Unit/Q；只是任意比例存在性，没有 paper 常数内容 |
| S3050QUnitIdentification 0 | 一般不真 | 除非 S3050Unit=0；paper Q 不为 0 |
| S3079PaperConstantTarget（unit/Q 三组独立常数） | 未证/需新来源 | S3079 只给 unit/Q 定义；要证其与 (a,b,c) 无关，需要 S2921Q 与 c_root 的来源恒等 |
| Q 应取 c_root 还是 c_norm | 应取 c_root 的单位 S3050Unit | S3050Unit 已经是 paper root q 的 -c_root log p；S2921Q 是 q-pilot line-bundle log（c_norm 侧），不能直接当 paper c_root |

因此 S3050QUnitIdentification 是真命题这句话只在平凡比例存在性意义下成立；它不能证明 paper 的 q-pilot 识别。把 Q 取成 S3050Unit（paperRootQ）时，常数 c=1；若取 S2921Q，c 依赖数据，仍需新的来源等式/三组独立性。

## 3. 受影响 green 结论清单（保留，标 deviation）

### 3.1 仍是 paper 口径、可保留的

| 结论 | 文件:行 | 判定 |
|---|---|---|
| `rootHalfCoefficient` = order/(2l) | `RootNormalizedContainmentActual.lean:56-58` | **paper c_root 定义**，保留 |
| `qVFamPaperRootCoefficient` = order/(2l) | `QVFamRootFactorCorrectionActual.lean:54-57` | **paper c_root**，保留 |
| `qVFamPaperThetaTensorCoefficient j` = j²·order/(2l) | 同上 `:59-63` | **paper theta 系数**，保留 |
| old tensor coefficient = (2l)·root coefficient | 同上 `:65-72` | **deviation 修正恒等式**，保留 |
| `qPilotPaperRegion` = c_root region | `S800LeastLambdaOHullActual.lean:75-88` | **paper qRegion**，保留 |
| `qPilotPaperRegionLog` / `paperHullLog` / `qPilotPaperRegionLog_le_paperHullLog` | 同上 `:104-131` | **paper block target（条件于 pos/fin）**，保留 |
| `S799LeastLambdaOPaperTargetActual` paper least-hull target | `S799...` | paper 方向；保留（其条件/口径另行核对） |

### 3.2 正确但不是 paper 陈述（标 deviation，不删除）

| 结论 | 文件:行 | 问题 |
|---|---|---|
| `qPilotNormRegion` = qPilotClassicalRegion c_norm | `RootNormalizedContainmentActual.lean:82-85` | c_norm=m，不是 paper q_v 的 m/(2l) |
| `qPilotNormRegion_subset_rootNormHull` | 同上 `:99-107` | **c_norm region vs c_root hull**；不是 paper 同系数包含 |
| `qPilotNormLog_eq` | 同上 `:109-120` | 只给 c_norm q log 公式；不是 paper `−|log q_v|` |
| `qPilotNormLog_le_rootNormHullLog` | 同上 `:122-139` | **c_norm q vs c_root hull**；不是 paper `−|log q| ≤ −|log Θ|` |
| `qPilotClassicalLog_eq` | `RootHullContainmentInequalityActual.lean:104-114` | c_norm formula，correct in model |
| `qPilotClassicalLog_le_rootThetaHullLog` | 同上 `:122-133` | mixed c_norm/c_root；not paper target |
| `actualQPilotLogShellRegion` = `qPilotNormRegion` | `Ind3OutputHullQPilotActual.lean:73-75` | c_norm region |
| `actualQPilotLogShellRegion_subset_ind3OutputHull` | 同上 `:77-82` | c_norm region ⊆ c_root hull；mixed |
| `actualQPilotLog_le_ind3OutputHullLog` | 同上 `:95-107` | **mixed c_norm/c_root 比较**；不是 paper `−|log q|≤−|log Θ|`；必须重述/改接线 |

**处理原则**：这些结论在 c_norm 模型内仍正确（olean 保留）；不得删除/覆盖，也不得把它们当 paper target。需要新增 paper 接线，而不是改旧文件（本任务 scope 只新增接口）。

## 4. 下一步/协调

1. watchdog 编译 `Mzk1PaperTargetNormalizationActual.lean`；若尚未在 `extra-targets.txt`，请 Lead 加入（当前 Lead 已列该文件在名单中）。
2. 新接口依赖 `S800LeastLambdaOHullActual`（green）与 `QVFamRootFactorCorrectionActual`（green）；不含旧 c_norm 目标。
3. 若要消费 Ind3 输出，需把 `Ind3OutputHullQPilotActual` 的 c_norm q 读数换成 `paperQLog`/`qPilotPaperRegion`；**这是接线任务，不是本文件自动完成**；旧 green 保留历史。
4. 全局目标还需：procession j 权重/card、arch/非 arch 归一化、Ind1/Ind2/Ind3 的实际 hull、以及 M 的 V/gap 项；块级 `PaperTargetNormalization` 只是 component。
5. 不得用 `Mzk1PaperTargetNormalizationActual.PaperTargetNormalization` 直接替代完整 Cor3.12；其 theorem 只给块级条件结论。

## 5. 文件/worktree 状态

- 新 Lean：`tmp/sheaf/xif/paper/Mzk1PaperTargetNormalizationActual.lean`（watchdog **DONE EXIT=0**；olean 85,984B；不自行编译）；
- 本文件：`coord/P0-NORMALIZATION-FIX.md`；
- 未编辑 `RootNormalizedContainmentActual` / `RootHullContainmentInequalityActual` / `Ind3OutputHullQPilotActual` / `S800` / `QVFamRootFactorCorrectionActual`；
- 原文只读：`tmp/iut1.txt`、`tmp/iut2.txt`、`tmp/iut3.txt`；行号如 §1。