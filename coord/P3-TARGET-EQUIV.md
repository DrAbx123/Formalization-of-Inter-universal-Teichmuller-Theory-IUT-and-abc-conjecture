# P3-TARGET-EQUIV — `M ≥ 0` ⟺ `L6ReducedInequality` 等价链（task-107）

日期：2026-11-13（mainline）  
状态：**CONDITIONAL REDUCTION**；纯代数部分已证，对象识别缺口逐条标出；不含 sorry/axiom。

## 0. 结论先行

1. **已证（本任务 Lean）**：`M = V+gap-(sF-1)A` 与 `M = A-R` 的代数恒等；在**字典假设** `M = c·(T(l)·D − e·log p)`（c>0）下，`M ≥ 0 ⟺ e·log p ≤ T(l)·D`，并特化到 `L6ReducedInequality C l D_exact`。
2. **仍未证（关键缺口 GAP-P3-DICT）**：把 paper hull/gap/shift 量 `V,gap,sF,A,R` 与 abc 显式量 `e,log p,T(l),D_exact` 联系起来的**对象字典**。仓库现有节点只有单向/条件片段（见 §3），没有整体等价。
3. **单向 green**：`DExactLowerTarget`（L7）⇒ `L6ReducedInequality`（L6）由 `l6Reduced_of_dExactLower` 给出（依赖 Mestre–Oesterlé、Θ-data legality、`0≤log p`）；**反向不成立/未知**。
4. **诚实边界**：不得把 `L6ReducedInequality`/`SSIneqExplicit` 当作目标 `M≥0` 的等价物；等价性依赖显式字典输入。

## 1. 产物

| 文件 | 内容 |
|---|---|
| `tmp/sheaf/xif/paper/Mzk1TargetReductionActual.lean` | `MExpr`、`ExplicitInequality`、`TargetReductionBridge`（含 `hR`/`hbridge` 显式输入）、`M_eq_A_sub_R`、`targetM_nonneg_iff_explicit`、`targetM_nonneg_iff_L6`、`L6_of_DExactLower`、rows（7 行） |
| 本文件 | 链审计、gap 清单、下一步最小包 |

## 2. 已证节点（纯代数）

- `MExpr V gap sF A := TargetM V gap sF A`（复用 `Mzk1StepVReductionActual.targetM_eq_A_sub_R`）；
- `targetM_eq_A_sub_R : R = -(V+gap-sF*A) → M = A-R`（复用，green）；
- `TargetReductionBridge.targetM_nonneg_iff_explicit`：
  `0 ≤ M ↔ e·log p ≤ T(l)·D`，证明 = `rw [hbridge]` + `mul_nonneg_iff_of_pos_left hc` + linarith（**条件于 hbridge**）；
- `TargetReductionBridge.targetM_nonneg_iff_L6`：
  实例化 `e=C.e, logp=log C.p, Tval=T l, D=D_exact` 后 ⇔ `L6ReducedInequality C l D_exact`（**条件于 hbridge**）；
- `L6_of_DExactLower`：green 单向 consumer（L7⇒L6）。

## 3. 链与缺口（file:line 依据 `coord/P3-EXACT-REDUCTION.md`）

| 段 | 节点（file:line） | 状态 |
|---|---|---|
| signed 等价 | `Mzk1StepVReductionActual.lean:41` `signed_ineq_iff_M_nonneg` | **GREEN**（纯代数） |
| M=A−R | `Mzk1StepVReductionActual.lean:47` | **GREEN** |
| q/Theta 目标定义 | `S2717Cor312FullTargetActual.lean:69-76,81-100` | GREEN（定义，无证明） |
| C3 体积恒等 | `S2807ThetaHullVolumeIdentityActual.lean:39-58` | GREEN（等价恒等） |
| StepV per-label 上界 | `S3014StepVProcessionAverageActual.lean:18-32,35-45` | GREEN（条件）+ GAP(volume 家族) |
| StepV 分解/单元 | `S3029StepVAlignmentActual.lean:25-60`; `S3050StepVQExpansionActual.lean:17-60` | GREEN（代数）+ 平凡识别 |
| q-pilot 识别 | `S3016StepVQPilotIdentificationActual.lean:29-43`; `S3019...:30-57` | GAP（bridge） |
| abc L6/L7 | `Mzk1ThetaDataLegalityActual.lean:88`; `Mzk1DExactLowerActual.lean:68,73,83` | GREEN（单向 L7⇒L6） |
| paper StepV box | `Mzk1PaperStepVBoxActual.lean:25-65` | GREEN（box 代数）+ GAP(Section-1 dictionary) |
| StepV/object dictionary | `Mzk1StepVIdentificationActual.lean:19-36` | CONDITIONAL |
| deficit | `Mzk1PaperNormThetaActual.lean:34-90`; `Mzk1PaperNormDeficitActual.lean:33-104` | GREEN（代数）+ GAP(diff/arch/torsion 字典) |

**GAP-P3-DICT（本任务核心缺口）**：`M = c·(T(l)·D_exact − e·log p)` 的字典。当前树中不存在把
`(V,gap,sF,A,R)`（S2717/S2807 的 hull/volume 量）与 `(e,log p,T(l),D_exact)`（prime-conductor 量）
逐项对应的已构造对象或已证等式。P3 审计同样记录：StepV 链只给 **Theta 侧上界**（`S3014_processionAverage_le`），
不能推出 `−A ≤ −R` 所需的下界/识别；`S3050QUnitIdentification` 对任意 `Q≠0` 平凡真，不能作为识别证据。

## 4. 不能由本任务跨越的边界

- 不构造 `StepV` 的 paper 系数来源；不把平凡比例识别当对象识别；
- 不把 `SSIneqExplicit`/`L6` 反向当作 `M≥0` 的证据（反向方向未证）；
- `hbridge` 是显式输入字段；若后续有对象字典证明，可把 `TargetReductionBridge` 的该字段替换为定理并去掉假设。

## 5. 下一步最小包（建议）

1. **P3-DICT-1**：从 `S2717QPilotLogVolume`/`S2717UpperGap` 与 `S2807` 恒等建立 `A,R,V,gap` 到 `D_exact,e,log p` 的第一段（候选：`Mzk1PaperStepVBoxActual` 的 box 差 + `Mzk1StepVIdentificationActual.StepVDictionary`）；
2. **P3-DICT-2**：把 `S3019MissingBridge`（nativeBadLocalWeight×baseQLogMagnitude）与 `qPilotLineBundleExtended` 的素因子指数对齐（P3-EXACTREDUCTION §4.2 的 1–4 项）；
3. 完成 1–2 后，`targetM_nonneg_iff_L6` 的条件 `hbridge` 可由定理替换，届时本文件从“条件等价”升级为“无条件等价”。


## 6. DICT-A 第一段（GAP-P3-DICT，2026-11-13 后续）

新文件（待 watchdog 名单）：`tmp/sheaf/xif/paper/Mzk1P3DictionaryActual.lean`

已实现（全部复用 green 输入，纯代数）：
- `boxSlack l D Q S T := paperRHS - paperLHS`（`Mzk1PaperStepVBoxActual`）；
- `boxSlack_eq`：slack = `(1/l)D + (1/l)S + ((2l-10)/3)T`（Q 抵消）；
- `paperStepV_iff_slack_nonneg`：box 不等式 ⟺ slack ≥ 0；
- `T_pos_of_five_le`：l≥5 ⇒ T(l)>0；
- `l6_iff_scaled`：**T(l) 分母字典** `e logp ≤ T(l)D ⟺ e logp·((l+4)(l-3)) ≤ 6l(l+5)D`（l>3，乘正分母）；
- `targetM_nonneg_iff_paperBox`：条件于 **DICT-B**（`M = c1·boxSlack`，c1>0）时目标 ⟺ paper box 不等式；
- `targetM_nonneg_iff_L6_of_dicts`：条件于 **DICT-B + DICT-C** 时目标 ⟺ L6。

精化后的缺口（比 task-107 单一 hbridge 更细）：
- **DICT-B**：paper 对象 `(D,Q,S,T)` 与算术量（log disc / q 系数 / s^Q / T(l)D_exact）的识别 —— 未构造；
- **DICT-C**：paper box 是**上界**方向，L6 是**下界**方向；树内只有单向/条件，反向 UNKNOWN。

结论：目标 ↔ L6 的等价链现在只剩 DICT-B、DICT-C 两个命名缺口；DICT-A 本身 green。
