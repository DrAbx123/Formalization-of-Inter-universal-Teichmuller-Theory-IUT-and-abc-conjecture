# P3-EXACT-REDUCTION — Step V 链盘点与目标显式化（task-89）

日期：2026-11-13；qpilot。**Status: READ-ONLY chain audit + source-level interfaces**；不自行编译；watchdog 状态见 §6。

## 0. 结论先行

1. **目标代数形式**：`M = V+gap-(sF-1)A`；`M>=0` 等价于 signed 形式 `-A <= -R`（`R=-(V+gap-sF A)`）。这一等价是纯实数代数，green。
2. **仓库已有链**：S2717/S2807 把目标写成 q/Theta 的 signed log-volume 比较；S3014/S3029/S3050 给出 Theta 侧 per-label StepV 上界；S3016/S3019 给出 StepV q-pilot 与 global q-pilot 的识别目标；Mzk1DExactLower 给出 abc 侧显式不等式 `e log p <= T(l) D_exact`。
3. **但没有已证的“目标 <=> 显式不等式”整体等价**：目前是若干**单向/条件**节点；其中最大的缺口是 StepV q-pilot 的 paper 系数识别（S3050QUnitIdentification 只平凡真）、S3019MissingBridge、S3014ProcessionData 和 DExactLowerTarget。
4. **S3050QUnit 的判定**：paper 应取 `c_root=order/(2l)`；`S3050Unit` 正是 `-c_root log p`（StepV 的 `j²` 乘以它）。`S3050QUnitIdentification Q` 对任意 Q≠0 **平凡为真**（∃c, unit=cQ），不是 paper 识别；有意义的是 Q=S3050Unit（c=1）或 Q=S2921Q（c 数据依赖，需新来源）。

## 1. 目标与 signed 形式

HANDOFF §2.1（`D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md:84-100`）：
```
l_q=-A, l_Theta=-R=V+gap-sF*A;  M=l_Theta-l_q=A-R=V+gap-(sF-1)A; target M>=0.
```
等价 signed 形式：`-A <= -R`（纯 linarith；本任务 Lean 文件 `signed_ineq_iff_M_nonneg`）。
注意：paper 原文 Cor 3.12 的目标是 `-|log Θ| >= -|log q|`（`tmp/iut3.txt:10178-10180`），即 `-R >= -A`；与上述一致。

## 2. 节点表（按内容搜索核对，不按文件名）

| 节点 | 文件:行 | 内容 | 状态 |
|---|---|---|---|
| 目标 q/Theta 形式 | `S2717Cor312FullTargetActual.lean:69-76,81-100,103-...` | `S2717QPilotLogVolume`、`S2717UpperGap`、`PaperCor312Full` 定义；无目标证明 | **GREEN（定义）** |
| C3 tensor 体积恒等 | `S2807ThetaHullVolumeIdentityActual.lean:39-58,63-...` | `S2807_thetaHullVolume_eq_haarRegion` / `..._upperGap_iff_neg_tensorLogVolume` | **GREEN（等价恒等）** |
| StepV per-label 上界 | `S3014StepVProcessionAverageActual.lean:18-32,35-45,63-77` | `S3014PerLabelBound`、`S3014_processionAverage_le`、`S3014ProcessionData` | **GREEN（条件）+ GAP(volume 家族)** |
| StepV 分解 | `S3029StepVAlignmentActual.lean:25-42,45-60` | `StepVTerm+DifferentTerm+logp+ExceptionalTerm`；`S3029AlignmentData` | **GREEN（代数）+ 条件字段** |
| StepV 单元 | `S3050StepVQExpansionActual.lean:17-24,28-36,43-53,56-60` | `S3050Unit`; `S3029StepVTerm=label²*Unit`; `S3050QUnitIdentification` | **GREEN（代数）+ 平凡/待来源** |
| StepV q-pilot 识别 | `S3016StepVQPilotIdentificationActual.lean:29-43`；`S3019StepVQPilotIdentificationProofActual.lean:30-57` | `S3016IdentificationTarget`；`S3019MissingBridge` | **GREEN（目标等价）+ GAP(bridge)** |
| abc 显式 L6 | `Mzk1ThetaDataLegalityActual.lean:87-89`；`Mzk1DExactLowerActual.lean:67-78,85-...` | `L6ReducedInequality C l D := e logp <= T(l) D`；`DExactLowerTarget`；`l6Reduced_of_dExactLower` | **GREEN（算术/条件）+ GAP(L7)** |
| paper StepV box | `Mzk1PaperStepVBoxActual.lean:34-52,55-65` | `paperLHS<=paperRHS`；差 `(1/l)D+(1/l)S+((2l-10)/3)T>=0` | **GREEN（box 代数）+ GAP(Section-1 dictionary)** |
| StepV/object dictionary | `Mzk1StepVIdentificationActual.lean:19-36` | `StepVDictionary` 条件装配；object identification GAP | **CONDITIONAL** |
| paper 归一化 deficit | `Mzk1PaperNormThetaActual.lean:15-33`；`Mzk1PaperNormDeficitActual.lean:20-80` | `thetaSumPaper=c_lana*A`；deficit 展开/反例 | **GREEN（代数）+ GAP(diff/arch/torsion 字典)** |

## 3. 显式链（当前真实方向）

### 3.1 signed 目标（已证等价）
```
TargetM := 0 <= V+gap-(sF-1)*A
TargetSigned := -A <= -R,  R=-(V+gap-sF*A)
theorem signed_ineq_iff_M_nonneg : TargetSigned <=> TargetM
```
这是纯代数等价；不构造任何对象。

### 3.2 Step V 侧（只有上界，不是目标下界）
```
S3014PerLabelBound(l,label) =
  (-stepVLambda(l,label,J,l) + (Σ_i ord(Different_i)+1)) logp
  + Σ_{i∈exceptional}(3+log(ramIdx_i))
S3029StepVTerm = label² * S3050Unit
S3050Unit = (ord J)/(2l) logp = -(qOrder/(2l)) logp
```
`S3014_processionAverage_le` 只能给 `volume <= average bound`；因此 StepV 链给的是 **Theta 侧上界**，不能直接推出 `-A <= -R`（需要下界/识别）。

### 3.3 abc 显式 L6/L7
```
T(l) = 6*l*(l+5)/((l+4)*(l-3))     （Mzk1PrimeConductorRouteActual.lean:58）
L6ReducedInequality C l D_exact := e*log p <= T(l)*D_exact
DExactLowerTarget C l D_exact := (1-1/l)*log p <= D_exact
```
`l6Reduced_of_dExactLower`（Mzk1DExactLowerActual:67-78）在 `MestreOesterleBound + ThetaDataLegality + 0<=logp + L7` 下给出 L6。**方向是 L7⇒L6**；没有证明 `M>=0 ⇒ L7` 或反方向。
因此“目标 <=> 显式不等式”**尚未闭合**；目前只有 `signed目标` 的纯代数等价，以及 `L7 ⇒ L6` 的单向条件链。

### 3.4 显式链图
```
TargetM  <=>  -A <= -R                       [algebra]
                  ?  (q/Theta identification; S2717/S2807)
Theta-Hull  <=  StepV per-label upper          [S3014/S3029]
                  ?  S3050Unit/Q paper bridge
abc L7: (1-1/l)logp <= D_exact
   =[green, l6Reduced_of_dExactLower]=> L6: e logp <= T(l)D_exact
   =[green, ssIneqExplicit_of_dExactLower]=> SSIneqExplicit
```
`?` 处是 MISSING/条件；不能把 L6/SIneq 当作 `TargetM` 的等价物。

## 4. S3050QUnitIdentification 判定

定义：`S3050QUnitIdentification Q := exists c, S3050Unit = c * Q`（S3050:56-60）。

| Q | 判定 | 说明 |
|---|---|---|
| `Q=S3050Unit`（paperRootQ） | **真，c=1** | `S3050Unit=-c_root logp`，是 paper c_root 单元；这正是 paper Q 的正确选择 |
| `Q≠0` 任意实数 | **真（平凡）** | `c=S3050Unit/Q`；命题没有 paper 常数内容 |
| `Q=0` | 假（除非 unit=0） | 不可能是 paper q 系数 |
| `Q=S2921Q`（qPilotLineBundleLogVolume，c_norm 侧） | 比例存在但 c 数据依赖 | 需要新来源等式；不是 paper c_root 恒等 |

**结论**：Q 应取 `c_root` 的 `S3050Unit`（或等价的 `paperRootQ`）；`S3050QUnitIdentification` 本身**平凡真**，不能作为“paper q 识别已证”的证据。有意义的是 `S3079PaperConstantTarget`（unit/Q 三组独立常数）或 Q 与 S2921Q 的来源等式；当前 **未证/需新来源**。


## 4.2 task-91：S3050Unit 与 S2921Q 的精确换算判定

新文件：tmp/sheaf/xif/paper/Mzk1S3050ConstantSourceActual.lean（watchdog **DONE EXIT=0**，20:34:26Z，96s；olean 106224B）。

可证的部分（局部，已机器验证）：
  localSignedQLog p jValue := localNormOrder p jValue * log p   (= ord J * log p)
  (2*l) * S3050Unit p jValue l = localSignedQLog p jValue
  S3050Unit = localSignedQLog / (2l)

即 S3050Unit 是 local c_root（带符号 q log / 2l）；与 c_norm 的局部 q log 相差因子 2l。

不可证/不能直接等同的部分（全局）：
- S2921Q（S2921HeightBridgeActual.lean:28-31）是
  S2736QPilotLineBundleLogVolume (qPilotLineBundleExtended J)
  = log absNorm (qPilotIdeal * J) 的全局 line-bundle log；
- qPilotIdeal 是 Gaussian 的四个坏素理想乘积，qPilotIdeal_absNorm = 5*5*2161*2161
  （S2735QPilotLineBundleActual.lean 的 qPilotIdeal_absNorm）；
- S3050Unit 是单个 tensor 因子上的 ord J/(2l) log p；
因此一般没有 S2921Q = 2l * S3050Unit 的逐字等式；正确的全局形只能是
  S2921Q = -(2l) * Σ_b weight_b * S3050Unit_b + (support/J 项)
需要先把 qPilotLineBundleExtended 的素因子指数、tensor 因子、每 b 权重对齐。

精确缺失的来源对象（open named input）：
1. qPilotIdealExtended 的素因子指数到各 tensor 因子 (b, i) 的映射；
2. 每 b 的权重 weight_b 与 qPilot line bundle 的局部 q log 的等式；
3. S2736QPilotLineBundleLogVolume = -Σ_b weight_b * localSignedQLog_b（含 J/arch 0 项）；
4. 再与 S3019 的 nativeBadLocalWeight * baseQLogMagnitude 对齐（S3019MissingBridge）。
这些对象在树内均未构造；不能把 S3050QUnitIdentification 的平凡比例当成上述来源恒等。

## 5. 剩余 named Prop/最小下一包

1. `S3014ProcessionData`：per-label 的 `volume` 家族（actual theta hull per label）——**缺失**；
2. `S3016IdentificationTarget` / `S3019MissingBridge`：StepV q-pilot = weighted global q-pilot——**缺失**；
3. `S3050QUnitIdentification`：平凡真，需换成 paper constant/来源恒等；`S3079PaperConstantTarget` 未证——**需新来源**；
4. `DExactLowerTarget`（Mzk1DExactLower:67-70）：L7 几何下界——**PENDING**；
5. `Mzk1PaperStepVBox` Section-1 dictionary；`Mzk1StepVIdentification.StepVDictionary` object identification——**GAP**；
6. `Mzk1PaperNormDeficit`：`diff/arch/torsion` 与 paper per-place data 的字典——**GAP**。



### 5.2 task-95：S3014ProcessionData 的 actual 候选

新文件：tmp/sheaf/xif/paper/Mzk1StepVProcessionActual.lean（watchdog **DONE EXIT=0**，20:39:49Z，65s；olean 112,056B）。

已构造（机器验证 green）：
  stepVVolume label := S3029StepVTerm places tuple istar jValue l label
  stepVExtraTerm := S3029DifferentTerm + log p + S3029ExceptionalTerm
  stepVProcessionData (h : 0 <= stepVExtraTerm) : S3014ProcessionData ...
  stepVProcessionAverage_bound : (1/n) Σ volume <= S3014ProcessionAverageBound

其中 stepVVolume 来自 actual S3029StepVTerm，而 S3029StepVTerm = label²·S3050Unit（S3050）。
**StepVExtraNonneg 已关闭（green）**：`Mzk1StepVExtraNonnegActual.lean` watchdog **DONE EXIT=0**（21:16:02Z，67s；olean 132,520B）证明 `localNormOrder different >=0`、`S3029DifferentTerm >=0`、`S3029ExceptionalTerm >=0`，故 `StepVExtraNonneg` 无条件成立；`stepVProcessionDataActual` / `stepVProcessionAverage_bound_actual` 为无条件实例。

仍精确缺：
1. ~~StepVExtraNonneg~~（已证）；
2. S3029StepVTerm 与 arithmeticTupleNormalizedLogVolume 的实际 per-label StepV image region 的等式；S3014 的 volume 要真正成为 normalized log-volume，而不是 bound 标量。
3. 异常集 exceptional 的实际选择（e_i > p−2）及 S3029ExceptionalTerm 的界。


### 5.3 task-100：S3029AlignmentData 实际化

新文件：tmp/sheaf/xif/paper/Mzk1StepVAlignmentActual.lean（watchdog **DONE EXIT=0**，20:50:01Z，78s；olean 103,264B）。

实际对齐（机器验证 green）：
  D := S3029DifferentTerm
  Q := S3050Unit p jValue l        （paper c_root unit）
  S := S3029ExceptionalTerm
  T := 0
  cD=1, cQ=cS=cT=c0=0; sS=1, sT=0
  qCoeff label = label^2; labelRest = 0

于是：
  S3029DifferentTerm = cD*D + cQ*Q + cS*S + cT*T + c0
  S3029ExceptionalTerm = sS*S + sT*T
  S3029StepVTerm label = label^2*Q = qCoeff label*Q + 0（S3050）
并调用 S3029_perLabel_affine 得到 actual per-label affine。

与 StepVExtraNonneg 的关系：
- alignment 本身仍不推出；但 **actual 数据现已证明** `0 <= S3029DifferentTerm + log p + S3029ExceptionalTerm`（`Mzk1StepVExtraNonnegActual.lean`，green），故 `StepVExtraNonneg` 可消；
- different/exceptional 非负来源 file:line：`localNormOrder_arithmeticTupleLocalDifferent_nonneg`、`S3029DifferentTerm_nonneg`、`S3029ExceptionalTerm_nonneg`（同文件）；
- 另缺 StepV scalar 与 arithmeticTupleNormalizedLogVolume 的实际 per-label image 等式（同 task-95 §5.2）。



### 5.5 task-116：per-label StepV actual region + exceptional 集

新文件：tmp/sheaf/xif/paper/Mzk1StepVVolumeActual.lean（watchdog **DONE EXIT=0**，21:30:45Z，61s；olean 106,320B）。

已构造（机器验证 green）：
  stepVRegion label := thetaTensorScaledRegion (c i = if i=istar then stepVLambda p label jValue l else 0)
  stepVRegion_volume_eq_of_scalingData：
    ArithmeticTuplePureFractionalScalingData c
    => arithmeticTupleNormalizedLogVolume (stepVRegion label) = S3029StepVTerm label
  ramifiedExceptional := {i | p-2 < logShellRamificationExponent_i}
  S3029ExceptionalTerm_ramified：exceptional 取 ramifiedExceptional 时逐字对齐。

剩余唯一源对象（volume identity 的最后一块）：
  ArithmeticTuplePureFractionalScalingData for the one-factor coefficient stepVLambda：
  需要 qroot^{label²} 的 p-power/unit 数据；
  以及非 istar 因子系数 0 的 actual unit 数据（localGenerator 范数 1、commonExponent/order_eq 等）。
  该 datum 尚未构造；不能把它作为假设换 green。

### 5.4 task-111：actual D_exact 与 L7→L6 接口

新文件：tmp/sheaf/xif/paper/Mzk1DExactActual.lean（watchdog **DONE EXIT=0**，21:12:30Z，57s；olean 26,176B）。

实际 D_exact（机器验证 green）：
  nativeDExact T arch := nativeGlobalQPilotNormalizedLogMagnitude T + arch
                      = Σ_b nativeBadLocalWeight T b * baseQLogMagnitude T b + arch

这是 native 实际加权 base-q log-magnitude + 显式 arch 参数。已证：
  nativeDExact_eq_weighted_sum
  nativeDExact_l6_of_l7：
    DExactLowerTarget C l (nativeDExact T arch)
    + MestreOesterleBound + ThetaDataLegality + 0<=log C.p
    => L6ReducedInequality C l (nativeDExact T arch)

**L7 本身未证**：
  DExactLowerTarget C l D := (1-1/l)*log(C.p) <= D
是显式条件 NativeDExactL7Gap，不是实际数据的推论。

**精确缺口**：
1. arch 项未构造（tree 内无实际 arch 读数）；当前 arch 是参数；
2. native 权重 nativeBadLocalWeight = 1/[K_w:F_v] <= 1，与 Mzk1DExactFromHullActual 的
   L7_term 假设 hw : 1 <= w 不相容；不能直接套其 L7 证明；
3. 需要 bad place 的 order/residue norm 下界（或 q 的显式下界）才能给出
   (1-1/l)logp <= Σ weight*baseQLogMagnitude；
4. DExactLowerTarget 与 C.p 的 prime-conductor 输入没有与 T 的 bad family 对齐。

### 5.1 最小下一包依赖顺序（S3014 actual volume → L6ReducedInequality）

1. S3014ProcessionData：为每个 label 选实际 theta-hull volume 并证明
   volume label <= S3014PerLabelBound；
2. S3029AlignmentData 实际化：给出 qCoeff label = label²、labelRest，并把
   StepVTerm 对齐到 S3050Unit；
3. S3050 局部源：localSignedQLog 与 S3050Unit 的 2l 换算（本任务新文件可证）；
4. S3050→S2921 全局源：qPilot ideal 指数/权重/线丛 log 的等式（本任务 §4.2 的 open input）；
5. S3019MissingBridge：StepV q-pilot = weighted global q-pilot；
6. S2807/S2717：把 signed q/Theta 比较落到 C3 tensor 体积；
7. Mzk1DExactLower.DExactLowerTarget：L7 几何下界；再由 green
   l6Reduced_of_dExactLower 得 L6ReducedInequality；
8. 最后才是 SSIneqExplicit 与 M>=0 的完整目标组合。
其中 1、2、4、5、7 是当前真正缺的定理；3 是纯代数，6/8 是桥接/目标组合。

**最小下一包**：先完成 1（S3014 actual volume family）与 3（2l 局部换算），并行做 4（S3050→S2921 全局源）；2/5/7 随后。

## 6. 新 Lean 接口

文件：`tmp/sheaf/xif/paper/Mzk1StepVReductionActual.lean`（source-level；watchdog 状态待查；不在当前 Lead 名单时请 Lead 加入）。
- `StepVReduction.signed_ineq_iff_M_nonneg`：`-A <= -R <=> 0 <= A-R`；
- `StepVReduction.stepVUnit_eq_rootCoefficient`：`S3050Unit = (ord J/(2l))*log p`；
- 只编码 green 的代数事实：signed 等价、`TargetM` 与 `R` 关系、`S3050Unit` 的 c_root 公式；S3050QUnit 的真值判定在文档 §4（不写成不实的 Lean 定理）。
- 不写目标假设、不造 PUnit/True/toy。

## 7. 文件/证据

- 链盘点的源码/行号见 §2；原文 `tmp/iut3.txt:10152-10180`（Cor 3.12）与 `tmp/iut1.txt:3703-3726`（q_v=q^{1/2l}）；
- task-85 新接口 `Mzk1PaperTargetNormalizationActual.lean`；task-89 新接口 `Mzk1StepVReductionActual.lean`；
- 本文件 `coord/P3-EXACT-REDUCTION.md`；未编辑既有 green 文件；未自行编译。

## 7. task-118：素导子类 hD → 实际 D_exact 归约（2026-11-13 后续）

新文件（待 watchdog 名单）：`tmp/sheaf/xif/paper/Mzk1PrimeConductorUnconditionalActual.lean`

把 `paperGap_of_primeConductor` 的抽象 `hD : (1-1/l)log p ≤ D_exact` 换成对**实际**
`nativeDExact T arch = ∑_b nativeBadLocalWeight T b · baseQLogMagnitude T b + arch`
的定理，条件只剩两个内容级输入：

- **GAP-PC-WEIGHT**：`∀ b, nativeBadLocalWeight T b = 1`（局部完备次数 1；素导子 + l∤e_p 的
  tame 情形预期，但未构造`localCompletionDegree = 1` 的证明）；`nativeBadLocalWeight_eq_one_of_localCompletionDegree_one`
  已把 `degree=1` 化为 `weight=1`（rfl 级）。
- **GAP-PC-LOGSUM**：`Real.log (C.p) ≤ ∑_b baseQLogMagnitude T b`（实际 base q log 幅度之和
  与 `log p` 的识别，未构造）。
- `arch ≥ 0`（显式假设）。

产出定理：
- `nativeDExact_L7_of_conditions`：上述条件 ⇒ `DExactLowerTarget C l (nativeDExact T arch)`；
- `primeConductor_ssIneqExplicit_of_actual`：`SSIneqExplicit (sL l) (e log p) l ((l+5)/4 · nativeDExact)`
  **只依赖显式外部参数 `MestreOesterleBound` + 两个内容缺口**；外部定理未当已证、无 axiom/sorry。

结论：hD 由抽象假设降为两个可寻址的实际内容缺口；若 GAP-PC-WEIGHT/LOGSUM 后续证出，
该文件即给出素导子类的（条件于外部 Mestre–Oesterlé 的）真实 SSIneqExplicit 定理类。
