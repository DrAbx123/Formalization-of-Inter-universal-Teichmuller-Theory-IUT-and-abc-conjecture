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

  task-122 进展：Mzk1StepVScalingDataActual.lean（watchdog DONE EXIT=0，21:35:24Z，60s；olean 209,240B）已用生产构造 arithmeticTuplePureFractionalScalingData_ofGenerator 把 data 归约为 generators：
  stepVScalingDataOfGenerator（给定 g_i, ||g_i||=p^{-c_i}）
  stepVRegion_volume_eq_ofGenerator（volume identity = StepVTerm）
  剩余唯一源对象 StepVQRootSourceGap：qroot^{label²} at istar + 零因子 unit generators + norm 等式。


### 5.6 StepVQRootSourceGap 的精确 source map 缺口

StepVQRootSourceGap 要求存在
  generator : (i : ι) → CommonPrimeCompletion (places i (tuple i))
  generator_norm : ||generator i|| = p^(-stepVScalingCoefficient i)
其中 c_istar = stepVLambda，其他 c_i = 0。

现有 qroot 对象都在别的层：
- qThetaRoot T b : rootNormedExtension T b（Mzk1ThetaPilotObjectActual.lean:52-54），
  即 IntermediateField.adjoin (sourceRootField T b) {rootNormedElement}（PaperRootCompletionTensorActual.lean:54-60）；
- qrootOf D v : completionAt D.Kt v（Iut/Concrete/ThetaLocalConstruct/Data.lean:281-291），
  但需要 D : InitialThetaData，不是 S3029 的通用 K/V/places/tuple；
- S3029 的 jValue : CommonPrimeCompletion (places istar (tuple istar)) 只是通用 completion，
  没有 qroot/root extension 字段。

因此缺三个映射/等式：
1. rootMap : rootNormedExtension T b → CommonPrimeCompletion (places istar (tuple istar))（把 qThetaRoot 搬到 S3029 completion；需与 qVFam place 对齐）；
2. rootMap 的 norm 保持：||rootMap (qThetaRoot^label²)|| = p^(-stepVLambda)；
3. 非 istar 因子（若 ι 非 Unit）的 norm-one unit generators（||g_i||=1）；
4. 以及 S3029 的 istar/jValue 与 qVFamTensorPlaces/qVFamTensorTuple 的来源对齐。
这些都没有在树内构造；StepVQRootSource 是显式结构，但 StepVQRootSourceGap 仍 open。

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


## 8. GAP-PC-WEIGHT 归约（2026-11-13 后续）

新文件（待 watchdog 名单）：`tmp/sheaf/xif/paper/Mzk1PrimeConductorWeightOneActual.lean`

利用已有 green 对象 `FinitePlaceCompletionDegree`：
- `localCompletionDegree = finrank (K_w / (Fmod)_v)`（`ProcessionNormalizationWeightsActual:49`）；
- `finrank_adicCompletion_eq_relativeCompletionDegree`（:325，条件 `hfinite` + `hagree`）；
- `relativeCompletionDegree_eq_one_iff`（:284，`e=f=1 ↔ degree=1`）。

新定理：
- `nativeBadLocalWeight_eq_one_of_tame_data`：**GAP-PC-FINITE**（`Module.Finite` 完成整数环）+
  **GAP-PC-AGREE**（`localDataAgreesWithPlaceData`）+ **GAP-PC-UNRAM/RESIDUE**（relative `e=1`、`f=1`）
  ⇒ `nativeBadLocalWeight T b = 1`；
- `nativeBadLocalWeight_eq_one_of_tame`：包装 `PrimeConductorTameLocalData`（e=f=1 的命名 Prop）；
- `PrimeConductorTameLocalData`：素导子 tame 情形（l∤e_p ⇒ 坏位处不分歧、剩余次数 1）的待证内容。

**缺口定位（语义 > 编译）**：
1. **GAP-PC-FINITE**：`Module.Finite O_v O_w` 对 adic completion 整数环；Mathlib 4.32.2 无
   `IsIntegralClosure` 的 completion 版（见 `FinitePlaceCompletionDegree` 注释 :310 附近）。
2. **GAP-PC-AGREE**：completed local data 与 number-ring place data 的 `ramificationIdx'/inertiaDeg'`
   一致（Mathlib 无比较余域/指数的定理）。
3. **GAP-PC-UNRAM/RESIDUE**：素导子 + l∤e_p tame ⇒ relative e=f=1（需 E[l] 的局部域分歧计算）。

若 1–3 证出，则 `GAP-PC-WEIGHT` 关闭，task-118 的 `nativeDExact_L7_of_conditions` 只剩 GAP-PC-LOGSUM。


## 9. GAP-PC-LOGSUM 归约（2026-11-13 后续）

新文件（待 watchdog 名单）：`tmp/sheaf/xif/paper/Mzk1PrimeConductorLogSumActual.lean`

实际等式（green）：
- `baseQLogMagnitude_eq_order_mul_log`（BaseQLogVolumeActual:74）：
  `|log q_b| = order_b · log (residueNormBase (nativeBaseSectionPlace T b))`；
- `baseQ_order_pos`（:106）：`0 < order_b`。

新定理（GAP-PC-LOGSUM 归约）：
- `sum_baseQLogMagnitude_eq`：GAP-PC-RESNORM（每个坏位 residue norm = C.p）⇒
  `∑ |log q_b| = (∑ order_b)·log C.p`；
- `log_le_sum_baseQLogMagnitude`：再加 `[Nonempty Bad]`、`log C.p ≥ 0` ⇒
  `log C.p ≤ ∑ |log q_b|`（用 `∑ order_b ≥ card ≥ 1`）；
- `nativeDExact_L7_of_residueNorm` / `primeConductor_ssIneqExplicit_of_actual_residueNorm`：
  把 task-118 的 GAP-PC-LOGSUM 换成 **GAP-PC-RESNORM**。

**结论**：GAP-PC-LOGSUM 不再是“整条未证”，而归约为 GAP-PC-RESNORM
（素导子坏位 residue norm = p，即每个坏位剩余次数 1 的算术识别；预期由 tame/素导子给出，未构造）。
若 GAP-PC-RESNORM 证出（与 GAP-PC-WEIGHT 三个子缺口一起），task-118 的 SSIneqExplicit 将成为
素导子类上只依赖外部 Mestre–Oesterlé 参数的真实定理。


## 10. GAP-PC-RESNORM 归约（2026-11-13 后续）

新文件（待 watchdog 名单）：`tmp/sheaf/xif/paper/Mzk1PrimeConductorResNormActual.lean`

利用 green：
- `residueNormBase_eq_lower_pow`（ArithmeticQPilotBaseChange:126）：
  `residueNormBase w = residueNormBase (comap w) ^ localResidueDegree w`；
- `nativeBaseSectionPlace_comap`（BaseQFamilyActual:71）：`comap (nativeBaseSectionPlace T b) = b.1`。

新定理：
- `residueNormBase_nativeBaseSectionPlace_eq_pow`：`residueNormBase (nativeBaseSectionPlace T b)
  = residueNormBase (b.1) ^ localResidueDegree (nativeBaseSectionPlace T b)`；
- `residueNormBase_nativeBaseSectionPlace_eq_Cp`：GAP-PC-RESDEG（residue degree=1）+
  GAP-PC-BADCHAR（`residueNormBase b.1 = C.p`）⇒ `residueNormBase (nativeBaseSectionPlace T b) = C.p`；
- `primeConductorResidueNormData_of_data`：把 LOGSUM 文件的 `PrimeConductorResidueNormData` 由这两条数据给出；
- `log_le_sum_baseQLogMagnitude_of_data`：RESNORM 兑现后 LOGSUM 成立（再加 nonempty + log C.p≥0）。

**结论**：GAP-PC-RESNORM 归约为两条内容缺口：GAP-PC-RESDEG（坏位实际剩余次数 1，tame 情形）
与 GAP-PC-BADCHAR（坏 moduli place 的 residue norm 与素导子 p 的识别）。两者都是实际对象上的
算术识别，未构造；无新增假设换 green。


## 11. GAP-PC-BADCHAR 归约（2026-11-13 后续）

新文件（待 watchdog 名单）：`tmp/sheaf/xif/paper/Mzk1PrimeConductorBadCharActual.lean`

分解 `BADCHAR: residueNormBase (b.1) = C.p` 为三条命名内容输入：
- **GAP-PC-NORMFORMULA**：`residueNormBase place = residueCharacteristic place ^ residueInertiaDegree place`
  （可寻址：`FinitePlaceDegreeSumBound:39 under_eq_span_residueCharacteristic` +
  `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver`；尚未拼装）；
- **GAP-PC-BADCHAR-PRIME**：`residueCharacteristic (b.1) = C.p`（坏位残数特征 = 素导子，需
  T 的 bad place 与 conductor prime 的实际识别）；
- **GAP-PC-BADCHAR-DEG**：`residueInertiaDegree (b.1) = 1`（坏位剩余次数 1）。

定理：`badCharData_of_data`（三输入 ⇒ BADCHAR）、`resNormData_of_badChar`（再加 RESDEG ⇒
`PrimeConductorResidueNormData`）；rows=5。

**结论**：BADCHAR 归约为 NORMFORMULA / PRIME / DEG 三条；其中 NORMFORMULA 最可能先在本地
Mathlib 对象上拼装（absNorm/inertiaDeg 已有 lemma），PRIME 与 DEG 属素导子类实际构造缺口。


## 12. NORMFORMULA 关闭 + RESNORM→BADCHAR 当前链（2026-11-13 后续）

**GAP-PC-NORMFORMULA 已关闭**：`Mzk1P3NormFormulaProofActual.lean` watchdog **DONE 35s@22:58:24，olean=True**。
定理：`residueNormBase place = (residueCharacteristic place : ℝ) ^ residueInertiaDegree place`
（拼装 `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver` + `under_eq_span_residueCharacteristic`
+ `Ideal.inertiaDeg'_eq_inertiaDeg` + `Ideal.absNorm_span_singleton`）。

**RESNORM → BADCHAR 链（当前精确状态）**：
```
GAP-PC-RESNORM  (residueNormBase (nativeBaseSectionPlace T b) = C.p)
├── GAP-PC-RESDEG   localResidueDegree (nativeBaseSectionPlace T b) = 1
│      ⟺ residueNormBase (nativeBaseSectionPlace T b) = residueNormBase (b.1)   [GREEN: P3ResNormSlack/P3ResDeg]
└── GAP-PC-BADCHAR  residueNormBase (b.1) = C.p
       ├── GAP-PC-NORMFORMULA  residueNormBase = char ^ inertiaDegree        [GREEN: P3NormFormulaProof]
       ├── GAP-PC-BADCHAR-PRIME  residueCharacteristic (b.1) = C.p          [GAP: 需要 conductor 识别]
       └── GAP-PC-BADCHAR-DEG    residueInertiaDegree (b.1) = 1             [GAP: 剩余次数 1]
```
即：`RESNORM = RESDEG ∧ (NORMFORMULA ∧ PRIME ∧ DEG)`，其中 NORMFORMULA 已 green、
RESDEG 已化为可寻址等式（RESDEG ⟺ residue-norm 等式，green），只剩 **PRIME / DEG** 两条实际算术识别缺口。

**新文件（已 green）**：
- `Mzk1P3ResNormSlackActual`（RESDEG ⟺ 范数等式）
- `Mzk1P3ResDegActual`（坏位特化）
- `Mzk1P3NormFormulaActual` / `Mzk1P3NormFormulaProofActual`（NORMFORMULA 形式化+证明）
- `Mzk1P3BadCharPrimeActual`（PRIME 单方向：char=q ⇒ under=span{q}）
- `Mzk1P3FiniteCompletionActual`（FINITE 条件化：separable+integralClosure ⇒ Module.Finite）
- `Mzk1P3AgreeActual` / `Mzk1P3AgreeDegreeActual`（AGREE rfl 形式 + AGREE∧FINITE ⇒ local degree = relative degree）
- `Mzk1P3UnramResidueActual`（e=f=1 ⟺ relative degree 1；待 watchdog 终验）
- `Mzk1P3GapLedgerActual`（GAP 台账，14 行，已同步 NORMFORMULA green）


## 13. 第三批拆分（2026-11-13 后续）

新增文件（待 watchdog 名单）：
1. `Mzk1P3ArithmeticRelativeBridgeActual.lean` — **rfl 桥**：
   `ArithmeticQPilotBaseChange.localResidueDegree = FinitePlaceCompletionDegree.relativeResidueDegree`、
   `localRamificationIndex = relativeRamificationIndex`（同 number-ring 公式，仅命名空间不同）。
   含义：RESDEG/UNRAM-RESIDUE 的“local”与“relative”措辞是同一对象，AGREE 缺口的实际内容是
   completed-valuation-ring 数据 ↔ number-ring 数据的比较，而不是 local* 与 relative* 的名字差异。
2. `Mzk1P3BadCharPrimeEquivActual.lean` — **BADCHAR-PRIME 等价**：
   `b.1.maximalIdeal.asIdeal.under ℤ = span{C.p} ↔ residueCharacteristic (b.1) = C.p`（green）。
3. `Mzk1P3BadCharDegActual.lean` — **BADCHAR-DEG 等价**：
   `residueInertiaDegree (b.1) = 1 ↔ absNorm (b.1) = residueCharacteristic (b.1)`（来自 NORMFORMULA green）。
4. `Mzk1P3TameFromConductorActual.lean` — tame 假设/结论形状：
   `TameConductorHypotheses (l≥11, l∤e, e≠0)`、`tameConclusion (e=f=1)`、
   与 `UnramResidueData` 的 rfl 对应；**推导目标 `TameDerivationTarget` 标 GAP-PC-TAME**（不硬凑）。
5. `Mzk1P3AgreeResidueFieldActual.lean` — AGREE residue-field 碎片：
   `relativeResidueDegree = finrank (O_k/p_res) (O_K/P)`（green，条件实例）；
   completed-side 对应等式标 **GAP-PC-AGREE-FIELD**。

**更新后的 P3 GAP 树（第三批后）**：
- BADCHAR-PRIME ⟺ under-ideal 识别（green 等价）+ 实际 under 数据（GAP: conductor 识别）；
- BADCHAR-DEG ⟺ absNorm 等式（green 等价）+ 实际 absNorm 数据（GAP: residue degree）；
- RESDEG/UNRAM：local* = relative*（rfl 桥）+ 实际 e=f=1（GAP-PC-TAME/AGREE）；
- NORMFORMULA：**已关闭**（green）；
- DICT-B/C：由 qpilot lane 处理，本 lane 不碰。


### 13.1 AGREE 分量精确化（rfl 桥的作用范围）

`localDataAgreesWithPlaceData (k := k) place` 的定义（FinitePlaceCompletionDegree）为：
```
localRamificationIndex (completion)  = relativeRamificationIndex (number-ring)
∧ localInertiaDegree (completion)   = relativeResidueDegree (number-ring)
```
其中 completion 侧两项由 **adic completion 整数环的极大理想**定义
（:180 `IsLocalRing.maximalIdeal (... adicCompletionIntegers k)).ramificationIdx' ...`；
:187 的 inertiaDeg' 版本），number-ring 侧两项由 `comap` 的极大理想定义。

**rfl 桥消掉的是命名混淆，不是 AGREE 分量**：
- `ArithmeticQPilotBaseChange.localResidueDegree` / `localRamificationIndex`
  = `FinitePlaceCompletionDegree.relativeResidueDegree` / `relativeRamificationIndex`（**同 number-ring 公式**，rfl）；
- 因此 RESDEG/UNRAM-RESIDUE 的措辞统一到 **relative（number-ring）指数**语言；
- AGREE 的两个分量**仍是真缺口**：
  1. **GAP-PC-AGREE-RAM**：completion 侧 `ramificationIdx'` = relative `e`
     （Mathlib 无 adic completion 下 `ramificationIdx'` 不变性；只有不等式与 tower 条件）；
  2. **GAP-PC-AGREE-FIELD**：completion 侧 `inertiaDeg'` = relative `f`
     （Mathlib 无 `𝒪_v/𝔪_v ≃+* 𝓞 k/v` 的 residue-field 同构）。
- 另有独立 **GAP-PC-FINITE**（`IsIntegralClosure 𝒪_w 𝒪_v K_w`，即 `Module.Finite`）。

结论：AGREE 不可由 rfl 桥消掉；rfl 桥的价值是让 RESDEG/UNRAM 的 `localResidueDegree` 写成
`relativeResidueDegree`（completion 文件的 relative 语言），从而与 AGREE 的右侧一致。


## 14. AGREE-RAM/FIELD 的直接 FLT 来源（2026-11-13 后续）

**关键发现**：仓内已移植的 FLT 文件
`tmp/external/ported/flt/FLT/DedekindDomain/Completion/BaseChange.lean` 直接包含所需定理
（在 `namespace adicCompletion` / `section RamificationInertia`，`w : v.Extension B`）：

- **:685 `ramificationIdx_eq_ramificationIdx`**：
  `(w.1.completionIdeal L).ramificationIdx (v.adicCompletionIntegers K) = w.1.asIdeal.ramificationIdx A`
  ——即 **AGREE-RAM**（completion 侧 ramification index = number-ring 侧 e）。
- **:721 `inertiaDeg_eq_inertiaDeg`**：
  `w.1.asIdeal.inertiaDeg A = Ideal.inertiaDeg (w.1.completionIdeal L) (v.adicCompletionIntegers K)`
  ——即 **AGREE-FIELD**（completion 侧 inertia degree = number-ring 侧 f；证明用
  `inertiaDeg_tower` + base 侧 `AdicValuation.lean:318 inertiaDeg_asIdeal_completionIdeal`：`Ideal.inertiaDeg (v.completionIdeal K) A = 1`）。
- 另有 `:739-744` 的 tower 等式与 `ramificationIdx_mul_inertiaDeg_eq_finrank` 可直接配合。

**转换到本仓 `localRamificationIndex` / `relativeRamificationIndex` 的 `'` 形式**：
- `Ideal.ramificationIdx'_eq_ramificationIdx`（FLT 文件中已用，需 `completionIdeal_ne_bot`）；
- `Ideal.inertiaDeg'_eq_inertiaDeg`（Mathlib Inertia.lean:119，需 maximal 实例）；
- 我们的 `local*` 定义用 `IsLocalRing.maximalIdeal (adicCompletionIntegers ...)`，与
  `v.completionIdeal K` 定义一致（`AdicValuation.lean` 的 `completionIdeal`）。
- `w : v.Extension B` 由 `nativeBadToKPlace`/`nativeBaseSectionPlace` 与它们的
  `comap = b.1` 引理构造（`⟨place, under_eq⟩`）。

**状态**：`FLT/DedekindDomain/AdicValuation.olean = True`；
`FLT/DedekindDomain/IntegralClosure` 等待 `FLT/Mathlib/RingTheory/Localization/BaseChange.olean`（lead 已修 pin、重编中）；
`FLT/DedekindDomain/Completion/BaseChange.lean` 需其依赖链（Completion/AdicValuation 等）绿后加入/重编。
绿后写 `Mzk1P3AgreeFLTActual.lean`：import `tmp.external.ported.flt.FLT.DedekindDomain.Completion.BaseChange`，
把 `:685`/`:721` 经 `ramificationIdx'`/`inertiaDeg'` 转换后套到 `localDataAgreesWithPlaceData` 的两个分量。

### 14.1 BADCHAR-PRIME 精确缺口（无法对一般 T 证明）

`PrimeConductorCurve`（`Mzk1PrimeConductorRouteActual.lean`）只有字段
`p : ℕ`、`hp : Nat.Prime p`、`e : ℕ`；**没有任何对象把 `C.p` 与 `T.arithmetic.Fmod` 的坏模位
`b.1` 的 residue characteristic/under-ideal 联系起来**。因此
`GAP-PC-BADCHAR-PRIME (residueCharacteristic (b.1) = C.p)` 对任意 `T` 不可证：
- 可证部分是 `under ℤ = span{C.p} ↔ residueCharacteristic (b.1) = C.p`（green，P3BadCharPrimeEquiv）；
- 缺的是 **C 的构造**：由实际 bad 位数据定义 `C.p`（或给 bridge hypothesis `C.p = residueCharacteristic (b.1)`）。
同理 BADCHAR-DEG 需要实际 bad 位的 `residueInertiaDegree = 1`（tame/conductor 局部计算），
可证部分是等价 `f=1 ↔ absNorm = char`（green，P3BadCharDeg）。


### 14.2 AGREE-FLT 草稿与当前 FLT 阻塞（2026-11-13 07:40 CST）

草稿文件：`tmp/sheaf/xif/paper/Mzk1P3AgreeFLTActual.lean`（待 Lead 加 watchdog）。
- import `tmp.external.ported.flt.FLT.DedekindDomain.Completion.BaseChange`；
- `completionExtension place : v.Extension (𝓞 K)`，其中 `v := (comap (k := k) place).maximalIdeal`，
  `w.1 := place.maximalIdeal`，under-ideal 等式由 `NumberFieldFinitePlace.comap_maximalIdeal` 给出；
- `localRamificationIndex_eq_relativeRamificationIndex`：FLT `:685` + `Ideal.ramificationIdx'_eq_ramificationIdx`；
- `localInertiaDegree_eq_relativeResidueDegree`：FLT `:721` + `Ideal.inertiaDeg'_eq_inertiaDeg`；
- `localDataAgreesWithPlaceData_of_implies`：合取。
需要实例假设：`[FiniteDimensional k K] [Algebra.IsSeparable k K]`
（+ 由 Mathlib 提供的 `IsIntegralClosure 𝓞K 𝓞k K`、`Module.Finite 𝓞k 𝓞K`，若缺按错误补）。

**当前 FLT 阻塞**：
- `FLT/DedekindDomain/IntegralClosure.olean = False`：最新仍 4 处 pin
  （:112 rewrite pattern、:139 `Set.coe_setOf`、:194/:199 `finrank_of_isFractionRing` 实例、:266 induction zero）；
  Lead 已修 `:112 if_pos`、`:139 Set.coe_setOf`、`:199 finrank_of_isFractionRing`、`:266 | zero => simp`，等下一轮。
- `FLT/DedekindDomain/Completion/BaseChange.olean = False`，其唯一缺失依赖就是 `IntegralClosure.olean`
  （per-file log 全是 "object file ... IntegralClosure.olean does not exist"）。
- `FLT/DedekindDomain/Completion/AdicValuation.olean = False`，同为链上等待。


## 15. GAP-PC-AGREE-RAM/FIELD 关闭（2026-11-13 后续）

**产物**：`tmp/sheaf/xif/paper/Mzk1P3AgreeFLTActual.lean` — watchdog **DONE EXIT=0 43s@11:13:10Z，olean=True**。

内容（复用仓内 FLT `DedekindDomain/Completion/BaseChange.lean`）：
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion.ramificationIdx_eq_ramificationIdx`（:685，签名由 qpilot #check 确认）；
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion.inertiaDeg_eq_inertiaDeg`（:721）；
- primed 转换 `Ideal.ramificationIdx'_eq_ramificationIdx` / `Ideal.inertiaDeg'_eq_inertiaDeg`（注意：p、q 是显式 binder，必须传两个 Ideal）；
- 构造 `lowerPlace (place) = (comap place).maximalIdeal`、`placeExtension : (lowerPlace place).Extension (𝓞 K)`（`HeightOneSpectrum.ext` + `under_def` + `comap_maximalIdeal`）。

定理：
- `localRamificationIndex_eq_relativeRamificationIndex`（**AGREE-RAM 关闭**）；
- `localInertiaDegree_eq_relativeResidueDegree`（**AGREE-FIELD 关闭**）；
- `localDataAgreesWithPlaceData_of_implies`（AGREE 整体成立，条件为内容假设：`[FiniteDimensional k K]`、`[Algebra.IsSeparable k K]`、`[Algebra (𝓞k) K]`、两个 `IsScalarTower`、`[IsScalarTower ℤ (𝓞k) (𝓞K)]`、`[Module.Finite (𝓞k) (𝓞K)]`、`[Module.IsTorsionFree (𝓞k) (𝓞K)]`、`[IsIntegralClosure (𝓞K) (𝓞k) K]`；`Algebra.IsIntegral (𝓞k) (𝓞K)` 用 `Algebra.IsIntegral.tower_top (R := ℤ)` 实例提供）。

**P3-E GAP 树更新**：
```
SSIneqExplicit（条件于外部 Mestre–Oesterlé 参数）
├── GAP-PC-WEIGHT  ← FINITE（GAP）/ AGREE（**PROVED**）/ UNRAM-RESIDUE（GAP tame）
├── GAP-PC-RESNORM ← RESDEG（≈范数等式, green）/ BADCHAR（NORMFORMULA green + PRIME/DEG GAP）
└── GAP-PC-FINITE  ← 仍为内容缺口（IsIntegralClosure ⇒ Module.Finite 的完成环版本）
```
即 AGREE-RAM/FIELD 已从缺口变为**已证定理**（条件仅为 T 的算术内容假设）。


## 16. P3-E 最终条件装配（AGREE + FINITE 均关闭）

**新产物（watchdog 证据）**：
- `tmp/sheaf/xif/paper/Mzk1P3FiniteFLTActual.lean` — **DONE 65s@11:25:09Z，olean=True**；
  `moduleFinite_completedValuationRings` / `nativeBadToKPlace_moduleFinite`：
  用 FLT `DedekindDomain/Completion/BaseChange.lean` 的 `(priority 1001) Module.Finite
  (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)` 实例；
  **注意**：必须先 `let v := (comap place).maximalIdeal`、`let w := placeExtension place` 再
  `inferInstance`（直接 inferInstance 会 metavariable 匹配失败）。
- `tmp/sheaf/xif/paper/Mzk1P3FinalAssemblyActual.lean` — **DONE 58s@11:28:57Z，olean=True**；
  `ssIneqExplicit_final`：端到端 `SSIneqExplicit`，其中
  **AGREE（FLT :685/:721）与 FINITE（FLT 实例）均已关闭**。
- `tmp/sheaf/xif/paper/Mzk1P3ArithInstancesActual.lean`（待 watchdog）：对 `T.arithmetic` 构造
  - `FiniteDimensional Fmod K` ← `FiniteDimensional.trans`（Fmod→F→K）；
  - `Algebra.IsSeparable Fmod K` ← `Algebra.IsSeparable.trans`（两步 Galois ⇒ separable）；
  - `Module.Finite (𝓞 Fmod) (𝓞 K)` ← `IsIntegralClosure.finite`（𝓞Fmod integrally closed + Noetherian）；
  - 其余 7 个实例（Algebra (𝓞Fmod) K、IsScalarTower×3、IsIntegralClosure、IsTorsionFree、
    Algebra.IsIntegral）由 Mathlib NumberField/Basic 提供（文件内 `example := inferInstance` 登记）。

**P3-E 最终 GAP 树（16 后）**：
```
SSIneqExplicit  final（condition，[hMO] 外部参数）
├── AGREE-RAM / AGREE-FIELD      DISCHARGED（FLT BaseChange :685/:721）
├── GAP-PC-FINITE                DISCHARGED（FLT priority-1001 instance）
├── T 算术实例                    CONSTRUCTED（P3ArithInstances；Mathlib 提供余下 7 个）
└── 剩余内容输入：
    ├── GAP-PC-RESNORM 数据：hdeg（RESDEG）+ hunder/hinert（BADCHAR 下的 PRIME/DEG 实际识别）
    ├── GAP-PC-TAME：htame（relative e=f=1，素导子 tame 局部计算）
    └── arch: harch（≥0）
```
即 P3-E 已从“AGREE/FINITE 两条大缺口”缩到 **RESNORM 的 BADCHAR 数据识别 + tame 局部计算 + arch**
（外加外部 Mestre–Oesterlé Prop 参数），无 sorry/axiom。
