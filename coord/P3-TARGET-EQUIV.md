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
- **DICT-C**：paper box 与 L6 **非等价**。L6⇒box 在 S,T≥0、l≥5 下 green；box⇒L6 有反例（Ctwo, l=5,D=S=T=Q=0）。reverse 归约到 **L7/DExactLowerTarget**（不是 UNKNOWN）；boxSlack 单独不足。

结论：目标 ↔ L6 的等价链现在只剩 DICT-B、DICT-C 两个命名缺口；DICT-A 本身 green。


## 7. DICT-B 结构（task DICT-B）

新文件：tmp/sheaf/xif/paper/Mzk1P3DictBActual.lean（watchdog **DONE EXIT=0**，21:54:39Z；olean 149,680B）。**状态：INTERFACE（GAP 保留）**，不是 DICT-B 已证。

结构 P3DictB 的显式字段：
- 值：V gap sF A l D Q S Tstar c1（Real）；
- 算术候选：D_arith Q_arith S_arith T_arith（Real）；
- c1_pos : 0<c1；
- M_eq : MExpr V gap sF A = c1 * boxSlack l D Q S Tstar；
- D_eq/Q_eq/S_eq/T_eq : 各自与算术候选的等式。

已证 integrated theorem（接口层）：
  P3DictB.targetM_nonneg_iff_paperBox：
    0 <= MExpr V gap sF A
    <=> paperLHS l D Q S Tstar <= paperRHS l D Q S Tstar
  （直接复用 Mzk1P3DictionaryActual.targetM_nonneg_iff_paperBox，与 DICT-A 对齐）。

实际候选（新文件 Mzk1P3DictBArithActual.lean，watchdog DONE EXIT=0 22:04:54Z；olean 27,560B）：
- D_arith := primeConductorLogDisc C = C.e * log(C.p)（PrimeConductorCurve carrier 定义；不是从实际 Δ 证出）；
- Q_arith := nativeQArith T = nativeGlobalQPilotNormalizedLogMagnitude T；
- P3DictB.ofPrimeConductorData / ofPrimeConductorData_target_iff 为实际候选 builder；
- 状态仍 INTERFACE：hQ（paper Q=(l+1)/24 logq=sF*A）与 hM 是命名输入。

GAP（未构造；P3DictB 是命名接口，投影定理不等于 DICT-B 关闭）：
- D_arith = log disc（paper D = log d^K / log disc）——缺实际 log disc 对象；
- Q_arith = q 系数（paper (l+1)/24 log q = sF*A）——需 q 侧读数的实际字典；
- S_arith = s^Q 项 / arch/shell；T_arith = T(l)D_exact 或 l*_mod log s^<=；
- 对应实际对象/等式不在树内；P3DictB 只把 M_eq 作为唯一用于定理的字段，其余字段是显式候选，不是已证事实。
- DICT-C（box 与 L6）：**非等价**；L6⇒box green（S,T≥0,l≥5），box⇒L6 反例；reverse 归约到 L7/DExactLowerTarget。


## 8. Q 系数实际关系（Mzk1P3DictQCoeffActual，green 22:20:48Z，olean 229,448B）

纯代数 green：
  paperQCoeff_eq_sL_AL : ((l+1)/24)*logq = sL l * AL l logq
  （sL=l(l+1)/12, AL=logq/(2l)）
native 关系：
  nativeSignedLogQ := -nativeQArith
  nativePaperA := nativeQArith/(2l)
  nativePaperQ_eq_neg_sL_mul_A :
    ((l+1)/24)*nativeSignedLogQ = -sL l*nativePaperA

实际 q packet：
  qPacket_normalizedLogVolume = -baseQTotalLogMagnitude/(2l)（无权重和）
  nativeQArith_eq_weighted_sum = Σ nativeBadLocalWeight*baseQLogMagnitude（有权重和）
  ⇒ 两者差正是 GAP-PC-QHALF = nativeQArith = baseQTotalLogMagnitude（GAP-PC-WEIGHT 的权重=1 情形）。
条件定理：
  nativeSignedLogQ_eq_twoL_mul_qPacket_of_qhalf (hQ：GAP-PC-QHALF) :
    nativeSignedLogQ = 2l * qPacket.normalizedLogVolume

结论：paper Q 系数的**纯代数部分已关闭**；到实际 q packet 只差 GAP-PC-QHALF（权重和为无权重和），即 GAP-PC-WEIGHT；DICT-B 仍 INTERFACE。

**归约（green 22:23:30Z）**：`GAP_PC_QHALF_of_weight_one` —— `(∀ b, nativeBadLocalWeight T b = 1) ⇒ GAP_PC_QHALF T`；配套 `nativeSignedLogQ_eq_twoL_mul_qPacket_of_weight_one`。因此 P6 的 QHALF 已归约到 P3 的 GAP-PC-WEIGHT（条件归约，不是新假设）。


## 9. DICT-C 方向分析（新文件 Mzk1P3DictCDirectionActual）

DICT-C 的精确形式是双向等价
  0 <= boxSlack l D Q S T  <=>  L6ReducedInequality C l D_exact
在现有 tree 中不能双向成立：

- **L6 ⇒ box**（green，在 S,T>=0、l>=5 下）：
  boxSlack_nonneg_of_L6。
  证明：L6 给 T(l)>0 且 e logp>=0，故 D>=0；代入
  boxSlack=(1/l)D+(1/l)S+((2l-10)/3)T，三项均非负。
- **box ⇒ L6（反向）为假**：
  boxSlack_nonneg_not_implies_L6 给出 Ctwo(p=2,e=1), l=5,D=S=T=Q=0：
  boxSlack=0 但 L6 要求 log2 <= 0，假。
- 因此 DICT-C 需要额外的 D=D_exact 与 e·logp 下界来源（L7/DExactLowerTarget），
  boxSlack 单独不能推出 L6；也不能用 L6⇒box 充当双向等价。
- 现有 green 的分工：
  paperStepV_inequality：D,S,T>=0 ⇒ box；
  l6Reduced_of_dExactLower：L7⇒L6；
  没有 box⇒L7/L6。
DICT-C 保持 GAP（reverse 归约到 L7/DExactLowerTarget）。补定理：
- `L6ReducedInequality_of_DExactLower_and_box`：在 `D=D_exact`、`DExactLowerTarget`、MestreOesterle、ThetaDataLegality、hlogp 下 ⇒ L6；证明显示 **boxSlack 假设未被使用**，因此 reverse 的真正来源是 L7，而不是 boxSlack≥0。


### 9.1 DICT-C 批量结果（watchdog green）

第一批（2026-11-12）：
- Mzk1P3DictCBoxFromL6Actual.lean：boxSlack_nonneg_of_L6，DONE 22:36:40Z；
- Mzk1P3DictCReverseL7Actual.lean：L6ReducedInequality_of_DExactLower_and_box，DONE 22:36:39Z；
- Mzk1P3DictCCounterexampleActual.lean：boxSlack_nonneg_not_implies_L6，DONE 22:36:36Z；
- Mzk1P3DictDLogDiscActual.lean：primeConductorLogDisc 非负/正性，DONE 22:36:30Z；
- Mzk1P3DictQPacketActual.lean：qPacket normalized = -baseQTotal/(2l)，DONE 22:36:14Z；
- Mzk1P3DictCDirectionActual.lean：总方向文件 DONE 22:29:12Z。

第二批（待 watchdog）：
- Mzk1P3DictCEquivUnderL7Actual.lean：boxSlack_iff_L6_of_L7（条件等价：L7 + side conditions）；
- Mzk1P3DictQWeightDiffActual.lean：nativeQArith-baseQTotal=(Σ(weight-1)baseQ)，QHALF⇔加权差=0；
- Mzk1P3DictCBoxFormulaActual.lean：slack formula 与充分非负条件（DONE 22:42:04Z）。

第三批（D/Q/L7 actual sources，全部 DONE）：
- Mzk1P3DictDLogDiscBoundActual.lean：MestreOesterleBound ⇒ primeConductorLogDisc ≤ 5 log p（DONE 22:46:21Z）；
- Mzk1P3DictQNonnegActual.lean：nativeQArith ≥ 0（DONE 22:49:39Z）；
- Mzk1P3DictCReverseNativeDExactActual.lean：D=nativeDExact + L7 ⇒ boxSlack≥0 ↔ L6（DONE 22:49:39Z）。

第四批（D/Q 实际来源）：
- Mzk1P3DictDLogDiscSourceActual.lean：PrimeConductorDeltaMinSource（actual Δ_min 与 e·logp 的 log-abs 等式）为命名 GAP；MestreOesterle 界 green（DONE 22:52:39Z）；
- Mzk1P3DictQPacketSignedActual.lean：qPacketSignedLogQ=2l·qPacket.normalizedLogVolume=-baseQTotalLogMagnitude，green（DONE 22:56:36Z）。

第五批（D/Q/L7 收尾，全部 green）：
- Mzk1P3DictQHALFWeightOneSummaryActual.lean：QHALF⇐WEIGHT 重导出 + signedLogQ 条件式（DONE 23:04:21Z）；
- Mzk1P3DictL7NativeTargetActual.lean：nativeDExactL7Target 定义与 target⇒L6（DONE 23:04:21Z）；
- Mzk1P3DictL7ArchMonotoneActual.lean：DExactLowerTarget_nativeDExact_of_arch_le（DONE 23:00:46Z）；
- Mzk1P3DictDSourceRefinedActual.lean：PrimeConductorDeltaMinSourceRefined（absValue 非负 + log 等式）与 toSource（DONE 23:00:45Z）；
- Mzk1P3DictQSourceBuilderActual.lean：PaperQSource 从实际 qPacket 构造，logQ=-baseQTotal（DONE 23:04:21Z）。

第六批（收尾接口，全部 green）：
- Mzk1P3DictBDArithNativeActual.lean：P3DictB.ofNativeDExact（D_arith=nativeDExact）+ target⇔paperBox（DONE 23:07:47Z）；
- Mzk1P3DictDOrdInterfaceActual.lean：PrimeConductorOrdSource（p/e/ordValue 接口）+ e 非负/≤5（DONE 23:07:44Z）；
- Mzk1P3DictQHALFRegressionActual.lean：weights=1 ⇒ QHALF signedLogQ 回归测试（DONE 23:09:29Z，首次 FAIL 因 qPacket 未 open，已修）。


### 9.2 round8/9：D/Q 实际来源闭合状态

round8（全部 green）：
- Mzk1P3DictDCurveDataSourceActual.lean（DONE 23:24:08Z）：本地镜像 Iut CurveData.disc；PrimeConductorDiscDataSource（disc=p^e 显式命名）⇒ primeConductorLogDisc=log(disc)；
- Mzk1P3DictL7ArchLowerActual.lean（DONE 23:33:31Z）：L7(nativeDExact arch) ⇔ arch ≥ (1-1/l)logp - nativeGlobal；
- Mzk1P3DictDLogSourceWeakActual.lean（DONE 23:36:25Z）：弱 source log(disc)=e logp（替代 disc=p^e）⇒ 构造 carrier 并证 logDisc=log(disc)；
- Mzk1P3DictQWeightDegreeActual.lean（DONE 23:39:17Z）：nativeBadLocalWeight=1 ⇔ localCompletionDegree=1；
- Mzk1P3DictQAbsLogIdentityActual.lean（DONE 23:29:22Z）：paperQAbsLog(qPacketSignedLogQ)=qPacket.normalizedLogVolume，及 2l 逆式。

round9：
- Mzk1P3WeightDegreeOneActual.lean（DONE 23:42:25Z，olean 43,088B）：
  localCompletionDegree_eq_one_of_relativeDegree_one；
  nativeBadLocalWeight_eq_one_of_relativeDegree_one；
  nativeBadLocalWeight_eq_one_of_unram_residue：
  UNRAM=1 + RESIDUE=1 + FINITE + AGREE ⇒ weight=1。
  即 P3 的 GAP-PC-WEIGHT 归约到 mainline 的 UNRAM/RESIDUE 两条（此前已有 FINITE/AGREE 桥）。

结论：
- D：disc=p^e 不可由 CurveData 单独消；可弱化为 log(disc)=e logp，仍命名输入；
- L7：等价于 arch 下界，缺实际下界，不是代数重排；
- QHALF：精确归约为 localCompletionDegree=1，且已与 UNRAM/RESIDUE 合流。


### 9.3 round10：ResidueFieldEquiv 与 tame 局部计算

- Mzk1P3WeightDegreeOneResidueEquivActual.lean（DONE 2026-11-13T00:04:45Z）：
  relativeResidueDegree_eq_one_of_residueFieldEquiv（对接 shehdd 的 ResidueFieldEquiv）；
  nativeBadLocalWeight_eq_one_of_residueEquiv_unram：
  ResidueFieldEquiv + UNRAM=1 + FINITE + AGREE ⇒ nativeBadLocalWeight=1。
- Mzk1P3BadCharTameDegreeActual.lean（DONE 00:04:45Z）：
  relativeCompletionDegree_eq_one_of_unram_residue；
  localCompletionDegree_eq_one_of_unram_residue（再加 FINITE+AGREE）。
- Mzk1P3WeightDegreeOneLocalEFActual.lean（DONE 2026-11-13T00:19:22Z，olean 43,368B）：
  localCompletionDegree_eq_one_of_local_unram_residue；
  nativeBadLocalWeight_eq_one_of_local_unram_residue：
  本地 localRamificationIndex=1 + localInertiaDegree=1 + FINITE + AGREE ⇒ weight=1（不依赖 FLT）。
- Mzk1P3WeightDegreeOneFinrankActual.lean（DONE 2026-11-13T00:30:48Z，olean 50,408B）：
  relativeCompletionDegree_eq_one_of_FLT_finrank_one；
  nativeBadLocalWeight_eq_one_of_FLT_finrank_one：
  FLTCompletionFinrankInput + FINITE + AGREE + finrank=1 ⇒ weight=1。
- Mzk1P3FLTCompletionInputActual.lean（DONE 00:25:55Z）：乘性公式/FLTFinrank 输入/归约接口（不 import FLT）。
- Mzk1P3WeightDegreeOneFinrankActual.lean（DONE 00:30:48Z，olean 50,408B）：FLTCompletionFinrankInput+finrank=1+FINITE+AGREE ⇒ weight=1。
- Mzk1P3AGREEFLTBridgeActual.lean：乘性公式+FLTCompletionFinrankInput+relativeCompletionDegree_eq_finrank_of_FLT 已写；
  当前 red 仅因 BaseChange 依赖 olean（IntegralClosure/Bilinear）未生成，等 mainline 依赖绿后修 #check 声明名。
- FLT BaseChange 定位：tmp/external/ported/flt/FLT/DedekindDomain/Completion/BaseChange.lean:684-686
  ramificationIdx_eq_ramificationIdx；:719-721 inertiaDeg_eq_inertiaDeg。
  依赖链尚未全部绿（UniformRing DONE、ModuleTopology 修），等 olean 后可直接 import 对接
  AGREE-RAM/FIELD（无需新假设）。


### 9.4 FLT finrank 通道（2026-11-13）

- Mzk1P3AGREEFLTBridgeActual.lean（DONE 00:49:13Z）：import FLT Completion/BaseChange；#check 三声明；
  relativeCompletionDegree_eq_residue_mul_ramification；FLTCompletionFinrankInput；relativeCompletionDegree_eq_finrank_of_FLT。
- Mzk1P3FLTMultiplicityActual.lean（DONE 00:52:07Z）：FLT :751 全局 e*f=finrank wrapper。
- Mzk1P3FLTFinrankSupplyActual.lean（DONE 00:54:45Z）：FLTCompletionFinrankInput_of_FLT_global（FLT global + factor/finrank 对齐 ⇒ FLTCompletionFinrankInput）。
- Mzk1P3FinalWeightAssemblyActual.lean（DONE 00:57:13Z）：nativeBadLocalWeight_eq_one_of_FLT_global_finrank_one。
- Mzk1P3WeightOneChannelsActual.lean（DONE 10:51:33Z，olean 73,616B）：
  两条并列充分条件：
  D 直接：UNRAM=1 + RESIDUE=1 + FINITE + AGREE ⇒ weight=1；
  F FLT：FLT global e*f=finrank + factor/finrank 对齐 + FINITE + AGREE + finrank=1 ⇒ weight=1。
  两条都是 conditional；GAP-PC-WEIGHT 未无条件关闭。
