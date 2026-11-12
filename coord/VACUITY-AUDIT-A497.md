# VACUITY AUDIT A497 — step3115/qΘ 链的空转审计

触发：`thetaPilotLogImage := qPilotLogImage / (2·l.value)`（定义即 q 除以 2ℓ），导致 `q ≤ theta` 的比较、`qThetaStepXIContract.targetSigned := thetaSigned`、`target_le_theta := rfl` 全部是定义/算术空转，不是 paper Cor 3.12 内容。

## 根因（逐字定义）

`tmp/sheaf/xif/paper/Mzk1QPilotSHEDoubleImageActual.lean`：
```lean
noncomputable def qPilotLogImage (b) : Real := localSignedLog (qVFamily T b)   -- = Real.log ‖q_V‖ < 0
```
`tmp/sheaf/xif/paper/Mzk1QPilotR4Stage5AlignActual.lean`：
```lean
def thetaPilotLogImage (b) : Real := qPilotLogImage T b / (2 * (l.value : Real))   -- :50  ← 空转根源
def qThetaHullReadout (b) : Real := qPilotLogImage T b                              -- :91
def qThetaDetReadout (b) : Real := thetaPilotLogImage T b                           -- :95
theorem qPilotLogImage_lt_thetaPilotLogImage (b) : qPilotLogImage T b < thetaPilotLogImage T b  -- :70
  -- 证明只用 q<0 与 2ℓ>1：-A < -A/(2ℓ)，与 Θ-pilot 几何无关
def qThetaStepXIContract (b) (ipl) (hipl) (apt) (hapt) : StepXIContract where
  qSigned := qPilotLogImage T b
  thetaSigned := thetaPilotLogImage T b      -- :110
  targetSigned := thetaPilotLogImage T b     -- :111  ← target 直接定义为 θ
  q_le_target := le_of_lt (qPilotLogImage_lt_thetaPilotLogImage T b)  -- 空转
  target_le_theta := le_rfl                                           -- 空转
```

## A. 判定为**空转（vacuous）**的声明

| file:declaration | 判定依据 |
|---|---|
| `Mzk1QPilotR4Stage5AlignActual.thetaPilotLogImage` | 定义为 `q/2ℓ`，非 Θ-pilot 区域 log-volume |
| `Mzk1QPilotR4Stage5AlignActual.twoL_mul_thetaPilotLogImage` | 上述定义的代数重写（真等式但只关于该定义） |
| `Mzk1QPilotR4Stage5AlignActual.qPilotLogImage_lt_thetaPilotLogImage` | 仅用 `-A < -A/(2ℓ)`（A>0, 2ℓ>1），无几何内容 |
| `Mzk1QPilotR4Stage5AlignActual.thetaPilotLogImage_neg` | 空转定义的直接推论 |
| `Mzk1QPilotR4Stage5AlignActual.qThetaReadout_ordered`（`q≤θ`） | 上述比较的直接重述 = 空转 |
| `Mzk1QPilotR4Stage5AlignActual.qThetaStepXIContract` | `target := θ`, `q_le_target` 空转, `target_le_theta := rfl` |
| `Mzk1QPilotR4Stage5AlignActual.cor312Conclusion_of_qThetaDoubleImage` | 由空转 contract 经 `cor312_of_constructed_stepXI` 得 `q≤θ` |
| `Mzk1QPilotR4Stage5AlignActual.QThetaReadoutPackage`（字段 hull_lt_det 等） | 字段内容即上述空转比较/算术恒等式 |
| `Mzk1QPilotR4Stage5AlignActual.qThetaReadout_strict` / `twoL_mul_qThetaDetReadout` / `qThetaReadoutPackage` | 空转定义上的重写 |
| `Mzk1QPilotR4Stage5AlignActual.step3115_comparison_of_qThetaPackage` | 空转包的 `hull≤det` |
| `Mzk1QPilotR4Stage5AlignActual.qThetaHDD`/`qThetaDSC`/`qTheta_fourTriangleReadout` | 读法=空转 q/θ 对，`hull_eq/theta_eq` rfl |
| `Mzk1QPilotR4Stage5AlignActual.qTheta_step3115_comparison` | = 空转 `qVertexReadout_ordered` |
| `Mzk1QPilotR4Stage5AlignActual.qThetaFourTriangleSynthesis` | 用空转 contract/读法/比较填充 FourTriangleSynthesis |
| `Mzk1QPilotR4Stage5AlignActual.cor312Conclusion_of_qThetaFourTriangle` | 由上述空转合成得 `q≤θ` |
| `Mzk1QPilotR4Stage5AlignActual.qThetaHullVolume_eq_twoL_mul_detVolume` / `qThetaDetVolume_lt_hullVolume` / `qThetaVolume_pair_pos` | 空转定义的算术恒等式 |
| `Mzk1QThetaHullDetAlignActual.qThetaReadout_ordered_iff_packetDet_mul_le_one` / `qThetaPacketDet_mul_q_le_one` | 从空转比较倒推的判据（算术条件，非几何） |
| `Mzk1Step3115ComparisonActual.qThetaHDD` / `step3115_comparison_proved` | 空转 HDD 读法与比较 |
| `Mzk1Step3115ComparisonActual.detReadout_twoL_mul_eq_hull` | 空转定义的根关系重写 |
| `Mzk1Step3115ComparisonActual.qThetaFourTriangleSynthesis` / `cor312Conclusion_of_qThetaSynthesis` | 依赖空转 step3115/contract |
| `Mzk1Step3115WiringActual.qTheta_r4_literal_assembly` | 用空转 qTheta 实例消费 R4；其 Cor312Conclusion 分量为空转 |
| `Mzk1Step3115WiringActual.Step3115WiringEvidence.qTheta_step3115_filled` / `step3115WiringEvidence` | 打包空转结论 |

## B. **真实（非空转）**但条件/依赖显式 named 缺口的声明

| file:declaration | 判定 |
|---|---|
| `Mzk1QPilotSHEDoubleImageActual.qPilotLogImage` / `qPilotLogImage_exp` / `she_arrow_apply` / `sheArrowStatement_proved` | 真实：局部 q 的完成范数 log、SHE 根关系 `θ^{2ℓ}=q` |
| `Mzk1QPilotR4Stage5AlignActual.qPilotLogImage_neg` | 真实（局部 q 负 log） |
| `Mzk1QPilotR4Stage5AlignActual.qThetaHullVolume` / `_pos` | 真实：正的局部 |log q|（但**不是** Θ-pilot 体积） |
| `Mzk1QPilotR4Stage5AlignActual.abcConjecture_of_qThetaStage5Estimates` | 真实条件定理（hheight/hmain 为显式 named IUT IV 缺口；hullVolume 用真实 |log q|） |
| `Mzk1FourTriangleSharedActual.*`（HDDDecomp/HDD/fourTriangleReadout/FourTriangleSynthesis/cor312Conclusion_of_fourTriangleSynthesis） | 真实泛型定义/条件定理（`step3115_comparison` 为结构字段，非空转） |
| `Mzk1R4LiteralAssemblyActual.literalIQInterface` / `literalIQInterface_hull_logVolume_eq_ofReal` / `r4_literal_assembly` | 真实条件：literal 全局 IQ 接口 + 显式 `hcomp`（IUT IV 两条比较，真缺口） |
| `Mzk1R4LiteralAssemblyActual.r4_finiteColumns_comparison` | 真实（finiteSup 上界） |
| `Mzk1R4EndgameCompositionActual.r4_endgame_composition` | 真实条件（S 任意、hcomp 显式；**但若以空转 qTheta 实例代入 S，则 Cor312 分量空转**） |
| `Mzk1IUT312TopStatementActual.*` | 真实条件于 tree `StepXIContract`；注意 contract 的 `targetSigned` 自由，单独不构成 3.12 证据 |
| `Mzk1StepXIContractAssemblyActual` / `Mzk1StepXIScalingActual` | 真实泛型构造（不空转，但 paper 内容仍取决于 contract 数据来源） |
| `Mzk1HullDetStep3115Actual.*`（hull lane） | 真实：hullReadout=packetLogVolume、detReadout=-log|q|、`packetDet*q≤1 ↔ hullReadout≤detReadout`；**不是** q/(2ℓ) 空转（其 det 是独立 q 读法） |
| `Mzk1Step3115WiringActual.hullDet_step3115_evidence` | 真实（复用 hull lane 具体读法） |
| `Mzk1ExplicitABCWeakeningActual.*` | 真实（ExplicitABC ⇒ ABCConjecture 收口引理） |

## C. `Cor312Conclusion` / `StepXIContract` 过弱性复核

- `IUTIII/Corollary312/StepXI/Contract.lean`：`StepXIContract` 只含三个自由实数 `qSigned/thetaSigned/targetSigned` + 证据 Prop 字段；`Cor312Conclusion contract := qSigned ≤ thetaSigned`。**结构本身不约束 target 与论文对象的关系**；qTheta 实例把 `targetSigned := thetaSigned` 后 `q ≤ target ≤ theta` 退化为 `q ≤ θ`，其 `q ≤ θ` 又由定义 `θ := q/(2ℓ)` 空转成立。
- 因此 **`StepXIContract`/`Cor312Conclusion` 单独不是 3.12 证据**：必须有把 `qSigned/thetaSigned/targetSigned` 固定到 paper 对象（q-pilot 体积、Θ-pilot hull 体积、IUT IV 比较）的构造定理。
- 真正内容在 `Cor312ToABCBridgeInterface` 的两个逐 ε 字段：`height_le_normalizedRegionVolume` 与 `regionVolume_le_normalizedWeight`（IUT IV §2 两条 named 比较）——即 `hcomp`，这两条是 named 真缺口，不可用空转 `q≤target` 充数。

## D. 行动项

1. **停止**把 `Mzk1Step3115ComparisonActual` / `Mzk1Step3115WiringActual` / `Mzk1QPilotR4Stage5AlignActual.qTheta*` / `Mzk1QThetaHullDetAlignActual` 的 qTheta 链当 3.12 证据；文件保留但标注 VOID。
2. **重定义独立 Θ-pilot 读法**：用 literal thetaPilot region 的真实 log-volume（hull/qpilot lane 的 `thetaPilotOn`/`logVol hull` 或我们 literal 载体上的 θ-hull 体积），不得由 q 除以 2ℓ 定义。
3. `R4LiteralAssemblyActual`/`R4EndgameCompositionActual` 的 `r4_literal_assembly` 保持真实条件定理，但只允许以**非空转** `FourTriangleSynthesis` 实例消费；`hcomp` 仍为 IUT IV 两条 named 比较。
4. `Cor312Conclusion` 使用须附带 contract 构造来源说明；不得由任意 contract（尤其 `target:=theta`）直接宣称 3.12。
## E. 登记与文件更新（lattice, A497）

- `coord/DAG-BLOCKED.json` 新增: `vacuity:qtheta-thetaPilotLogImage`、`vacuity:qthetaStepXIContract`、`vacuity:step3115_comparison_proved`、`vacuity:qThetaFourTriangleSynthesis`（CHAIN-BROKEN）；`named-gap:hcomp-iut4-comparisons`、`named-gap:independent-theta-pilot-readout`（OBSTRUCTION/named）。blocked_total=73。
- 新建 `coord/NAMED-GAPS-A497.md`（真实 named 缺口 + VACUOUS 禁用清单 + 可用真实候选 + DAG-BLOCKED 登记）。
- `coord/MAIN-CHAIN-AUDIT-A496.md` 已加 A497 更正：qTheta/step3115 链不得计入 3.12 进度。
- `coord/ROUTE-DECISION-A496.md` 已加 A497 执行状态（LANA reference-only 不变；qTheta 链标 VOID）。

