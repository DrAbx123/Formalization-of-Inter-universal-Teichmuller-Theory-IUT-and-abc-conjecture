# P7-GATE-REVIEW — P7 全链 gate 复核 + 最终 assembly 缺口清单

Status: **P7 / ABC gate NOT PASSED**（2026-11-13 05:2x Asia/Shanghai，READ-ONLY）。
依据：coord/FINAL-ASSEMBLY.md、coord/R29-STATUS.md、coord/GATE-STATUS-R29.md、dag/watchdog/watchdog.log/state.json、实际 olean 存在性；未编译、未运行 comparator/#print axioms 复核。

## 0. 结论先行

- P7 的最终链仍是 **PENDING-EXTERNAL**：lana `Iut` 链（Pi1 → Cor312/ThetaData/Basic → Concrete/ThetaRegion → Wall/* → MainTheorem）的 olean 全部不存在，故 assembly 文件 1/3/5 无法编译。
- 已 green 的只是 **skeleton/lana-free alternative**（文件 2/4/6/7），不是 `∀D, Wall.SSIneq D` 的实际证明。
- 旧的 `Mzk1FinalConditionalABCActual.final_conditional_ABC` 已 **RETRACTED/VACUOUS**：`hfull` 被 `Mzk1FinalConditionalVacuityActual.hfull_unsatisfiable` 证明不可满足；不得用作 ABC 结论。
- V4 final gate 仍是条件候选：F4.a/F4.b/F4.c 三个 `sorryItems`，其中 F4.c 为 ABC-strength；不是终态证明。
- 因此 P7 gate 当前为 **RED/blocked**，不是 green。

## 1. P7 前置 lana/ole 链（均缺）

| 前置 module | ole | 说明 |
|---|---|---|
| `Iut/WallEquiv/Basic.olean` | **NO** | FINAL-ASSEMBLY 文件 1 的 lana consumer（classicalABC_of_ss） |
| `Iut/MainTheorem.olean` | **NO** | FINAL-ASSEMBLY 文件 3 的 lana MainTheorem |
| `Iut/Wall/MultiContainer.olean` | **NO** | FINAL-ASSEMBLY 文件 5 的 lana SSIneq 声明 |
| `Iut/Cor312/ThetaData/Basic.olean` | **NO** | Iut/Cor312 链根 |
| `Iut/Cor312/Statement.olean` | **NO** | Iut/Cor312 Statement |
| `Iut/Concrete/ThetaRegion.olean` | **NO** | Concrete ThetaRegion |
| `Pi1/FundamentalGroup/GenericPoint.olean` | **NO** | Pi1 shim 链终点 |

watchdog 当前 state 中与本链相关的外部失败仍是 lana/lana_tgfree（`Iut/*` 未产生任何 DONE）；`Iut` 链没有可用 olean。

## 2. P7 assembly 文件现状（FINAL-ASSEMBLY order）

| # | 文件 | ole | watchdog 最后状态 | 判定 |
|---|---|---|---|---|
| 1 | `tmp/sheaf/xif/paper/Mzk1SSIneqConsumerChainActual.lean` | **NO** | NONE | PENDING-EXTERNAL：`Iut/WallEquiv/Basic` 缺；定理 `abcConjecture_of_forall_ssIneq` 以 `∀D, SSIneq D` 为显式输入；无 sorry/axiom |
| 2 | `tmp/sheaf/xif/paper/Mzk1StepXISSIneqDictionaryShaActual.lean` | YES | NONE (ole 早先) | GREEN SKELETON：`StepXISSIneqDictionary` 的 sC/logq/V/l/A 字段未实例化；仅纯算术 iff |
| 3 | `tmp/sheaf/xif/paper/Mzk1FinalABCBridgeActual.lean` | **NO** | NONE | PENDING-EXTERNAL：`Iut/MainTheorem` 缺；`classicalABC_implies_ABCConjecture` 条件于 lana ClassicalABC |
| 4 | `tmp/sheaf/xif/paper/Mzk1StepXIMinimalStatementShaActual.lean` | YES | NONE (ole 早先) | LANA-FREE ALTERNATIVE：定义 `StepXIMinimalStatement := SSIneqExplicit`；不是 lana `Wall.SSIneq` 的 inhabitant |
| 5 | `tmp/sheaf/xif/paper/Mzk1StepXIMinimalStatementActual.lean` | **NO** | NONE | PENDING-EXTERNAL：`Iut/Wall/MultiContainer` 缺；真正的 `Wall.SSIneq` 声明 |
| 6 | `tmp/sheaf/xif/paper/Mzk1StepXICor312FullAssemblyActual.lean` | YES | NONE (ole 早先) | GREEN CONDITIONAL：由 `requirementContract`/`SourceLinkFactorization` 等显式数据组装，不等于最终 ABC |
| 7 | `tmp/sheaf/xif/paper/Mzk1Cor312FullActual.lean` | YES | NONE (ole 早先) | GREEN RE-EXPORT：canonical re-export，仍条件于上游接口 |

## 3. 最终 assembly 缺口清单（按阻塞顺序）

### G1. lana `Iut` 链缺 olean（P0/P7 共享硬阻塞）
- 缺：Pi1 shim 链、`Iut/Cor312/ThetaData/Basic`、`Iut/Cor312/{LeftHandSide,RightHandSide,Statement}`、`Iut/Concrete/ThetaRegion`、`Iut/Wall/*`、`Iut/MainTheorem`（FINAL-ASSEMBLY §0）。
- 影响：文件 1、3、5 无 ole；P7 无法开始。
- 当前证据：上述 `.olean` 全部 `NO`；watchdog 无对应 DONE 行。

### G2. G4 SSIneq dictionary 字段未实例化
- 文件 2 的 `structure StepXISSIneqDictionary` 要求 `sC_eq : sC = sFactor nC`、`logq_eq : logq = 2*l*A`、`V_eq : V = lanaLogVol`、`hl`；当前只有 skeleton/纯算术 iff，没有 `D : InitialThetaData` 上的实例。
- 这正是 FINAL-ASSEMBLY 文件 2 的 “fields TODO”；不是绿色目标。

### G3. SSIneq 输入本身未证
- 文件 1 的结论是 `(h : ∀D, Iut.Wall.SSIneq D) → ABCConjecture`；文件 5 的 `StepXIMinimalStatement D := Wall.SSIneq D` 只是定义/展开，不是 inhabitant。
- 因此最终链 still conditional on the Scholze–Stix inequality; gate NOT passed. FINAL-ASSEMBLY §6 明说 “ABC gate NOT passed until the SSIneq input is proved”。

### G4. lana-free alternative 不能替代 lana target
- 文件 4 的 `StepXIMinimalStatement` 定义为我们的 `SSIneqExplicit`，不是 lana `Wall.SSIneq`；只能在显式算术 shape 上自证，不能作为 P7 对 lana 目标的证明。

### G5. V4 final gate 是条件候选，不是终态
- `S3135FinalAssemblyGateV4CandidateActual` 的 `s3135FinalAssemblyGateV4CandidateReport` 明确 `sorryItems`：F4.a `S3135ValueMonoidIdentification`、F4.b paper input `S3135CompletionBaseFieldUnitScalar`、F4.c card P `ABCHeightWeightAdditiveBoundV2`（ABC-strength）。
- 即使 ole 存在，仍是条件 gate；不得把 V4 Candidate 当无条件 ABC。

### G6. 旧 conditional/vacuous ABC 必须排除
- `Mzk1FinalConditionalABCActual` header 已标 RETRACTED/VACUOUS；`hfull` 被 `Mzk1FinalConditionalVacuityActual.hfull_unsatisfiable` 证明不可满足（该文件 ole 存在）。
- 任何最终报告若引用 `final_conditional_ABC`/`final_theorem_package` 作为结论，属审计违例。

### G7. 其他 final-assembly 尝试不是 canonical
- `Mzk1FinalAssemblyAssumptionsActual.lean`、`Mzk1FinalAssemblyConsumerGlueActual.lean`：无 ole；watchdog 最后为 2026-11-11 FAIL；不是当前 P7 链。
- `Mzk1FinalAssemblySelfChecks/Shape/StatementChecksActual`：ole 存在但只是 shape/self-check，不提供 SSIneq inhabitant。

### G8. 验收证据未做
- 未对文件 1/3/5 运行 `#print axioms`（无 ole）；未运行最终 comparator/公理闭包。
- 即使未来 ole 出现，必须验证：trio 编译 + `#print axioms` 仅 `propext, Classical.choice, Quot.sound` + 目标类型 comparator；否则 gate 不能签。

### G9. P0–P6 residual 仍会传导到 P7
- P4-POS（`Mzk1PaperFaithfulHullActual` 正性）仍 conditional/RED；P3 `TargetReduction`/DExact 仍有 RED；P5 C-Divisor/C-Theta 缺 order-at-O/WeilDivisor API 与一般线丛平凡化；P6 GAP-NORM-ARCH、GAP-SOURCE-NATIVE-Q 未闭。
- 详见 `coord/R29-STATUS.md` §2、`coord/GATE-STATUS-R29.md`、`coord/R29-GREEN-AUDIT.md`。

## 4. 可行的下一步（不改题）

1. 先只处理 lana `Iut` 链：按 FINAL-ASSEMBLY §0 的拓扑顺序检查 Pi1 → Cor312/ThetaData/Basic → Statement → Concrete/ThetaRegion → Wall/* → MainTheorem；确认缺 olean 的精确首错并修 vendor/API drift（这是 P7 唯一真正的 unlock）。
2. 一旦 `Iut/WallEquiv/Basic` 与 `Iut/MainTheorem` 出现 ole，再编译文件 1/3；文件 2 的字段实例化与文件 5 的 `Wall.SSIneq` 声明随后接入。
3. 每步都需 trio + `#print axioms`；禁止用文件 4 的 lana-free alternative 或 V4 candidate 替换终态目标。
4. 在 lana 链未通前，P7 只能继续做文档/审计；不要新增假设换 green。

## 5. 证据索引

- `coord/FINAL-ASSEMBLY.md` §0/§1/§6（P7 文件顺序与 blockers）；
- `coord/R29-STATUS.md` §2（P0–P6 residual）；
- `coord/GATE-STATUS-R29.md`（当前 watchdog/olean gate）；
- `coord/R29-GREEN-AUDIT.md`（35 个 R29 green 文件的条件/空洞风险）；
- `.lake/build/lib/lean/Iut/**`（均缺）；`tmp/sheaf/xif/paper/Mzk1SSIneqConsumerChainActual.lean:2`、`Mzk1FinalABCBridgeActual.lean:2`、`Mzk1StepXIMinimalStatementActual.lean:2`；
- `Mzk1FinalConditionalVacuityActual.lean:43-47`（hfull_unsatisfiable）；`S3135FinalAssemblyGateV4CandidateActual.lean:111-114`（sorryItems）。