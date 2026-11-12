# DECOMP-MASTER-PLAN — 8 lane 分解工作流（A991）

日期：2026-11-12。**Status: PLAN / EXECUTABLE CHECKLIST**。只写文件；不手工编译，所有 Lean 编译交 `DshDagWatchdog`。

## 0. 目标与当前状态

统一目标：把 **`M := V − (sF−1)·A ≥ 0`**（SSIneq / normalized wall）分解成逐项恒等式/不等式，使每一项有定义来源、符号与可审计证书；**不是**用等价改写、代理 `M0`、或自由字段代替目标。

当前事实：
- `R = |log Θ|` 来自 `rhs = vol.processionVol thetaHull`，是抽象 `LogVolumeData` 字段；`globalThetaHullLogVolume` 需 `I.sourceSetVolume`/实际 holomorphic hull 或 concrete C3 tensor Haar；无 l=5 具体 C3/measure ⇒ **R 不可数值计算**（`coord/C3M-FEASIBILITY.md`）；`M=A−R` 仅符号化；
- R 的生产 `posRealAction` 不存在（`R-PRODUCTION-STATUS.md`、`C-R-FIELD-STATUS.md`、`C-LREAL-DATA-STATUS.md`）；
- 配对候选 C1–C6 已有初稿（`DECOMP-PAIRING-CANDIDATES.md`），全部未证；
- A 线已终结；C3/C3b 代理 INVALID；B1/B1-FIX2 STOP；B 证书证明计划存在但无数值上界（`B-PROOF-PLAN.md`）；
- 所有 Lean 编译由 watchdog 负责；lane 只写文件并报路径/定理/gap。

## 1. 8 步工作流（每步 owner / 产出 / 验收）

| 步 | 工作流 | 主 owner | 产出 | 验收标准 |
|---|---|---|---|---|
| S1 | **R 展开 / 目标分解**：把 `M` 或 `R` 展开为逐位/逐项定义；写清 `R=−rhs`、`rhs=vol.processionVol thetaHull`、`M=A−R`、`T_v/H_v/arch/torsion` 的来源 | hull | `coord/DECOMP-R-EXPANSION.md` | 每个符号有定义/源文件行号；无自由谓词；明确区分“可计算/不可计算”；R 的抽象字段与 per-v 数据逐条列出 |
| S2 | **正项清单**：列出所有候选非负项（hullPacket、tame/wild buffer、arch、torsion、σ 项），给公式、符号、来源 | qpilot | `coord/DECOMP-POSITIVE-TERMS.md` | 每项有公式+sign 证明或明确 `GAP/UNKNOWN`；禁止把“假设非负”写成“已证非负” |
| S3 | **配对候选**：把负项 `−T_v` 与正项 `H_v/arch/buffer` 配对；给出 `(∀…bound) → M≥0` 的算术引理 | qpilot | 更新 `coord/DECOMP-PAIRING-CANDIDATES.md`（C1–C6） | 每个候选有精确 `def` 形状、蕴含证明草稿、循环使用标记；至少一个候选的 failure mode 写清 |
| S4 | **LP 搜索**：对候选线性组合/权重做可行性搜索；输出 primal/dual 证书（Farkas/对偶界） | abc | `coord/DECOMP-LP-SEARCH.md` + `coord/decomp_lp_*.json/csv` | 有可复现的 LP 输入（有限系数、明确变量）；feasible 给 primal 值，infeasible 给 dual certificate；**不得用 M0/代理** |
| S5 | **循环审查**：检查依赖 DAG（目标是否被当假设、bound 是否用 M、E1/E4 接口是否循环）；标记所有循环边 | stage4 | `coord/DECOMP-CYCLE-AUDIT.md` | 每个候选/引理列 proof deps；无 target-as-hypothesis；无“bound 由 M 推出再用 bound 证 M”；E1/E4 接口使用需显式 |
| S6 | **恒等式 Lean 化**：只对 S1–S5 稳定且无循环的恒等式/算术引理写 Lean；不写目标本身 | abc + stepxi | `tmp/sheaf/xif/paper/Mzk1Decomp*Actual.lean` | 陈述完整、无 `sorry/axiom`、无自由字段；每个文件声明其消费的 S1–S5 节点；落盘后交 watchdog |
| S7 | **watchdog 编译**：文件落盘自动入队；lane 不手跑 `lake/lean/sage/WSL` | mainline | watchdog 队列/结果表 | 每个文件 `EXIT=0`、olean fresh、`#print axioms` trio、零 sorryAx；失败回 S6，不手改编译输出 |
| S8 | **审计**：stage4 逐文件审计语义/证据隔离/登记 | stage4 | `coord/STAGE4-AUDIT-RESULT-*.md` + `EVIDENCE-ISOLATION` | 无 §4 阻断；条件/接口/GAP 标签诚实；`lana-transitive`/lana-free 口径明示；无“未证说成证” |

## 2. 8 条 lane 的分工

| lane | 分解角色 | 主责步骤 | 当前输入/边界 |
|---|---|---|---|
| **mainline** | 集成、watchdog、gate 汇总；不写数学主张 | S7（主）、S1/S6 集成 | `DAG-NEXT.md`、watchdog 结果；所有文件落盘后统一编译 |
| **hull** | R/hull 侧展开与 hull 正项；hull/det/arch 术语 | S1（主）、S2 支持 | `C3M-FEASIBILITY.md`、`R-PRODUCTION-STATUS.md`、`VcI.lean` 读法；R 不可数值 |
| **qpilot** | q 侧/正项/配对；R 生产与 q-pilot 读数 | S2（主）、S3（主） | `R-PRODUCTION-STATUS`、`C-R-FIELD-STATUS`、`C-LREAL-DATA-STATUS`；posRealAction 无生产 |
| **shehdd** | paper/StepXI/Cor 3.12 恒等式与接口审查 | S5 支持、S6 支持 | StepXI/paper 链；不把接口当已证 |
| **abc** | LP、ABC 装配、Face5/E1/E4 条件链；恒等式 Lean 化 | S4（主）、S6（主） | `Mzk1OurFrameworkABCActual`、`FACE5-*`、E1/E4 接口；ABC 非已证 |
| **stage4** | 循环审查、审计、证据隔离 | S5（主）、S8（主） | 审计结果/registry；无 §4 阻断才 PASS |
| **lattice** | 本 master plan、S1 台账、DAG/文档/状态同步 | S1 支持、S5 支持、S8 支持 | `FINAL-STATUS`/`ROUTES`/`AUDIT_LEDGER`；只写文件 |
| **stepxi** | 源数据/符号约定/具体输入；恒等式 Lean 化支持 | S1 支持、S6 支持 | `CONCRETE-DATA-INVENTORY`、`Mzk1E1OrderActual`；E1 反例/数据边界 |

## 3. 可执行清单（按顺序，不允许跳步）

### Phase P1 — 分解冻结（S1+S2）
- [ ] hull 产出 `DECOMP-R-EXPANSION.md`：逐项列 `R/rhs/thetaHull`、`T_v/H_v/arch/torsion`、`M=A−R`；每项给源文件/行号；标 `COMPUTABLE / SYMBOLIC / UNKNOWN`。
- [ ] qpilot 产出 `DECOMP-POSITIVE-TERMS.md`：每项公式+符号+来源；未知项标 GAP；禁止“假设即正”。
- [ ] lattice 把 S1/S2 节点登记到本文件/`FINAL-STATUS`；未过 P1 不进 P2。
- **P1 gate**：所有项有定义来源；R 的不可计算性如实标注；无自由谓词。

### Phase P2 — 配对与 LP（S3+S4）
- [ ] qpilot 更新 `DECOMP-PAIRING-CANDIDATES.md`：C1–C6 每项给精确 `def`、蕴含证明草稿、失败模式；至少覆盖 per-place、bad-prime group、arch、wild、G-constrained。
- [ ] abc 建 `DECOMP-LP-SEARCH.md`：固定变量（T_v,H_v,arch,torsion 的系数/权重）、写出 primal/dual；feasible 给证书，infeasible 给 Farkas 证书；**不重用 M0**。
- [ ] lattice 同步候选表到 FINAL-STATUS/ROUTES；LP 结果标 DATA/CERT，不标定理。
- **P2 gate**：至少一个候选有完整 primal/dual 证书；所有候选有 failure mode；无代理变量。

### Phase P3 — 循环审查（S5）
- [ ] stage4 写 `DECOMP-CYCLE-AUDIT.md`：对 S1–S4 每个候选列 proof deps；检查 target-as-hypothesis、E1/E4 循环、`M` 自证；标记循环边。
- [ ] 任何循环候选退回 P2，不进 P3。
- **P3 gate**：DAG 无环；无 target-as-hypothesis；无自由字段替代。

### Phase P4 — Lean 化与编译（S6+S7）
- [ ] abc/stepxi 只写已冻结的恒等式/算术引理到 `tmp/sheaf/xif/paper/Mzk1Decomp*Actual.lean`；不得写目标本身、不得 `sorry/axiom`、不得自由字段。
- [ ] 文件落盘后由 mainline watchdog 编译；lane 不手跑 `lake/lean/sage/WSL`；回报只给路径/定理/gap。
- [ ] 编译失败回 S6；不手改编译结果；olean fresh/trio/零 sorryAx 才进 P5。
- **P4 gate**：watchdog `EXIT=0`、olean fresh、trio、零 sorryAx。

### Phase P5 — 审计与收口（S8）
- [ ] stage4 逐文件审计 + 证据隔离登记；条件/接口/GAP 标签；lana 口径。
- [ ] lattice 更新 `FINAL-STATUS`、`ROUTES`、`AUDIT_LEDGER` 指针；只写文件。
- **P5 gate**：无 §4 阻断；审计 PASS；无“未证说成证”。

## 4. 当前起点与本轮不做

- 当前只到 **S1 部分 / S3 初稿**：`DECOMP-PAIRING-CANDIDATES.md` 有 C1–C6 但未证；`R` 不可数值；`M=A−R` 符号化；无 Lean 恒等式文件。
- 本轮不写 Lean、不跑编译、不声称 M≥0；只搭工作流与分工。
- 明确禁止：代理 `M0`；等价改写；自由字段；手工编译；未审先标 PASS；把 R 的抽象字段当数值。

## 5. 报告格式

每个 lane 每步只报：`step | 产出路径 | 定理/定义名（无则写 NONE） | 已知 gap | 依赖节点`；不贴编译输出；watchdog 结果由 mainline 汇总。

## 6. 指针

- 目标分解/配对：`coord/DECOMP-PAIRING-CANDIDATES.md`；
- R 不可计算：`coord/C3M-FEASIBILITY.md`；R 生产：`coord/R-PRODUCTION-STATUS.md`、`C-R-FIELD-STATUS.md`、`C-LREAL-DATA-STATUS.md`；
- B 证明计划：`coord/B-PROOF-PLAN.md`；B1-FIX2：`coord/EXPLORATION-B-B1-FIX2.md`；
- 状态/审计：`coord/FINAL-STATUS.md`、`coord/EXPLORATION-ROUTES.md`、`AUDIT_LEDGER.md`、`coord/STAGE4-AUDIT-RESULT-A932.md`；
- DAG：`coord/DAG-NEXT.md`。
