# EVIDENCE-ISOLATION-REGISTRY — 主line green vs 上游 ported（A856）

日期：2026-11-12。维护者：stage4。**无 Lean 文件改动。**

## 0. 两条原则

1. **主line green（我们的文件）** = 位于本仓库、用我们的 toolchain（leanprover/lean4:v4.32.2）编译、
   并经 `#print axioms` 检查为 **trio `[propext, Classical.choice, Quot.sound]`** 的声明；只有这些可进最终证据链。
2. **上游 ported（脚手架）** = 任何外部仓库的源码/移植副本（vendor 树、ported 树、外部 clone）；
   **一律不进证据链**，只能作为参考/待移植对象。移植副本只有在「去 sorry/axiom + 编译 + trio gate」后才能升级为 green。

## 1. 主line green（我们的文件）清单口径

### 1.1 口径与权威记录

| 记录 | 内容 | 状态 |
|---|---|---|
| `coord/GREEN-INVENTORY.md` | tmp/sheaf/xif/paper 树快照：17,226 源文件 / 8,702 oleans / **8,525 green oleans（源与 olean 匹配）** / 177 orphan | 引用（qpilot/lead 快照） |
| `tmp/xif_guarded_results.log` | watchdog 队列的 EXIT 记录（224,682 行） | **历史**（watchdog 已停，最后更新 2026-11-11T17:39Z；尾部含旧队列 FAIL，不可当当前状态） |
| `dag/watchdog/runtime-status.json` | 13,064 节点：PROVED **13,030** / GAP 34；proved_like 13,030；fresh_ok 13,018；**mismatch 41** | 历史快照（17:32Z，watchdog 停前） |
| 每文件 `#print axioms` | trio 检查（项目 gate） | 当前唯一可用的逐步证据 |

**green 判定（三条件缺一不可）**：源码在仓库内 + olean 由我们 toolchain 生成 + `#print axioms` 仅 trio。
`GREEN-INVENTORY` 的 8,525 是「源/olean 匹配」计数，**不等于**每文件 trio 已验；最终主张必须以逐文件 axioms 打印为准。

### 1.2 本 lane（stage4）近期已验证文件（olean 存在 + `lake env lean` EXIT=0 + trio 打印）

| 文件 | olean | 备注 |
|---|---|---|
| Mzk1ThetaCancelActual | 有 | A805/A808：c_lana=ssCoeff 相消 + p=11 r=0 修正事实 |
| Mzk1P2DeficitActual | 有 | A804：p=2 log 归一化（r=1 ⇒ 0；r=2 仅记录） |
| Mzk1Stage4A703CorrectionActual | 有 | hfull 不可满足机器证明 + RETRACTED 台账 |
| Mzk1RetiredBoundaryAuditActual | 有 | A704 retired 清单 |
| Mzk1VendorCompileStatusActual | 有 | A712 vendor 编译状态 |
| Mzk1VendorRevisionConsistencyActual / V2 / V3 / V4 | 有 | A713–A719 import 一致性（broken=0） |
| Mzk1VendorOleanCoverageActual / V2 / V3 | 有 | A722/A724/A796 olean 覆盖快照 |
| Mzk1Stage4FinalBoundaryV2AuditActual | 有 | V2 边界审计（log-only） |
| Mzk1Stage4FinalSemanticsRegistryActual | 有 | 三态语义登记（7 行） |
| Mzk1Stage4BadSumNatRadicalActual | 有 | BadSumWeightBound natRadical 等价 |
| Mzk1Stage4Gap2StrengthRelationActual | 有 | Gap2 形状/强度关系 |
| Mzk1Stage4Gap2ArithmeticConsumerActual | 有 | Gap2 算术化 consumers |
| Mzk1Stage4BadSumTightnessActual | 有 | badSum=log N（historical，见 A703 retracted 标注） |
| Mzk1Stage4CorrectedRegionB1SupportActual | 有 | B1 支持引理（superseded supplementary） |

- 说明：上表为**本 lane 代表性清单**，不是全仓库 green 清单；全仓库以 `GREEN-INVENTORY` + 逐文件 axioms 为准。


## 2. 上游 ported（脚手架，不进证据链）清单

### 2.1 8 个 vendor 根树（A847 静态审计）

| root | lean 文件 | oleans | sorry | axiom 声明 | license 提及 | 证据状态 |
|---|---|---|---|---|---|---|
| Pi1 | 114 | 50 | 0 | 0 | 114/114 | 脚手架 |
| PadicLogVolume | 2 | 2 | 0 | 0 | 2/2 | 脚手架 |
| TateCurvesTheta | 78 | 78 | 3 | 0 | 78/78 | 脚手架（含 3 sorry） |
| TemperedFundamentalGroups | 744 | 576 | 1 | 0 | 744/744 | 脚手架（含 1 sorry） |
| Oka | 828 | 123 | 0 | 12 | 828/828 | 脚手架（含 12 axiom 声明） |
| EllipticCurves | 480 | 25 | 11 | 1 | 480/480 | 脚手架（含 11 sorry/1 axiom） |
| ContinuousKummerTheory | 38 | 22 | 0 | 0 | 38/38 | 脚手架 |
| FormalSchemes | 647 | 77 | 0 | 0 | 647/647 | 脚手架 |

### 2.2 外部移植树

| 树 | 规模 | sorry/axiom 状态 | olean/编译 | 证据状态 |
|---|---|---|---|---|
| `tmp/external/ported/flt`（Imperial FLT 移植） | 150 lean（19 Definitions@fermats-last-theorem 6e837e75 + 131 FLT@f6c6a2f） | **18 sorry / 15 knownin1980s（axiom 机制）** | 34/150 | **排除**（FLT-PORT-EVIDENCE-AUDIT §1） |
| `tmp/external/ported/lana` | 114 lean | 0 sorry / 0 axiom / 0 knownin1980s | 6 olean（A712 快照） | 脚手架 |
| `tmp/external/flt-lean`（anthropic P2M 分布） | Definitions 1,450 + P2M 29,507 + Theorems 29,504 | 源扫描 0 sorry/axiom/opaque；但 Theorems 为 `p2m_exact_reverting` 包装 | 未移植 | 脚手架（port 需 §7 方案） |
| FLT271（ImperialCollegeLondon/FLT@a3210204，v4.35.0；本地 `tmp/external/flt271`） | 271 lean（FLT 260 + FLTTest 2 + blueprint-verso 6 + ...） | **70 sorry / 3 axiom 声明**（`FLT/Assumptions/{KnownIn1980s,Mazur,Odlyzko}.lean`）；Patching 14 = 7 顶层 + 7 Utils，import 闭包 19 | 0 compiled | 脚手架（stage4 A868 复核；许可合规，需降级；不得进证据链） |
| `external/flt-lean-recon-20261016`、`external/fltport-prod-20261017` | 旧 recon/prod 树 | 未核 | - | 脚手架 |
| 其它 `tmp/external/*`（ClassFieldTheory、CompElliptic、iut-lean 系列等） | 未审 | 未核 | - | 脚手架 |

### 2.3 隔离规则

1. 上游文件/移植副本**不得**出现在最终证据链、不得写进 green 计数、不得作为 §12/3.12 的证明依据；
2. 引用上游只能作为「reference skeleton / 待 port 目标」，并在审计文档标注（FLT-PORT-EVIDENCE-AUDIT、PORT-SOURCES-AUDIT）；
3. 升级条件：去 sorry/axiom → 我们 toolchain 编译 → olean 与源匹配 → `#print axioms` trio（三条件全满足）；
4. 上游 `knownin1980s` 类 axiom、`opaque`/`implemented_by`/`extern`/`unsafe` 产生的额外公理：一律 FAIL。

## 3. 后台队列产物审计（#print axioms 抽检 / 上游隔离）

### 3.1 队列/构建状态（当前实测）

| 项 | 值 | 判断 |
|---|---|---|
| watchdog heartbeat | `running: 0, pending: 1007`；last at 2026-11-11T14:51:55Z | **已停**（lead 明示 watchdog 关闭） |
| `tmp/xif_guarded_results.log` | 224,682 行；最后写入 2026-11-11T17:39:23Z（距今 > 900s） | 历史记录，**不可当当前队列状态** |
| `dag/watchdog/extra-targets.txt` | 15 条（Iut/MainTheorem 等旧条目） | 旧队列残留（watchdog 停后不再消费） |
| `dag/watchdog/runtime-status.json` | 13,064 节点：PROVED 13,030 / GAP 34；fresh_ok 13,018；**mismatch 41** | 历史快照（17:32Z）；mismatch 41 需按需重审 |
| 后台 job（job_list） | **0** | 无运行中后台产物 |

**结论**：watchdog 停止后没有新的队列产物；当前所有 green 主张来自**手动单文件** `lake env lean` + olean 生成
（本 lane 近期 19 个文件全部 EXIT=0 + trio，见 §1.2）。历史 `runtime-status` 的 41 mismatch 与
`tmp/xif_guarded_results.log` 尾部的 EXIT=1 条目均为旧队列遗留，不作为当前证据。

### 3.2 #print axioms 抽检协议（当前唯一有效 gate）

对每个要主张 green 的文件：

1. 生成/确认 olean（`lake env lean -o .lake/build/lib/lean/<path>.olean <file>`）；
2. 写 probe（或直接用文件内 `#print axioms`）：`#print axioms <目标定理>`；
3. 期望输出仅 `[propext, Classical.choice, Quot.sound]`；
4. 机械判据：输出中不得出现 `sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler`、`knownin1980s`、
   `implemented_by`、`extern`、自定义 axiom 名；任一命中 ⇒ FAIL；
5. 上游隔离抽检：对 vendor 树抽样编译的模块同样跑 `#print axioms`（A847 静态扫描：Tate 3 sorry、TG 1 sorry、
   Oka 12 axiom 声明、EllipticCurves 11 sorry/1 axiom ⇒ 这些树中相应文件**一律不得进入证据链**）；
6. 本 lane 近期抽检结果：Mzk1ThetaCancelActual、Mzk1P2DeficitActual、Mzk1VendorRevisionConsistencyV4、
   Mzk1VendorOleanCoverageV3 等 `#print axioms` 均只含 trio（见各自构建输出）。


---

## 4. 链二（chain 2）审计与分类（A881）

### 4.1 产出盘点

| 产出 | 类型 | 编译/olean | 状态标注 | 审计判定 |
|---|---|---|---|---|
| `tmp/sheaf/xif/paper/Mzk1Chain2CoreActual.lean` | **MODEL** Lean 文件（Chain2Data/shellVolume/model_requirement_and_box/middle_case_exists/chain2_model_ssIneq） | 本轮 `lake env lean` **EXIT=0**，已生成 olean | 文件头明确 “MODEL (explicitly labelled, not paper objects)”；`chain2Rows` 每行标 MODEL DEF/PROVED/UNDETERMINED | **诚实**：未冒充 IUT 对象；`Chain2Data` = 纯数据模型 |
| `tmp/sheaf/xif/paper/Mzk1Chain2ContainerInterfaceActual.lean` | **DESIGN/interface**（Chain2LocalData + 三个 criteria，全部未评估） | olean 已有（此前） | 文件头 “DESIGN (not Lean objects from the paper; all fields are data/Props, no theorem claimed)”；rows DATA/CRITERION/NOT EXECUTED | **诚实**：仅接口，无结论 |
| `coord/CHAIN2-ATTACK.md` | 作战文档 | — | “链二存活，进入 Phase 2；…本文是接口/作战计划，不是证明；所有核心命题仍为 PENDING” | 状态可用，但标题“存活”易误读为数学结论 ⇒ 建议改为“程序性存活（Phase 2 接口）” |
| `coord/CHAIN2-CONTAINER-EXPERIMENT.md` | 实验设计 | — | “local experiment NOT EXECUTED; No survival claim” | 诚实 |
| `coord/CHAIN2-RESULTS.md` | 模型数值记录 | — | “MODEL-LEVEL numbers … NOT a proof of SSIneq and NOT a Lean result” | 标注诚实，但**数值有错**（见 §4.3） |
| `tmp/sheaf/xif/paper/S2570Chain2Actual.lean` | 旧 mod-613 多项式链（与链二无关，仅名称含 Chain2） | olean 已有 | — | **非链二**，不得计入 |

### 4.2 `#print axioms` 抽检（`Mzk1Chain2CoreActual`）

probe `tmp/a881_chain2_probe.lean`（`lake env lean` EXIT=0）：

| 声明 | axioms | 判定 |
|---|---|---|
| qPilotInFamily_holds | propext, Classical.choice, Quot.sound | ✅ trio |
| qPilotRegion_subset_possibleImage | 同上 | ✅ |
| model_requirement_and_box | 同上 | ✅ |
| middle_case_exists | 同上 | ✅ |
| chain2_model_ssIneq | 同上 | ✅ |
| chain2CoreRows_length | （无公理） | ✅ |
| Chain2ContainerInterfaceActual.chain2Rows_length | （无公理） | ✅ |

### 4.3 发现：`CHAIN2-RESULTS.md` 数值错误（doc-level，须由 owner 重算）

`CHAIN2-RESULTS.md` 的模型使用 “p=11, unramified, e=n=1, r=0 ⇒ logMuPaper = log 11 = 2.3979”，
但按绿色公式 `paperShellLogMu(p,e,r,n) = (1+[p=2]−1/e−r/n)·log p`：

- p=11, e=n=1, r=0 ⇒ 系数 = 1 − 1 − 0 = **0** ⇒ **logMuPaper = 0**（ROUTES 也注明“非分歧奇素数给 0”），不是 log 11；
- 文档中 “c = (l+4)(l−3)/(24l) = 54/120 = 0.45” 计算错误：l=5 时 (9·2)/(24·5)=18/120=**0.15**（= ssCoeff(5)）；
- 其余量没错：A = logQ/(2l) = log22/10 = 0.30910；V_req = (sFactor(2)−1)A = 1.5·0.30910 = **0.46365**；
  U = ((l+5)/4)log11 = 2.5·log11 = **5.9947**。

**按正确 logMuPaper 重算**：V(t) = 0 − t·log11 = −2.3979·t；要求 0.46365 ≤ V(t) ≤ 5.9947 ⇒
整数 t ∈ {−1, −2}（V=2.3979 / 4.7958）——**中间情形仍存在（结论 ALIVE 方向不变）**，但理由和表格全错：
原文档称 “G={0} 是 MIDDLE、任何含 t=0 且 t>−1.5 的 G 都行”是**错误**的（t=0 给 V=0 < req）。
⇒ `CHAIN2-RESULTS.md` 判为 **数值不可靠（需重算/改写）**；其“alive”结论在修正后仍成立，但须以 t=−1/−2 重写。

### 4.4 分类（证据链 / 研究记录）

| 类别 | 内容 | 说明 |
|---|---|---|
| **可入证据链** | 无（链二目前 0 项） | 链二尚未产生任何 IUT 对象或真实 Θ-data 定理；C2.1/C2.2/C2.3 均 PENDING |
| 仅研究记录（可引用为“模型/接口”） | `Mzk1Chain2CoreActual`（modelled, trio）、`Mzk1Chain2ContainerInterfaceActual`（design）、`coord/CHAIN2-ATTACK.md`、`coord/CHAIN2-CONTAINER-EXPERIMENT.md`、`coord/CHAIN2-RESULTS.md`（数值需修正） | `Chain2Data` 不得当作 IUT 对象；模型结论不得写入 3.12 证据 |
| 禁止计入 | `S2570Chain2Actual`（旧 mod-613 链） | 名称碰撞，非链二 |

**规则**：链二模型/接口文件即使 trio 通过，也只能作为 research record；升级为证据链的前提是：
(i) 把 `Chain2Data` 的 `baseShellVolume/logp/allowedLower/allowedUpper/qPilotOrd` 替换为真实 Θ-data/局部对象的计算值；
(ii) C2.1/C2.2/C2.3 成为可编译条件命题且中间 G 有非空数值实例；
(iii) 经 `#print axioms` trio gate 与 EVIDENCE-ISOLATION 登记。三点全部满足前，链二不得出现在最终证据链。

---

## 5. A884：G 候选源级核验 + 更新后链二 gate

### 5.1 G1/G2/G3（+G4）lana 引用核对（逐行，源级）

**核对基准**：仓库根 `Iut/` 树（不是 `tmp/sheaf/lana*` 旧副本；旧副本行号不同，引用时必须钉住根树）。

| ID | 引用 | 实测（根 `Iut/`） | 判定 |
|---|---|---|---|
| G1 | `LogLink/Thm311Rest.lean:473` `rlf_unique` | L473 = `theorem rlf_unique (B B' : ValBPS V bad) (h : B.PF = B'.PF) : Nonempty (Unique (B.Iso B')) := by` | ✅ 精确匹配 |
| G1 | 同文件 L478 `rlf_cocycle`、L490 `mem_rposOrbit_iff`、L529 `rlfData` 的 `unique` 字段、L78–90 文档 | L478 = `theorem rlf_cocycle ...`；L490 = `theorem mem_rposOrbit_iff ...`；L529 = `unique : ∀ a b, Nonempty (Unique ((rlfData L a).Iso (rlfData L b)))`；L78–90 = Thm 1.5(v)/ThetaLink 文档 | ✅ 全部匹配 |
| G1 | `ThetaLink/Link.lean:206` `scaling_iff` | L206 = `theorem scaling_iff (c : ℝ) (hc : 0 < c) : Nonempty ((GlobalRealified.scale c hc).obj (thetaPilotObj D) ≅ qPilotObj D) ↔ ...` | ✅ |
| G2 | `Concrete/Ind1Invariance.lean:110/144/192` | L110 `componentVol_image_linearEquiv`；L144 `componentVol_image_algEquiv`；L192 `IsLeastHull.componentVol_eq` | ✅ |
| G3 | `Concrete/LocalConstruct/ScaleVolume.lean:118`；`Prop14.lean:108` | L118 `componentVol_prod_incl_smul_integral`；L108 `componentVol_prime_pow_smul_integral` | ✅ |
| G4 | `Tripod/CyclicBound.lean:180/239/253`；`Tripod/CyclicIsogeny.lean:933` | L180 `h_eq_heightOn_graph_add`；L239 `def CyclicGraphBoundHyp`；L253 `cyclicBound_of`；L933 `theorem main_bound` | ✅ |
| 检索声明 | “`Step (xii)`/`xii` 在 lana 无命中” | 根 `Iut/` 与 `tmp/sheaf/lana_latest` grep `xii` = **0** 命中；根树仅 `Thm311Rest:621` 提 `Step (xi)` | ✅ 与 qpilot 说法一致 |
| olean 状态 | G1–G4 候选文件 olean 尚未产出 | `.lake/build/lib/lean/Iut/{LogLink/Thm311Rest,ThetaLink/Link,Concrete/Ind1Invariance,Concrete/LocalConstruct/ScaleVolume,Concrete/LocalConstruct/Prop14,Tripod/CyclicBound,Tripod/CyclicIsogeny}.olean` 全部 **不存在** | ✅ 与 qpilot “根构建队列中”一致；**引用目前只能是源级**（不可编译验证） |

⇒ **G1/G2/G3/G4 的 file:line 引用全部真实匹配**（根 `Iut/` 树，行号与声明名逐项核对通过）；
**唯一注意**：行号只对根树有效；`tmp/sheaf/lana*`、`tmp/online/*` 等旧副本行号不同，不得混用。

### 5.2 更新后 `Mzk1Chain2CoreActual` 的 `#print axioms` 抽检（fresh）

- 当前源文件 mtime 2026-11-11T18:49:06Z；`lake env lean` **EXIT=0**，已生成**新 olean**（mtime 18:49:44Z > 源）；
- probe `tmp/a884_chain2_probe.lean`（fresh，13 个声明）：

| 声明 | axioms | 判定 |
|---|---|---|
| qPilotInFamily_holds / qPilotRegion_subset_possibleImage / model_requirement_and_box | propext, Classical.choice, Quot.sound | ✅ trio |
| middle_case_exists / chain2_model_ssIneq | 同上 | ✅ |
| survival_iff | 同上 | ✅ |
| middle_case_exists_baseZero（修正后 base=0, allowedLower=-1 witness） | 同上 | ✅ |
| g1_union_eq_single / g1_allowedLower_unique / g1_survival_computable | 同上 | ✅ |
| g3_width_bound（新签名 `(budget) (h : G3Type D budget)`） | 同上 | ✅ |
| chain2ConstraintRows_length / chain2CoreRows_length | 无公理 | ✅ |

- 注：本轮首次编译曾瞬时失败（`g3_width_bound` 旧签名缺 `budget`）；owner 在 18:49:06Z 更新文件后 fresh 编译通过、olean 重新生成 ⇒ **最终状态 green（trio）**。

### 5.3 审计注记（模型层平凡性，防误读）

以下“PROVED”仅指模型层恒真/投影，不含 IUT 内容，不得当作链二已证：

- `g1_union_eq_single` 与 `g1_allowedLower_unique` 是 `rfl`/定义展开；
- `g1_survival_computable` 只是 `survival_iff` 的 re-export（未用 G1 假设）；
- `g3_width_bound` 是把假设 `h : G3Type D budget` 直接投影（`:= h`）；
- `chain2ConstraintRows` 的 4 条 lana 引用行标 “LANA (olean needed)” —— 在根 `Iut` oleans 产出前均不可编译验证。

⇒ 链二分类不变：**模型/接口，研究记录，非证据链**（升级条件见 §4.4）。新增的 G1/G3 类型化约束仅提高接口清晰度；
在 lana 候选 oleans 产出、且 C2.1/C2.2/C2.3 成为可编译条件命题前，不改变分类。

---

## 6. A888：`scaling_iff` 行号裁定 + rlf 行号实测

### 6.1 裁定

**基准**：仓库根 `Iut/` 树（`Iut/ThetaLink/Link.lean` 当前 **246 行**，`Iut/LogLink/Thm311Rest.lean` 当前 **634 行**）。

| 引用 | 说法 | 实测 | 裁定 |
|---|---|---|---|
| qpilot | `scaling_iff` @ `Iut/ThetaLink/Link.lean:206` | Link.lean **L206** = `theorem scaling_iff (c : ℝ) (hc : 0 < c) : Nonempty ((GlobalRealified.scale c hc).obj (thetaPilotObj D) ≅ qPilotObj D) ↔ ...`；同文件 L40 仅为 docstring 提及 | ✅ **正确** |
| lattice | `scaling_iff` @ `Iut/ThetaLink/Link.lean:559` | Link.lean **只有 246 行，不存在 L559**；L559 实际位于 **`Iut/LogLink/Thm311Rest.lean:559`**，内容是 **usage 站点** `frobScale c hc := scaling_iff D c hc`（Thm15v 实例字段），不是定理定义 | ❌ **错误（跨文件混行）**；正确为 `Link.lean:206`（定义），若引 usage 则 `Thm311Rest.lean:559` |
| 双方 | `rlf_unique` @ Thm311Rest:473 | L473 = `theorem rlf_unique (B B' : ValBPS V bad) (h : B.PF = B'.PF) : Nonempty (Unique (B.Iso B')) := by`（docstring L470） | ✅ 一致，正确 |
| qpilot | `rlf_cocycle`（L478+） | **theorem 在 L479**；L478 是 docstring `/-- The unique isomorphisms form a cocycle. -/` | ⚠ 行号应写 **479**（478 为注释行） |
| qpilot | `mem_rposOrbit_iff`（L490） | **theorem 在 L491**；L490 是 docstring | ⚠ 应写 **491** |
| 双方 | `rlfData` 的 `unique` 字段 523/529 | `def rlfData` 在 **L523**；`structure Thm15v` 的 `unique` 字段在 **L529**（`cocycle` 字段 L531） | ✅ 529 正确；523 是 rlfData 定义行，说“rlfData 的 unique 字段”应引 **529**（结构体字段），可同时引 523 定位 rlfData |

### 6.2 复核命令（可复现）

- `grep -n scaling_iff Iut/ThetaLink/Link.lean` ⇒ 仅 L40（doc）与 **L206**（theorem）；
- `grep -n scaling_iff Iut/LogLink/Thm311Rest.lean` ⇒ L90（doc）与 **L559**（`frobScale := scaling_iff D c hc`，usage）；
- `grep -n "theorem rlf_unique|theorem rlf_cocycle|theorem mem_rposOrbit_iff|def rlfData|unique :" Iut/LogLink/Thm311Rest.lean` ⇒ **473 / 479 / 491 / 523 / 529**；
- 旧副本行号（`tmp/sheaf/lana*`、`tmp/online/*`）略有漂移（如 Link.lean:205 或 206），**不得混用**；引用必须钉住根 `Iut/`。

### 6.3 处置建议

1. `coord/CHAIN2-ATTACK.md` 中 lattice 的 `scaling_iff @ Link.lean:559` 改为 `Link.lean:206`；
   若要引“唯一 1/s 缩放”的使用点，可并列 `Thm311Rest.lean:559 (frobScale := scaling_iff D c hc)`；
2. qpilot 的 `rlf_cocycle:478`、`mem_rposOrbit_iff:490` 建议改为 theorem 行 **479 / 491**（478/490 为 docstring 行）；
3. 所有 lana 行号引用统一注明树根（`Iut/`），并在需要时附 grep 证据；
4. 该裁定不改变 G1/G2/G3 的语义与链二分类（研究记录，非证据链）。

---

## 7. A896：证据版本钉死（根 `Iut/` 树权威）+ 失效引用清单

### 7.1 权威版本

**唯一权威**：仓库根 `Iut/` 树。当前关键文件指纹（2026-11-12 实测）：

| 文件 | 行数 | sha256 前 16 位 | 关键声明行 |
|---|---|---|---|
| `Iut/LogLink/Thm311Rest.lean` | **634** | `ee557313f3010dd0` | `rlf_unique` **L473**；`rlf_cocycle` **L479**；`mem_rposOrbit_iff` **L491**；`def rlfData` **L523**；`Thm15v.unique` **L529** |
| `Iut/ThetaLink/Link.lean` | 246 | — | `theorem scaling_iff` **L206**（L40 为 docstring） |
| `Iut/Concrete/ThetaRegion.lean` | 387 | — | `def Cor312VariantHolds` **L375** |
| `Iut/WallEquiv/Gap.lean` | 1004 | — | `variant_of_ss_gap` **L543**；`SSIneq ↔ Corollary312Variant` **L549** |
| `Iut/Tripod/Main.lean` | 135 | — | `abc_of_variant` **L120** |
| `Iut/Tripod/ClassicalAbc.lean` | 290 | — | `classicalABC_of_statementI` **L286** |
| `Iut/Wall/Constraints.lean` | 342 | — | `wall_idAlgOn_iff` **L304** |
| `Iut/WallEquiv/Basic.lean` | 198 | — | `exists91_iff_ss` **L116** |
| `Iut/MainTheorem.lean` | 40 | — | `classicalABC_of_variant` **L36** |
| `Iut/Abc/FormalConjectures.lean` | 244 | — | `classicalABC_iff_ltConstantMul` **L146** |
| `Iut/LogLink/GalKummer.lean` | — | — | `xi_iff_ss` **L386/L420** |

### 7.2 `tmp/` 副本作废声明（不得引用其行号）

以下副本为历史/旧 revision，**行号与根树不一致**，只可作只读研究材料，不得作为引用依据：

| 副本 | 实测 | 与根树关系 | 判定 |
|---|---|---|---|
| `tmp/sheaf/lana/iut/Iut/...` | `Thm311Rest.lean` **586 行**，`rlf_unique` **L427**；`Link.lean` `scaling_iff` **L205**；hash `8a0c2998d3030744` | 旧 revision，行号严重漂移（427 vs 473） | **作废（不得引用行号）** |
| `tmp/sheaf/lana_latest/Iut/...` | 633 行，`rlf_unique` **L472**；`Link.lean` **L205**；hash `2c44918d8b96784c` | 近根树但 off-by-one/内容有差 | **作废（引用前必须核对）** |
| `tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut/...` | 586 行，`rlf_unique` **L427**；hash `1ae81f1a22d7c33d` | 旧 revision | **作废** |
| `tmp/online/lana-agents__iut/iut-main/Iut/...` | 634 行，`rlf_unique` **L473**；hash `ee557313f3010dd0`（=根树） | 与根树同 revision | 可作镜像核验，但引用仍以根 `Iut/` 为准 |
| `tmp/external/ported/lana/Iut/...` | 仅 114 文件子集；`LogLink/Thm311Rest.lean`、`ThetaLink/Link.lean` **不存在** | 部分移植 | **作废（覆盖不足）** |

⇒ **规则**：所有 lana 引用必须写 `Iut/...` 根路径 + 行号，并注明“根 `Iut/` 树”；凡引 `tmp/sheaf/lana*`、`tmp/dsh-oct6-*` 行号的文档一律视为**失效引用**。

### 7.3 链二文档引用核对（全部钉住根树）

| 文档 | 引用 | 核对 | 状态 |
|---|---|---|---|
| CHAIN2-ATTACK.md L61–63/L150/L156 | G1 rlf（473/479/491/523/529）+ Link.lean:206 + G2 110/144/192 + G3 118/108 | 全部与根树实测一致；L61 明写“根 `Iut/` 树” | ✅ 有效 |
| CHAIN2-G-CANDIDATES.md L7–9/L19–22/L27–28/L32/L35 | 同上 + CyclicBound 180/239/253 | 与根树实测一致；L27 明写“源（根 `Iut/` 树）” | ✅ 有效 |
| CHAIN2-CORE.md / VOLUME-DATA.md / PHASE2.md / RESULTS.md / CONTAINER-EXPERIMENT.md | 无 `Iut/...:line` 引用（0 条） | — | ✅ 无风险 |

（唯一小瑕疵：CHAIN2-ATTACK L144 引 `Iut/WallEquiv/Gap.lean:530-549` 为区间；530 是 docstring、543 是 `variant_of_ss_gap`、**549 才是 `SSIneq ↔ Corollary312Variant`**，建议精确到 543/549。）

### 7.4 单-sorry 文档失效引用清单

`coord/SORRY-ACCEPTANCE.md` 中以下引用**失效**：

| 位置 | 失效引用 | 实际 | 修正 |
|---|---|---|---|
| §0/§1(1)/§6（3 处） | `Iut/Cor312/Concrete/ThetaRegion.lean:375` | **路径不存在**（根树无 `Iut/Cor312/Concrete/`）；`def Cor312VariantHolds` 实际在 **`Iut/Concrete/ThetaRegion.lean:375`**（387 行文件） | 改为 `Iut/Concrete/ThetaRegion.lean:375` |
| 依赖构建节 | `Iut/Cor312/Concrete/*` 构建列表 | 路径不存在 | 改为 `Iut/Concrete/*`（或按实际模块列表） |
| §3 备选 walls | `Iut/LogLink/*` `xi_iff_ss`（通配） | 实际 `Iut/LogLink/GalKummer.lean:386` 与 `:420` 两处 `xi_iff_ss` | 精确到 `GalKummer.lean:386/420` |
| §0 计划 | `ThetaRegion.lean:375`（无目录） | 见上 | 加 `Iut/Concrete/` 前缀 |

**已核对有效的 SORRY-ACCEPTANCE 引用**：`Iut/WallEquiv/Gap.lean:543`（`variant_of_ss_gap` ✓）、`Iut/MainTheorem.lean:36`（`classicalABC_of_variant` ✓）、`Iut/Tripod/Main.lean:120`（`abc_of_variant` ✓）、`Iut/Tripod/ClassicalAbc.lean:286`（`classicalABC_of_statementI` ✓）、`Iut/Wall/Constraints.lean:304`（`wall_idAlgOn_iff` ✓）、`Iut/WallEquiv/Basic.lean:116`（`exists91_iff_ss` ✓）、`Iut/Abc/FormalConjectures.lean:146`（`classicalABC_iff_ltConstantMul` ✓）、`Iut/Abc/Classical.lean`（`ClassicalABC` def ✓）、`Iut/LogLink/GalKummer.lean:386/420`（`xi_iff_ss` ✓）。

### 7.5 处置

1. `SORRY-ACCEPTANCE.md` owner（abc）：修正 §7.4 三处路径 + `Iut/Cor312/Concrete/*` 构建列表 + `Iut/LogLink/*` 通配引用；
2. `CHAIN2-ATTACK.md` owner（lattice/qpilot）：Gap 区间引用精确为 `L543`/`L549`；
3. 所有 lane：今后 lana 引用一律 `Iut/` 根 + 注明树根；禁用 tmp 副本行号；
4. 本 registry 为准（§5–§7）；任何新文档引用与本节冲突时以根树实测为准。

---

## 8. A932：E4/E1/框架/C0/B 证书批次审计（trio 全过；分类登记）

### 8.1 `#print axioms` 抽检（probe `tmp/a932_probe.lean`，`lake env lean` EXIT=0）

7 个文件 28 个声明全部通过：

- 全部为 `[propext, Classical.choice, Quot.sound]` 或子集（`rankThree_certificate` 仅 `[propext]`）；
- `*Rows_length` 声明无公理；
- **无 `sorryAx`、无外部 axiom**；olean 均新鲜（olean mtime > source mtime）。

### 8.2 分类表

| 文件 | 分类 | 可入证据链？ | 依据/缺口 |
|---|---|---|---|
| `Mzk1E4DictionaryActual` | **INTERFACE** | ❌ | `RegionLe`/`E4Dictionary` 为泛型 def；`E4Dictionary_iff` = `Iff.rfl`，`e4_inequality` 只是应用，`e4_of_unconditional` = `fun _ => h`；**未构造实际 P/VolShell**，E4 对真实对象 = GAP；文件头已诚实声明 |
| `Mzk1E1ConcreteActual` | **PROVED-CONDITIONAL + MODEL + GAP** | ❌（条件定理可引用，模型数据不可） | `qSideContribution_eq_zero_of_order_zero`、`E1PaperScaledHull_of_order_zero` 基于绿色定义（真实 P）✓，但前提 `P.line.C3.q.order = 0` 未证；`ConcreteDatum`（l=5, bad {2}/{2,11}）与 `concreteQSide` 为 **MODEL**；**actual `PaperQPilotObjectActual` 构造未做 = GAP**（rows 已自标） |
| `Mzk1OurFrameworkABCActual`（更新版） | **CONDITIONAL / INTERFACE（非 ABC 进展）** | ❌ | `ourFramework_ABCConjecture : OurFrameworkAssumptions → ABCConjecture`，但证明只消费 `A.E3_interface : ClassicalABCNatShape`（与 ABC 等价）⇒ **以 ABC 等价输入得 ABC，逻辑上成立但无新内容**；E1/E4 字段记录未用；**E2 是无约束 `Prop`（无任何内容，不可当假设钩子）**；未 import 新 `Mzk1E4DictionaryActual`（E4 走 `Face5ConstructionObligation`）⇒ 与“E4 接入”表述不符，需 owner 澄清 |
| `Mzk1C0TargetsActual` | **CONDITIONAL-PROVED（target 形式）+ INTERFACE（gap 谓词）+ PARTIAL** | ❌（仅条件接口） | T1/T1'/T2 为纯算术蕴含（显式 `hdef/hθ/hscaled/horth` 假设；trio）；`TensorMetricOrthogonality`/`TensorAutCommutationDefect` 仅是 Prop 谓词；Status: PARTIAL + 试金石 defer + 判定句 + E-C0-1..3 登记齐全；lana 引用根树行号**实测有效**（Gap.lean 747-754/756/771/895/961/30-36/459/463/66） |
| `Mzk1C0Ind2ArchActual` | **MODEL + PARTIAL** | ❌ | `Ind2Data`/`ArchDefectData` 为模型结构；`ind2Term_nonneg`/`lt_logp`/`eq_zero_iff`/`pos_iff`/`archDefect_model_nonneg` 证明的是**模型性质**；`ArchDefectValueGap` 明确记录识别缺口；tensorAut 推导与 archDefect 识别均 GAP（依赖 lana） |
| `Mzk1BCertificateFullActual` | **PROVED-ARITHMETIC（rank-2 MODEL）** | ❌ | `rfRankTwo := 5`；`rankTwo_certificate : rfRankTwo ∣ D.c`（由 4 条整数方程 `linarith`，trio）——是 **rank-2 模型算术核心**，非一般证书引理；一般秩 = GAP（quotient/finrank） |
| `Mzk1BCertificateGeneralActual` | **PROVED-ARITHMETIC（rank-3 MODEL）** | ❌ | `rankThree_certificate : (5:ℤ) ∣ c`（`[propext]` 子集）、`second_coordinate`、`third_zero` 均为 rank-3 模型算术；一般有限秩 GAP（`Submodule.index/quotient` 或 Smith 标准形；rows 提到 TauCetiPort API 线索） |

### 8.3 关键裁定

1. **本批无一项可进最终证据链**：E4 是接口（无实际对象）、E1 只有 order=0 的条件定理、框架文件以 E3（ABC 等价）为输入（循环式装配，不是 ABC 证明）、C0 是条件形式/模型、B 证书是 rank 2/3 模型算术；
2. **"已证"仅限**：E1 的 order=0 蕴含（真实绿色定义，条件）、C0 T1/T1'/T2 条件算术形式、B rank-2/3 模型算术核心；引用时必须带条件/模型标签；
3. **"条件"**：E1PaperScaledHull_of_order_zero、ourFramework_ABCConjecture（E3 输入）、C0 target 形式；
4. **"接口"**：E4Dictionary 全部、C0 的 TensorMetricOrthogonality/TensorAutCommutationDefect 谓词、OurFrameworkAssumptions（E2 空 Prop）；
5. **"GAP"**：E4 实际 P/VolShell 构造、E1 实际 P 构造、C0 tensorAut 推导与 archDefect 识别、B 证书一般秩、OurFramework 的 E1/E2/E4 实际内容；
6. **需 owner 澄清**：`Mzk1OurFrameworkABCActual` 的“E4 接入”实为 `Face5ConstructionObligation`，未接新 `Mzk1E4DictionaryActual`；E2 为空 Prop，建议删除或填真实陈述；E3 是 ABC 等价输入，最终步骤是条件装配。

### 8.4 合规备注（按 EXPLORATION-AUDIT 模板）

- 状态标注：C0 两文件已带 Status/PARTIAL/试金石 defer ✓；E4/E1/框架/B 证书文件头有“label/GAP/conditional”说明，但无模板六态 Status 行；
- 试金石：本批多为接口/模型/条件，均无不等式主张；建议按模板各补一句 defer（C0 两文件已写）；
- 外部登记：C0 的 E-C0-1..3 是 lana 内部 gap，建议标 G-C0 而不是 E-C0（与外部文献假设区分）；OurFramework 的 E1–E4 是假设字段，其中 E3 应标“ABC-equivalent input”；
- 版本钉住：C0 两文件 lana 引用为根 `Iut/` 行号且实测有效 ✓；其余无 lana 引用；
- 本批均不改变 registry §1 的 green 计数（它们不进入主链证据）。

---

## 9. A938：A932 结果指针同步 + `lana-transitive` 标签 + ABC delta 审计

### 9.1 结果文件指针

- A932 队列审计详细结果：`coord/STAGE4-AUDIT-RESULT-A932.md`（逐文件行、清单、复现命令）；
- 本 registry §8 为摘要；两者冲突时以结果文件 + 本 §9 的 hash 钉住为准；
- 旧 A932 快照（`Mzk1OurFrameworkABCActual` hash `8052B1EF…`，2,642B）**作为历史保留**，仅用于当时审计记录，不得对当前文件引用其结论。

### 9.2 `lana-transitive` 标签（lattice 澄清口径）

按严格 lana-free 口径（**import 闭包不得出现任何 `Iut.*`**）：

| 文件 | 直接 import | 闭包 | 标签 | lana-free citable？ |
|---|---|---|---|---|
| `Mzk1E1ConcreteActual.lean`（`0298633FF022292F`） | 全为 green LeanFormal/Mathlib | 经 `Mzk1E1DictionaryActual → Mzk1VPaperActual → … → tmp/sheaf/n8/closure/SourceInputBinding` 到达 `Iut.Foundations.Frobenioid`（18 条 lana 边中有 1 条此路径） | **`lana-transitive`** | ❌；仅“条件接口/wiring”口径可引用，且不得用其支撑任何 lana 事实 |
| `Mzk1OurFrameworkABCActual.lean`（当前 `983A95B0…`；历史 `8052B1EF…`/`9A4B9B11…`） | 全为 green LeanFormal/Mathlib（imports: ABCBridge/E1Dictionary/E4Dictionary/StepVVolumeUpper/Face5Proof/E1Order） | 同上（闭包 442 模块，18 条 lana 边，均经既有 green LeanFormal 模块） | **`lana-transitive`** | ❌；仅条件接口/wiring 可引用 |
| `Mzk1E4DictionaryActual.lean` | `import Mathlib.Tactic` | 纯 Mathlib | **lana-free** | ✅ 接口可 citable |
| `Mzk1C0TargetsActual.lean` | `import Mathlib.Tactic` | 纯 Mathlib | **lana-free** | ✅ 条件目标可 citable |

### 9.3 ABC 文件 delta 审计（A938）

| 版本 | hash | size | 状态 | 审计结论 |
|---|---|---|---|---|
| 旧快照（A932 审过） | `8052B1EF16C81EE8` | 2,642B | 历史 | E2 空 Prop、E4=Face5 未接 E4Dictionary、声明 4 个；仅历史参考 |
| lattice 钉住版（A933） | `9A4B9B11E44D5C52` | 4,274B | **已被后续编辑覆盖，当前不在盘上** | 其 olean（11:19:31Z）可加载：`ourFramework_ABCConjecture`/`E1`/`E2`/`E4` 均 **trio**、`assumptionInterfaceRows_length` 无公理 ⇒ 与 lattice 描述的“E2 真实化 + E4 接 E4Dictionary”一致（**oleans 级验证；文本级未能重读**） |
| **当前 HEAD** | **`983A95B0BB021168`** | **5,238B**（src 11:25:55Z；olean 11:19:31Z **过期**） | **EXIT=1（2 errors）** | **不可认证**：① L80/L87 `unfold Mzk1E1OrderActual.E1AllocationForm at A/h` 失败（该 def 有显式参数；应 `exact A.E1_allocation` / `simpa [Mzk1E1OrderActual.E1AllocationForm] using h` 后再 `rw [hq]`）；② L109 在 `List (String × String)` 中放了 3-tuple（应改列表类型为 `String × String × String` 或去掉第三项） |

**delta 语义（源码级，未认证）**：
- `E2VolumeUpper` 已定义（真实 `V ≤ ((l+5)/4)·logdf logd logf + C0`，`logdf = logd + logf` 来自 green `Mzk1StepVVolumeUpperActual`），`ourFramework_E2` 消费 `E2_volume_upper` ✅（源码可见）；
- `E4` 已接 `E4Dictionary`（来自 `Mzk1E4DictionaryActual`），`ourFramework_E4 := e4_inequality A.E4_dictionary A.E4_containment` ✅（源码可见）；
- **`E4_face5 : Face5ConstructionObligation` 仍未被任何声明消费**（仅字段）⇒ lattice 说法成立；建议删除或补 bridge（不阻断）；
- `ourFramework_ABCConjecture` 仍只消费 `E3_interface`（ABC-equivalent）⇒ 仍为条件装配、非 ABC 证明；
- 新增 `ourFramework_E1_allocation`/`ourFramework_E1_of_qSide_zero`（E1 分配形式）但当前编译失败：不可认证。

### 9.4 当前阻断判定

**ABC 文件当前 HEAD 处于“owner 编辑中/未完成”状态**：源码 hash `983A95B0…`、olean 过期、独立编译 EXIT=1（2 个可修复错误）。
按队列 §4-1（olean 非当前源码重编）与 §4-3（语义声明未认证）**不能给 green/可 citable 结论**，需 owner：
1. 修复上述两处编译错误（或回退到可编译的 `9A4B9B11…` 版本）；
2. 重新编译并生成新 olean，给出新 hash；
3. 重跑 `#print axioms`（含 `ourFramework_E2`/`E4`/`E1_allocation`）与零 sorryAx 检查；
4. 之后 stage4 按新 hash 复审 delta。

---

## 10. A940：ABC 最终 hash `4E7BAF5A…` 复审 → **REJECT（阻断）**

| 项 | 实测 | 判定 |
|---|---|---|
| SHA | `4E7BAF5AF3272752D51BE3658B4AE8248E6372C04D6EECDFD83EF07757DCD6DA`（5,457B，src 11:34:36Z） | 与 lattice/lead 报告一致 ✅ |
| 独立编译 | `lake env lean` **EXIT=1**，2 errors：L92-94 `ourFramework_E4_face5 := A.E4_face5`（字段已删、`Face5ConstructionObligation` 未定义 ⇒ 自动隐式变量 + invalid field） | ❌ 不能编译 |
| olean | 234,760B @ 11:35:02Z（mtime fresh）但**内容不匹配源码**：probe 显示 olean 中 `ourFramework_E4_face5` unknown；其余 6 声明 trio | ❌ 非当前源码重编 |
| E2/E4 | 源码与 olean 均证实 E2 真实量由 `ourFramework_E2` 消费、E4Dictionary 由 `ourFramework_E4` 消费 | ✅（仅限“好版本”语义） |
| E4_face5 | 字段已删 ✅；`Mzk1Face5ProofActual` import/open 已删 ✅；**但 `ourFramework_E4_face5` 定理残留**（唯一编译错误） | ❌ 残留 |
| 语义 | 条件装配、只消费 E3、非 ABC 证明 | ✅ |

**结论**：`4E7BAF5A…` **不通过**（源码 EXIT=1 + olean/源码不匹配）⇒ 不得登记 green、不得 citable；历史 hash `8052B1EF…`/`9A4B9B11…`/`983A95B0…` 亦仅历史。
**修复**：删除残留 `ourFramework_E4_face5` 定理（L92-94）→ 重编 → 新 olean → 新 hash；再由 stage4 复审。

---

## 11. A941：`Mzk1CompletionUnconditionalActual` 审计（PASS，附 lana-transitive）

| 项 | 实测 | 判定 |
|---|---|---|
| src SHA | `9ABB87A3D663ACC37FC8581C51196A5DEEBBBB62AA38DAF52910C5CD58146A4D`（5,409B；mtime 11:39:48Z） | ✅ 与 hull 报一致 |
| olean | SHA `440DCA48EE09F61FD62897951EA782EA91B37D8F70E60B73E253D0409DC5A887`；342,624B；mtime 11:40:42Z > src | ✅ fresh |
| 独立 `lake env lean` | **EXIT=0**，文件内 4 个 `#print axioms` 均为 trio | ✅ |
| probe（11 声明：instance/valExpVal/unitValExp 系列/4 主定理） | 全部 `[propext, Classical.choice, Quot.sound]`；**零 sorryAx**；无 axiom 声明 | ✅ |
| instance bridge | `@[implicit_reducible] def commonPrimeCompletionValued := inferInstanceAs (Valued (Completion place.val) ...)`；`#print` 证实为 **def（结构构造）**，不是 axiom；`CommonPrimeCompletion := NormalizedCompletion place.val`（定义等式） | ✅ definitional |
| 语义（无条件性） | `no_natRootSystem_of_valExp_pos`：对任意 `K`/`p`/`place`、任意 unit `u`，`0 < unitValExp place u → ¬ Nonempty (NatRootSystem u)`（纯指数整除论证，无额外假设）；`completionFirstFieldObstruction_empty`、`actualCompletionRootBlock_empty`、`oldSourcePilotWithActualCore_empty` 对任意 `I : OriginalInput l (FinitePrimePlace 2 7)`、任意 `placeI`、具体 q candidate **无条件**成立 | ✅ 真无条件（相对于数据对象 `OriginalInput` 与 `FinitePlaceAtPrime`；不是 axiom/sorry） |
| 依赖定义 | `NatRootSystem`（`LeanFormal/IUT/IUTII/Kummer/NatRootSystem.lean:17`，无 sorry/axiom）、`CommonPrimeCompletion`（`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCommonPrimeCompletion.lean:20`）均为我们的 green 定义 | ✅ |
| import 闭包 | 123 模块，**1 条 lana 边**：`LeanFormal.IUT.IUTII.Kummer.ContinuousKummerGerm -> Iut.Foundations.ContinuousH1` | ⚠ **lana-transitive**（非 lana-free citable；与 E1/ABC 同口径） |

**结论：A941 通过**（EXIT=0、olean fresh、trio、零 sorryAx、instance bridge definitional、主定理对实际 place/q 无条件）；citable 口径按 **`lana-transitive`**（仅条件/接口/内部结论可引用，不得作 lana-free 证据）。

## 12. A942：`Mzk1OurFrameworkABCActual` 定版 `5AA68ED7…` 复审（**PASS**）

| 项 | 实测 | 判定 |
|---|---|---|
| src SHA | `5AA68ED7F613838112FFE642D9476A5A6039D21FEF9CFAEBFAEB1254C0725BED`（5,246B；mtime 11:39:09Z） | ✅ 与 lattice 定版一致 |
| olean | 234,760B；mtime 11:41:12Z > src；SHA 前缀 `F94B60E7D839A44B` | ✅ fresh |
| 独立编译 | **EXIT=0**（0 errors / 0 warnings） | ✅ |
| `E4_face5`/`Face5ConstructionObligation`/`Face5Proof` 引用 | 源码 **0 个** | ✅ 残留已删 |
| olean↔源码一致性 | probe：`ourFramework_E4_face5` **unknown identifier**（olean 来自无该定理的最终源码）；`ourFramework_ABCConjecture`/`E1`/`E1_allocation`/`E1_of_qSide_zero`/`E2`/`E4` 六个声明均 **trio**；`assumptionInterfaceRows_length` 无公理；零 sorryAx | ✅ 一致 |
| E2/E4 消费 | `ourFramework_E2` 返回 `E2_volume_upper`（真实 `E2VolumeUpper`）；`ourFramework_E4 := e4_inequality A.E4_dictionary A.E4_containment` | ✅ |
| 语义 | 条件装配：`ourFramework_ABCConjecture` 只消费 `E3_interface`（ABC-equivalent）；E1/E2/E4 为上游显式字段；**不是 ABC 证明**；`lana-transitive` 标签保留 | ✅ |

**结论：A942 通过（无阻断）**：SHA/olean/EXIT/trio/sorryAx/语义全部符合；citable 仅限“条件接口/wiring（lana-transitive）”，不得当 ABC 证明或 lana-free 证据。

## 13. A943：`Mzk1E1ExplicitCounterexampleActual` 审计（PASS，局部反例）

| 项 | 实测 | 判定 |
|---|---|---|
| src SHA | `7FABE3E4AB3411FEF63E124F584AC8832A1532F90F013321057BC92D797767D9`（2,271B；mtime 11:44:18Z） | ✅ |
| olean | 22,504B；mtime 11:44:47Z > src；SHA 前缀 `955B739F…` | ✅ fresh |
| 独立 `lake env lean` | **EXIT=0** | ✅ |
| probe（`explicitQCandidate` 及 3 条导出声明） | 全部 `[propext, Classical.choice, Quot.sound]`；零 sorryAx；无 axiom | ✅ |
| 语义 | `explicitQCandidate` 由 green `finitePlaceQCandidate_nonempty` 经 `Classical.choice` 选取（definitional，非 axiom）；`explicitQCandidate_exponent_pos`（exponent>0）、`explicitQCandidate_qSide_ne_zero`（`localSignedLog < 0` ⇒ `QSideContribution ≠ 0`）、`bareE1_false_for_explicit_local_q`（由 `e1_iff_qside_zero` 得裸 E1 假） | ✅ 显式局部反例成立 |
| 完整性 | 文件自述：“parameterized explicit-data counterexample, **not a full SourceDefinition31Data term**” ⇒ **完整 `SourceDefinition31Data` 反例仍缺** | ⚠ 局部/参数化反例，非全域反例 |
| import 闭包 | 13 模块，**0 条 lana 边** | ✅ **lana-free** |

**结论：A943 通过**（EXIT=0、olean fresh、trio、零 sorryAx）：确证“显式 q candidate exponent>0、局部 qSide≠0、裸 E1 不成立”；限制：不是完整 `SourceDefinition31Data` 反例（需另行构造/登记）。

---

## 14. A947：E1Concrete/E4 delta + `Mzk1QPilotLineLActual` + FINAL-STATUS 一致性

### 14.1 `Mzk1E1ConcreteActual`（新 `5DBD8772…`）—— PASS（doc-only delta）

| 项 | 实测 |
|---|---|
| src SHA / size / mtime | `5DBD87729C1D1DB3DC702A16C5411CA6914E054F16506C43400F799D94D5BE3D` / 5,306B / 11:46:06Z |
| olean | 164,864B @11:47:05Z，fresh |
| 独立编译 | EXIT=0，0 errors/warnings |
| probe | 3 定理 trio + `e1Rows_length` 无公理；零 sorryAx |
| delta 内容 | **仅文档**：A943 update 段（引用 E1 反例；正确接口 = `E1AllocationForm`）+ Audit status（PARTIAL、试金石 defer、GAP actual P）；数学/结构/imports 未变，**无新假设** |
| 分类 | PROVED-CONDITIONAL + MODEL + GAP；**lana-transitive**（闭包经 green 到 lana） |

### 14.2 `Mzk1E4DictionaryActual`（新 `49F0501B…`）—— PASS（doc-only delta）

| 项 | 实测 |
|---|---|
| src SHA / size / mtime | `49F0501BC62A489825304EEBA28F7E8E360D2D093EDDFFEFD7CD73A5D855794C` / 3,723B / 11:46:06Z |
| olean | 77,960B @11:47:33Z，fresh |
| 独立编译 | EXIT=0，0 errors/warnings |
| probe | 4 定理 trio + `e4Rows_length` 无公理；零 sorryAx |
| delta 内容 | **仅文档**（A943 update + Audit status PARTIAL/试金石 defer/GAP）；接口与定理未变；imports 仍 `Mathlib.Tactic`；**无新假设** |
| 分类 | INTERFACE；actual P/VolShell 未构造、E4 GAP；**lana-free** |

### 14.3 `Mzk1QPilotLineLActual`（`A1765858…`）—— PASS（parametric/interface）

| 项 | 实测 |
|---|---|
| src SHA / size / mtime | `A1765858D81AD8BB53EA81B5B6DA8E96C3D8C4930D3ACD40968126BE33CFC888` / 3,906B / 11:51:53Z |
| olean | 180,024B @11:52:41Z，fresh |
| 独立编译 | EXIT=0 |
| sorry/axiom | 源 0 sorry / 0 admit / 0 axiom；probe 3 定理 trio + rows_length 无公理；零 sorryAx |
| 语义 | L-carrier 接口：`QPilotLineActualL`（C1 `SourceInputBinding`、C2 `SourceLogKummerData`、C3L `SourcePilotRegionDataL`）；`core := sourcePilotRegionLToCore I L.C3L`；`qScalar_neg` 由 `localSignedLog_neg`；两个 nonempty 定理均 **parametric**（需 C1/C2/C3L 或 object）；rows 如实标 **C1/C2 源义务 OPEN** |
| 依赖 | `S1391C3LSourcePilotActual` 的 `SourcePilotRegionDataL`/`sourcePilotRegionLToCore`/`actualSourcePilotRegionDataL` 为 green 定义；闭包 294 模块、**16 条 lana 边** |
| 分类 | PROVED-PARAMETRIC + INTERFACE（**非** actual q-pilot 构造）；**lana-transitive**，非 lana-free citable |

### 14.4 `coord/FINAL-STATUS.md` 一致性 —— PASS

- 资产表 **18 项 hash 实测全部匹配**（Lean：ABC `5AA68ED7…`、Completion `9ABB87A3…`、E1 反例 `7FABE3E4…`、E1Order `8B67B543…`、E4 `49F0501B…`、E1Concrete `5DBD8772…`、C0Targets `2D1649F1…`、C0Ind2Arch `39FD73B4…`、BFull `2D20DA0E…`、BGeneral `ED2BEF73…`、BLemma `865D6E94…`；数据：c1_margin_v2 `E7DACBE4…` 117,581B、c2_invariants.jsonl `619404CE…` 64,336,856B、b1 csv `DA5F9FE2…`、b1 json `8BC9D642…`、b1_curves_500.json、a3_support `A1E461CF…`）；
- 数据口径：c1 4154 行、c2 4154 行、a3 80 样本、b1 941 行/109 found —— 与文中声明一致；
- **无“未证说成证”**：文件头明写 ABC 未无条件证明；仅有的“无条件”为旧 schema 不可能性（A941 PASS）与“B 线无无条件上界”的否定澄清；“已证”为 lana 引理或“不是已证事实”；
- housekeeping：E4/E1 行“待 delta 复审”已在 §14.1/14.2 解决，建议更新为 PASS；`Mzk1QPilotLineLActual` 未列入资产表，建议补（分类 PROVED-PARAMETRIC/INTERFACE、lana-transitive、C1/C2 OPEN）。

---

## 15. A951：`Mzk1QPilotLogNonposActual` 审计（PASS）

| 项 | 实测 |
|---|---|
| src SHA / size | `A70D3BAF9EFC85FA528DD15AD87F0FF1C76E955FD49E43646116F9C4747FC51F` / 1,773B |
| olean | 13,536B @11:59:28Z，fresh |
| 独立编译 | EXIT=0（0 errors/warnings） |
| probe | `badQAbsLog_nonneg`、`sourceQPilotSignedLog_nonpos`、两个 `*_initial` 版本全 trio；零 sorryAx |
| 语义 | 仅重导出 green 事实：`#print` 证实 `Theorem311Source.sourceBadQAbsLog_nonneg` 证明为 `Finset.sum_nonneg …`；`sourceQPilotSignedLog_nonpos` 为 `neg_nonpos.mpr …`；initial 版本为例化；无新假设 |
| 依赖口径 | 闭包 129 模块、5 条 lana 边 ⇒ **lana-transitive** |

**结论：PASS**；作为 aux 引理仅条件/内部 citable（lana-transitive），不得当 lana-free 证据。

## 16. A951：`Mzk1A946LineBundleBridgeActual` 审计（PASS）

| 项 | 实测 |
|---|---|
| src SHA / size | `CEB476324AF29EF80B47AC82B086EED00DA27D97519205A662B3FABD965C0C65` / 1,532B |
| olean | 14,352B @11:58:18Z，fresh |
| 独立编译 | EXIT=0 |
| probe | `sourceL_eq_completion`、`sourceL_identified` 均 trio；零 sorryAx；源无 sorry/admit/axiom |
| 语义 | `sourceL_eq_completion := rfl` 证明 L carrier 与 completion carrier **定义相等**（`#print` 证实两 def 项结构相同）；`sourceL_identified` 应用 green `OrigXiFPaperCompletionLineBundleCarrier_identified`（证明 `⟨rfl, injective⟩`）；仅 green 事实 |
| 依赖口径 | 闭包 229 模块、5 条 lana 边 ⇒ **lana-transitive** |

**结论：PASS**；bridge 引理可条件/内部引用（lana-transitive）。

## 17. A952：`Mzk1E1CounterexampleAtDataActual` 审计（PASS，数据层反例，条件=badPlaces 非空）

| 项 | 实测 |
|---|---|
| src SHA / size / mtime | `449DD701F33185F50E7F90D96EFFD27610AB1B76615A7121C258FD89A2369CE9` / 2,411B / 12:03:28Z |
| olean | `B357108CF4F39F4C…`，48,896B @12:03:58Z，fresh |
| 独立编译 | EXIT=0（0 errors/warnings） |
| probe | `sourceQPilotSignedLog_neg`、`qSideContribution_source_ne_zero`、`bareE1_false_at_data` 全 trio；`rows_length` 无公理；零 sorryAx |
| 语义 | 依赖 green `sourceQPilotSignedLog_neg_of_nonempty := neg_neg_of_pos (sourceBadQAbsLog_pos_of_nonempty …)`；`#print` 证实后者为显式 `Finset.sum_pos'` 证明（`qParameter_contracting` 等），非 sorry/axiom |
| 条件范围 | 对**任意** `S : SourceDefinition31Data l` 且 `Nonempty S.badPlaces` 成立；`badPlaces` 非空为显式假设（文件自述），未宣称所有数据 badPlaces 非空；不依赖具体 I/place |
| 依赖口径 | 闭包 130 模块、5 条 lana 边 ⇒ **lana-transitive** |

**结论：PASS**；数据层条件反例可引用（条件 = `badPlaces` 非空；lana-transitive）。注意与 A943 的 `Mzk1E1ExplicitCounterexampleActual`（place/q 层、lana-free）互补：本条是 **`SourceDefinition31Data` 数据层**反例，仍非“任意数据无条件反例”。

---

## 18. A956：`Mzk1SPaperQPilotIdentificationsActual` 审计（PASS，PROVED-PARAMETRIC）

| 项 | 实测 |
|---|---|
| src SHA / size / mtime | `EC827699E7CC441B3948AB4403B26B06F56209FF2DE4D2D9E3DDA05BAB8CB7EC` / 3,865B / 12:11:51Z |
| olean | `659C766F539202D6…`，58,336B @12:12:38Z，fresh |
| 独立编译 | EXIT=0（0 errors/warnings） |
| probe | `sPaperQPilotObject` / `sPaperQPilotObject_qPilotLogVolume` / `sPaperQPilotObject_nonpos` 全 trio；`sPaperRows_length` 无公理；零 sorryAx（唯一 “sorry” 在注释 L16） |
| 四字段来源 | 均 green：`OrigXiFPaperStripIdentified_anchor`（`⟨rfl, target_q_eq_source⟩`）、`sourceL_identified`（A951 审过）、`OrigXiFPaperLogKummerIdentified_of_arrow`（显式证明项）、`sourceQPilotSignedLog_eq_neg_badQAbsLog`（`congrArg Neg.neg …`）+ `sourceQPilotSignedLog_nonpos_initial`（A951 审过） |
| SelfGroup/namespace | `SelfGroup` 为 `Theorem311Source.IPLAPTDataActual` 的 **abbrev**（plumbing 类型参数）；`open`/限定名仅寻径，无额外假设 |
| 结构完整性 | `OrigXiFPaperQPilotObject` 12 个字段全部填充（boundary/strip/strip_eq_source/oneColumn/lineBundle/logKummer/qPilotLogVolume/qPilotLogVolume_eq/四个 paper_* identification），编译通过 |
| 参数化 | 对任意 `I` 与任意 `b : OrigXiFQPilotFirstFieldType (l := l)` 构造；**未宣称 b 存在** ⇒ 参数化构造，非无条件全域对象 |
| 依赖口径 | 闭包 231 模块、5 条 lana 边 ⇒ **lana-transitive** |

**结论：PASS**；分类 PROVED-PARAMETRIC（green 来源、无 sorry/axiom）；仅条件/内部口径可引用，不得写成“actual q-pilot 对象无条件构造”，不得作 lana-free 证据。

---

## 19. A964：`Mzk1C1DonorConditionalActual` 审计（PASS，条件构造；C3L/RF GAP 已记录）

| 项 | 实测 |
|---|---|
| src SHA / size / mtime | `2140D85F768631002AD8949B0E8EA497947AA4A08C2DF33C2C2FEF8CC3CA5249` / 4,426B / 13:06:27Z |
| olean | `322C54C764527D7D…`，149,856B @13:07:15Z，fresh |
| 独立编译 | EXIT=0（0 errors/warnings） |
| probe | `packetOfHypotheses`/`nonempty_packet_ofHypotheses`/`sourceInputBinding_nonempty_ofHypotheses`/`nativeOldC1Bridge_nonempty_ofHypotheses`/`sourceLogKummerData_nonempty_ofHypotheses` 全 trio；`rows_length` 无公理；零 sorryAx |
| 条件性 | `NativeC1DonorHypotheses` 五字段 X/S/e/R/F 与 `NativeC1PaperSource` 字段逐项一致（`#print` 验证）；所有 nonempty 定理带 H 前提；文件头写 “CONDITIONAL (not an unconditional existence theorem)”；未宣称 R/F 已构造（A948 GAP） |
| C3L 缺口 | 文件头 + rows 记录 “GAP (carrier mismatch)”：`QPilotLineActualL` 特化 `FinitePrimePlace 2 7`，packet input 为 `NativePlaces X.S`；**未伪造 bridge** |
| 引用 green | `#print` 证实上游引理为 green 简单项（`Nonempty.intro P.sourceInputBinding` / `P.nativeOldC1Bridge` / `sourceLogKummerDataActual I C1`）；trio 传递闭包无 sorryAx |
| 依赖口径 | 闭包 348 模块、18 条 lana 边 ⇒ **lana-transitive** |

**结论：PASS**；分类 PROVED-CONDITIONAL（green plumbing，条件于五字段可居留）；C1/C2 conditional 可引用；C3L/RF = GAP；不得写成无条件存在定理或 lana-free 证据。

---

## 20. A967：`Mzk1LGenericConditionalActual` 审计（PASS；class-B 条件记录，未声称 S1391 构造）

| 项 | 实测 |
|---|---|
| src SHA / size / mtime | `A883497B41BAE816A4DAC3234307408C2D6ABB86303EA62371D4DD15188EEBD0` / 5,558B / 13:26:37Z |
| olean | `F22C85F8AF795BF9…`，519,496B @13:27:25Z，fresh |
| 独立编译 | EXIT=0（0 errors/warnings） |
| probe | `qPilotLineActualLGenericOfAssumptions` / `qPilotLineActualLGeneric_nonempty_of_assumptions` / `qPilotLineActualLGeneric_nonempty_of_c3` 全 trio；`lGenericRows_length` 无公理；零 sorryAx（唯一 “sorry” 在注释 L23） |
| class-B honesty | 文件头明写 “class-B generic C3L record (explicit data assumptions; **NOT a construction**)”；docstring 明写 C3 data 为显式假设、不声称 actual S1391 构造；rows “actual S1391 construction | NOT claimed” |
| 未声称 S1391 构造 | 全文无 `SourcePilotRegionDataL`/`sourcePilotRegionLToCore` 声明；`ConcreteQAlgebraicClosure` 仅注释说明其专化；`#print` 验证 root/Kummer 槽位为 DATA TYPES（`rootsData : Type` 等），未伪造 concrete carrier |
| 条件结构 | `LGenericAssumptions` = C1+C2+C3L 显式字段；两条 nonempty 定理 parametric 于 V/I，分别需 assumptions 或显式 C1/C2/C3L；无隐藏假设 |
| 依赖口径 | 闭包 294 模块、16 条 lana 边 ⇒ **lana-transitive** |

**结论：PASS**；分类 CLASS-B CONDITIONAL（generic data record + green plumbing）；可作接口/条件引用；不得写成 actual S1391 构造、无条件存在定理或 lana-free 证据。

---

## 21. A986/A988 纪律记录：禁止手动编译，编译统一走 DshDagWatchdog

2026-11-12：用户经 mainline 通知全部 lane——**任何人不得手动运行 `lake`/`lean`/`sage`/WSL 任务**；所有编译由 `DshDagWatchdog`（已启用）执行；lane 只写 Lean 文件并回报路径/main 定理/gap；watchdog 结果与 gate 汇总由 mainline 负责。

对审计口径的影响（stage4）：
- 本 registry/结果文件中 **A986 之前** 的记录带有当时手动 `lake env lean` 的 EXIT/olean/#print axioms 证据；此后**不得**再以手动编译为验收来源；
- 新审计结论只依据：watchdog 队列结果（EXIT、olean、`#print axioms` gate 汇总，由 mainline 提供/引述） + 源码级 SHA/语义检查（只读，不触发编译）；
- stage4 不再发起编译；若需要某文件的 gate 证据而 watchdog 尚无结果，登记为 **PENDING-WATCHDOG**，不自行编译、不伪造 green；
- 既有已登记 PASS 的 hash/证据维持有效（历史证据，不改写），但**新文件**必须走 watchdog 后由 mainline gate 汇总确认。

---

## 22. A991：分解类主张审计模板（DECOMP-AUDIT-TEMPLATE.md）

- 文件：`coord/DECOMP-AUDIT-TEMPLATE.md`（2026-11-12；stage4；**未编译**，只读初审）；
- 内容：分解类主张要件 A–F（恒等式来源 / 每项非负证明 / 循环性 / sorry-axiom / gate 状态（PENDING-WATCHDOG）/ 文件头标注）+ 14 项审计清单 + 固定审计流程；
- 只读初审结论（快照 2026-11-12T14:30Z）：
  - `DECOMP-PAIRING-CANDIDATES.md` = **PARTIAL**：缺显式 Status、恒等式来源行（应引 VcI:741/Gap:523/895/LHS:88/RHS:107）、arch 与 torsion 归入 GAP、权重归一引用、逐项非负证明；循环性暂未发现；
  - `C-MARGIN-FIX.md` = **PASS**（分析级）：恒等式来源充分（根树行号齐全），M=A−R 由定义推出，已标 MODEL 并作废 M0 代理结论；
  - `FACE5-PER-PLACE-TARGETS.md` = **PASS**（模型级）：V−(sF−1)A 精确分解且引 VcI 行号，arch 项明确未证等价；
  - `CHAIN2-PHASE2.md`/`CHAIN2-RESULTS.md` = **PASS（模型级）**：V(t)=base−t logdf 为模型定义，状态诚实（BLOCKED ON stepxi）；
  - `C3-DATA-INVENTORY.md` 无分解主张，不适用；
- 本 registry 与结果文件不因该模板改动任何 green 计数；后续分解类 Lean 文件必须以 watchdog gate 为准。
