# DECOMP-AUDIT-TEMPLATE — 分解类主张的审计模板（A991，stage4）

日期：2026-11-12。适用范围：任何形如 M = Σ 项、V - c·A = Σ 项、deficit = term1 + term2、
“把目标分解为若干可加项”的主张（文档或 Lean 文件）。本文件只定标准与初审，不编译（A986/A988）。

## 1. 分解类主张的必备要件（缺一即 PARTIAL/FAIL）

### A. 恒等式来源

1. 精确等式：写出目标分解的完整等式与方向（M := …、M = …），所有符号的定义就地给出或指向定义；
2. 来源引用：每个非平凡等式必须给出可核来源之一——
   - lana 根树：Iut/...:line（A896：根 Iut/ 行号；不得用 tmp 副本行号）；
   - 论文：定理/命题/公式编号 + 页码；
   - 我们 green Lean 声明：文件 + 声明名 + watchdog/mainline gate 的 EXIT/olean/trio 记录；
3. 推导链：从定义/来源到分解的推导步骤（不允许“数值观察”充当恒等式来源）；
4. 归一化口径：nC、1/nC、Σ_c w_c（是否 Σ=1）、l 与 ℓ、A 的定义（|log q| vs logQ/(2ℓ)）、
   T_v/H_v 的 per-place vs per-packet 定义；
5. 边界项：arch 项（log(√2π) 是否为 (1/nC)Σ_i hullPacket_i(∞) 的已证等价？）、torsion 项（r/n 从哪一步进入？）、
   坏位有限支撑（finite_support_hullPacket 类引理）必须显式引用；
6. 未识别项：任何“类似/约等于/取作”的项必须标 GAP 或 MODEL，不得混入恒等式。

### B. 每项非负证明

1. 对每个被求和的项，单独给出非负证明（Lean 定理或显式假设）：0 ≤ T_i、0 ≤ arch、0 ≤ torsion、0 ≤ H_v（或明确的负项清单）；
2. 若某项可为负（如 H_v 在 ramified place、T_v vs H_v 的配对差），必须列入“负项/条件项”，不能假定非负；
3. 条件型充分条件（C1Bound v → 0 ≤ M）必须明确是充分条件，其假设本身不得被当作已证；
4. 求和引理：Finset.sum_nonneg / Finset.sum_pos 的应用需给出每项证据；linarith 只能做最后算术合并；
5. 严格/非严格（<0 vs ≤0）与零项情形（e=1、tame、unramified r=0）必须分别核对；
6. 禁止用“数值表所有行都 ≥0”代替非负证明（零违例 ≠ 证明）。

### C. 循环性

1. 分解必须在不假设目标（M ≥ 0、SSIneq、Cor312）的前提下成立；
2. 若分解的某一步用到目标或其等价形式（例如用 SSIneq 推 arch 的具体值）⇒ FAIL；
3. 条件定理的方向：(∀ v, Bound v) → 0 ≤ M 是充分条件，不是等价改写；不得报告为“目标已化归为 Bound”；
4. 若某候选（如 C3）把恒等式部分与新算术混在一起，必须拆开：恒等（green）+ 非负（假设/待证）分列；
5. 依赖 DAG：分解结论不得反过来作为其自身来源；引用外部定理时检查是否已隐含目标。

### D. sorry / axiom 检查

1. 主张 PROVED 的 Lean 文件：零 sorry、无 axiom/opaque，#print axioms 仅 trio；
2. 若保留 ssIneq_sorry（唯一允许的 named sorry，SORRY-ACCEPTANCE.md/A871），必须标明：分解链不得绕过或伪装该 sorry；
3. 文档/模型主张不得出现“已证/sorry-free”字样除非有 gate 证据；
4. 出现 sorryAx 任意位置 ⇒ 该 Lean 结论不得进入证据链。

### E. 编译/gate 状态（A986/A988 口径）

1. 禁止手动编译；新 Lean 文件落盘后由 DshDagWatchdog 处理；
2. 文档登记该文件 gate 状态：PENDING-WATCHDOG / WATCHDOG-EXIT=0 / GATE-FAIL（附 mainline gate 汇总引用）；
3. 无 watchdog 结果时只能写 PENDING-WATCHDOG，不得写 PROVED/green；
4. 审计只做只读源码检查（SHA、语义、引用闭包）并引用 watchdog 结果；
5. 数值/模型表与 Lean 定理分列；MODEL/NUMERIC 不得升级为 PROVED。

### F. 文件头与标注

- 强制 Status: 行（MODEL / NUMERIC / PARTIAL / STOP / PROVED / PENDING-WATCHDOG）；
- 目标记号与方向（M := V - (sF-1)A 等）必须在文档开头定义；
- 每个表/结论行标 MODEL/NUMERIC/PROVED/ASSUMED/GAP；
- 已知缺口（arch 识别、torsion 来源、权重归一、wild buffer、C3L carrier 等）逐条列 GAP 段。


## 2. 审计清单（逐项 PASS/FAIL）

| # | 检查项 | 通过条件 | 失败即 |
|---|---|---|---|
| 1 | 状态行 | 六态之一，与内容一致 | PARTIAL/FAIL |
| 2 | 等式完整性 | 每个符号有定义，方向明确 | FAIL |
| 3 | 恒等式来源 | 每项来源 file:line / 公式编号 / green 声明 | PARTIAL |
| 4 | 推导链 | 有步骤，非“观察” | PARTIAL |
| 5 | 归一化 | nC/权重/A/T/H 口径一致且已声明 | PARTIAL |
| 6 | arch 项 | 定义 + 与 hullPacket∞ 的等价证明或显式 GAP | GAP |
| 7 | torsion 项 | 进入位置与符号已说明/证明 | GAP |
| 8 | 每项非负 | 每项有证明或列入负项/条件项 | PARTIAL |
| 9 | 求和合并 | sum_nonneg/linarith 每项依据链完整 | PARTIAL |
| 10 | 循环性 | 不假设目标；充分条件方向正确 | FAIL |
| 11 | sorry/axiom | 零 sorryAx（PROVED 主张） | FAIL |
| 12 | gate 状态 | PENDING-WATCHDOG 或 watchdog 结果 | PARTIAL |
| 13 | 数值标注 | 数值表标 MODEL/NUMERIC，无“零违例=证明” | FAIL |
| 14 | GAP 清单 | 已知缺口逐条列出 | PARTIAL |

## 3. 已落盘分解相关文档初审（只读，快照 2026-11-12T14:30Z 附近；不编译）

### 3.1 coord/DECOMP-PAIRING-CANDIDATES.md（A991）—— PARTIAL（需补恒等式来源与非负证明）

| 检查 | 现状 | 判定 |
|---|---|---|
| 状态行 | 无显式 Status 行（末尾有 “No candidate is proved” 但非状态行） | ❌ 需补 Status: MODEL/PARTIAL |
| 恒等式来源 | M = sum_v[-T_v+H_v]+arch-torsion 未给来源行；V/A/(sF-1) 定义未引 lana 行；H_v/T_v 公式引了 hullPacket 名称但无 file:line | ⚠ PARTIAL：应引 Iut/WallEquiv/VcI.lean:741（V 分解）、Iut/WallEquiv/Gap.lean:523/895（gap/M 定义）、Iut/Cor312/LeftHandSide.lean:88（A）、RightHandSide.lean:107（R） |
| arch 项 | 写 “arch = log(√2π) (global, once)”，未证它等于 (1/nC)Σ_i hullPacket_i(∞)；FACE5/C-MARGIN-FIX 均标 sign depends on actual arch data | ❌ GAP（arch 识别未证） |
| torsion 项 | “−torsion”，但 r/n 从哪一步进入 V/A 未给推导 | ❌ GAP |
| 权重归一 | T_v 用 weight_v，H 用 1/nC；未写 Σ_v weight_v = 1 / Σ_c w_c = 1 的引用 | ⚠ PARTIAL |
| 每项非负 | 只说 if displayed inequality holds then all terms nonnegative ⇒ sum_nonneg+linarith；未给 arch > 0、torsion ≥ 0 的证明；C1 自认 H_v 可为负；C2 buffer 需 e_p ≥ 1；C4 的 deficit 未定义 | ⚠ PARTIAL（条件型可用，但需逐项证明/负项清单） |
| 循环性 | 未发现假设 M≥0 的推导；C1/C2/C4/C6 是充分条件方向正确；C3 用 green thetaSumPaper_eq_clana_mul（恒等）+ C1/C2（正确拆分） | ✅ 暂未发现循环 |
| sorry | 无 Lean 文件、无 sorryAx 声明；仅 formalization plan | ✅（尚无文件） |
| gate | 无 Lean 文件落盘 ⇒ 未来文件应标 PENDING-WATCHDOG，不得写 green | ⚠ 需补声明 |

**需补**：状态行；完整恒等式来源（VcI:741/Gap:523/895/LHS:88/RHS:107）；arch 与 torsion 的进入方式（证或 GAP）；权重归一引用；arch>0、torsion/buffer 非负的逐项证明或负项清单；C4 的 deficit 定义；未来 Lean 文件标 PENDING-WATCHDOG。

### 3.2 coord/C-MARGIN-FIX.md —— PASS（分析级；恒等式来源充分）

- 状态行 ✅ MODEL/analysis，并明确 C3/C3b 的 M0 结论 INVALID for paper target；
- 恒等式来源 ✅ 逐条引根树 lana 行（LeftHandSide.lean:88、RightHandSide.lean:107、VcI.lean:741、Gap.lean:523/895、VcI.lean:889-891）；
- 推导 ✅ M := V+gap-(sF-1)A = A-R 由定义推出；逐项展开给出；
- 未证项/GAP ✅ 明确列出 calculator 与 paper 的差异（1/nC、Σ_c w_c、Ind2 模型式、M0 代理无效）；
- 循环性 ✅ 未用目标推恒等式；无 sorry/无 Lean 定理主张；
- 备注：该文档不改写任何 Lean；其 corrected 20-curve table 为 MODEL 数值，未冒充定理。

### 3.3 coord/FACE5-PER-PLACE-TARGETS.md —— PASS（模型级，来源充分）

- 状态行 ✅ model-level per-place decomposition … not an IUT theorem, not Lean evidence；
- 恒等式来源 ✅ VcI.lean:741/806/844、IdentifiedCopies.lean:444 等；V-(sF-1)A 的分解为精确式（含 finite support 引用）；
- 边界项 ✅ 明确 arch 为 (1/nC)Σ_i hullPacket_i(∞)，且注 sign depends on actual arch data；未声称 arch=log(√2π) 恒等；
- 非负性 ✅ 未主张 M≥0；数值表标 model（含 p=11 负项）；
- 结论 ✅ 未把模型表当定理；无 sorry/gate 问题（无 Lean 文件）。

### 3.4 coord/CHAIN2-PHASE2.md / CHAIN2-RESULTS.md —— PASS（模型级；状态诚实）

- CHAIN2-PHASE2.md Status ✅ model calculation … Not an IUT theorem, not Lean evidence；并标 A884 BLOCKED ON stepxi / 数值待重算；
- 分解 V(t) = base - t logdf 是模型定义，非 lana 恒等式；文档未冒充恒等式（可接受，但引用时须标 MODEL）；
- 已知误差（c=0.15、p=11 e=10、arch 差异）在文档内注明；无循环/无 sorry 主张。

### 3.5 其他相关文档

- coord/C3-DATA-INVENTORY.md：仅定义/数据清单（V/rhs/gap 来源行齐全），无分解主张 ⇒ 不适用本模板；
- coord/EXPLORATION-C-C1.md：M = ΣH+ΣInd2−ΣT 为 MODEL 计算器公式；已在 A918 审计标 MODEL/PARTIAL；与 C-MARGIN-FIX 的差异（1/nC、Σ_c w_c、Ind2）一致，不重复判定；
- Lean 侧（如 Mzk1PaperFaithful312HqnegActual 的 signedLog 恒等式）不在本轮文档初审范围；若其结论被用作分解恒等式来源，须按 §1-A 引声明名 + gate 状态。

## 4. 初审汇总表

| 文档 | 恒等式来源 | 每项非负 | 循环性 | sorry | gate/状态 | 判定 |
|---|---|---|---|---|---|---|
| DECOMP-PAIRING-CANDIDATES | ❌ 无来源行/arch/torsion 未证 | ⚠ 仅条件式 | ✅ | ✅ 无 | ⚠ 需 PENDING-WATCHDOG | PARTIAL |
| C-MARGIN-FIX | ✅ 根树行齐 | 不适用（无 M≥0 主张） | ✅ | ✅ | MODEL，无 Lean | PASS |
| FACE5-PER-PLACE-TARGETS | ✅ 精确式+行号 | 不适用（未主张 M≥0） | ✅ | ✅ | MODEL，无 Lean | PASS |
| CHAIN2-PHASE2/RESULTS | 模型定义（非恒等式），已标 MODEL | 不适用 | ✅ | ✅ | MODEL，BLOCKED ON stepxi | PASS（模型级） |
| C3-DATA-INVENTORY | 无分解主张 | — | — | — | — | 不适用 |

## 5. 对后续分解类主张的固定审计流程

1. 先查 §1 要件 A–F 是否齐全；
2. 逐项查 §2 清单，记录 PASS/PARTIAL/FAIL；
3. Lean 文件：只读 SHA/源码语义/引用闭包，gate 状态引用 watchdog/mainline（不自行编译）；
4. 输出格式：文档/文件 | 恒等式来源 | 每项非负 | 循环性 | sorry | gate | 判定 | 需补项；
5. 任何 FAIL 项（循环性、sorryAx、数值冒充定理）⇒ 该分解结论不得进入证据链；PARTIAL 只能作为待办/研究记录。
