# TEAM BRIEF — IUT xi-f / 3.12 / ABC — 2026-11-10 (Lead)

每个 teammate 的第一步：完整读本文件，然后读你自己的 task + 下面列出的文件。
This brief is authoritative for protocol. 目标、纪律、管线、所有权都按这里执行。

## 0. 目标与绝对纪律

目标：从基础三公理 `propext, Classical.choice, Quot.sound` 出发，无条件构造 IUT 3.12 的全部前置对象并证明 ABC。

硬性纪律（违反即返工，不接受借口）：
- 禁止 `sorry`、额外 axiom（自定义 axiom/opaque/unsafe/False.elim 桥）、`True`/`PUnit`/空结构冒充对象、value-layer surrogate、toy carrier、把 interface 等价当证明、削弱量词/改对象/改题面。
- 不等式没有捷径：不构造原文对象不判 ≤/≥/等式。缺对象就构造对象；构造不了就写 exact Missing 结构/Prop，带原文页码/行号，记为缺口，不算 progress。
- 不要 idle：缺 A 对象就构造 A；A 暂时卡住就换相邻对象/相邻文件。只有在读完原文、确认 source 数据确实不足时才允许 blocked，并写明缺的数学数据。
- 修改我们的答案，不是改题目。原文允许的输入保持原范围，不擅自加强/减弱。

## 1. 编译管线（唯一编译方式；严禁自己编译）

中央 watchdog 常驻，从队列读文件编译（最多并行 10，串行结果日志）。
- 队列：`tmp/xif_guarded_queue.txt`。你的工作流：写/改 Lean 文件 → 追加 workspace 相对路径（正斜杠，如 `tmp/sheaf/xif/paper/S3131FooActual.lean`）到队列 → 继续写下一个文件 → 定期看结果。
- 结果：`tmp/xif_guarded_results.log`（每文件 `EXIT=0|1 FILE=... SIZE=...` + 输出/错误 tail）。watchdog 日志：`tmp/xif_guarded_watchdog.log`。
- 隔离：`tmp/xif_guarded_quarantine.txt`（失败文件 fingerprint；源文件 mtime 变化后自动 REVIVE）。
- 失败后：读 results 里的具体 error → 修文件 → 重新 append 该路径（不要等）。同一文件连续 3 次失败要报 Lead。
- **严禁**：`lake`、`lean`、`lean_auto`、`build_guard`、任何编译/检查/等待编译的命令。看到自己在等编译就是违规；写完就换下一个文件。
- citable 口径：EXIT=0 + olean 比源新（`.lake/build/lib/lean/<path>.olean`）+ axioms probe（小文件 `#print axioms`，probe 也 append 队列，输出在 results log）只含 `[propext, Classical.choice, Quot.sound]`（允许子集）。
- 不要改 `tmp/xif_priority.txt`（Lead 管理）；不要改别人的文件；只 append 队列。
- watchdog 正在运行，队列里有文件时会自动编译；无文件时每 30s 空转。不要重启/杀死它。

## 2. 所有权与文件

- 你只写：`tmp/sheaf/xif/paper/` 下**你自己的 S313x 前缀新文件** + task 里明确指派的既有文件。
- `LeanFormal/**` 生产源码默认只读（Lead 明确指派除外）。不要碰其他 stream 的文件。
- 每个文件 < 200 行，一个文件一个主题，小步快跑。建议一次写 2-5 个文件再查一次 results。
- 可用一次性 subagent 处理不相交小节；subagent 必须同样 write-only、不许编译、写你自己的前缀文件。
- 不要提交 git、不要删文件、不要改 tmp/xif_guarded_*.txt 的内容（append 队列除外）。

## 3. 当前已核实现状（2026-11-10 00:10；来自 results/olean/ledger）

Batch A 主线（coord/ROADMAP-2026-11-02.md §2）：固定同一份合格输入 C，交付 Q_C、H_C 对象识别、H_C 有限、Q_C ≤ H_C。
- 已 citable（fresh olean + EXIT0）：`S3130QCSourceActual`（fixed bad place b 的 actual q_v family/Q_C source data，条件于 S2135PrimeAlignmentRequired）、`S3130QCLeHCActual`（把同-C 的 Q_C≤H_C 明确记为 gap `S3130QCLeHCGap`，未证）、`S3130PaperSignedHullFiniteActual`（PaperSignedHull 上的 Batch A package：H_C 有限、Q_C≤H_C.toReal，但依赖 PaperSignedHull 的 inhabitant/字段）、`S3128Cor312StepXIAssemblyActual`（finite route StepXI assembly，EXIT0）、`S3127G2UniversalUnitActual`、`S3128Cor312ToABC{Input,HeightBound}ConsumerActual`、`S3128ABCRpowConsumerActual`（均条件式 consumer）。
- C3 consumer chain S2888-S2909 已关闭（三公理，见 `C3_CONSUMER_CHAIN_CLOSURE.md`）；C3 normalized tensor Haar / region finite 有 actual（S2746/S2823/S2736c/S3128C3RegionVolumeSplitBound 目标）。
- stage1 fourth joint 组件：`S1204SHEOneColumnReadoutActual`、`S1215SourceSHEHDDCompatibilityActual`、`S1300HDDHullDetActual`、`S1385HDDHullDetActual`、`S3128Stage1SHEHDD*Actual`、`S3128Stage1FourthJoint{Consequences,Complete}Actual`（部分 citable）；`S3128Stage1FourthJointFullChainActual` 缺 olean。
- 实际 hull 载体：`S3129IQHullLogVolumeSourceActual`（source Q_l log-shell image + Haar + finiteness；**当前无 olean**，被 `tmp/sheaf/l1-f5/SourceQlLogShellConcrete.lean` EXIT1 挡住）；`PaperIQHullLogVolumeInterfaceCandidateActual`（C3 normalized Haar candidate，无 olean）。
- ABC 下游：`ABCFrontier.lean` F4/F5 是仅剩两个算术比较 clause（IUT IV §2）；`Cor312ComparisonGapReduction.lean` 给出 5 个 named inputs 的 reduction；`ABCGap2FiniteC3SupplyActual` 被 C3 split bound 挡住。
- 已知失败文件（不要重复旧错误）：
  - `tmp/sheaf/l1-f5/SourceQlLogShellConcrete.lean`：`Unknown identifier isometry_localField_algebraMap`（line48）、kernel deterministic timeout（line58）。
  - `tmp/sheaf/xif/paper/S3128C3RegionVolumeSplitBoundActual.lean`：typeclass instance stuck（line80）、type mismatch/rewrite failed/linarith（89/91/97/102）。
  - `tmp/sheaf/xif/paper/S3129SourceP1BoundariesActual.lean`：explicit universe params invalid（`(R : SourceTheorem311Realization.{...})` 写法错）、`le_ceil` 不存在。
  - `tmp/sheaf/xif/paper/S3129SourceP2BoundariesActual.lean`：同 universe 写法错，且源码里出现 `sorry`（必须重写，不许留）。
  - `S3127G2ActionCoverNaturalActual`、`ABCGap2FiniteC3SupplyActual`：队列里被 quarantine 依赖挡住。
- 重要：`S3130QCLeHCGap`（Q_C≤H_C）是 Batch A 唯一未闭合比较；但不要用"同一个 average 定义两边"的方式绕过——Q_C 必须来自 actual q 侧读数，H_C 必须来自 actual Θ-hull/procession 归一化读数。

## 4. 本批工作流（8 streams；文件前缀即所有权）

| # | stream | 文件前缀 | 任务（详见各自 task） |
|---|---|---|---|
| 1 | mainline | S3131* | Batch A 主线：fixed C 上 Q_C/H_C 同一输入识别 + 用 actual q 读数/hull 归一化证 Q_C≤H_C |
| 2 | hull | S3132*, tmp/sheaf/l1-f5/ | 修 SourceQlLogShellConcrete；actual Θ-hull/compactness/Haar/procession average；H_C 实际构造 |
| 3 | qpilot | S3133* | actual global q-pilot 对象/divisor/log-volume 读数；接到 Q_C |
| 4 | shehdd | S3134* | Stage1 fourth joint：(hull+det)∘(SHE) 实际组合；SHE/HDD 数据闭环 |
| 5 | abc | S3135* | F4/F5 在 source-faithful carrier 上的实际 discharge 路线；Q_C≤H_C → ε-comparison/height bound |
| 6 | stage4 | S3136* | Stage 4 host：Frobenioid presentation/anabelian G2/fiber 实际链（修 ActionCover 等） |
| 7 | lattice | S3137* | Stage 2 核心对象：actual log-theta lattice / log-shell / log-volume（LogThetaLatticeActual 目前 SOURCE-ONLY） |
| 8 | stepxi | S3138* | Step XI source-level 桥：SourceProcessionStepXI* / finite→source residual / P1/P2 boundaries 重写 |

## 5. 报告

- 每完成一批（2-5 个文件入队）或每 10-15 分钟，`send_message` 给 `lead`：stream、文件、主要定理、EXIT 状态、还缺什么、下一步。≤15 行。
- 需要 Lead 决策、跨 stream 冲突、同一文件 3 次失败 → 立刻报。
- 不要等许可；Lead 没回就继续下一个文件。收尾报告要可核验（文件路径 + 定理名 + results 里的 EXIT 行）。

## 6. 原文与笔记入口

- 原文抽取：`papers/motizuki_corpus/text/`（III Cor 3.12 :10324-10353；IV Thm 1.10 :1255-1385；IV §2 :2329-2332；Formalization of IUT (2026-04) :116-125/:443-621；Explicit estimates :1-56）；`tmp/source-extract/`。
- 笔记：`tmp/sheaf/xif/FROM-SCRATCH-NOTES.md`、`SOURCE-CONSTRUCTION-NOTES.md`、`C3_CONSUMER_CHAIN_CLOSURE.md`、`coord/ROADMAP-2026-11-02.md`、`coord/IUT-PAPER-ROUTE.md`、`AUDIT_LEDGER.md` 末尾条目。
- 路线禁令（coord/IUT-PAPER-ROUTE.md §4）：`ABCFrontier`、`Cor312ToABCBridgeInterface`、`Frontier*Clause`、`cor312Gap*` 是 interface，不是 milestone；不能当进度。


## 7. 等待/轮询策略（2026-11-10 Lead 更新）

- 等待 watchdog 编译结果时按命中率自适应：连续几次等待都能拿到新 EXIT 行（说明队列顺畅）→ 把等待间隔缩短（如 30–60s）；
  如果连续等待无变化（队列拥堵、依赖未就绪、quarantine 未 revive）→ 适当延长（2–5 分钟），期间不要空转，继续写下一个文件/下一个对象。
- 永远不要为了等编译而停手：写文件、append 队列、继续下一个主题；EXIT 行出现后集中修一遍。
- 单个文件编译超过 ~2 分钟即视为过重：拆分模块、显式类型、少 unfold；超过 10 分钟的 compile 会被 Lead 杀掉。


## 8. "非论文对象"构造政策（2026-11-10 用户提问后 Lead 定）

三类严格区分：
1. **论文对象本身**（paper object）：直接构造/证明，最高优先。
2. **论文对象的前置组件**（prerequisite component）：定义/结构形状与论文一致、是论文对象的一部分（如 C^boxplus_LGP 的 DivisorialMonoidOn/structure functor 层），只是它的某些识别数据缺失（J_v、Frobenioid 同构、x-mu unit portion）。允许构造，算前置进展，但必须：(a) 形状与论文对齐；(b) 缺失部分写成字段级 exact Missing + 页码；(c) 文件明确标注“前置组件，不是论文对象本身”；(d) 写明将被哪个论文对象/消费者消费。
3. **替代物/孤岛**（surrogate/island）：不能被任何论文对象消费的替换性构造（value-layer surrogate、玩具结构、平行非论文塔）。默认不构造；唯一例外是用来**证伪某条路线**的负结果（如 abc 在具体 Haar 模型上 refute 卡(1)），记录为负结果，不计为进度。

判断问题：若中途停止，这个构造会被论文对象复用吗？会 => 前置组件，值得写；不会且只用于替代 => 不写。


### 7.1 编译期间不要改文件（2026-11-10 追加）

watchdog 启动编译时抓取的是当时文件内容；若你在编译未结束时继续编辑同一文件，这轮编译是**旧版本**，结果作废且占用 slot。
规则：一个文件 append 之后不要再改它，先写下一个文件；确需再改，改完后再 append 一次（watchdog 会重编新版本）。若发现结果里 EXIT 对应 SIZE 与你当前文件不符，说明编译的是旧版本，直接再 append。


## 9. 负结果的含义与"无条件"定位（2026-11-10 用户提问后 Lead 定）

外部负结果（Higuchi 2026《A Formal Negative Result for the Passage from Step (xi-e) to Step (xi-f)》）：
- 它证明的是：** qualitatively package（IPL/SHE/APT + abstract linkage/cohabitation/closed half-line）不能逻辑推出数值桥** -|log q| ∈ R_{≤ -|log Θ|}；不否定 IUT，而是说明必须额外给出数值桥/数值引理（该文 §6: repaired proof 需要什么）。
- 对本项目的含义：**不允许从定性/接口数据直接得出 q/Θ 比较**；必须构造实际数值对象（actual q-pilot/Θ-hull 读数、实际 Haar/归一化、paper-faithful 系数、log-volume 计算）并证明数值比较本身。
- 负结果分类：(i) 模型/约定错误（如值层 surrogate faithfulness 假、旧系数约定 e 因子）→ 换正确对象/修正答案；(ii) 旧形式化目标错误（如 S2167/S2130 等）→ 从路线剔除；(iii) tree 契约缺数据（如 placeToMod 无投影、cusp 无实数编码）→ 构造论文对象/记录 exact missing，禁止改 contract 伪造；(iv) 外部负结果（Higuchi）→ 指出必须新增的数值桥内容。
- "无条件证明"的目标不变（无 sorry/额外 axiom；假设只能是论文允许的输入），但内容必须包含论文的数值桥：当前对应 = mainline 的无条件 paper-normalized 比较 + lattice 的 R1 same-C 识别 + abc 的 F4/F5 两卡 + 实际 log-shell value-group/归一化。负结果不构成对目标的否证，而是把"捷径"排除掉。


## 10. 数值桥来自四三角形（2026-11-10 用户确认）

用户明确：(xi-e)→(xi-f) 的定性输入不足；数值桥必须由**四三角形**结构产生。
- 1st：BPS --multiradial algorithm--> multiradial representation（stepxi S3139 mutation：gluing-witness 不变性 + Ind1/Ind2 非干扰；residual=3 数据字段）。
- 2nd/3rd：(dsc) APT + IPL ⇒ 1st/2nd/3rd triangles（S3138 source Step XI、IPL/APT 因子化、S3134 IPL 数据）。
- 4th：(hull+det)∘(dsc)SHE + IPL ⇒ q/Θ simultaneous comparison（shehdd S3134FourthJoint* + hull S1204/S1215/S1300/S1385 actuals + H_C actual hull）。
- 然后 Cor 3.12（CΘ ≥ −1）→ IUT IV Thm 1.10 → ABC。
要求：4th triangle 必须实际**产生**数值比较（compose actual hull+det readout with SHE output and derive signed inequality），不得以 named hypothesis 代替；R1 same-C 读数等式是 4th triangle 输出与 Stage-2 读数之间的 seam，能由 4th triangle 供给的就优先由它供给，否则保留精确 named residual。


## 11. "不许长期挂抽象"（2026-11-10 用户提醒后 Lead 定）

用户提醒：抽象对象可能失败；要实际对象。补充规则：
- 每个仍以具名 Prop/structure（named residual）形式存在的缺口，必须有 owner + 构造计划（用哪个实际对象/数据构造），并在 ledger 记录；不得长期挂账。
- 不允许用 interface/抽象等价长期替代实际对象；能构造就先构造，构造不出就给 exact missing source data（哪条几何/算术数据缺、页码），并说明为什么当前 actual 输入不足。
- 所有"已 actual"文件必须 EXIT0 + trio probe（propext/Classical.choice/Quot.sound 之外无 axiom）；负结果（模型/约定失败）保留在 ledger，用于修正对象选择。
- 当前抽象残量清单（必须逐个攻）：R1 M0–M5 模型识别；R2 两条 normalization 恒等式；F4 (a) ValueGroupSplitting、(b) paper scaling-zero、(c) card P（ABC-strength）；first-triangle 3 字段（log-shell capsule、SourceLGPData、F_mod→R）；LGP 的 Ψ/J_v/Frobenioid iso/×μ；cusp ε real encoding；placeToMod（contract-separation，genuine source missing）。


### 7.2 批量产出规则（2026-11-10 用户要求：12 线程，写 2–4 个文件再等）

- 用户环境是 12 线程；watchdog -MaxParallel 12。每个 teammate 应**每批写 2–4 个文件**（各自小、单主题），一次 append 全部，然后统一看一次 results，修失败、再写下一批。
- 不要写一个文件就停下来等编译；也不要在两个文件之间空转。目标：始终让队列里保持 ≥6–10 个待编译文件，让 12 个 lean 槽位跑满。
- 每批的 2–4 个文件要互相独立（不互相 import 成链），这样能并行编译；依赖链上的文件是例外（等前一个 olean 后再 append 后者）。
- 每批结束后：检查 EXIT/错误；3 次失败的文件报 Lead 并换下一个；继续下一批。
- 编译中的文件不得编辑（§7.1）；append = 该版本终稿。

### 7.3 批量 4 文件 + 短等（2026-11-10 用户要求，替代 §7.2 的 2–4）

- 每批**写 4 个文件**（小、单主题、互相独立以并行编译），一次 append 全部，然后**短等**（如 60–120s 看一次 results；不要长等）。
- 队列目标：保持 ≥10–12 个待编译文件，让 12 个 lean 槽位跑满。看到队列变浅（<8）立即再写下一批 4 个。
- 依赖链文件等前一个 olean 再 append；编译中的文件不编辑（§7.1）；每批报告：4 文件 + EXIT + 下一步。
- 失败文件修好后立刻再 append；同一文件 3 次失败报 Lead 并换下一个主题。

### 7.4 分段短等（2026-11-10 用户要求）：不要一次长等

- 不要一次等很久（例如 5–10 分钟）才看 results；把等待**拆成多次短等**：append 完一批后，每 **20–40 秒**检查一次 results；看到你的文件 EXIT 就立刻处理。
- 等待期间**不要空转**：一边写下一批 4 个文件，一边在切文件之间做短检查；编译在后台跑，写文件和查结果交替进行。
- 某文件持续未出现 COMPILING = 可能被 missing path 静默 defer（见 §7.2 陷阱）：先查 import 路径，不要盲目长等。
- 批次报告可以分多次发：先报已 EXIT 的，再报新增的，不必等全批完成才报告。

### 7.5 数学工具制造（2026-11-10 用户指令）：没有工具就制造工具

- 当证明因**缺少现成数学工具**（Mathlib 无引理、repo 无桥）而阻塞时：不要只记录 "no such lemma" 就停；**自己制造一个通用可复用工具**——独立文件、一般性陈述、任何 consumer 可直接 apply（例：从 C_c 积分推出 Haar 唯一性；degree-one + matching prime ⇒ completion ≃+*；p-adic completion 范数计算；通用 normalization/readout 引理）。
- 把**通用工具**（完整证明）与**实例化数据**分离：数据真缺时记为 named exact missing，工具本身保持已证可复用。
- 工具文件单独立项（probe + ledger），然后回到被阻塞的证明使用它。现成 Mathlib 引理可作积木，但默认路线是造缺失的工具。
- 已派：abc=一般 Haar 唯一性工具（C_c→Measure.ext）；hull=一般 completion 比较工具；qpilot=p-adic completion 范数工具。其它 stream 按此原则处理自己的阻塞。

### 7.6 先查仓库/Mathlib 再制造（2026-11-10 用户指令，补充 §7.5）

- **制造工具之前必须先搜**：`LeanFormal/`、`tmp/`（含 `tmp/archive_*`、`tmp/sheaf/gap-exploration-*/snapshots`、`vendor/`）、`.lake/packages/mathlib/Mathlib/`；已有工具直接复用（这次就找到了三个关键工具，见 `coord/TOOL-INVENTORY.md`）。
- 只有确认缺失才制造通用工具；新工具登记进 `coord/TOOL-INVENTORY.md`。
- 本次已找到：Mathlib `Measure.ext_of_integral_eq_on_compactlySupported`（Haar 唯一性直接用）；repo completion 环等价族（`completionIsometryEquiv`、`NormalizedCompletion ≃+* Completion`、`CommonPrimeCompletion`、`NormalizedIntegers`、`AdicCompletion ≃+* Ô_v`）；repo p-adic norm 工具（`norm_completionMap_pow_*`、`FreyTateAnalyticInput` 的 padicNorm 限制引理）。

### 7.7 Citable 验证工具（2026-11-10，防假绿）：tools/xif_citable_check.ps1

- 用法：`pwsh -NoProfile -File tools/xif_citable_check.ps1 -File <相对路径>.lean [-Probe <probe>.lean]`。
- 检查：source 存在；olean 存在且 fresh；results.log 最后 EXIT=0；文件含**真实声明**（theorem/lemma/def/abbrev/structure/class/instance/inductive，非注释/doc-only）；可选 probe 绿且输出含 trio 或 no-axiom 证据、无 sorryAx。
- 输出 JSON verdict（CITABLE / NOT_CITABLE + reasons）；非 CITABLE 退出码 1。
- **规则**：任何 stream 报告“closure/citable”前必须跑该工具通过；doc-only/注释-only 文件不得计入闭环。已实测：gate=CITABLE、S3137M2aClosureActual=NOT_CITABLE(NO_REAL_DECLARATIONS_DOC_ONLY)、hull ThetaHalfFinalComposition=CITABLE。

### 7.8 大批量任务（2026-11-10 用户要求：太慢，每次多写几个文件一起等，派大任务）

- **每批 6–8 个小文件**（仍单主题、互相独立），一次全部 append，然后**一次短等**（60–120s）再检查/修复；不再一次只写 3–4 个就等。
- 大任务拆成 6–8 个文件的连续批次，一口气推进一个完整里程碑（例：paper-route 端到端、task-72 模型组装、R1 构造），每完成一批立刻接下一批，不要空转。
- 队列保持 ≥12 个待编译文件；若自己批次完成后队列<8，立即再写 6–8 个。
- 每批报告：文件清单 + EXIT + probe/checker + 下一批计划（可拆多条消息）。失败文件同批内修好再 append。

### 7.9 仓库优先（强制 prior-art 检查，2026-11-10 用户强调：仓库里有很多东西，先搜再写）

- **每个任务/残量/构造在写 Lean 之前**，必须先做精确 prior-art grep（精确类型名/定理名/结构名），覆盖：`LeanFormal/`（全库，不只 paper）、`Iut/`、`tmp/local-cft-port/`（可 import oleans）、`tmp/archive_sorry_20261028/`、`tmp/sheaf/gap-exploration-20261030/snapshots/`、`vendor/promachina/snapshots/`（源码参考）、`papers/motizuki_corpus/`（论文原文）。
- **报告格式**：`prior art: <file>:<line> <decl name>` → 决定 `reuse (import)` / `adapt (copy with V/theta/arith changes)` / `none (write new, 说明为何现有资产不适用)`。
- 已有资产能直接 import/复用就**不要重写**（例：`SourceUnitRegionHaarDataActual.sourceHaarActualFamily` 已含完整 injective theater family + link laws + OriginalInput；`FinitePlacePadicScalarStructure:29` 已有 `Fact (completionRationalPrime place).val.Prime` 实例）。
- 严禁再出现'重新造已存在证明'导致 EXIT=1 的情况；写新文件前先给 prior-art 结论（可一句话）。

### 7.10 深度搜索强制令（2026-11-10 用户要求：任何任务先深度搜仓库，禁止重复做然后忘记）

1. 每个任务/批次 STEP 0: 先跑 tools/xif_deep_search.ps1 -Query '<精确类型名/定理名/结构名>'，再读 coord/PRIOR-ART-INDEX.md 对应小节；
2. 批次报告第一行必须是 STEP 0 prior-art: <queries> -> <hits> -> reuse|adapt|none；没有该行不验收；
3. 新发现立即追加 coord/PRIOR-ART-INDEX.md（日期 + file:line + decl + reuse/adapt/none），否则视为未完成；
4. 禁止重证已存在结果；能 import 就 import；vendor 等独立工程不能 import 时须写清为何现有资产不适用；
5. 必须搜索旧尝试目录（tmp/sheaf/xif/paper/S2xxx、S3xxx、archive、gap-exploration）；
6. 报 pins/registry 必须带版本/日期（当前 registry frozen 14041），过期信息先核对.
