# 本仓库与 LANA/iut：差异、价值与合作入口

日期：2026-11-20  
读者：本仓库维护者、LANA/iut 维护者，以及决定下一步研究投入的人  
用途：说明两边分别做了什么、各自边界在哪里，以及本仓库的具体成果怎样变成一项可审查的合作任务。

本文以用户指定的 [R0–R7 交接](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md) 第 19 节为 III.3.12 当前状态的主要证据，不从论文开头重做审查。本文把工作树中的 Lean 源码、完整证明思路、已编译证明、目标闭合和论文语义验收分开描述；出现 `Actual`、`Source` 或 `proved` 字样本身不作为验收证据。

**如何使用这份长报告**

| 你要决定什么 | 首选入口 | 读到什么就可以停 |
| --- | --- | --- |
| 值不值得给 LANA 写信？ | [给维护者的结论](#decision) → [正向数学资产](#assets) | 能指出一个有名字的定理、一个具体消费者以及中间还要核对的等式。 |
| 哪些东西是我们多做的？ | [资产](#assets) → [两仓实测差分](#overlap) → [两个本地路径的实际调用](#local-foundations) | 区分本地证明、上游已有代码、同代码在新问题中的使用。 |
| 我想亲手验算一个例子 | [固定例的三种槽策略](#worked-example) | 能独立算出默认、恰等和有余量三个数，再指出哪一步还在模型之外。 |
| 想知道 LANA 到底证明到哪里 | [下游证明及 Wall](#lana-chain) → [字段对照](#dictionary) | 能写出两个已知蕴涵的方向，知道哪一方向不能使用。 |
| 准备负责原文这一步 | [来源接口](#source-contract) → [R0–R7 与 IV](#r-milestones) | 能从同一输入指出第一项欠缺的对象，而不是复述最终不等式。 |
| 今天准备联系对方 | [可直接发出的短消息](#outreach) → [合作验收单](#review-contract) | 明确请对方审查什么，以及这次没要求他们接受什么。 |

路线图中的链接都指向本文件。涉及第三方代码的路径以第 1 节的 LANA 提交为准；本地路径相对于项目根目录，除非另有说明。

<a id="decision"></a>

## 0. 一页结论

**本仓库不是“已经证明原文 III.3.12”的仓库，也不是“没有可交付成果”的仓库。它的差异化价值，是把原文来源侧的缺口拆到了可构造、可反驳、可交接的精度。**

LANA/iut 的强项是：有具体的 `InitialThetaData`、具体的 Corollary 3.12 variant 数据、Theta 区域之后的 hull/log-volume 接口，以及已证明的 `Cor312VariantHolds → ClassicalABC` 下游链。LANA 明确把 variant 本身列为未证明，并把 multiradial algorithm 产生 Theta 区域这一段列在项目范围之外。

本仓库最有用的对接点，正是这个来源侧空位：

1. 本仓库把 Theorem 3.11 的 `OriginalInput` 边界写成 Lean 类型，并且没有把 evaluation 输出偷塞进输入。
2. 它已有从 source choices 出发的 procession/profile 与 Ind1/Ind2 quotient 载体，以及对这些接口真正能表达什么的证明。
3. 它把 xi-e ⇒ xi-f 的实数消费者写成精确接口：若原文允许输出族有正确的 q-readout 覆盖，且每个输出受原文 hull 上界控制，就可推出目标比较。
4. 它也明确证明了某些“看起来能接上”的路线确实不够：标量 profile 丢失槽标记；当前 value-layer hull 在指定假设下无界，不能冒充论文有限 hull。
5. 最新交接把剩下的首个判别任务锁到具体输入 `p=3, ℓ=5, d=3`、目标槽元组 `(G,B,B)`、换位 `τ=(2,0)`：从 III.3.10.2 的实际 evaluation 构造 carrier map，检查 `E_τ(1) ∈ U_{2,3}`。

最值得直接展示的正向结果有两类：本仓把 q 的消失阶和剩余次数一起带进带符号读数；还把有限位张量整格的相对 Haar 对数送入一个明确方向的 hull 不等式。它们的证明不以整条 III.3.12 已解为前提。上游已有自己的 q 和 hull 实现；这些本地结果的用途是给出来源和归一化的对照，而不是替上游补一个事实上已存在的定义。

两条尤其适合向维护者展示的证据：附篇 A 用 `ℚ₃ × ℚ₃` 给出一个**满秩格与其 hull 仍差指数 3**的算例，说明相对 Haar 下界不能升级为等式；附篇 E 指出旧 `SourcePilotRegionData` 不仅“没构造出来”，而且已有 `sourcePilotRegionData_isEmpty` 的 Lean 证明体。前者可以拿来核对体积，后者明确告诉接收方**哪一个旧接口不应移植**。

所以，最合适的请求是：**LANA 已从 `InitialThetaData` 定义具体模型区域，并证明给定变体不等式后的 ABC 归约。本仓有来源侧的定理和一个能区分两种读数的固定例。请一起审查：原文求值能不能把该例中的一个指定点送进同一输入的允许区域？** 不需要对方先接收整仓，也不要求先相信原文 3.12。

<a id="snapshot"></a>

## 1. 比较快照与证据标准

| 项目 | 本次核对的版本 | 说明 |
| --- | --- | --- |
| 本仓库 `D:\lean` | HEAD `a997af4b1cb2339d1e7403ef0781a16f809f4476`，2026-11-15；比较使用 2026-11-20 的当前工作树 | 工作树有许多修改/未跟踪文件；若干关键证据不是 HEAD 提交内的干净快照。本文按当前本地文件内容说明，并在引用处标出相关路径。 |
| LANA/iut | `main` = `553076af459e7a401bfee63a4607814d1c854477`，提交日期 2026-11-03 | 2026-11-20 的 `FETCH_HEAD`、本地 `origin/main` 和 GitHub 官方 refs API 返回同一 SHA；续办时一次 `git ls-remote` 连接被重置，改用 API 独立复核成功。上游引用固定在此提交；本地 LANA 克隆工作树干净。 |
| Lean 工具链 | 本仓库 `leanprover/lean4:v4.32.2`；LANA `leanprover/lean4:v4.32.0` | 不是可直接互相 import 的同一构建环境。两边 Mathlib 与 Lake 依赖固定也不同；跨仓移植需走版本/接口适配。 |
| 本轮编译验收 | 未运行 | 交接 §19.5 对当前固定例明确记载 `statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 均为 `NOT_RUN`。这不否定源码里已有证明体，但不能把它写成已重验或 3.12 已闭合。 |

**证据的读法**

可对外分享的上游起点：[固定提交的 README](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/README.md)、[具体变体](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/ThetaRegion.lean)、[ABC 消费者](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/MainTheorem.lean)。本仓非提交文件则需要随附，不能请对方按本地盘符取阅。

- “源码中有 Lean 定理/证明体”指该文件写出了相应声明与证明项；本轮没有重新运行 Lean/watchdog 时，不升级成“当前版本已编译”或“kernel-closed”。
- “条件消费者已证明”与“消费者所需条件已构造”是两件事。例如 `S1447`/`S2452` 的逻辑消费者存在，不代表原文 output family 已经构造。
- “模型中算出数值”与“证明原文对任意合法输入的结论”是两件事。固定 `p=3, ℓ=5, d=3` 的 literal 模型计算不能代替全量词的原文结论。
- 本文不按 Lean 行数、文件数或 Project import 数评估进度。它们不说明目标是否减少了真实缺口。

## 2. 两边究竟在证明什么

| 维度 | 本仓库 `D:\lean` 当前 3.12 工作 | LANA/iut `main` |
| --- | --- | --- |
| 主要问题 | 从 III.3.11 的原文来源数据，沿原允许 evaluation/output 语义，接出 III.3.12 xi-e/xi-f 比较。 | 把指定的 Corollary 3.12 variant 作为显式前提，证明它足以推出标准 ABC；同时形式化与 variant 相关的具体输入和数学结构。 |
| 输入侧 | `Theorem311Source.OriginalInput` 包含 Definition 3.1 数据、Hodge-theater family、索引等价和 arithmetic alignment；它不包含 Theorem 3.11 的 evaluation 输出。 | `InitialThetaData` 是具体结构；`concreteVariantData D` 从 `D` 派生 q-pilot 与 RHS 数据。 |
| 3.12 对象 | 重点是原文允许的实际输出族、其标记 readout、原 hull 与有限性，以及来源映射。 | `Cor312VariantHolds` 是维护者指定的变体。`RHSData.thetaPilot` 在抽象层是字段，在具体层从 `D` 构造；不声称已识别为原文算法的允许像。 |
| Ind1 读法 | 交接追踪原文允许的标签/槽重排，以及一个实际输出是否由原 evaluation 产生。 | `Cor312VariantHolds` 采用 IUT IV 指定标签读法；`Cor312LiteralHolds` 才是对所有 label positions 的 literal reading。代码证明 variant 蕴含 literal reading；反向步骤不因此自动成立。 |
| ABC 端点 | 仓库中有 ABC bridge 与大量条件消费者，但本次原文 3.12 研究没有验收一条无条件 ABC 证明。 | `Iut.classicalABC_of_variant : Cor312VariantHolds → ClassicalABC` 已给出明确下游定理。它证明的是蕴含，不是 `Cor312VariantHolds` 本身。 |
| 当前成果性质 | 来源侧对象模型、部分 source quotient、精确下游接口、阻碍反例/自然语言推导；固定输入的原文来源桥仍开放。 | 更集成的具体输入/下游推导链；variant 与原文算法的关系有明确 honesty boundary，前件本身未证。 |

LANA 的 README 把这一区分写得很清楚：仓库不声称 verify IUT，variant 本身 unproved/out of scope，而 ABC implication 是已证明结果。参见 `D:\lana-iut-latest-20261120\README.md:5`、`:44`、`:52` 与 `Iut\MainTheorem.lean:35`。

### 2.1 LANA 的 variant 不是已证明的原文 III.3.12

LANA 不是靠隐藏假设或一个 Lean `axiom` 把 3.12 填上。`Iut/Cor312/Statement.lean` 明说 variant 无 proof、无 axiom，并明确声明不能读作 Mochizuki 发表的 Corollary 3.12：

- 发表文本的 `−|log(Θ)|` 是 multiradial algorithm 输出；LANA 把 `RHSData.thetaPilot` 当作输入。
- container、log-volume、hull 与论文命题对象的对应，留作逐模块的 specification，不是该陈述文件内证明的定理。
- 输入类型中的 hull-admissibility 等条件是显式字段。
- variant 定义为 `X.qPilot.lhs ≤ X.rhsData.rhs`，见 `Iut/Cor312/Statement.lean:33`、`:40`、`:66`、`:78`。

LANA 的 `Iut/Cor312/RightHandSide.lean:26`、`:60`、`:84` 进一步明确：RHS 数据里有容器、procession、log-volume、hull 系统和 `thetaPilot` admissible regions；“产生这些区域的 multiradial algorithm”不在该仓库范围内。它证明了**给定区域之后如何取 hull 和计算 RHS**，没有证明**原文算法确实给出所需区域/输出**。

### 2.2 本仓库也没有因此自动赢得原文定理

本仓库的 `OriginalInput` 同样是输入合同，不是从所有原文允许的算术数据自动构造全部 Definition 3.1 对象的证明。它没有 evaluation output/readout 字段；交接的缺口正是从输入与实际 III.3.10.2 evaluation 生成原文允许输出，而不是把 `OriginalInput` 换一个名字就完成证明。见 [SourceOriginalInput.lean:41](../LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean) 与交接 `:1937`、`:1943`。

## 3. 本仓库在目标附近已经有的具体成果

以下是“可以拿给对方看”的数学对象和 Lean 定理，不是项目规模或抽象承诺。

### 3.1 原始输入合同明确到 Definition 3.1 数据

`LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean:41` 的 `OriginalInput` 精确包含：

- `initial : SourceDefinition31Data l`；
- `family : SourceHodgeTheaterFamily l V`；
- `index_equiv`，把 family index 对应到原 Theorem 3.11 的 `(n,m)` 整数对；
- `arithmetic_alignment`，保证每个 theater 的 arithmetic data 与初始 data 一致。

其后有可核对的 index 注入、theater 区分、horizontal/vertical shift 与 link 的 q/scale 兼容，以及 commuting-square 结构等定理。文件后段的 `source_root_bundle`、`sourceOriginalInputBoundary` 进一步登记 Definition 3.1 clauses 并把 evaluation/output 排除在输入合同外，见同文件 `:1550`、`:1640`。

**对合作的意义：**LANA 可以审查一个来源侧合同到底能否喂给 `InitialThetaData`；这比拿一个“任意 `ThetaData`”字段填满就宣布对齐，更容易逐项发现假设差异。**边界：**合同已有不等于它已从更弱输入构造，也不等于 evaluation 已经形式化。

### 3.2 从 source choices 构造了部分 procession quotient

`tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean:56` 把源数据生成的商作为 `SourceMultiradialCarrier`；`:67`、`:75`、`:82` 分别定义商上的 log-volume、possible-image 和 level。`:107` 证明 possible-image 非空，`:115` 给 Ind3 的上比较，`:126`、`:136` 证明 Ind1/Ind2 下商映射不变，`:146`、`:156` 给出 Ind3 下 log-volume 与 level 的行为，`:165` 从源选择得到商载体非空。

这里的“部分”是数学边界，不是谦辞：该文件开头 `:31`–`:34` 明确留下第一三角形的算法变换 `BPS → quotient target`，并说明没有用 `sorry`、`axiom`、`True`、`PUnit` 或 toy carrier 把缺口盖住。

**可交付点：**LANA 已有容器/hull 方向的 RHS API；本仓库的 quotient 载体可以作为候选来源 API，讨论它是否能为 `thetaPilot` 给出实际 image。此映射还没有证明。

### 3.3 一个重要的负向定理：标量 profile 已丢失槽标签

`S3138SourceProcessionProfileActual.lean:49` 证明实际 theater 的 Theta log-volume 对 family index 不变；`:59` 证明 source choices 间读数恒定。接着 `sourceStepXIProfile`（`:67`）的 possible image 按定义是同一个标量读数的单点集。

这排除了一个很容易消耗大量时间的错误方向：只要接口只携带这个标量 profile，再增加取值次数、迭代层、加权平均或对该常值再施函数，都无法恢复“标记在第几个张量槽”的信息。这个结论来自 Lean 中的真实 source profile，不是意见判断。具体固定例中，好槽投影为 `1`、默认坏槽投影为 `3^(-6/5)`，差 `6 log 3/5`；数值与标记细节见交接 `:1897`–`:1905`。

### 3.4 xi-e ⇒ xi-f 的数值消费者已经拆干净

`tmp/sheaf/xif/paper/S1447ReportFMarkedTraceActual.lean:326` 的 `s1447Comparison_of_exactCoverage` 与 `:337` 的 `s1447Comparison_of_signedCoverage` 是准确的实数证明：

- 若每个 paper-allowed output `D` 的 readout `ν(D) ≤ H`，并有一个实际输出满足 `ν(D)=Q`，则 `Q ≤ H`；
- 若没有等号见证，但每个 `ε>0` 都有允许输出满足 `Q−ε ≤ ν(D) ≤ H`，用中点反证同样得 `Q ≤ H`；
- `s1447Comparison_of_outputReadoutProjection`（`:354`）统一消费 exact 或 signed-epsilon coverage。

因此论文里的 “perhaps only up to some sort of approximation” 被落实为可检验的 exact/signed-epsilon 条件，不再用“存在近似”含混带过。**缺的不是实数代数这一步，而是实际的 paper output family、readout、coverage 和统一 hull bound。**

### 3.5 缺失的原文输出被列成可供 LANA 对接的结构

`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:124` 的 `S2452PaperOutputFamily` 不是一个已构造的结果，而是精确列出 xi-e/xi-f 需要交付的对象：

- 原文固定输入对应的输出集合 `P_C : Set (ActualOutput R)` 及其非空性；
- paper q 与 q 读数 `Q_C = -|log q|`；
- 输出读数 `nu_C` 及其与 source profile log-volume 的识别；
- 每个输出被 paper signed hull log-volume 统一控制；
- exact 或 signed-epsilon coverage。

给定这份结构之后，`:182` 的 `Q_C_le_signedHull` 和 `:247` 的固定 `C` consumer 可推出比较。该文件 `:12`–`:40` 直接说明：当前没有构造实际 paper family、readout、coverage 或 pointwise readout identification，且该结构在本文件没有 inhabitant。这个接口特别适合让 LANA 的 RHS/region 作者逐字段判断哪些字段已由他们拥有、哪些需要来源侧补造。

### 3.6 已证明 value-layer hull 路线会失败，不把错误有限性推给原文

`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean:379` 的 `sourceHolomorphicHull_logDegree_unbounded` 与 `:428` 的 `sourceHullVolume_eq_top_of_degreeFaithful` 证明：在**当前 value-monoid scaling model、pointwise degree-faithfulness 假设**下，hull 的 log-degree 无界、volume 可以是 `⊤`。

这不是说论文需要的真实 hull 也无限；结论恰恰是当前值层点值模型缺少原文 `O`-module / `IQ` 的限制结构，不能用它冒充论文有限 hull。更准确的表达是：本仓库已用定理排除一条错误替代路线，并把需要重建的 ambient structure 指出来。该文件目前是本地未跟踪文件，见第 1 节快照提示。

### 3.7 固定输入的自然语言计算给出了判别性试验

交接 §16.6 固定 `p=3, ℓ=5, d=3`，其中 `q_s = -(3/20) log 3`。这里要把三种 **literal 模型** 分开。下面三行共用同一 q，不能把一行的见证归给另一行：

| 第一行 `j=1` | 第二行 `j=2` | 全局模型读数，单位 `log 3` | 与 q 的差，单位 `log 3` |
| --- | --- | ---: | ---: |
| 默认槽 | 默认槽 | `-3/8` | `-9/40` |
| 默认槽 | 原槽 2 加两次整数据换位 `τ20`、`τ21` | `-3/20` | `0` |
| 两槽全开 | 三槽全开 | `-9/80` | `+3/80` |

第二行三个获益元组各给全局读数加 `(3/40) log 3`，总增益 `(9/40) log 3`，刚好填平第一种策略的亏损；**并没有再多出一个正余量**。多出的 `(3/80) log 3` 来自把第一行也放开。交接 §19.1 另以局部格指数记第二行所需乘积为 `3^(18/5)`，不能把这个未经同样归一化的乘积直接取对数当成最终增益。

三种数都不是 `H_orig`。这个区别直接影响分工：模型数值可独立复核，而实际 III.3.10.2 evaluation 是否给出 `E_τ(1) ∈ U_{2,3}` 需要来源侧论证。见[逐元组复算](#worked-example)与交接 §19.3。

### 3.8 普通单位的局部 p-adic witness 已有可复用定理

`Iut/Concrete/LocalConstruct/LogLattice.lean:361` 的 `exists_padicLog_eq_of_norm_le_rpow` 在适用的 valuation/norm 条件下构造 principal unit `u=1+a` 使 `padicLog (u)=y`。交接固定例令 `y=6/r_bad`，计算 `v_3(y)=7/10>1/2`，因此得到普通单位 shell 的标量 witness。

这个局部数值 lemma 能省掉重新证明普通单位对数的工作；它**没有**完成带标记 tensor 中的单位放置、槽换位、原 evaluation 输出成员关系或整体 readout 识别。`Iut/Concrete/ThetaRegion.lean`、`Ind1Invariance.lean` 等本地文件与 LANA 也存在重合，不应包装成本仓库独家成果。

## 4. 更大范围的本仓库：做了什么，不能怎样读

本仓库不是只有这几份 `S31xx` 文件。工作树 `LeanFormal/IUT/` 下有 `Foundations`、`ABC`、`ABCBridge`、`IUTI` 至 `IUTIV`、`Audit`、`Verification` 等；Θ 专题实际在 `Foundations/Theta`、`IUTII/Theta` 等处，并非同级的 `LeanFormal/IUT/Theta`。`coord/LEAN-INDEX.md` 将 `tmp/sheaf/xif/paper/` 标为当前活动正式化位置，将 `Iut/` 视作可复用来源。

从已有索引与交接可负责任概括的范围是：

- **基础层：**有限群商、局部域/赋值、Tate 曲线与 theta、Kummer/log-shell、有限 etale 与曲线/基本群等专题理论；大量供体散落在 `LeanFormal/IUT/Foundations/` 及相邻索引化的专题库中。
- **IUT I–III 对象层：**Definition 3.1 数据、Hodge theaters、几何/算术对齐、Frobenioid 与 Theorem 3.11/Ind1–3 的模型和来源合同；但“有对应文件”不等于原文所有构造已从 source input 推出。
- **IUT III 3.12 / xi-f：**存在 paper-oriented 消费者、条件式桥、值层 q/hull 模型、actual source profile/quotient、标记 coverage 消费者和阻碍定理。精确剩余工作见第 5 节，不把中间条件定理计成原文结论。
- **IUT IV/ABC：**存在许多高度、体积、算术、tensor/hull 条件消费者和 `Cor312ToABCBridgeInterface` 一类条件接口。目标文件和交接会区分“给定 hCor312 后能推出什么”与“如何构造源忠实的 hCor312”。本次没有验收无条件 ABC。
- **独立 ABC-only 分支：**交接 §17–18 研究了不经过原 III.3.12 的整数 ABC 归约和连分数路线，给出若干自然语言归约、精确量词/停止条件，但共同的全局估计仍开放。它是不同目标，不能拿来充当 3.12 证据，也不能拿 3.12 研究进展冒充完整 ABC。
- **研究工程：**有源索引、DAG、队列、审计账本和 Lean watchdog 验收规范。这使研究过程可以交接与追责；但队列/脚本也不是数学证明，而且须按现行 `SHEAF.md` 与索引使用。

交接文档的 R0–R7 不是八个已证明模块，而是端点、source q、paper readout、hull、算术消费者和下游高度估计的分层证明路线。§8–16 包含扭点域/单位格、different、Galois transport、标记槽、固定例和工作量判据的逐项研究；这些自然语言推导很有价值，但 §19.5 明确把当前固定例的四项 Lean/目标验收全部记为 `NOT_RUN`。

## 5. 3.12 还难在哪几步

| 必须过的关 | 有哪些基础 | 还缺的对象或证明 |
| --- | --- | --- |
| 同一输入的跨列求值 | `OriginalInput`、条带方块、模型重排 | 从实际 III.3.10.2 求值得 `D_τ`，识别标记及积分载体，证 `E_τ(1)∈U₂,₃` 与输出的原文履历。 |
| 从输出读回 q | 带重数的 q 除子、实际格、S1447 的 exact/epsilon 消费者 | 同一输出的投影、张量秩、位权和行权给出正确的 `Q−ε` 下侧覆盖。 |
| 原文 hull 的有限性 | 指定整格模型的 Haar 比较与局部有界性 | 在正确的 `O`-模上控制**所有**允许输出，而非只控制本例的三个置换或无界的值层模型。 |
| 从固定例回到全称 | 模型端已有有限枚举和族的分析 | 对每个原合格输入完成相应构造，再验来源语义；若向 ABC 走，还要接到 LANA 的指定槽读法。 |

第一行的点级成员是最便宜、最能区分路线的试验；不是后三行的替代。四项形式验收见 §14。

## 6. LANA 的优势和边界

| 优势 | 源码证据 | 不能多推的一步 |
| --- | --- | --- |
| 面向所有 `D` 的具体区域 | `Iut/Concrete/ThetaRegion.lean:359`、`:375`；在 `RHSData` 上算法化取 hull 和读数 | 不是原文多辐射算法允许像的来源证明。 |
| 变体到标准 ABC 的下游链 | `Iut/MainTheorem.lean:35` 组合 tripod 的三步；另有锁定有限例外式 ABC 的 Comparator | 前件 `Cor312VariantHolds` 明列且未证；历史验收的对象是蕴涵。 |
| 算术、几何及外部包的集成 | `README.md:46`、`:54`；`lakefile.toml` 固定 `genl`、`pi1`、`belyi` 等；[逐点 étale Θ 的例子](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/EtaleTheta/ThetaLevelKummer.lean#L442) | 几何表示的 Tate orbicurve Theorem B 与 `LocalThetaData.PivBad` 间的桥，README 仍列为未形式化。 |
| 已直接研究争议中的 xi 与 wall | 附篇 B.3–B.6 的 `WallEquiv`、`LogLink` 给出具体模型下的蕴涵、等价和不足性证据 | 既不能声称本仓独家研究 xi，也不能把格模型中的等价原样赋予原文 evaluation。 |

## 7. 重叠、差异和不该夸大的地方

### 7.1 已知源码重叠

交接 §16.1 曾点验七份文件。本次把同一问题扩大到两边 **`Iut/` 子树内的全部 `.lean` 文件**：本仓 950，LANA 694；694 个共有路径逐份比对，统一换行后全部相同。本仓另有 256 个路径，全部在 `Iut/Foundations/`。这个统计不含 `LeanFormal/`、`tmp/sheaf/`、`Iut4Sec1/`、外部包或跨路径同义实现，详见[可复算清单](#overlap)。因此：

- 这些文件不能作为本仓库相对于 LANA 的独家成果；
- 不能因一份文件在本仓库的目录中，也就把它称为“我们先做/只有我们有”；
- LANA 对同一代码继续维护的具体版本，应以当前上游文件和其提交为准；本地工作树里的差异需单独 diff。

### 7.2 真正的互补面

| 缺口/能力 | LANA 已有 | 本仓库已查到 | 仍待合作证明 |
| --- | --- | --- | --- |
| 具体初始 Theta data | `InitialThetaData` 及 `concreteVariantData D` | `OriginalInput` 对 Definition 3.1/Hodge theater family 的 source-facing 合同 | 两种结构在定义/量词/依赖上是否有保语义的 map 或 equivalence。 |
| Theta-pilot region | 抽象层 `RHSData.thetaPilot` 为字段；具体层从 `D` 构造 `thetaPilotOn` | actual source quotient/profile 与槽标记模型研究 | 对同一输入，从原 evaluation 构造输出、核实它在所指区域内，并对齐读数。 |
| 右端 hull 与 readout | hull system 和 procession-normalized RHS 定义 | paper signed-hull consumer 与 finite-hull 失败分析 | 两边的 ambient object、volume 和标记 readout 是否相同。 |
| q-vs-hull 数值比较 | 若 `Cor312VariantHolds`，已能往 ABC 走 | exact/signed coverage + uniform output bound 的数值 consumer | 给出真实 `P_C`、q projection、readout equality、upper bound、finiteness。 |
| 最终目标 | ABC conditional on variant | 原 III.3.12 source bridge 的自然语言与固定判别例 | 先证明固定输入来源 membership，再决定是否能推全量词 variant/original theorem。 |

最可辩护的“本仓库优势”就在表中第二、三、四行的来源侧：**没有停在另一个 `q ≤ hull` 布尔字段，而是把真实 output/readout 的消费者和来源缺失物拆开，并已发现现有标量模型与值层 hull 不足以填它们。**

### 7.3 劣势与合作风险

- 本仓库没有已接受的原文 III.3.12 theorem；来源 evaluation 桥仍未构造，四项当前验收未运行。
- 当前工作树不干净；关键自然语言交接与部分 Lean 文件未跟踪/未提交，LANA 维护者无法通过本仓库 HEAD 自动重现全部引用。
- 两边的 Lean 版本、依赖树和命名/API 不同；不适合第一步就 bulk import。
- 本仓库研究跨度很广，`tmp/sheaf` 有不少专题试验。未经目标可达性审查，无法承诺每个文件对当前 LANA variant 都有用。
- 固定输入数值成功只证明该模型有余量，不自动推广到任意 `D`；槽置换定理/静态 region membership 也不自动证明原 evaluation 生成了该点。
- 若把“条件定理已证明”宣传成“条件已构造”，会损害与 LANA 合作的可信度。必须把数学已证明项、条件假设、来源构造、编译状态分栏报告。

## 8. 怎样并入：把工作分成三次可独立接受的交付

1. **字典审阅。** 先定要证明原 III、全槽 literal，还是 LANA 的 IV 固定槽变体。选同一 `D` 和对应 source input。独立交出某一坏位的有符号 q 等式，或某个有限张量块的相对 Haar 等式；附篇 A、F 列了现有字段。
2. **固定例来源。** 把 `(B,B,G)` 的标记点沿 `τ=(2,0)` 送到 `(G,B,B)`。记录实际输出、源和靶的整格、目标区域的类型、成员及投影读数。模型点与原文成员分开验收；若只有前者，给出缺的结构态射。逐项任务书见附篇 E.9、F.8。
3. **推广与移植。** 只有第二项过关，才检查另一换位、整片区域、所有输入、全部允许像的有限性，以及与 LANA variant 的方向。独立有用的第一项不必等待这项大工程。双方各留自己的依赖锁，按实际 import 闭包移植，交付包见附篇 D.6。

`S2452PaperOutputFamily` 是第三项的验收表，不是已完成的数据：`P_C` 要有原文成员资格，`readout_eq` 在同一输出上成立，`upper` 约束每个允许输出，`coverage` 从下侧命中 q。这四件事都不是只在 `RHSData` 找一个相近名字就能实现。

<a id="outreach"></a>

## 9. 可以直接发给 LANA 的说明

### 英文短版

> **Subject: A fixed III.3.12 source-evaluation test for your concrete theta region**
>
> We compared our Lean work with `lana-agents/iut` at `553076af`. Your code constructs a concrete theta region from `InitialThetaData` and proves `Cor312VariantHolds → ClassicalABC`. Our complementary results concern the source-side q multiplicity, a relative Haar comparison for integral tensor lattices, and what information a scalar procession readout loses.
>
> Could we review one example together? For `p=3, ℓ=5, d=3`, an all-slot model clears the signed q readout by `(3/80) log 3`; opening only the second row gives equality. What neither calculation supplies is an actual III.3.10.2 evaluation sending the marked point for `(B,B,G)` into the allowed target region for `(G,B,B)` under the swap `(2,0)`. We can supply the declarations and calculation. Which concrete carrier and normalization would you use to test that membership? We are proposing a fixed-input review, not a proof of Corollary 3.12 or a request to merge the repository.

### 发出前请保留的限定

信中附上源码或固定提交的入口，尤其是被 Git 忽略的本地研究包。若不附可重建的依赖闭包，就明确这是一份审阅材料，不是已能在 LANA 工具链直接编译的 PR。未构造的 `BPS → 商`、原允许输出族和实际求值映射要保留原名，方便对方答复具体是哪一项。

## 10. 合作时先对齐哪些读数

固定例的 `q_s` 与 S2452 的 `Q_C` 都是有符号读数；附篇 C 的 `Q` 则是未开根的非负 q 高度，经 `−Q/(2ℓ)` 才得到它的比较左端。§11 的 `H_lit` 来自指定模型的见证计算，`H_orig` 指全部原允许像的 hull。LANA 供 ABC 消费的是指定槽 `H_IV(D)`，其源码给 `H_IV(D) ≤ H_literal(D)`；没有把 §11 的数字识别为这个 `D` 的完整右端。

<a id="worked-example"></a>

## 11. 一份可以在纸上独立复核的固定例

这里复算的是交接 §16.3、§16.6 指定的算术选槽模型。
以下字母 `G` 表示好位置，`B` 表示标记的坏位置；不表示好坏两种 Hodge theater。
始终使用有符号对数，故 `−9/80 > −3/20`。增加可选槽改善下界，是使读数变大、离零更近。
数值表只对这里的区域、见证与归一化作断言，不把它当作已在 Lean 中计算的 LANA 全局 RHS。

### 11.1 输入从哪里来

交接给的是一族曲线，不是单独挑的两个实数：

```text
k₀ = ℚ(√13),  α = (1+√13)/2,  N(α) = −3
d = 3+30t,  u = α^d
E_d : y²+xy = x³+u
c₄ = 1,  Δ = −u(1+432u),  j = 1/Δ
```

- 素数 3 分裂为两个位置。在 `(α)` 处，判别式深度为 `d`；在共轭位置，它是单位。
- 因此同一素数上真的出现两种深度，并各占权重 `1/2`。不是把不同素数拼成一个混合测试。
- 本次固定 `t=0`，故 `d=3`。选 `ℓ=5`，根深度 `x=d/(2ℓ)=3/10`；好位置深度为 `0`。
- `d` 在这里是曲线族的整数参数，不是 `k₀` 的次数，也不是两行的槽数。
- `j=1` 有两个槽，`j=2` 有三个槽。这里 `j` 是行标；上面写 `j=1/Δ` 时是曲线的 j 不变量。
- 取默认槽时它总在末位。放开一行，指允许把标记搬到该行所有位置，然后对每个有序元组取 hull。
- 取 hull 后才按元组权重求和，最后两行各占 `1/2`。先对所有元组平均再选择一个换位，是另一运算。

曲线、标记和根的来源见[交接 §16.3](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1467)。
该节还核查了指定族的大像条件；这些算术数据并不提供两个相邻 theater 间的 evaluation。

### 11.2 不用符号计算器的计数法

对固定元组，定义“代价”为读数除以 `−log 3`。这个数越小，实际有符号读数越大。
若可选槽中有 `G`，指定的整序见证给代价 `0`；若全是 `B`，代价为 `j²x`。
选取的 `k` 个不同位置都为 `B` 的权重是 `(1/2)^k`；这是元组的乘积权重，不依赖于有没有重复出现同一地方。
因此第 `j` 行选 `k` 个候选位置时，平均代价为 `j²x / 2^k`。

| 行 | 槽位数 | 选一个 | 选两个 | 选三个 |
| --- | ---: | ---: | ---: | ---: |
| `j=1` | 2 | `x/2` | `x/4` | 无此情形 |
| `j=2` | 3 | `2x` | `x` | `x/2` |

对照物不是第一行的任意标记，而是同一输入的固定 q。其代价为 `x/2`，所以 `q_s=−3 log(3)/20`。
两行默认：平均代价 `(x/2+2x)/2=5x/4`。这给 `−3 log(3)/8`，比 q 少 `9 log(3)/40`。
仅第二行两个候选：平均代价 `(x/2+x)/2=3x/4`。这给 `−9 log(3)/40`，还比 q 少 `3 log(3)/40`。
仅第二行三个候选：平均代价 `(x/2+x/2)/2=x/2`。恰达到 q，不需要从第一行借余量。
两行全开：平均代价 `(x/4+x/2)/2=3x/8`。正余量来自第一行的改动，等于 `x log(3)/8`。
因此只靠这套整序见证、按新增候选位置计费，从两个默认位置起，至少需增加两个位置才能达到 q。
一次增加给第二行的改善已是一次增加的最大值，仍然不够；把两次都用在第二行即可。
**这是见证数目的最小值，不是原文证明需要几步、几人或几天的下界。**

### 11.3 逐项对照：第二行的八个有序元组

表中代价没乘 `−log 3`，也没乘行权重。默认标记为槽 2，槽号从 0 开始。

| 目标 `(0,1,2)` | 默认槽代价 | 三槽择优后 | 理由 |
| --- | ---: | ---: | --- |
| `(G,G,G)` | `0` | `0` | 默认就好。 |
| `(G,G,B)` | `4x` | `0` | 槽 0、1 都可改善；只计一次。 |
| `(G,B,G)` | `0` | `0` | 末槽为好。 |
| `(G,B,B)` | `4x` | `0` | 要把默认标记搬到槽 0。 |
| `(B,G,G)` | `0` | `0` | 末槽为好。 |
| `(B,G,B)` | `4x` | `0` | 要把默认标记搬到槽 1。 |
| `(B,B,G)` | `0` | `0` | 作为目标时无改善；却是两个关键拉回的源元组。 |
| `(B,B,B)` | `4x` | `4x` | 没有好槽可选。 |

每个元组的权重是 `1/8`，第二行在全局再乘 `1/2`。
每个改善项的全局收益是 `4x × (1/8) × (1/2) × log 3 = (3/40) log 3`。
三个获益项合计 `(9/40) log 3`；两条换位都改善 `(G,G,B)`，不能把它计算两次。
第一行从默认改为两槽时，唯一获益目标是 `(G,B)`，权重 `1/4`，改善 `x`。
乘行权重 `1/2`，独立给出 `(3/80) log 3`。这也是一个不依赖上一张公式表的交叉核对。

### 11.4 这不是从十二个元组里挑十二个不相容的动作

第一行四个、第二行八个，共十二个元组。原文动作拟施于整条带数据的源，而不是为每个元组分别发明一个动作。
`τ20=(2,0)` 是对换槽 2 和槽 0，不是把元组从第三行搬到第一行；`τ21=(2,1)` 同理。
目标是 `(G,B,B)` 时，沿 `τ20` 拉回得到 `(B,B,G)`；源默认槽恰是好槽。
目标是 `(B,G,B)` 时，沿 `τ21` 拉回也得到 `(B,B,G)`；两次检验不等于用了两种互不相干的算术输入。
第三个获益目标 `(G,G,B)` 可由其中任一换位处理。对每个目标投影取并后的 hull，获益项不因两个见证而倍增。
这里用到了上游在 `Ind1Invariance.lean` 已写出的元组和张量**同时**重排。这些重排公式不应作为本仓原创出售。
原文还含自然子胶囊的嵌入；对换并不一般保持固定的嵌入。需要说明是连嵌入一起运输，还是原求值许可另一种代表。
若找到整个带嵌入方块的自然性，未标记槽交换 `η=(0,1)` 可用 `τ21=ητ20η` 减少重复论证。
若没有，自由置换标签集合只能给出模型的同构，不能把任何一个原输出登记为允许。

### 11.5 第一个点为什么有辨别力，也为什么不够

在同一个目标 `(G,B,B)` 看标记乘数作用于 `1`：

| 步骤 | 好槽版本 | 默认坏槽版本 |
| --- | --- | --- |
| `j²` | `4` | `4` |
| 根深度 | `0` | `3/10` |
| 投影绝对值 | `1` | `3^(−6/5)` |
| 坏、好两次对数读数的距离 | 两者相差 `(6/5) log 3` | 同一目标元组中的比较 |

如果某个源接口只能给所有选择同一个实数 `L`，那么任何只吃 `L` 的函数都在两种选择给出同一个值。
上表要求两个不同的投影值，这就构成了对**该接口充分性**的否证。在更早的有标记张量层找代表，仍然是一条不同的路线。
另一方面，即使构造出 `E_τ(1)` 并证明它属于原区域，一个点的集合也不能直接当作有正 Haar 体积的区域。
要支持第 11.3 节的体积论证，还要运输格或邻域，或证明 hull 的定义和归一化能把该点级见证提升成所需的整体比较。
而要证明原 hull 有限，依赖的是**所有允许像**的共同上控制，不是刚刚选择的三个实际例子的有限性。

三个不同的停止结果由此都很有用：找到来源成员，才做整区域；只找到静态区域成员，记录缺少来源；
只测到恒定标量，则把这条路线停在标量之前，不重复跑枚举。

## 12. 两个可单独交付的算术接口，以及一个几何消费者

本节回应一个实际问题：对方若暂时不研究 III.3.10.2，是否还能从这套工作得到有用的东西？
答案不是“拿走全部 Foundations”，而是下面这些可逐条检查的接口。附篇 A 另列靠近 q 与相对 Haar 的主供体。

### 12.1 Frey 曲线：不仅知道支集，还知道约分后的准确重数

输入是本仓 `IsABCTriple a b c`，即本原正整数情形。对象是一个实际的 `ℚ`，其 `.den` 是**约分后**的自然数分母。
见 `LeanFormal/IUT/ABCBridge/Arithmetic/ABCInvariantCoprimality.lean:15`、`:25`：

```text
T = a² + ab + b²
J = 256 T³ / (a² b² c²)
```

给定素数 `p`，`ABCInvariantLocalValuations.lean:228` 至 `:280` 里的声明可以逐个读：

| 对象 | 准确结论 | 一个可检验的区别 |
| --- | --- | --- |
| 奇素数 `p` | `v_p(J.den) = 2 v_p(abc)` | 不只是“`p` 是坏素数”；保留重幂的深度。 |
| `p=2` | `v₂(J.den) = max(0, 2 v₂(abc) − 8)` | 在 `ℕ` 的减法中会截断为零。 |
| 奇素数支集 | `p ∣ J.den ↔ p ∣ abc` | 可从约分后的分母返回原三元组支集。 |
| 二素数支集 | `2 ∣ J.den ↔ 5 ≤ v₂(abc)` | `2 ∣ abc` 不足以推出 `2 ∣ J.den`。 |

验证思路：`T` 与 `abc` 互素；奇素数不会从系数 256 抵消，2 则最多抵消八次。
例如 `(1,8,9)` 与 `(1,32,33)` 都是本原三元组。前者 `v₂(abc)=3`，后者为 `5`。
直接用有理数约分得到分母 `81` 和 `4356`，2 重数分别为 `0` 和 `2`。这两个例子故意跨过 `v₂(abc)=5` 的阈值。
从整数输入出发的合作者可以先核对这个预测，而无须接受有关 theater 或 Θ 区域的任何假设。

**上游对照。** `Iut/Tripod/Height.lean:558` 的 `posLog_j_eq_of_mem_badAll` 从上游自己的乘性约化和 Tate 数据得到 `qOrder × inertDeg × log p`。
本地结果回答“给定 `a,b,c`，约分后的奇位极点到底几重”；LANA 的结果回答“给定其曲线和 Tate 局部数据，这个极点怎样进入高度”。
一个可能的适配是先识别两边同一条曲线、同一 `j` 和同一地方，再核消失阶与绝对值的归一化；不能直接把两个公式等号拼起来。
这个方向与交接 §17 的浅极点、深极点分拆有关，但原 III.3.12 并不依赖先解决这个整数 ABC 分支。

### 12.2 范数与赋值：应移交适配经验，不应把 donor 的定理说成原创

`tmp/local-cft-port/PadicField/FieldNorm.lean:28` 的范数定理适用于 `ℚ_p` 有限扩张构成的域塔；
`:50` 的 `PadicField.v_norm` 还要求 `x ≠ 0`。所用的是离散赋值，结论是：

```text
v_K(N_{L/K} x) = f(L/K) · v_L(x)
```

代码头标为 LANA Project。它在本仓是**已有来源的移植供体**，不是“LANA 缺一个范数定理”的证据。
本地额外可指的适配在 `tmp/sheaf/xif/paper/Mzk1PadicFieldValuedQpActual.lean:33`：
`padicField_v_eq_valuation` 在底域 `ℚ_[p]` 把 donor 的 `PadicField.v` 和该域现有的 valuation 对齐，随后 `:63`、`:66` 产生相应 coherence。
`coord/LEAN-INDEX.md` 在“局部范数公式”记录该局部包的历史 watchdog `DONE`。本报告没有用今天的工作树重新验证。

为什么这个细节决定能不能直接复用？LANA `Iut/Concrete/LocalTheory.lean:59` 的 `ordp` 是按 `ordp(p)=1` 归一化的实值量。
它由完成域的范数、`localDeg` 和 `log(p)` 定义。离散赋值的 uniformizer 取值为 1，并不总是 `ordp` 的 uniformizer 取值。
适配时要逐个说明塔、有限维实例、剩余次数和分歧指数，并确认非零条件。只在 `ℚ_p` 上证明一致，不能越过这张有限扩张的字典。
**可以交付的东西是**底域的一致性证明及准确的未接入条件；不是第二份 LANA 数学同名副本。

### 12.3 Step V 的实际张量点为什么比一个体积字段更有用

`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean:668` 不是把 possible image 声明成任意集合。
它给出可拆开的成员见证：`φ ∈ Φ`、`x ∈ O_hol`、以及 `s = φ(tprod(update 1 istar varpi) * x)`。
所以若作用族含恒等且单位参考含 `1`，可直接指定 `φ=id`、`x=1`，保留下来的不只是读数，还有**哪一个槽、哪个乘数、哪个张量点**。
这恰是前述单点检查所需的形状；但该见证来自 Step V 的算术输入，不是 III.3.10.2 的原求值。

同文件 `:678` 的正测度定理要求 `varpi ≠ 0`、至少一个 `φ₀∈Φ`、以及张量块上的 Borel/Haar 配置。
它并不靠“单点测度为正”：乘数为单位，参考开集经可逆作用得到的整个像给出正测度。
所以合作若要从“有一个原成员”推进到“有一个原正体积区域”，已有合适的比较模型可用。
对方要核的是**整片**见证怎样由同一来源送过去，而不是重新证明开集的 Haar 性质。

再往后 `:814` 的 `arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound` 是一个有方向、有常数的上界。
需要给出到有限乘积的代数等价 `e`、保持指定 unit-log 格的作用族，及包含所有高分歧因子的例外集。
写 `λ=ord(varpi)`、`d_i=ord(different_i)`，右端是 `(-λ+Σd_i+1) log p + Σ_exceptional(3+log e_i)`。
左端是**指定 Step V possible images 的 hull**的归一化对数体积。这与原文所需的全部实际 evaluation 像不是同一个已识别的集合。
这里可以建议的合作：给同一模型点和格，比较 LANA 的局部上界是否采用相同例外集、相同分母、相同方向。
若三者相同，两边有共同验算对象；若不同，对方能指出第一个不一致的项，而不是被要求接受一个新总定理。

## 13. 不在热点文件旁边，但能解释整仓做法的四处代码

这四项代表输入、代数、条带与审计四层。选择标准是能沿着真实的值或定理指到下一处使用；不是按目录数或行数列功劳。

### 13.1 IUT I：让坏位集合只来自一个截面

在 `LeanFormal/IUT/IUTI/InitialTheta/SourceSignQuotientConstruction.lean:30`，`SourceSignQuotientGeometricCore` 包括带符号作用的几何对象、商见证、群正合列、标量扩张及尖点。
该结构刻意不放一份可独立改动的坏位选择。`toSourceCompletionSignQuotient`（`:74`）把已有几何核与实际 `SourcePlaceSelection` 组装在一起。
`:166` 的 `toSourceCompletionSignQuotient_selected_places` 与 `:187` 的 `toSourceCompletionSignQuotient_place_comap` 给出选择与收缩的核对。
再沿 `:196` 的 `toSourceSignQuotientData`，可以把这一个截面下传，不必在两个结构里猜“同名坏位”是否其实指两个集合。

这为什么值得保留？右端有一个 selected place，左端的 q 来自它的上方位；如果允许两个输入分别自由选择截面，对齐失误仍有可能在类型层看似合理。
这为什么不足以称原 theorem？几何核自身仍要作为该构造的输入。不应说仅凭一条任意椭圆曲线已经生成了全部群、商及 witness。
与 LANA 对接时，若对方已经有指定截面和上述结构，就优先从它们生成本仓需要的投影；不把整个 source 结构原样复制过去。

### 13.2 IUT II：经典 Kummer 单射与曲线上逐点求值不相同

本地 `LeanFormal/IUT/IUTII/Kummer/AbsoluteKummerInjection.lean:70` 通过一个单位的 `n` 次根 `α` 给出 `σ ↦ σα/α`。
条件是底域特征 0、`n ≠ 0`、Galois 作用在 `μ_n` 上平凡。本地 `:46` 给出“所有 `n` 次单位根已在底域”的充分条件。
`:119` 的 `absoluteKummerMap_eq_one_iff` 识别核：类平凡，当且仅当这个单位本身是底域里的一个 `n` 次幂。
`AbsoluteKummerQuotient.lean:60` 的 `absoluteKummerMapQuotient_injective` 真正把它用到商群 `Kˣ/(Kˣ)^n`，而不是只在文件首行 import。
此处的 Lean 余域是群同态；`AbsoluteKummerContinuity.lean:33`、`:74` 再处理局部常值与连续性。这个商定理本身不声称满射。

LANA 的问题更具体。`Iut/EtaleTheta/ThetaLevelKummer.lean:342` 定义逐点的 `EtaleThetaAtPoint`，`:442` 构造 `exists_etaleThetaClass`。
那里要有 Tate 参数、相应偶数层和点的合格条件；在这些条件下沿点的截面限制类，读出实际 theta 层函数值的 Kummer 类。
所以向 LANA 说“你们缺 Kummer 求值”是不准确的；向本仓说“上游已经有某个求值，因此两列之间的算术来源箭头一定已经有”也不准确。
前者已有几何曲线层的逐点限制，后者要的是同一输入、指定换位的相邻列允许区域成员。检验时先说清是哪一种 evaluation。

`LeanFormal/IUT/IUTII/Kummer/CompatibleRoots.lean:25` 提供另一个很便于单独核对的结论：
给同一 `value` 的两个相容有理根系，固定 `q∈ℚ`，两次取根的比值升到 `q.den` 次方为 `1`。
证明是把 `q.den·q` 化为整数、用两个根系在指数 1 处的相等；结论判断选择误差是挠元。
它既不为任意算术幺半群造出一个相容根系，也没有说明张量槽、格或体积不受这个挠元影响。这是合理的停止位置。

### 13.3 Frobenioid 与条带：已有作用的自然性，不等于识别了论文的群

`LeanFormal/IUT/IUTII/Frobenioid/PrimeStripUnitsActionFactorization.lean:52` 输入 `g_v : G →* Π_v`。
现有 `F.unitsAction v` 与 `g_v` 复合，得到具体作用于该条带单位群的同态；`:81` 同样给出 times-mu 商上的作用。
`:74` 证明再沿 `H →* G` 拉回应如何复合，`:118` 证明在相应 strip 等价下的兼容。这比“假定有某个相容作用”多了可直接使用的公式。
在 `LeanFormal/IUT/IUTII/Frobenioid/SourceKappaOrbitFactorizationProvider.lean:72` 取所有 `Π_v` 的乘积，投影就是一份实际分解。
`:84`、`:102` 再把任意已有 `g_v` 分解为元组同态接这些投影；`:111` 用它构造 reduced interface 上的作用数据。
这解释了为什么某些登记可以说“存在实例”而仍不足以闭合来源问题：此实例的群是乘积群，不是已经识别的论文 `Aut(‡A) ≅ G_w`。
文件开头的 faithfulness boundary 明确写出这个差别。若 LANA 有指定的算术群，应拿其实际 `g_v` 来用该自然性，不要把通用乘积群强行命名为那个算术群。
这类工作可以省掉得到作用**以后**的等变性推导；它没有造出第 11 节所需的跨列 evaluation。

### 13.4 诊断文件：一个两行实数例子解释为什么共同上界不够

`LeanFormal/IUT/Audit/Diagnostics/Countermodels.lean:13` 的 `slack_common_container` 取 `q=−1`、`theta=−2`、`target=−1`。
有 `q<0`、`q≤target`、`target≤−1`，却没有 `target≤theta`，也不能推出 `q≤theta`。
所以“两个量都放进同一容器”不是需要的紧比较。一个共同上界可以很松，点的来源和体积方向都可能在这一步丢掉。
同文件 `:20` 故意把 `x≤y` 当作假设再推出 `x≤y`，提示审阅者辨认换名后的循环。
这些是**弱接口的反例**；对象是几个实数，不是任一原文允许输入，更不是对论文的反例。
和 `SourceImageHullVolume` 的无界性并排看更清楚：前者排除一条逻辑推理；后者在一个指定的值模型及 `hdeg` 下提供真实无界序列。

## 14. 哪些“已经跑过”有凭据，哪些没有

原始日志是 `dag/watchdog/watchdog.log`。以下均为 **2026-11-15、UTC、当时文件** 的成功退出记录，今天只读取日志。
有编译成功的包应获得应有的信用；也不应当让五天前一个文件的成功退出替今天的新目标签字。

| 当次 UTC | 包名 | 原日志行号 | 可支撑的叙述 |
| --- | --- | ---: | --- |
| 01:40:23 | `Mzk1IVThm110SlackReductionActual` | 244159 | IV 的 slack 归约有历史成功运行；仍须核 theorem 的前提。 |
| 01:54:53 | `QPilotGlobalLogVolumeFromQActual` | 244311 | 从 q 参数得到局部/全局量的这一文件曾成功编译。 |
| 01:55:48 | `S3133RealifiedQPilotDivisorActual` | 244315 | 含重数的实化 q 除子包不是单纯的研究备忘。 |
| 01:55:52 | `S3133QPilotReadoutActual` | 244317 | 有带权带符号的读数文件的成功记录。 |
| 01:56:41 | `S3133RealifiedQPilotLogVolumeActual` | 244318 | 带符号 q 体积文件有单独的成功记录。 |
| 01:57:36 | `S3133QPilotLogVolumeAgreementActual` | 244320 | 已写出的多路 q 读数一致性有自己的成功记录。 |
| 02:12:07 | `Mzk1PadicFieldValuedQpActual` | 244399 | 底域赋值适配在两次中间失败后重新取得 `DONE EXIT=0`。 |

这些日志事件定位到时间及文件名；不从一次 `EXIT=0` 推出其所有依赖无 `sorry`，也不将历史记录当作工作树所有文件的哈希证明。
对 LANA 的 `Comparator`，可核的是上游配置和他们留下的既有验收记录；附篇 B 分列目标声明、Solution、允许公理及记录的日期。
对本次共同比较，核对了 Git 版本、工作树文件、规范化文本和有限算术；**没有**在任一仓库启动 Lean 或验收器。

| 2026-11-20 本次固定例语义桥 | 状态 | 尚缺什么才可以升级 |
| --- | --- | --- |
| `statement_compiles` | `NOT_RUN` | 为真实源、靶、嵌入、标记和量词写准确类型，按本仓 watchdog 得到对应日志。 |
| `proof_body_checked` | `NOT_RUN` | 在同一版本核对实际证明体及所调引理，不用另一个幺半群/静态区域替换。 |
| `kernel_closed` | `NOT_RUN` | 对相同声明检查传递公理、未证依赖和内核验证，而不只看该文件无 `sorry` 字样。 |
| `target_accepted` | `NOT_RUN` | 冻结目标、复核原文语义、运行相应 comparator；一个固定例的通过也不能登记为全称 3.12。 |

<a id="review-contract"></a>

## 15. 第一次合作怎样安排，怎样决定是否继续

**我的建议：先发 §9 的信，附 A.1、A.7 和 §11.3；整份报告留作他们想核查时的底稿。** 这三处分别回答“本仓有何正向结果”“两个看似相同的体积为什么会差”“第一次请我判断哪一个点”。

| 维护者愿意审什么 | 本仓先交什么 | 对方最有用的反馈 |
| --- | --- | --- |
| 只愿意审一个不依赖 IUT 主争议的引理 | q 局部重数及一条等式，或 A.7 的两个格、指数和秩归一化 | 指出可接入的上游声明；核对底域、位、权与分母是否相同。 |
| 愿意审原文这一步，但不准备改代码 | §11 的固定数据，E.9 的源元组、目标元组、原靶集及求值操作 | 指出实际 carrier/态射；或指出哪条原文许可尚不足以定义它。 |
| 愿意接受一小份代码 | 在对方选定的 pin 上移植一条明确依赖的引理，提供原作者归属与实际 import 闭包 | 在同一版本给出编译、用例和签名复核；是否接收按上游流程决定。 |

**安排时间时，先给审阅设预算，不给数学结果许期限。** 可先留 30 分钟读 §9 与 §11.3，另约一次 60–90 分钟的双边接口审阅；这些是建议的日历预留，不是预计在这段时间内证明成员或 3.12。
第一次会面只要回答下面四问，不必承担完整移植：

1. 固定的曲线、素数、坏位选择和上方截面，在两边分别用哪个对象表示？
2. 源 `(B,B,G)` 的参考 `1` 是在哪个张量块里？换位是否同时搬运自然子胶囊的嵌入？
3. 求值后给的是 `x∈U₂,₃`、静态 `x∈thetaFiniteOn`，还是仅一个实数？能否写出同一输入下的靶类型？
4. 若三者之一能实现，下一步核读数下界，还是先证所有输出的有限上界？不要把这两个方向当成一项。

如果双方只能提供字面相同的模型重排公式，当场记录这一事实，暂缓移植；仍可独立推进 q 或 Haar 的适配。
如果能给出保持标记的点级来源，则下一包只扩展到相同换位的区域，或用另一换位覆盖第二个获益元组。
如果有独立的全局度数证书，允许它绕过指定投影；但需要在同一输入上直接证 `q_s ≤ D ≤ H_orig`，并另处置原 hull 有限性。
至于全称 III.3.12 的完成时间，目前没有足以估计的证明路线或工作量上界。不能拿十二个元组的枚举成本换算成天数。

<a id="assets"></a>

## A. 不借助 III.3.12 也能复用的局部数学
即便不知道原文允许的 Θ 输出是什么，仍可以回答三个具体问题：一个坏位对 q 除子贡献几次？
整数纯张量在哪个格中张成？在同一张量块上，换掉 Haar 测度的归一化，哪一个体积差不变？
前两问需要分清除子所在的底域、张成所用的系数环；第三问需要固定参考格。
这些答案能供两边交叉核算，但都不以「q 已落入原文 Θ 的 hull」为前提，也不产生这个结论。
本篇从[局部结果索引](LEAN-INDEX.md#L99)选取本仓库七份数学源码；原比较的缺口以[交接 §19.3](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1941)为准。
本地链接指向 2026-11-20 工作树，不保证七份文件均收入 HEAD `a997af4b1cb2339d1e7403ef0781a16f809f4476`。
LANA 链接固定到上游仓库，均取 `553076af459e7a401bfee63a4607814d1c854477`。
以下按定义、定理类型和证明体比较数学内容，不作原创性判断；[索引中的旧构建记录](LEAN-INDEX.md#L149)不算本次重验。
### A.1 从一个坏位算起：除子的指数不是剩余次数
固定素数 $\ell\ge5$ 和 `X : N8NativeInput ℓ`。令 $B$ 为 `Bad (nativePlaceSelection X.S)`。
对每个 $b\in B$，底层是 $F_{\rm mod}$ 的有限位，$\tilde b$ 是输入所选、位于 $b$ 上方的 $F$ 的位。
用 $q_b$ 记 `qVFamily X.S b` 的参数，用 $n_b$ 记它在上方位的整值消失阶 `order`。
另记 $f_{\tilde b/b}=[\kappa(\tilde b):\kappa(b)]$，$N_b=|\kappa(b)|$；后者是剩余域大小，不一定是有理素数。
[重数的定义](../tmp/sheaf/xif/paper/QPilotGlobalLogVolumeFromQActual.lean#L50)是 $m_b=n_b f_{\tilde b/b}$，类型为自然数。
其中 $n_b$ 随参数，$f_{\tilde b/b}$ 随扩张；固定域塔和位，并没有固定该位上一切元素的阶。
有限位除子的一项是在底素理想处取系数 $m_b$，无穷部分为零，见[单点有效除子](../tmp/sheaf/xif/paper/QPilotGlobalLogVolumeFromQActual.lean#L57)。
这在底域上记录了上方零点的次数；没有选取一个同时在所有坏位生成这些局部因子的全局元素。

逐位的数值等式是 `localLogMagnitude (qVFamily X.S b)` $=m_b\log N_b$。
[证明](../tmp/sheaf/xif/paper/QPilotGlobalLogVolumeFromQActual.lean#L109)先在上方写成 $n_b\log|\kappa(\tilde b)|$，再用 $|\kappa(\tilde b)|=N_b^{f_{\tilde b/b}}$。
约化到正确的底位用的是所选提升的 `lift_comap`；这是式子里两处 $b$ 确实相同的理由。
所以若改用有理素数 $p$ 写对数，须把 $\log N_b=[\kappa(b):\mathbf F_p]\log p$ 的因子一并带过去。
这与把 $m_b$ 换成一个剩余次数是两回事；后者甚至在换对数底数以前就丢了 $n_b$。
辨别二者有个局部检验：同一离散赋值域中，非零元素 $t$ 的 $k$ 次幂有 $k$ 倍的阶，但所在位的剩余次数不变。
这只是检查系数对阶的依赖，不预设把 Tate 参数换成幂后仍是原曲线的输入。

全局这一步才要求 `[Fintype B]`。在实化除子幺半群 `GlobalDivisorMonoid` 中，
[q 除子](../tmp/sheaf/xif/paper/S3133RealifiedQPilotDivisorActual.lean#L58)是 $D_q=\prod_{b\in B}P_b^{m_b}$，$P_b$ 是底位 $b$ 的素除子。
乘号是幺半群运算，不是把不同完备域中的 $q_b$ 当作同一域的元素相乘。
度映射把一个素因子送到权 $\log N_b$，把 $n$ 次幂送到该权的 $n$ 倍。
也可先[直接取单因子的负度](../tmp/sheaf/xif/paper/S3133RealifiedQPilotLogVolumeActual.lean#L121)，只核对这个位置，而不枚举其余坏位。
[全局度公式](../tmp/sheaf/xif/paper/S3133RealifiedQPilotDivisorActual.lean#L100)由此把乘积变成有限和；Lean 用 `Multiplicative.ofAdd` 记录记法转换。

对数体积选的是**负**度：[符号定义](../tmp/sheaf/xif/paper/S3133RealifiedQPilotLogVolumeActual.lean#L57)给出 $V_q=-\deg D_q$。
于是 $V_q=-\sum_b m_b\log N_b=-\sum_b |\log q_b|$，见[重数公式](../tmp/sheaf/xif/paper/S3133RealifiedQPilotLogVolumeActual.lean#L74)及[局部大小公式](../tmp/sheaf/xif/paper/S3133RealifiedQPilotLogVolumeActual.lean#L99)。
同一输入的表示层量 `qPilotQGlobalLogVolume X` 也[等于此数](../tmp/sheaf/xif/paper/S3133RealifiedQPilotLogVolumeActual.lean#L87)；这是两种计算度的方法相等，不是两个载体同构。
要复用到 `hq`，可以逐项查[索引定位的系数](LEAN-INDEX.md#L197)：`actualFn` 提供的是剩余次数，不是完整的 $m_b$。
若消费端只有一个 `C3.q`，还须指出它对应哪个 $q_b$，以及其余各位由什么索引求和。
没有这种识别，单个对数既不能替代整族，也不能靠在等式两端加负号来弥补。
### A.2 从 q 读数到 LANA 的左端：权重和开根各算一次
固定同一 $X,b$，现在多给一个 `h : S2135PrimeAlignmentRequired X.S b`，即所涉有理素数落在指定的 `primeStrip 2 7` 中。
这不是定义 $D_q$ 的前提，而是从 `s3130QCSourceData` 读取这个坏位时所需的对齐条件。
[逐位读数](../tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean#L68)取该来源数据中 `qV` 的 `localSignedLog`。
它和 `qVFamilySignedLog X.S b` 是定义相等：两处取同一个 clause-B 参数，不是因为不同参数有同样的范数。
这个读数[等于来源 `qNorm` 的实对数](../tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean#L81)，也[等于局部大小的相反数](../tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean#L88)。
故 $r_b=-m_b\log N_b$；在每个实际坏位 $r_b<0$。读数不是 p-adic 域内的单位对数。
若在同一 $b$ 选另一份对齐见证，读数仍等于同一个 `qVFamilySignedLog`；这不提供原先所需的对齐见证。

恢复 `[Fintype B]`，并给**每个** $b$ 一个对齐证明。对任意 $w:B\to\mathbb R$，
[加权读数](../tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean#L114)是 $R(w)=\sum_b w(b)r_b$；这一操作并不要求任意给的 $w$ 都为正。
第一种具体化是 $w\equiv1$：[单位权等式](../tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean#L123)给出 $R(1)=V_q$。
第二种是 `nativeBadLocalWeight X.S`，取自所选位的局部完备化次数的倒数，而不是另取 $m_b$ 作权。
[归一化等式](../tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean#L144)把这一个 $R(w)$ 识别为 `nativeQVPilotNormalizedSignedLogVolume X.S`。
[这里的符号结论](../tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean#L160)是全局非正。若要从逐项严格负推到总和严格负，还须使用坏位非空及相应权重为正。
因此 `qPilotRealifiedLogVolume` 与归一化读数不应只因都被简称为 $-|\log q|$ 就互换。

LANA 也保留了阶。对 `D : InitialThetaData`，[抽象 `QPilotData`](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Cor312/LeftHandSide.lean#L58)要求有限集恰好枚举 $F$ 的坏位，并给出在该集上为正的权。
其[左端定义](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Cor312/LeftHandSide.lean#L81)先求 $\log Q=\sum_w w_Q(w)\,\mathrm{qOrder}(w)\log p_w$，再取 $-\log Q/(2\ell)$。
抽象字段没有强制每个权都等于 $f_w/[F:\mathbb Q]$；在具体算术对象上则有可查的取值。

[Arakelov 的 `qDivisor`](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Arakelov/QPilot.lean#L63)是 $F$ 上的算术线丛：坏位取 Tate 参数，其余有限位取 1，无穷度量取 1。
[归一化度定理](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Arakelov/QPilot.lean#L78)给出该线丛的 `degNorm = D.qPilot.logQ`，并非只有一个命名的实数。
[逐项计算](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Arakelov/QPilot.lean#L97)用 $\mathrm{ord}_p(q)=\mathrm{qOrder}/e_w$；以 $e_w f_w/[F:\mathbb Q]$ 加权后，留下的是 $f_w\,\mathrm{qOrder}/[F:\mathbb Q]$。
在扭点域 `D.Kt`，LANA 另有用根参数构造的 `qPilotBundle`，不是把 $F$ 上的线丛换个名字。
其[归一化度](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Arakelov/QPilot.lean#L226)等于 $F$ 上 `qDivisor` 的归一化度除以 $2\ell$。
再取负号，LANA 给出了[从 `qRegion` 的 `logVol` 一直到具体 `lhs` 的等式](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Arakelov/QPilot.lean#L241)。
因此不能从 `LeftHandSide` 只定义标量，推断 LANA 没有 q 除子；也不能从两边都有度推断它们是同一算术对象。
复核时，先确定本仓库所选 $\tilde b$ 是对方哪一个 $w$，用的是未开根参数还是 $2\ell$ 次根。
再把同一底位 $b\mid p$ 的账按两边的约定各写一次：
- 本仓库归一化读数的一项是 $-w_{\rm nat}(b)n_b f_{\tilde b/b}\log N_b$。
- LANA 的具体 $-\mathrm{logQ}$ 在 $b$ 上的贡献是 $-\sum_{w\mid b,\;w\,{\rm bad}} f_{w/p}\,\mathrm{qOrder}(w)\log p/[F:\mathbb Q]$；这里尚未除以 $2\ell$。
- $f_{w/p}=f_{w/b}f_{b/p}$ 可以对齐剩余域的底数，但不能把一个选定的提升自动变成整条纤维的加权和。

可交回的第一条等式应是同一坏位的有符号贡献；全局除以 $2\ell$ 的操作须有唯一、可指认的位置。
### A.3 有限 p-adic 张量：纯张量、整格与整数参考区
固定素数 $p$、有限指标型 $I$。每个 $A_i$ 是有限维赋范 $\mathbb Q_p$ 代数，同时是超度量赋范域；文件在需要紧性处使用 `ProperSpace`。
写 $T=\bigotimes_{i\in I} A_i$（在 $\mathbb Q_p$ 上取张量积），$O_i=\{x\in A_i:\|x\|\le1\}$，把 $O_i$ 看成 $\mathbb Z_p$ 格。
[两个定义](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean#L42)分别产生集合 $P=\{\bigotimes_i a_i:a_i\in O_i\}$ 和子模 $L_{\rm int}=\operatorname{span}_{\mathbb Z_p}P$。
$P$ 只含一次纯张量的像；$L_{\rm int}$ 还允许有限次加法。源码给 $P$ 的是紧性，并没有在这里把 $P$ 当作开加法子群。
这个区别决定了能否拿 Haar 体积来数陪集：紧集未必是格，有限个纯张量之和也未必还是纯张量。

从真正的整张量积出发，[自然线性映射](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean#L71)是 $\bigotimes_{i\in I} O_i\longrightarrow T$，左端的基环为 $\mathbb Z_p$。
它在 $\mathbb Z_p$ 上单射，且像**恰是** $L_{\rm int}$；[像等式](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean#L81)本身还省掉了 `ProperSpace` 假设。
单射的证明用到每个 $O_i$ 在 $\mathbb Q_p$ 上张成 $A_i$：可选一组基，使各基向量范数不超过 1。
因此得到的是整张量积到其像的线性同构，不只是「存在某个同秩的自由模」。
这给使用者两种等价的表示：可以在整张量积里按多线性关系计算，也可以直接在 $T$ 的子模里比较元素。
单射保证后一种比较不凭空增加整张量之间的等式；它不曾断言所有环境张量都是整数张量。

该像是[有限自由且紧开的格](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean#L52)，放宽标量到 $\mathbb Q_p$ 后张成整个 $T$。
具体的[秩等式](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean#L90)为 $\operatorname{rank}_{\mathbb Z_p}L_{\rm int}=\dim_{\mathbb Q_p}T$；满秩没有指定它在另一个满格里的指数。
在各因子另带 `CharZero`、`CompleteSpace` 的声明中，所得是[$L_{\rm int}\subseteq L_{\log}$](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean#L95)，右边是整对数壳的张量格。
这里靠的是各因子整数格进入相应的对数壳格，不是断言对数映射把所有整数逐一送到自身。

给任意 $\mathbb Q_p$ 代数同态 $g:T\to\prod_{j\in J}E_j$，各 $E_j$ 为赋范 $\mathbb Q_p$ 代数且为域。
每个 $x\in P$ 的自然数次幂仍在 $P$：对纯张量取幂就是逐因子取幂，整数条件不变。
[逐坐标结论](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean#L126)是 $g(P)\subseteq\{y:\forall j,\ \|y_j\|\le1\}$，不要求 $g$ 满射。
理由是 $g$ 的坐标线性映射连续，故 $g(x)_j$ 的幂全落在紧集内；若范数大于 1，这些幂就无界。
若各 $E_j$ 也超度量，右边对 $\mathbb Z_p$ 线性组合封闭，[同一包含便对整个格成立](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean#L143)。
这没有说 $g$ 保持 $T$ 上任意向量的范数；即便有域乘积分解，也不能仅凭代数同构认定两个单位球相等。

LANA 在有限位张量块（packet）上有直接的对应物：[整数纯张量集合](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Integral.lean#L178)和[其 $\mathbb Z_p$ 张成的张量整环 `orderSubmodule`](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Integral.lean#L206)。
LANA 也给出了该整环的[开性与紧性](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Integral.lean#L439)，不是仅把「格」写进接口名称。
另一方面，LANA 的 [`integral`](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/MaximalOrder.lean#L184) 是环境张量代数里 $\mathbb Z_p$ 的整闭包，普遍结论是 `order ⊆ integral`。
对接时可把 $A_i$ 具体取为同一 $p$ 上相应的完备域，先检查两边对每一组 $(a_i)$ 给出的纯张量是否相同。
一个保持这些生成元的 $\mathbb Q_p$ 线性识别会把两边的 $\mathbb Z_p$ 张成互相送到；这一步不需要整环已正规。
若下一步要以整闭包为体积参考，则还要识别那个整闭包，或计算张量整环相对于它的指数；仅有秩等式不够。
### A.4 哪个环张成 hull？系数可以逐坐标选择
这次在 $E=\prod_{j\in J}E_j$ 工作，$E_j$ 为赋范域，范数非阿基米德。令 $O=\prod_j O_{E_j}$。
这里的 `integralRing` 是乘积里的整数环，不是沿对角嵌入的一份 $\mathbb Z_p$。
对 $S\subseteq E$，`hull S` 取所有包含 $S$ 的盒子 $\lambda O$ 之交，其中每个 $\lambda_j\ne0$。
每个这种盒子都是 $O$ 子模；只要它含 $S$，它就含 $\operatorname{span}_O S$。
故[正向包含](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldIntegralHullSpan.lean#L18)对每个 $S$ 成立，不先要求 $S$ 紧、非空或 $J$ 有限。

要得到[反向包含](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldIntegralHullSpan.lean#L26)，该定理假设 $J$ 有限，$S$ 紧且非空，并且 $\forall j\ \exists s\in S,\ s_j\ne0$。
非退化是逐坐标的：各坐标的见证可以不同；反之，仅仅知道 $S$ 含一个非零向量，不足以照用此定理。
紧性使每个坐标的最大范数在 $S$ 上达到。对坐标 $j$ 选取达到它的 $s^{(j)}$，记 $\lambda_j=s^{(j)}_j$。
非退化保证 $\lambda_j\ne0$；而这些最大值组成的盒子含 $S$，故对每个 $x\in\operatorname{hull}S$ 有 $\|x_j\|\le\|\lambda_j\|$。
现在取一个乘积整数：在第 $j$ 个坐标放 $x_j/\lambda_j$，在其余坐标全放 0。这是[证明中实际用的系数](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldIntegralHullSpan.lean#L41)。
以它乘 $s^{(j)}$，得到仅第 $j$ 个坐标等于 $x_j$ 的向量。对有限个 $j$ 相加即得 $x$，不需要一个点同时实现所有最大值。

两向合并，得到集合[等式 `integralSpan_eq_hull`](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldIntegralHullSpan.lean#L73)：$\operatorname{span}_{O} S=\operatorname{hull}S$。
此式不要求 $S$ 本来就是笛卡尔积，也不要求 $S$ 自己有正测度；因此可以从一批有来源的生成元算出它们的 hull。
若只为描述这个最小盒子，以上证明至多选一个点代表每个坐标；其余点的坐标范数已经受所选最大值控制。
这不表示其余点可从原输出族中删除：最小盒不变，比「给定读数仍由某个实际输出实现」弱。
若把系数改成对角的 $\mathbb Z_p$，上述逐坐标截取通常做不到；A.3 的张量格不能靠这条证明变成整个 hull。

LANA 的有限位也有[具体的最小 hull 存在定理](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Hull.lean#L159)，不只是一套抽象的闭包律。
对该 packet 的 admissible 区域 $U$，存在 packet 中的单位 $a$，使 $U\subseteq a\,\mathrm{integral}$，且这个集合包含于每一个覆盖 $U$ 的同类盒子。
其[可容许条件](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Admissible.lean#L56)是非空、闭包紧、可测、Haar 测度正且有限；不要求 $U$ 自己闭。
LANA 在各极大理想对应的商域中取投影范数的上确界，用[正测度排除零投影，再取最小可行半径](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Hull.lean#L175)。
本仓库则从紧集中的最大值点直接给出 $O$ 模生成式；两个结论共有「最小的盒子」，但使用它的条件不同。
可在两边都适用的紧集上复核：运输到同一组域因子，验证 `integral` 对应 $O$，且两组允许的盒子逐个对应。
具体说，运输后的本库盒子容纳 $U$，LANA 的最小盒就包含于它。
反向要用 LANA 的盒子也是本库允许的一种 $\lambda O$，且同样容纳 $U$；这才给出两个 hull 相同。
仅验证一个集合容纳 $U$ 而没有核对盒子类别，至多走了上述证明的一半。
### A.5 在同一算术张量块内，两个交指数给出精确的相对 Haar 对数
固定数域 $K$、素数 $p$、有限槽集 $I$。每个槽可以有自己的标号类型 $V_i$，不要求 $V_i$ 有限。
指定 `places : (i : I) → V i → FinitePlaceAtPrime K p`，再固定 `tuple : (i : I) → V i`。
于是每槽选到 $p$ 上一个实际有限位，得到一个张量块 $T$；以下量词针对每一组这样的选择，不是对不同元组先做平均。
在 $T$ 中记 $M$ 为 `arithmeticTupleIntegralLogLattice` 的加法群，$H$ 为 `arithmeticTupleCanonicalUnitReference`。
参考区名称中的 unit 指分解后各坐标的范数不超过 1；它含零，是加法群，而不是乘法单位群。
$M$ 是整**对数**张量格，不是 A.3 中仅由各槽赋值整数张成的 $L_{\rm int}$。
参考 $H$ 也不是任意选的基所张的格：[构造](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L29)把域乘积中的整数格沿分解映射拉回。
拉回所用的是加法同态，得到一个加法子群；[其载集](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L65)恰好是指定的 $H$，而且紧、开。
记 $C$ 为 `arithmeticTupleCanonicalHull`。要比较的是 $M$ 与 $C$ 相对于**同一个** $H$ 的体积。

先不要假设 $M\subseteq H$ 或 $H\subseteq M$。取交 $J_0=M\cap H$ 就能同时在两边数陪集。
定义 $i_M=[M:J_0]$，$i_H=[H:J_0]$；[源码](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L75)以 `intersectionIndex M H` 和交换参数后的 `intersectionIndex H M` 分别取它们。
二者都不是在尚未证明包含时就直接写下的 $[M:H]$ 或 $[H:M]$。
交在每个紧开群中都是开子群，紧性使陪集数有限，包含单位元使指数为正；[正性在此单列](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L83)。
由此先在不指定任何测度时[定义实数](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L92) $v_H(M)=\log i_M-\log i_H$。
如果 $M$ 较小，负号落在较大的指数前。此处的量是格本身的对数质量，不是把小格的正余体积取对数。

现在给 $T$ 配备 Borel 可测结构。对**任意**加法 Haar 测度 $\mu$，都有[相对 Haar 等式](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L128)：
$v_H(M)=\log\mu(M)-\log\mu(H)$；这里对数取在正的有限实数上，Lean 先对测度值取 `toReal`。
原因是 $M$ 与 $H$ 各自由 $J_0$ 的陪集分拆，每份的质量都是同一个 $\mu(J_0)$。
两边的商是 $i_M/i_H$，所以公式不依赖要求 $\mu(H)=1$ 的特殊选择。
若改用 $c\mu$，$0<c<\infty$，两个对数都增加 $\log c$；这是允许改测度尺度的理由，不是允许改参考格的理由。
事实上，对另一个正有限测度的参考区 $H'$，有 $v_{H'}(M)=v_H(M)-v_H(H')$，其中 $v_H(A)=\log\mu(A)-\log\mu(H)$。
因此若 LANA 一端的参考格换成了张量整环而非整闭包，需要补的恰是一个参考差，不是整体「重新归一化」四个字。
具体地，若张量整环 $R\subseteq H$ 且已知 $[H:R]=k$，则 $\mu(H)=k\,\mu(R)$，故 $v_R(M)=v_H(M)+\log k$。
从以 $R$ 为参考的结果返回以 $H$ 为参考的结果应**减** $\log k$；这个符号不取决于 $M$ 在 $R$ 的哪一侧。

对 hull，源码先给出[集合包含 $M\subseteq C$](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L96)。
证明把 $C$ 运到域乘积中：每个整对数生成元在原对数像内，因而在该像的 hull 内。
把乘积侧的 hull 模拉回 $T$，仍是 $\mathbb Z_p$ 子模；只要包含所有生成元，就包含 $M$ 的任意有限线性组合。
由测度单调、$\mu(M)>0$ 与 $\mu(C)<\infty$ 可取实对数，最后两边减同一个 $\log\mu(H)$。
[实际输出](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L143)仅是 $v_H(M)\le v_H(C)$，即格给 hull **下界**。
例如希望得到上界 $v_H(C)\le b$，知道 $v_H(M)\le b$ 毫无帮助；一个装得下 $M$ 的更大区域可能超出 $b$。
反过来，若目的是证明 $a\le v_H(C)$，则可先证明 $a\le v_H(M)$，不必精确算出整个 $C$。
只有在另证两者确为同一个格，或另算出它们之间的质量差以后，才有把这个下界升级为精确值的根据。
若另将 $C$ 实现为含 $M$ 的加法子群，且求得有限指数 $[C:M]=t$，陪集分拆便给 $v_H(C)-v_H(M)=\log t$。
在这种情况下，取等归结为 $t=1$；所引的 `le_hull` 并未计算这个指数。
### A.6 跨到 LANA：运送参考格以后，还差一个秩因子
本仓库也有[到域乘积的体积等式](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L157)。
给有限 $J$、有限维且闭球紧的赋范域因子 $E_j/\mathbb Q_p$，以及 $e:T\simeq_{\mathbb Q_p\text{-alg}}\prod_j E_j$。
在两边的 Borel 结构上分别任取加法 Haar 测度 $\mu,\nu$，定理给出 $v_H(M)=\operatorname{normalizedLogVolume}_{\nu}(e[M])$。
关键一步是[验证 $e[H]=\mathrm{unitRegion}$](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean#L168)。
同一连续加法同构运送 $M$ 与 $H$，推前 Haar 测度的未知比例在相对质量里相消；不必先证明 $e$ 等距。
结果是 $\log\nu(e[M])-\log\nu(e[H])$，不是 $\mu(M)=\nu(e[M])$，也不是已算出 $e[C]$ 的测度。
这点也能在有限群上核对：因 $e$ 单射，$e[M]\cap e[H]=e[M\cap H]$。
所以先运输再数陪集，两侧应分别得到 $i_M,i_H$，不只是最后两个对数之差碰巧相同。
把域因子按同一置换重排，两个商群仍各自同构；这一事实本身不为原 evaluation 提供带标记的槽置换。

LANA 对有限 packet 取的 [`integralAt`](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Volume.lean#L94) 正是 `integral p c`，不是 `order p c`。
其 [`componentVol`](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Volume.lean#L196) 对区域 $U$ 的定义是 $\log(\mu(U)/\mu(\mathrm{integralAt}))/d$，$d=\dim_{\mathbb Q_p}T$。
参考区本身的值为零。即使两边把它的 Haar 质量都取作 1，这个零值也检查不出是否漏除了 $d$。
设块的维数 $d>0$，区域 $U$ 的质量正且有限，并已证明运输把 $H$ 送到 `integralAt`、把 $M$ 送到 $U$。
在这些条件下，应比较的是 $v_H(M)=d\,\mathrm{componentVol}(U)$；局部各块的 $d$ 未必相同。
这是据两个定义写出的**待对接公式**；文件中没有一条以另一仓库的类型为参数的 Lean 定理。

LANA 的[单调性定理](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Volume.lean#L206)比较 $a\,\mathrm{integralAt}\subseteq b\,\mathrm{integralAt}$，前提中 $a,b$ 都是 packet 单位。
这里说的「单位」是在环境代数中可逆，不要求乘这个单位后仍是同一个整数格。
这条定理不能直接以任意 $\mathbb Z_p$ 满格代入 $a\,\mathrm{integralAt}$；要么构造这样的 $a$，要么回到一般集合的 Haar 单调性。
还能用 LANA 的[缩放律](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalConstruct/Volume.lean#L276)分别检验符号和维数：各槽在 $p$ 上，$U$ 可测且质量正有限时，
乘 $p$ 的**逆像**使 `componentVol` 增加 $\log p$；在未除以 $d$ 的相对对数里，对应增加的是 $d\log p$。
这一检验不需要 Θ 输出或全局平均；若同一局部块算出相反符号，应先检查拿的是像还是逆像。
### A.7 核算例：满秩的格可以严格小于它的 hull
只为核对系数环和符号，取 $E=\mathbb Q_3\times\mathbb Q_3$，$O=\mathbb Z_3\times\mathbb Z_3$，参考格 $H=O$。
令 $S=\{(1,1),(1,4)\}$。这是紧的非空有限集，且两个坐标上都有非零值，满足 A.4 的局部假设。
所有坐标的范数均不超过 1，所以 $S\subseteq O$；反过来，$S$ 含乘积环的单位元 $(1,1)$。
单用这个生成元，允许逐坐标选择整数系数时就能得到任意 $(a,b)\in O$。
因此 $\operatorname{span}_O S=\operatorname{hull} S=O$；并没有使用 $S$ 具有正 Haar 质量。

若只准用对角标量 $\mathbb Z_3$，生成的是 $M=\mathbb Z_3(1,1)+\mathbb Z_3(1,4)$。
两个向量之差为 $(0,3)$，所以 $M=\{(u,v)\in O:v-u\in3\mathbb Z_3\}$。
确切地说，满足同余式的点可写成 $u(1,1)+((v-u)/3)(0,3)$，故这是等式而不只是一个必要条件。
映射 $(u,v)\mapsto v-u\pmod3$ 是 $O$ 的加法群到 $\mathbf F_3$ 的满射，核为 $M$，故 $[O:M]=3$。
用生成矩阵的行列式也得到 3；它非零说明 $M$ 满秩，却不是 $\mathbb Z_3$ 的单位，故两格不同。
取幂等元 $(1,0)\in O$ 作用于 $(1,1)\in M$，结果却不在 $M$，因为两个坐标之差不是 3 的倍数。
可见 $M$ 不是 $O$ 子模，尤其不能写成 $aO$；这给出了不能直接套 LANA 盒子单调性定理的具体原因。

在 A.5 的符号下 $J_0=M$，从 $M$ 侧数是一个陪集，从 $H$ 侧数是三个。
不论 Haar 测度起初取什么尺度，都有 $v_H(M)=\log1-\log3=-\log3$，而 $v_H(\operatorname{hull} S)=0$。
这里的缺额恰为 $\log3$，不能用「双方满秩」把它消掉。
若用 LANA 的二维口径读同一对集合，结果为 $-(\log3)/2$ 与 0；这次取的是区域的质量比，没有把 $M$ 写成盒子。

还可以取 $U=M$ 看两类 hull 定理的适用域。有限集 $S$ 在这个二维空间里质量为零，不能直接满足 LANA 的 `admissible`。
$M$ 却是紧开正测度区域，含 $S$ 且包含于 $O$；最小性给出它在乘积整数环意义下的 hull 仍为 $O$。
这是一个域乘积上的手算例，不是把某个 `N8NativeInput` 或交接的 $(G,B,B)$ 元组实例化，也不声称实际算术格的指数恒为 3。
### A.8 这些结果能替哪一步，不能替哪一步
q 侧可向 `hq` 的使用者交付每个底坏位的素除子、实际重数和带负号的局部项；用单位权还能重算实化度。
应同时保存 $b,\tilde b,q_b,n_b,f_{\tilde b/b},N_b$，而不只抄最后一个实数。这样 LANA 能在对应坏位逐项核对其 Arakelov 算法。
格侧适合先交换一组有来源的整张量生成元及其像。证明它们属于同一目标区域，再取张成，比预设整个纯张量像是直积更弱。
若该区域本身不是子模，光证明它含生成元还不够；可先证明包含它的目标 hull 对相应系数环封闭，再将张成放入 hull。

若目标是一个下界，可对这些生成元验算满秩和交指数；这只给生成格的质量，需以**原区域确实容纳该格**为使用条件。
若目标是 hull 的上界，则应找一个确实包住所有相关输出、且属于定义 hull 所用类别的外盒，再给外盒的质量上界。
仅知道一个 $\mathbb Z_p$ 格含所有生成元，并不保证它也容纳这些生成元的 $O$ 张成；核算例正好区分了这两句话。
两种策略互不替代：前者给出可达到的内部大小，后者限制每个允许输出，不凭一个试验点就覆盖整个输出族。

原比较的[交接 §19.2](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1926)同时需要读数覆盖和对所有允许输出的统一上界。
本篇既未把所算的 $r_b$ 识别为那个带标记输出的投影，也未把算术块 $C$ 认作原允许像的 hull。
例如[固定输入任务](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1943)仍要从实际 evaluation 给出载体映射，再验证 $E_\tau(1)\in U_{2,3}$。
即使格指数和符号都算对了，对一个独立构造的满格计数也不是这个成员关系的见证。

可先做一项独立复核：在两边指定同一正维有限位块，写下纯张量在两种表示下的像、整数参考区的像，以及一对格的两个交指数。
用这张表先算未除秩的对数质量差，再按 LANA 的秩重算一次；出现差异即可定位是参考格、张量秩，还是集合包含方向有误。
本篇未运行 `statement_compiles`、`proof_body_checked`、`kernel_closed` 或 `target_accepted` 的新验收；引用的既有局部公式不改变 III.3.12 的状态。

<a id="lana-chain"></a>

## B. LANA 的定理链：哪条箭头通向 ABC，哪条停在 wall

取 `D:/lana-iut-latest-20261120` 的 `553076af459e7a401bfee63a4607814d1c854477`（提交于 2026-11-03，UTC）；2026-11-20 核读源码。
除末节显注「本仓库」外，`路径:行` 均相对该 LANA 快照。`→` 表示给定左端可得右端，`↔` 才允许反用。
读这张图要区分两个消费者：tripod 消费**对所有初始数据的变体**；wall 与 xi 的模型定理通常先固定**一个** `D`。

### B.1 从具体变体到标准 ABC：逐箭头查证明体
`InitialThetaData` 是带数域及后续算术字段的结构（`Iut/Cor312/ThetaData/Basic.lean:81`），并非任给一条曲线的别名。
记 `Var(D) := Corollary312Variant (concreteVariantData D)`。`Iut/Cor312/Statement.lean:89` 的定义就是 `X.qPilot.lhs ≤ X.rhsData.rhs`。
`Iut/Concrete/ThetaRegion.lean:359` 从同一个 `D` 组装两端；`:375` 的 `Iut.Cor312VariantHolds` 量化 `∀ D : InitialThetaData.{0}`。
这不是对任意拼装的 `Corollary312VariantData` 声称不等式，也不是某个固定输入的数值证书。
左端的 `QPilotData.logQ` 是坏处的加权 `ord(q)·log p` 之和（`Iut/Cor312/LeftHandSide.lean:81`）；具体权重还含剩余次数与域次数（`Iut/Concrete/ThetaRegion.lean:351`）。
`absLogQ = logQ/(2ℓ)`，`lhs = -absLogQ`（`Iut/Cor312/LeftHandSide.lean:88`、`:93`）；故不能直接代入某一坏处的 `log(q)`。
右端的 `RHSData.thetaPilot`、`thetaPilot_hullAdmissible` 是字段（`Iut/Cor312/RightHandSide.lean:88`、`:92`）。
`thetaHull` 对各 capsule 取 hull，`rhs` 再取 procession 体积（`Iut/Cor312/RightHandSide.lean:99`、`:107`）。
具体实例不是任意填表：`rhsDataOn` 给出 region 并证明其 admissibility（`Iut/Concrete/ThetaRegion.lean:320`）；这与证明它是原文算法的输出不同（`Iut/Cor312/Statement.lean:44`）。

| 输入 → 输出 | Lean 声明 / 证明位置 | 做了什么 |
|---|---|---|
| `Cor312VariantHolds → tripodTheory.StatementII` | `Iut.Tripod.abc_of_variant`，`Iut/Tripod/Main.lean:120` | 在选出的具体数据上用 `h312 D`；不是向调用者再索取一个高度界。 |
| `tripodTheory.StatementII → Genl.Curves.theory.StatementII` | `Iut.Tripod.curves_statementII_of_statementII`，`Iut/Tripod/GeneralPosition.lean:217` | 搬运紧有界集与点的次数；两种规范高度差计入常数。 |
| `Genl.Curves.theory.StatementII → Genl.Curves.theory.StatementI` | `Genl.Curves.statementII_implies_statementI` 的调用，`Iut/Tripod/GeneralPosition.lean:271` | 用 `genl` 的一般位置定理，不是直接删去紧有界条件。 |
| `Genl.Curves.theory.StatementI → tripodTheory.StatementI` | `Iut.Tripod.statementI_of_curves_statementI`，`Iut/Tripod/GeneralPosition.lean:242` | 取 tripod 曲线；三步合成为 `Iut.Tripod.statementI_of_statementII`（同文件 `:269`）。 |
| `tripodTheory.StatementI → Iut.ClassicalABCInt` | `Iut.Tripod.classicalABCInt_of_statementI`，`Iut/Tripod/ClassicalAbc.lean:226` | 专取次数一的有理点，得非零整数零和三元组的对称界。 |
| `Iut.ClassicalABCInt → Iut.ClassicalABC` | `Iut.classicalABC_of_int`，`Iut/Abc/Classical.lean:51` | 对正自然数取 `(a,b,−c)`；前两步的合成是 `Iut.Tripod.classicalABC_of_statementI`（`Iut/Tripod/ClassicalAbc.lean:286`）。 |
| `Iut.ClassicalABC ↔ FormalConjecturesABC.abc` | `Iut.classicalABC_iff_abc`，`Iut/Abc/FormalConjectures.lean:164` | ε-常数式与「每个 ε 只有有限个例外」等价。 |
| `Cor312VariantHolds → FormalConjecturesABC.abc` | `Iut.formalConjecturesABC_of_variant`，`Iut/Abc/FormalConjectures.lean:240` | 取上述等价的正向，交给 Solution。 |

`Iut/MainTheorem.lean:36` 的 `Iut.classicalABC_of_variant` 才是上游的主定理：`:37` 明写 `abc_of_variant`、`statementI_of_statementII`、`classicalABC_of_statementI` 三层调用。
它没有调用 `XiPrinciple`。相反，是 wall 分支在得到全部 `Var(D)` 后可以调用这条主定理（`Iut/Wall/EtaAlg.lean:223`）。

**第一行的算术依赖。** `Iut/Concrete/Main.lean:37` 的 `IsConcrete X` 要求 `X = concreteVariantData D`，不允许把变体用到任意 RHS。
例外集外的点与合格素数 `ℓ ≥ 7` 给出 `D`、`TowerArithmetic D` 及与该点的 `logQ`、different、conductor 关系，量词见 `Iut/Concrete/Main.lean:47`。
`Iut.Tripod.concreteThetaDataExistence'` 在 `Iut/Tripod/Main.lean:107` 构造 `D`，`:110` 由 `towerLocalHyp` 取塔算术；没有把塔算术留给主定理的调用者。
`ConcreteThetaDataExistence.toThetaDataExistence` 用 `TA.certificate`、`TA.localEstimate` 供给抽象接口（`Iut/Concrete/Main.lean:65`、`:73`）。
IV 的实际消费点是 `inv.theorem110 cert est pnt (h312 X hPX)`（`Iut/Implication/Corollary22.lean:535`）；`h312` 在这里仍是前提。
核对被调用处：`Theorem110Invariants.theorem110` 的四个参数依次是证书、局部估计、素数计数界和 `Corollary312Variant X`；结论左端是 `X.qPilot.logQ/6`（`Iut/Implication/Theorem110.lean:245`）。
`Iut.statementII_of_cor312` 调用 `Id.c2` 估计例外集之外的点，再用有限集的有界性合并（`Iut/Implication/Corollary23.lean:59`、`:90`、`:115`）。
`Iut/Tripod/Main.lean:122` 用 `cyclicBoundOdd`，`:125` 接 `northcottHyp`、挠点次数与高度/导子比较，`:131` 传入 `chebyshevBoundExplicit` 和 `primeCountingBoundExplicit`。
证明末行 `hX ▸ h312 D`（`Iut/Tripod/Main.lean:132`）说明为何一个全称的 `Cor312VariantHolds` 足够。

**后两种 ABC 的量词。** `StatementII` 的常数可依赖 `d, ε, K`，约束 `x ∈ K` 且次数 `≤ d`；`StatementI` 去掉 `K`，保留次数界（`Iut/Tripod/Basic.lean:374`、`:386`）。
在次数一，`logDiff_ratPt = 0`、`logCond_ratPt_le`、`logHeight₁_le_htCan_ratPt` 是从高度到整数的三条边（`Iut/Tripod/ClassicalAbc.lean:92`、`:143`、`:197`）。
`Iut/Tripod/ClassicalAbc.lean:229` 实际选常数 `2 * Real.exp C`；指数化的界见 `:266`。这一步不是把三元组的高度当作定义相等。
`ClassicalABC` 量化正的 `a,b : ℕ`、`Nat.Coprime a b`、`a+b=c`，结论 `c ≤ C·rad(abc)^(1+ε)`；声明并未另设 `0<C`（`Iut/Abc/Classical.lean:38`）。
有限例外式对 `{a,b,c}` 要求两两互素。`Iut/Abc/FormalConjectures.lean:167` 以 `ε/2` 界住例外的 radical 和 `c`；`:202` 反向对例外的 `c` 取上界 `M`，再用 `max 1 M`。
整数式本身也可从自然数式得到；`classicalABC_iff_int` 把它们合成等价（`Iut/Abc/Classical.lean:146`），但主链在此只用整数式到自然数式。

### B.2 Comparator 锁的是哪条命题，哪一天验过
`lakefile.toml:137` 将 `Challenge`、`Solution` 设为两个独立的 Lake 根。它们导出同名常量，不能把两者 import 进同一个环境来验收。
Challenge 只直接 import `Mathlib.Analysis.SpecialFunctions.Pow.Real`、`Iut.Concrete.ThetaRegion`（`Comparator/Challenge.lean:7`）；没有导入 ABC 证明来定义目标。
`ABC.radical` 是不同素因子的积（`Comparator/Challenge.lean:63`）；`_root_.ABC` 用严格不等式 `rad(abc)^(1+ε) < c` 定义**例外集**，断言该集合有限（`Comparator/Challenge.lean:69`）。
所对齐的外部声明是 formal-conjectures 的 `ABC.abc`，版本 `1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89`（`Iut/Abc/FormalConjectures.lean:12`）；复制的是陈述，不是导入它的占位证明。
Challenge 的 `Iut.abc_of_cor312Variant : Iut.Cor312VariantHolds → ABC` 只有一个 `sorry`（`Comparator/Challenge.lean:75`）；它是待比对的目标，不是供 Solution 调用的引理。
Solution 在共同两项 import 之外加 `Iut.Abc.FormalConjectures`（`Comparator/Solution.lean:9`），自己声明 `ABC.radical` 和 `ABC`（`:34`、`:40`）。
其同名定理以 `Iut.formalConjecturesABC_of_variant` 为证明项，结论特写 `_root_.ABC`（`Comparator/Solution.lean:49`），避开命名空间内另一个 `Iut.ABC`。
后者是高度理论 `T` 上的 `T.StatementI`（`Iut/Abc/Target.lean:37`）；与正式锁定的自然数三元组集合不是同一个定义。

| 检查对象 | 实际配置 / 证据 | 能回答的问题 |
|---|---|---|
| 目标与定义 | `Comparator/config.json:4` 只列 `Iut.abc_of_cor312Variant`；`:5` 的 `definition_names` 为空 | `ABC`、`ABC.radical` 不是可替换的定义洞；两边须连定义体匹配（`Comparator/README.md:71`）。 |
| 允许的公理 | `Comparator/config.json:6` 只列 `propext`、`Quot.sound`、`Classical.choice`；`:7` 关闭 `enable_nanoda` | 这是允许集合，不是本快照的一次公理检查输出。 |
| Challenge 的可信闭包 | `scripts/AuditComparatorChallenge.lean:40` 列禁入模块，`:44` 列禁入证明声明，`:73` 检查 | `Iut.MainTheorem`、`Iut.Tripod`、`Iut.Implication`、`Iut.Abc` 不能在 Challenge 侧预置证明。 |
| 占位与解答 | `scripts/AuditComparatorChallenge.lean:123` 要求目标含 `sorryAx`；`scripts/AuditComparatorSolution.lean:30` 对解答作 `collectAxioms` 并排除白名单外公理 | 挑战题的占位明示，解答不享受这个例外。 |

**日期要落到事件上。** 2026-10-08 的 `08c383b3c5` 把具体变体数据收为 `D` 的函数；读现型以 `Iut/Concrete/ThetaRegion.lean:359`、`:375` 为准。
2026-10-10 的 `26ad9fca92` 把有限例外式抽成顶层 `ABC`；现型见 `Comparator/Challenge.lean:69`、`:75`，不是锁 `Iut.ClassicalABC` 这个名字。
总 `README.md:1081` 记录 2026-10-10 通过；`Comparator/README.md:149` 另记 theta-pilot 区域重设计后于 **2026-10-11** 再次确认通过。
后一记录给出 comparator `07bc4ea`、配套 `lean4export` 与默认 Lean kernel（`Comparator/README.md:151`）；它不是 2026-11-03 的提交或 2026-11-20 的本地重跑日志。
两次记录分别见历史提交 `46bff33961`、`ce5a8455d7`；其后 2026-10-16 的 `95ca8e7bbd` 还更改了可信闭包，现 `LocalThetaData.decomp` 取真的 `decompGroup`（`Iut/Cor312/ThetaData/LocalConditions.lean:273`）。
`.github/workflows/lean_action_ci.yml:17` 配的是 `lean-action` 加 `--wfail`，不是 Comparator 重验凭据。
`scripts/check_comparator_signature.sh:135` 用 `pp.all` 打印公共声明的类型，`:164` 作文本比较；这与外部 comparator 检查解答证明项是两种检查。

**复现以实际锁为准。** `lean-toolchain:1` 是 `v4.32.0`；`lakefile.toml:16` 选同版 Mathlib，`lake-manifest.json:158` 锁到 `81a5d257c8e410db227a6665ed08f64fea08e997`。
下表保留短 SHA 供辨认；每行的 manifest 位置都有完整 `rev`，紧随其后是包名。左列 README 的旧值不是替代 lock 的第二种配置。

| 包 | README 旧值 → manifest 的 `rev` 前缀 | 两处定位 |
|---|---|---|
| `tempered-fundamental-groups` | `a2415c1 → 04ab863a` | `README.md:1009`；`lake-manifest.json:68` |
| `oka` | `405aadd → 7f2a6241` | `README.md:1010`；`lake-manifest.json:78` |
| `pi1` | `7647d28 → ed24c6c7` | `README.md:1011`；`lake-manifest.json:108` |
| `continuous-kummer-theory` | `98b67df → 1d5194fc` | `README.md:1014`；`lake-manifest.json:38`，现在还是根包直接依赖（`lakefile.toml:107`）。 |
| `orbicurve-cores` | `21ce4b7 → d08559e6` | `README.md:1016`；`lake-manifest.json:98` |
| `belyi` | `1d84db9 → 7206d783` | `README.md:1017`；`lake-manifest.json:88` |

陈述侧直接依赖 `Iut.Concrete.ThetaRegion` 不等于只信任这一个文件；其 import 在 `Iut/Concrete/ThetaRegion.lean:6`。`Comparator/README.md:84` 的模块计数属于历史记录，不能外推到此锁。
证明侧另有 `genl@179e26f6`、`heights@f4379dbc`（`lake-manifest.json:128`、`:118`）；它们确由 `Iut/Tripod/GeneralPosition.lean:7`、`:8` 导入，不能反写成 Challenge 的直接依赖。
从两个根的 import 行递归追踪仓内 `Iut.*` 源文件，Challenge 到 101 个，Solution 到 185 个；两者均未走 `Iut/Wall/`、`Iut/WallEquiv/`、`Iut/LogLink/`。
这是源码 import 检索，不含外包、隐式导入或逐声明 kernel 依赖；它回答的是「ABC 条件证明是否借用了下面的 wall 模型」。

### B.3 `Iut.Wall`：给哪个算法、比较哪两个输出
固定 `D`，记 `a = D.qPilot.absLogQ`，`s = sFactor (nC D)`，`V = logVol D (hullOf D (vcI D))`，`R = (concreteVariantData D).rhsData.rhs`。
`s` 是标签平方的平均数，`1 < D.wallS`（`Iut/Wall/Pilots.lean:55`、`:334`）；`absLogQ_pos` 给出 `a>0`（`Iut/Wall/Scaling.lean:381`）。所以 `−s·a ≠ −a`。
`Iut.Wall.SSIneq D` 是 `(s−1)·a ≤ V`；`Var(D)` 是 `−a ≤ R`。前者对 log-shell 容器取 hull，后者对 theta-pilot 区域取 hull，不能混作一个右端。
定义可以并排看：`Iut/Wall/MultiContainer.lean:88` 与 `Iut/Wall/Rss.lean:356`。
无 hull 的旧式另名 `SSIneqNoHull`；`ssIneq_of_noHull` 只从旧式推出新式（`Iut/Wall/MultiContainer.lean:94`、`:99`）。2026-10-14 的 `cdc9602190` 正是这次对象变更。
`Ind3 D` 是逐 capsule 包含于 **hull** 的 adelic 区域（`Iut/Wall/Ind3.lean:213`）。`Ind3.top` 取 hull 本身，`Ind3.base` 才取裸 `vcI`（`:216`、`:220`）。
`exists_ind3_logVol_iff` 给出 `∃ S : Ind3 D, logVol D S.1 = x ↔ x ≤ V`；反向在无穷处按 `exp(x−V)` 缩放 hull（`Iut/Wall/Ind3.lean:253`、`:259`）。
这个存在证明遍历的是定义允许的区域。它没有断言每一个这样缩出的区域都来自论文指定的最终 evaluation。

`Iut.Wall.EtaAlg` 接受两个不同的选择：`ι` 是输入 BPS 到 Θ 侧 BPS 的同构，`S` 是一个 `Ind3 D`；`out ι S` 才是区域（`Iut/Wall/EtaAlg.lean:108`、`:141`）。
其中 T1 让 Ind1/Ind2 改写 `S`；T2 使输出只依赖 étale-unit 部分；T3 要求每个输出 adelic 且在一次 Ind1 像的 hull 中（`Iut/Wall/EtaAlg.lean:112`、`:117`、`:123`）。
`InHullOfImage` 要求一次选定整族标签 `l`，其后 `∀ i` 同时约束各 capsule（`Iut/Wall/Rss.lean:338`）。不是各自看完体积再补一个无关标签。
`Iut.Wall D A` 对每对 sides 和每个 `Θ(h₁) → q(h₂)` 的 BPS link，要求存在反向类型的 `ι : A.Choice (A.qBPS h₂) h₁` 和 `S` 使 `η_anab = η_q`（`Iut/Wall/EtaAlg.lean:173`）。
`wall_iff_forall` 因 link 已非空，能消掉不进等式的 link 参数；它不消掉 `∃ ι S`（`Iut/Wall/EtaAlg.lean:157`、`:183`）。
`etaAnab_eq_etaQ_iff` 把这对 `ι,S` 的线性映射相等化为 `logVol D (A.out ι S) = −a`（`Iut/Wall/EtaAlg.lean:151`）。
`exists_out_of_wall` 用 T3 输出见证；`variant_of_wall` 接 `logVol_le_rhs` 得 `−a ≤ R`（`Iut/Wall/EtaAlg.lean:189`、`:201`；`Iut/Wall/Rss.lean:374`）。
q 端另有区域构造：`qRegion` 取一次幂乘 integral region，`logVol_qRegion` 算出它的体积是 q 的 lhs（`Iut/Wall/QPilotRegion.lean:314`、`:321`）。
`qRegion_first` 给出第零个 capsule 上 `qRegion` 与 `lgp D (integralRegion D)` 一致（`Iut/Wall/QPilotRegion.lean:331`）。
不能把这一个分量的 `rfl` 扩展为全局相等：后一个区域的全局 log-volume 是 `−s·a`（`logVol_lgp_integral`，`Iut/Wall/IdentifiedCopies.lean:444`）。

| 固定 `D` 时的箭头 | 证明 / 定义 | 限定与读法 |
|---|---|---|
| `Wall D A → Var(D)` | `variant_of_wall`，`Iut/Wall/EtaAlg.lean:201` | 正向适用于每个给定的 `A`；不保证该 `A` 满足 wall。 |
| `Var(D) ↔ NumericalWall D` | `numericalWall_iff`，`Iut/Wall/Checks.lean:61` | `:56` 只要求存在有指定读数的合格区域 `U`，未指定 `U` 从哪个算法来。 |
| `Var(D) ↔ ∃ A : EtaAlg D, Wall D A` | `exists_wall_iff`，`Iut/Wall/Checks.lean:173` | 从变体可做出常输出 `U` 的 `trivialAlg`（`:142`、`:168`），不是为指定算法证明 wall。 |
| `A.SHEq ↔ Wall D A` | `EtaAlg.sheq_iff_wall`，`Iut/Wall/Constraints.lean:137` | 上游已经把 xi-e 的一种读法写成 `A.out ι S` 与 `qRegion` 的 `Rss` 类相等（`:132`）。 |
| `A.SHESides ↔ 输出仅依赖 S` | `EtaAlg.sheSides_iff`，`Iut/Wall/Constraints.lean:116` | 两侧各可表达与某输出命中 q 类是两回事；这里没有 `SHEq` 结论。 |

`Rss.mk_eq_mk_iff` 比的是两个区域的 log-volume；商 `rssEquiv` 等价于实数（`Iut/Wall/Rss.lean:460`、`:486`）。同类不是区域相等，更不是带槽位标记的原文输出相等。
`not_isTrivial_of_lgpLaw` 则证明满足 LGP 平移律的算法不能恒输出 q 的读数（`Iut/Wall/Checks.lean:93`、`:98`）；这也区别了存在式见证与受约束算法。

### B.4 `WallEquiv`：在哪些模型里才能写双箭头
2026-10-13 的 `da52dfb3a0` 加入 `WallEquiv`。合取定理 `Iut.WallEquiv.wallEquiv` 列出的每个等价都带其模型和量词（`Iut/WallEquiv/Basic.lean:150`）。

| 输入 ↔ 输出，或单向 → | 声明及位置 | 额外条件 / 证法 |
|---|---|---|
| `Lana91 D H ↔ Wall D (theaterAlg D H) ↔ SSIneq D` | `lana91_iff_wall`、`wall_theaterAlg_iff_ss`、`lana91_iff_ss`，`Iut/WallEquiv/Basic.lean:95`、`:105`、`:111` | `H : σ → ThetaPmEllNFHT D` 且 `σ` 非空；`:80` 的 (9-1) 量化的是 P19 的 `ThetaLinkIso`。 |
| `Wall D (idAlg D) ↔ SSIneq D` | `wall_idAlg_iff`，`Iut/Wall/IdentifiedCopies.lean:488` | 这里是同一份环结构中的副本，实际输出 `lgp D S.1`；不是常区域 `trivialAlg`（`:468`、`:483`）。 |
| `Wall D A ↔ SSIneq D` | `Iut.WallEquiv.wall_iff_ss_of_thetaShift`，`Iut/WallEquiv/Basic.lean:131` | 对任意 `A` 须给 `A.ThetaShift`，即每项输出体积为 `−s·a + logVol(S)`（`Iut/Wall/MultiContainer.lean:105`）。 |
| `Exists91 D ↔ SSIneq D` | `exists91_iff_ss`，`Iut/WallEquiv/Basic.lean:116` | `Exists91` 预先指定 `lgp D S.1`（`:87`）；不同于只量化任意 `U` 的 `NumericalWall`。 |
| `SSIneq D ↔ ∃ S : Ind3 D, logVol D S.1 = (s−1)·a` | `ss_iff_exists_ind3`，`Iut/WallEquiv/Forms.lean:64` | 起作用的是该 hull 内可实现的体积区间，而非 arbitrary `EtaAlg.out`。 |
| `SSIneq D → Var(D)` | `Iut.WallEquiv.variant_of_ss`，`Iut/WallEquiv/Basic.lean:168` | 经 `idAlg` 正向消费；`:172` 的 `variant_iff` **没有**列出 `Var(D) ↔ SSIneq D`。 |
| `(∀ D, SSIneq D) → Cor312VariantHolds ∧ Cor312LiteralHolds ∧ ClassicalABC` | `Iut.WallEquiv.classicalABC_of_ss`，`Iut/WallEquiv/Basic.lean:180` | `:182` 逐 `D` 得变体，`:183` 分头导出 literal 与 ABC，**不是**由 literal 推出 ABC。 |

`cor312Literal_of_variant` 用同一 q 端和 `rhs_le_rhsLit`（`Iut/Concrete/Literal.lean:115`）；literal 把固定标签放大成所有位置之并，包含关系见同文件 `:91`。没有用反方向。
标签范围可直接查 `ivLabels = {distinguished …}` 和 `litLabels = Set.univ`（`Iut/Concrete/ThetaRegion.lean:237`、`:241`）；全称的 literal 绑定 `concreteVariantDataLit`（同文件 `:383`）。
`wall_facts` 另外给出度映射与 Θ-link 不同、两个 realified Frobenioid pilot 对象间不存在同构（`Iut/WallEquiv/Basic.lean:187`）。这不否定上文 BPS 层的 link 存在性：对象不同。

**反向到底差多少。** `gap D` 是 `R` 减去 `lgp` 作用于 `hull(VC(I))` 后的体积，`gap_nonneg` 给出非负性（`Iut/WallEquiv/Gap.lean:505`、`:514`）。
`ss_iff_le_rhs_sub_gap` 把 SS 写成 `−a ≤ R−gap D`，而 `Var(D)` 只给 `−a ≤ R`（`Iut/WallEquiv/Gap.lean:531`、`:537`）。
`variant_and_not_ss_iff` 把「有变体、无 SS」精确定位在 `R−gap D < −a ≤ R`（`Iut/WallEquiv/Gap.lean:554`）；这是区间刻画，不是已找到落在其中的真实 `D`。
`gapHullAt` 在无穷处为零，`gapHullAt_eq_zero` 排除非坏剩余特征；`gap_eq` 把差写成有限支撑的 Ind2 项的 procession 平均（`Iut/WallEquiv/Gap.lean:895`、`:945`、`:961`）。
若所有坏剩余特征的 `ind2Term` 也逐项为零，`ss_iff_variant_of_ind2Term` 才给一条返回 SS 的路（`Iut/WallEquiv/Gap.lean:986`）。这是充分条件，不是已证明的消失。
另有 `gapNoHull_pos` 的严格正性（`Iut/WallEquiv/Gap.lean:871`）；`:995` 的总结只给现行 `0 ≤ gap D ≤ gapNoHull D`，不能将旧差的严格性移给新差。
作局部数值复核，应选 `WallEquiv.ssIneq_iff_packets` 的 `hullPacket`（`Iut/WallEquiv/VcI.lean:889`）；`:896` 的 `vcIPacket` 只对应 no-hull 版本。
在满足 `IsTamePrime D p` 处，`hullPacket_tame` 把 hull 项写成按元组加权的 `∑ⱼ(1−1/eⱼ)·log p`（`Iut/WallEquiv/VcI.lean:844`）。这是容器项，不是 q 的阶。

### B.5 `LogLink`：已经形式化的 (xi)，以及它仍要什么
`Iut/LogLink/Lattice.lean:90` 的 `LogThetaLattice` 用整数格点 `(n,m)` 放 theater：纵向 `(n,m+1)` 是 log-link，横向 `(n+1,m)` 是 Θ-link。不要把 (xi) 画成纵向箭头。
2026-10-12 的 `d7d4cc9184` 引入这组模型。局部列已有 `LogColumn.upperSemiCompat`：在素数及相应范数条件下，迭代像经 Kummer 进入 log-shell（`Iut/LogLink/Column.lean:129`）。
这是包含而非满射到原文所需输出族；`LogColumn.kummer_log_ne` 还在单位 `1` 区分先取 log 和直接取 Kummer 的两条路（`Iut/LogLink/Column.lean:141`）。
`LatticeKummer` 在每个格点指定 `Scaling D`，并要求 `UnitInducedScaling`（`Iut/LogLink/Kummer.lean:248`）；`:271` 由此得体积相容，`:279` 得任意两点间 distortion 为零。
这不等于环结构一致：同一格子可取 `LatticeKummer.alt`；`alt_alien_horiz`、`alt_alien_vert` 分别排除其横、纵边上的环运输（`Iut/LogLink/Thm311.lean:275`、`:289`）。
`Thm311` 包含 Ind1/2 作用、跨顶点 multiradiality、垂直上半相容、shell 和体积相容、水平条带同构（`Iut/LogLink/Thm311.lean:141`）。
`thm311_model` 为给定 `L,K` 填这些字段（`Iut/LogLink/Thm311.lean:190`），并未在这些字段里预装 `XiPrinciple K`。

这里的输出律可查到定义体：`theaterAlg` 的 étale-unit 来自 `(H h).Fmu`，但输出行直接取 `lgp D S.1`（`Iut/HodgeTheater/Wall.lean:142`、`:143`）。
`LatticeKummer.model_out` 因而是 `rfl`；运输则按 `kum b * (kum a)⁻¹` 作用于区域（`Iut/LogLink/Thm311.lean:167`、`:170`）。两件事都不是从一个带标记的最终 evaluation 推出来的。
`XiPrinciple K := K.model.WallOn horizRel`（`Iut/LogLink/Thm311.lean:203`）。展开 `WallOn`，每条横边、每个 link 必须有 `ι,S`，使运输后输出的体积等于目标端 q 区域的体积（`Iut/Wall/MultiContainer.lean:295`）。
比较发生在同一个目标容器。`wallOn_iff_rss` 将它改写为运输后两者的 `Rss` 类相等（`Iut/Wall/MultiContainer.lean:305`），仍不要求两者是同一区域。

| 模型内的箭头 | 证据 | 没被消去的条件 |
|---|---|---|
| `ThetaShift → (WallOn L ↔ 逐边 (s−1)·a−distortion ≤ V)` | `MultiContainer.wallOn_iff_of_thetaShift`，`Iut/Wall/MultiContainer.lean:341` | 有向关系只查指定边；`distortion` 是目标 shift 减源 shift（同文件 `:248`）。 |
| `ThetaShift + VolCompat + 关系非空 → (WallOn L ↔ SSIneq D)` | `wallOn_iff_ss_of_volCompat`，`Iut/Wall/MultiContainer.lean:407` | 非空用于从逐边取出不等式；横边 `(0,0) → (1,0)` 在 `Iut/LogLink/Thm311.lean:208`。 |
| `Thm311 L K → (XiPrinciple K ↔ SSIneq D)` | `Iut.LogLink.xi_iff_ss`，`Iut/LogLink/Thm311.lean:219` | 接上 `thm311_model` 才得到 `WallEquiv.xi_iff_ss_model`（`Iut/WallEquiv/Basic.lean:138`）；等价本身不产出左端或右端。 |
| `Thm311 L K + XiPrinciple K → Var(D)` | `Iut.LogLink.variant_of_thm311`，`Iut/LogLink/Thm311.lean:214` | `hx` 是第二个实参；同文件 `:225` 的 `wall_of_thm311` 同样需要它。 |
| `(∀ D, ∃ L K, XiPrinciple K) → ClassicalABC` | `Iut.LogLink.classicalABC_of_xi`，`Iut/LogLink/Thm311.lean:241` | 先逐 `D` 选 `L,K`，再用 `classicalABC_of_thm311`（`:234`）；没有由 ABC 回推 xi 的结论。 |

对所有边要求 `Wall3` 与只在横边要求 `WallOn horizRel` 不同。前者在 `ThetaShift` 下出现的是 `+ abs(distortion)`（`Iut/Wall/MultiContainer.lean:373`），不能套给一条单向边。
若关系同时含一条边及其反向，`ss_of_wallOn_pair` 改用两条不等式抵消反号的 distortion（`Iut/Wall/MultiContainer.lean:356`）；仅有向右的横边不能这样抵消。
对一般关系，`variant_of_wallOn` 还要非空和 `TransportRealisation`；后者要求运输后的输出仍在目标的 hull 中（`Iut/Wall/MultiContainer.lean:429`、`:435`）。
`variant_of_wallOn_of_volCompat` 提供保体积的另一条路（`Iut/Wall/MultiContainer.lean:444`）；这条才是 `variant_of_thm311` 在 `Iut/LogLink/Thm311.lean:216` 调用的版本。
`Multiradial3` 要求运输到共同目标后各区域经 Ind3 重编号相同；配合 `ThetaShift`，`volCompat_of_multiradial3` 由最大输出在两个方向的比较消掉 distortion（`Iut/Wall/MultiConstraints.lean:94`、`:101`）。
`logVol_transport_out` 得 `−s·a + logVol(S)`（`Iut/LogLink/Thm311.lean:256`）。零 distortion 只是运输不改这个数，还得有 `logVol(S) = (s−1)·a` 才能命中 q。

**增添结构后，上游确实复查过 xi。** `thm311LGP_model` 含坏处 splitting monoid、全局单位与无穷处上半相容等字段（`Iut/LogLink/Thm311LGP.lean:126`、`:167`）。
例如 `ArchColumn.exists_surj` 从半径 `π` 的闭球中取子集，经反向映射满到迭代 log-link 的定义域（`Iut/LogLink/Arch.lean:225`）；可核对的满射对象不是 `qRegion`。
`xi_iff_ss_lgp` 取该结构的 `base`；`answerLGP` 同时给横纵零 distortion、Gaussian 度保持及 `XiPrinciple K ↔ SSIneq D`（`Iut/LogLink/Thm311LGP.lean:185`、`:198`）。
加入 bi-coric 和 mono-theta Kummer 数据后，`thm311_full_model` 的末项**仍是等价**，前面三项才是模型里的 3.11/LGP、3.11(iii)、1.5(v) 结论（`Iut/LogLink/Thm311Rest.lean:623`）。
并非每一层都把 unit-induced 当成外加假设：`GalInducedScaling.anabelian`、`AnabelianScaling.unitInduced` 从更具体的数据导出它（`Iut/LogLink/GalKummer.lean:281`、`:288`）。
`StripKummer` 从刚化 prime-strip 的 `link` 读出 Galois 同构；`StripKummer.xi_iff_ss` 是落到相应 `LatticeKummer` 后的等价（`Iut/LogLink/StripKummer.lean:168`、`:185`、`:198`）。
在全处模型，`FullKummer.logVol_transport` 对 adelic 区域证明保体积；`FullGalKummer.xi_iff_ss` 明写的是投影 `toFullKummer.toLatticeKummer` 后的 xi（`Iut/LogLink/GalKummerAll.lean:605`、`:648`）。
固定 `D` 换同类格子并不能制造 xi：`xi_iff_xi` 是将两边都化到同一个 `SSIneq D`（`Iut/LogLink/Thm311.lean:248`）。

### B.6 反例的精确论域：`Thm311Package`，不是初始 Θ 数据
2026-10-13 的 `180c049972` 引入 `Iut.WallEquiv.NonDerivable`。`Thm311Package` 把区域、体积、`a,V,R`、LGP 与运输列为字段（`Iut/WallEquiv/NonDerivable.lean:118`）。
其 `structural` 字段量化另给的 `D,L,K,B,M`；字段本身不把该 `D` 的局部算术绑定到这个抽象包的 `V`、`a`（`Iut/WallEquiv/NonDerivable.lean:203`）。
从真实输入到包有正向构造 `ofThetaData D K`：取的是实际 `D.qPilot.absLogQ`、`hullOf D (vcI D)` 的体积和该 `D` 的 RHS（`Iut/WallEquiv/NonDerivable.lean:327`、`:333`）。
`ss_ofThetaData_iff`、`xi_ofThetaData_iff` 证明这个像中的 SS、xi 确是前述 `SSIneq D`、`XiPrinciple K`（`Iut/WallEquiv/NonDerivable.lean:394`、`:398`）。构造方向不是「每包来自一个 `D`」。
包中已能导出 `V−s·a ≤ R`（`V_sub_le_R`，`Iut/WallEquiv/NonDerivable.lean:250`）。这不是所需的 `(s−1)·a ≤ V`：一个给 `V` 上界，一个要 `V` 下界。
`Thm311Package.xi_iff` 的正向在一条具体横边取见证，反向以 `ind3_exists` 取体积 `(s−1)·a`（`Iut/WallEquiv/NonDerivable.lean:273`、`:283`）。可直接看见点态等价用了哪条存在性。
`family` 在满足 `V−s·a ≤ R` 时取 `Reg := ℝ`、`vol := id`，以实数平移充当 LGP（`Iut/WallEquiv/NonDerivable.lean:408`、`:420`、`:429`）。

| 包内固定数据 | 算术判定 | Lean 见证 |
|---|---|---|
| `ℓ=7, logQ=14, a=1, V=R=1` | `s=14/3`，所需 `11/3 ≤ 1` 为假 | `counterexample`、`exists_package_not_xi`，`Iut/WallEquiv/NonDerivable.lean:484`、`:491` |
| `ℓ=7, logQ=14, a=1, V=R=4` | 同一阈值，`11/3 ≤ 4` 为真 | `exists_package_xi`，`Iut/WallEquiv/NonDerivable.lean:498` |

`nonDerivability` 合取的否定是 `¬ ∀ P, P.Xi` **以及** `¬ ∀ P, ¬P.Xi`（`Iut/WallEquiv/NonDerivable.lean:556`）。两项都量化 `P : Thm311Package`；不是 `∃ D, ¬SSIneq D`。
`exists_package_not_xi_nonneg` 即使固定 `ℓ` 和正的 `logQ`，还可取 `V ≥ 0` 的失败包（`Iut/WallEquiv/NonDerivable.lean:508`）。
`exists_package_not_xi_ge` 甚至对任给常数下界 `L` 造 `L ≤ V` 的失败包；这里让 `a` 随 `L` 增大（`Iut/WallEquiv/NonDerivable.lean:521`、`:525`）。所缺的是与 q 耦合的下界。
这些字段是否穷尽了原文 3.11 的内容，不是 Lean 定理；源码甚至将其对仓内已知结果的穷尽性也标为人工审计（`Iut/WallEquiv/NonDerivable.lean:18`）。
`classicalABC_of_forall_xi` 要的恰是真实数据像上 `∀ D, (ofThetaData D (K D)).Xi`（`Iut/WallEquiv/NonDerivable.lean:548`）；它说明这个主张**至少足以**推出 ABC，不说明从 ABC 推回它。

### B.7 两项可省的工作，以及不能代做的那一步
**1. 不重写变体下游。** 若交付的是每个 `D : InitialThetaData.{0}` 上的 `Var(D)`，直接消费者是 `Iut.classicalABC_of_variant` 或 `Iut.formalConjecturesABC_of_variant`（`Iut/MainTheorem.lean:36`；`Iut/Abc/FormalConjectures.lean:240`）。
这样可以略过另写一般位置、次数一特化和两种 ABC 互译；保留现成 Challenge 的有限例外目标，避免移植时把自己的 ε-常数定义误作已对齐的锁。
接入的判据不是符号相似：要使 `D` 上的 q 归一化与 RHS 的 procession/hull 匹配，才能交给 B.1；单个 `D` 上的一次成功不满足这个全称量词。

**2. 让 `logVol_le_rhs` 处理统一上界。** 固定兼容的 `D` 与论文输出族 `P_C`，先给每个实际标记输出 `x` 指派 LANA 区域 `Uₓ`，保留 `x` 的来源和标记，不按所需数值反选区域。
需验 `IsAdelic D Uₓ`、`InHullOfImage D Uₓ`、`ν_C(x) = logVol D Uₓ`；再用 `Iut/Wall/Rss.lean:374` 的 `logVol_le_rhs`，即得每个读数 `≤ R`，无需重做 packet 单调性。
若另外比较了这个 `R` 与论文的 signed hull（推出上界只需 `R ≤ paperHull`），这条复用就能提供本仓库 `S2452PaperOutputFamily.upper`（`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:151`）。
尚欠的另一字段是同族的 `coverage`（本仓库 `tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:153`）：或有精确命中，或对任意 `ε>0` 有输出使 `Q_C−ε ≤ ν_C(x)`。
这个单侧符号和量词见本仓库 `tmp/sheaf/xif/paper/S1447ReportFMarkedTraceActual.lean:304`、`:308`。
`exists_adelic_iff` 确能在一次 Ind1 像的 hull 中取得任何 `x ≤ R` 的读数（`Iut/Wall/Rss.lean:403`）；它的见证不带来自这一个 `P_C` 的原像。
上界和覆盖齐备后，本仓库 `tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:234` 的 `s2452_fixedC_qPilot_le_signedHull` 还要 `F.Q_C = C.qPilotLogVolume` 才消费固定实例。
本仓库的消费者还区分 q 的归一化 `Q_C_eq_neg_abs_log_q` 与 `readout_eq`（`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:145`、`:147`），不能拿上游的 `absLogQ` 名称当作两边相等的证明。

因此可以比较**研究对象**，不能宣称本项目唯一研究 wall：上游已有指定算法的 (9-1)、xi-e 的 `SHEq`、格上的 xi 与 SS 等价、以及区分正反模型的定理。
本项目可辨认的任务是从原文受限 evaluation 产生 `P_C` 中的标记见证，保持读数并接入 hull 上界；它不同于为模型的所有 `Ind3` 区域证明一个区间公式，也尚未由这个差别得到原文 3.12。
本次只核读源码与锁：`statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 均未在此快照重验；历史 Comparator 回执只对应 B.2 所述的条件命题。

<a id="r-milestones"></a>

## C. 从 R0–R7 看实际消费者：原 III、IUT IV 与整数 ABC

**两种终点有不同的量词。** 固定一组原 III.3.11 允许的输入，须证明这组输入的带符号读数 `qₛ ≤ Θₚ`，并证明 `Θₚ` 有限。
这里只固定输入来陈述和核查证明；原定理仍然要求对每一组合格输入成立。[原 III.3.12](IUT-TEXT/III.txt#L10326) 的 `Θₚ` 是全部允许像的 hull 的归一化读数，不是选出的某一行。
只求整数 ABC 则须先给每个 `ε>0` 选一个 `Kε>0`，再对所有本原正整数 `a+b=c` 证明 `c ≤ Kε·rad(abc)^(1+ε)`。
后一目标允许为每个点选不同的辅助域和素数；不允许见到三元组才选常数。[原端点及箭头方向](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L9)；[本地 ABC 定义](../LeanFormal/IUT/ABCBridge/Statement.lean#L32)。

| 交付给谁 | 同一输入上足以交付什么 | 不随之交付什么 |
| --- | --- | --- |
| 原 III.3.12 | `qₛ ≤ L ≤ Θₚ`，另证原 hull 读数有限；`L` 可以在另一空间算 | 不要求两空间相等；`qₛ ≤ U` 和 `Θₚ ≤ U` 也不能代替下界 |
| IV 的原 Θ 估计 | R1 的下界与 R2 的 `Θₚ ≤ H` 落在同一原读数，再用独立的算术上界 | 只有算术模型的 `−M ≤ H`，不能据此给原 Θ 定系数 |
| 算术 C4、D1 或 ABC | 独立构造的 `−M ≤ L ≤ U ≤ H` 足以接 C3 消去中项；ABC 还可改用统一有损的估计 | C4 不是 III 的逆定理，整数 ABC 也不恢复固定输入的来源或有限性 |

三种交付的区别见[交接 §1 的 A–D 四种情形](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L13)；下文写的是每条箭头的输入，而非文件名之间的连线。

**证据口径（2026-11-20）。** 本地 HEAD 为 `a997af4b1cb2339d1e7403ef0781a16f809f4476`，引用的是当日工作树，不能据此断言文件都在该提交内。
LANA 固定在 `553076af459e7a401bfee63a4607814d1c854477`；下引 `Iut/` 链接指向本仓副本，对引用的文件按统一换行核对，并非本地独创。
LANA 的 `genl` 是独立依赖；下引 `BelyiDescent.lean` 与其锁定版本 `179e26f6f7becc379b32ea526aaf7fb8ae81441a` 的文本相符。
`LeanFormal/`、`tmp/sheaf/` 的声明按本地类型读；相同公式不是两个 Lean 环境之间的类型转换。[交接快照与两仓版本](../dag/nodes/r0-r7-theta-comparison-handoff-20261118.json#L7)；[本地工具链](../lean-toolchain#L1)。
“有证明体”与“历史 watchdog DONE”分记；没有条件的构造时写“未构造”。本次不编译、不运行比较器，
当前版本的 `statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 四项均为 `NOT_RUN`，不覆盖旧记录。

### C.1 R0–R2：一份 q 算术字典，两种有方向的体积比较
**R0 给 R1 和 R3 的是带重数的 q 度。** 对坏基位 `b`，把其上所有 `P` 的 `f_P·ord_P(q)·log p` 相加，除以 `[F:ℚ]`，再对 `b` 求和得未开根的 `Q`。
本地 [Qb 的全纤维展开](../tmp/sheaf/xif/paper/Mzk1ULR0FullFiberActual.lean#L39) 与 [M 的求和式](../tmp/sheaf/xif/paper/Mzk1ULR0FullFiberActual.lean#L48) 给出该实现的 `M=Q/(2ℓ)`；R1 消费的是负号端 `−M`。
归并到一个基位不要求所有完备化中的 q 元素相等：共同的 `j` 可识别消失阶，随后用 `Σef`；不能只乘剩余次数而丢掉 `ord_P(q)`。
[全纤维与选位的比较](../tmp/sheaf/xif/paper/Mzk1ULR0FiberCrosswalkActual.lean#L43) 明列逐位阶、次数和及选位权重的条件；[负质量的有限求和](../tmp/sheaf/xif/paper/Mzk1ULR0QMEndpointActual.lean#L39) 消费这些等式。
R3 生效的是同一套单位：`D(F)` 为对数根判别式，`h̄=logHeight₁/[F:ℚ]`，截断导子也按次数除。[判别式](../tmp/sheaf/xif/paper/Mzk1ULR0D1WiringActual.lean#L24)；[高度与导子](../tmp/sheaf/xif/paper/Mzk1ULR0D1WiringActual.lean#L30)。
**LANA 已消费 R0 对应的量：** [logQ](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Cor312/LeftHandSide.lean#L81) 用坏位权重、`qOrder`、`log p`；[负的 lhs](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Cor312/LeftHandSide.lean#L88) 再除 `2ℓ`。
对接要核对坏位枚举、权重和开根次数，不是拿本地的一个 `Qb` 去填对方的 `logQ`。

**R1 给原 III 的是下界，给 C4 的是 `−M` 能通过中项。** [坏位参考区域的读数](../tmp/sheaf/xif/paper/Mzk1URBadPlaceActualMapActual.lean#L78) 已可算，
但要把它计入原 Θ，下界必须来自允许的输出，并在原测度参考和权重下不变小；仅写出一个算术格没有这层含义。
[单向运输](../tmp/sheaf/xif/paper/Mzk1ActualReadingTargetActual.lean#L159) 的中段 `Q_norm ≤ H_root` 有证明，外段 `Q_src ≤ Q_norm`、`H_root ≤ H_tgt` 则是参数。
若用算术下界证原 III，要的是 `qₛ ≤ −M`；反过来用原 III 供给 C4，要的是 `−M ≤ qₛ`。除非已证相等，否则不能倒用同一字典。
LANA 的[具体变体](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/ThetaRegion.lean#L375) 是 `∀ D` 的命题；[IV 1.10 证明](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/Theorem110.lean#L292) 正在 `h312'.trans hsum` 处消费它，未在这里构造原下界。

**R2 给 IV 的是同一 Θ 的独立上界。** 固定 `p`，每行 `1≤j≤(ℓ−1)/2` 枚举有序元组 `t:Fin(j+1)→E_p`（允许重复），按各槽权重的乘积平均。
在行内先固定标记槽，再控制每个元组的实际 hull；不能在看过元组后改取最有利的槽，再声称适用固定槽的结果。
[单行加权不等式](../LeanFormal/IUT/IUTIV/Estimates/StepVDistinguishedSlotAverage.lean#L87) 消费逐元组上界；[全 procession 平均](../LeanFormal/IUT/IUTIV/Estimates/StepVDistinguishedSlotAverage.lean#L109) 再消去行指标。
算术部分也不必从头做：[不同素数支集的分拆](../tmp/sheaf/xif/paper/Mzk1ULR2HsQSupportActual.lean#L40) 已给出特殊素数与其余项；截断部分仍要 `hbad'`。
[different 塔上界](../tmp/sheaf/xif/paper/Mzk1ULR2HlogdKTowerActual.lean#L32) 需要实际相对 different 的 `hbound`；两者都不是原允许像落入逐行外盒的证明。
LANA 在变体对象上有[具体局部估计](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/LocalEstimate.lean#L460)，从[逐包 hull 上界](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/LogVolumeBound.lean#L178) 汇成 [rhs_le](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/LogVolumeBound.lean#L210)。
因此可复用的是“已给区域怎样求上界”；若要给原 III 背书，还须对同一固定输入识别该区域与原输出及其全局读数。[变体自己说明的边界](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Cor312/Statement.lean#L44)。

### C.2 本地 IUT IV：从夹逼消去 Θ，再吸收一个明确的系数
令 `Q` 是未开根的 q 度，`κ=(ℓ+1)/4`，`cℓ=(1−12/ℓ²)/6`。[c3_to_c4](../tmp/sheaf/xif/paper/Mzk1P6C3C4Actual.lean#L9) 只消费三条大小关系：
`−M ≤ θ ≤ H` 且 `H ≤ κ(A−cℓQ)−M`。两端加回同一个 `M`，用 `κ>0` 除过去，得到 `cℓQ ≤ A`；中间空间不参与这步消元。
[c4_display](../tmp/sheaf/xif/paper/Mzk1P6C3C4Actual.lean#L18) 把它等价地写作 `Q/6 ≤ A+(2/ℓ²)Q`。这是 R3 要的精确算术式，不是新构造的 `Θₚ`。
[含论文算术量的版本](../tmp/sheaf/xif/paper/Mzk1UCC4PaperActual.lean#L86) 已替入 `dMod`、`eMod` 和素数计数常数；`hP5`、`htheta`、`hstepVIII` 仍在定理左边。
尤其要核对域：该版本的 [SAr_tripodal](../tmp/sheaf/xif/paper/Mzk1ULPaperLettersActual.lean#L112) 实际在 `T.arithmetic.F` 取判别式和导子，并不是名字相似的 `F_tpd`。
已知 `S_tpd≤S_F` 时，可把右端的 `S_tpd` 放宽为 `S_F`；反向换成更小的量必须有另一个上界。这是移植时要核对的条件。
本地 IV 1.10 的第二次化简可以独立复核。记 `S=log d_Ftpd+log f_Ftpd`、`E=e*ℓ+η_prm`，取 `ℓ≥7, d≥1, S,E≥0`。
从 `Q/6 ≤ (1+12d/ℓ)S+10E+(2/ℓ²)Q` 出发，[消项与正系数估计](../tmp/sheaf/xif/paper/Mzk1IVThm110LogQActual.lean#L22) 得 `Q ≤ 4dℓS+5ℓ²E`。
乘回 `2/ℓ²`，原先的误差最多是 `(8d/ℓ)S+10E`，恰好把 `12,10` 放宽为 `20,20`：`Q/6 ≤ (1+20d/ℓ)S+20E`。
[差额的两个系数](../tmp/sheaf/xif/paper/S3171IUTIVSection1DisplayActual.lean#L111) 与[只取 hCor312 的消费者](../tmp/sheaf/xif/paper/Mzk1IVThm110Actual.lean#L101) 表明不必再独立提供这条数值 `Q` 界。
这里的 `hCor312` 是已展开的算术不等式；签名并未从原 Θ 构造它，也不可把 `ℓ≥7` 的显示式直接用于 `ℓ=5`。
LANA 的 [theorem110](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/Theorem110.lean#L245) 输出同一个 `20,20` 形状。它要算术证书、局部估计、素数计数界和该 `X` 上的变体；
它[先汇总局部读数](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/Theorem110.lean#L258)，再接下界。互审最短的是比对 `Q`、`S` 与系数，不是重写求和或把两份 `h312` 当成同一个假设。
[本地 IV 的历史 DONE](../dag/watchdog/watchdog.log#L244332) 和 [C4 论文算术量版本的 DONE](../dag/watchdog/watchdog.log#L260380) 只为当时这两个文件作证。

### C.3 R3：把 C4 用在逐点选出的数据上，才有 D1
R3 的消费者不是固定的 `T`，而是 R6 将要调用的局部高度定理 D1：给定次数界 `d`、合格的 `K_V`、`η>0`，先定 `C`，
对其中每个数域 `L` 和 Legendre 点 `λ≠0,1`，有 `h̄_L(λ) ≤ (1+η)(D(L)+N_L(λ))+C`。`N_L` 是截断导子，不能计重数。
[IV 2.2 原范围](IUT-TEXT/IV.txt#L2382) 要在指定的局部条件（含 2 处的 j 界）、有限例外集外产生合格数据；例外与低点用统一常数覆盖，不要求给例外点造源。
本地 [mulKernel](../tmp/sheaf/xif/paper/Mzk1G1R3TorsionKernelActual.lean#L27) 直接以曲线群的 `[m]P=0` 定义扭点。对非奇异、`y≠0` 的复 Legendre 点，
[四倍判据](../tmp/sheaf/xif/paper/Mzk1G1R3FourCriterionActual.lean#L43) 双向识别 `[4]P=0` 与除法多项式的零点，已有对象可检验坐标而非只数根。
五倍也有具体结果：[ψ₅ 的次数为 12、首项系数为 5](../tmp/sheaf/xif/paper/Mzk1G1R3FiveDivisionActual.lean#L32)，[核条件](../tmp/sheaf/xif/paper/Mzk1G1R3FiveKernelActual.lean#L31) 化为 `[4]P=−P`；[另一支 y](../tmp/sheaf/xif/paper/Mzk1G1R3FiveKernelActual.lean#L52) 也在核中。
要用于 `ℚ(j(λ)) ⊆ ℚ(λ) ⊆ F ⊆ F(E[ℓ])`，仍须在同一闭包内识别所需 `[3],[5],[ℓ]` 的实际核、无穷远点、全部坐标及其生成域；四倍判据不代替一般 `ℓ`。
选 `ℓ` 的排除集、窗口和大像条件在使用 C4 之前确定；这保证 `ℓ` 随点变化，而常数不随点变化。[交接 §6 的 R3 验收](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L137)。
可先用本地 [IV 2.1 的避素数定理](../LeanFormal/IUT/IUTIV/Estimates/Section2.lean#L225)：存在统一 `ξ≥5`，每个有限素数集 `A` 外有素数 `p≤2(Σ_{q∈A} log q+ξ)`。
它不需要 C4；要让 `p` 成为合格的 `ℓ`，仍要给排除集的实际大小和窗口下端。计数常数也可单独核对：本地[最终的 4/3 界](../LeanFormal/IUT/IUTIV/Estimates/Section2.lean#L409) 在大 `x` 处比 LANA [接口所需的 3/2](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/Invariants.lean#L56) 更紧。
LANA 已有[自己的计数证书](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/ChebyshevExplicit.lean#L262)，故比较的价值是核对阈值与系数，不是声称填补了对方缺失的素数定理。
第一张表区分全部有限 q 位与入选坏位；第二张表只在入选纤维内分“使用的 lift”和其余 lift。[两张表的类型](../tmp/sheaf/xif/paper/Mzk1G1F2ThetaIndexTablesActual.lean#L40)。
[入选部分的分拆](../tmp/sheaf/xif/paper/Mzk1G1F2ThetaIndexTablesActual.lean#L81) 已给 `Q_bad=Q_used+hMinusQ` 且余项非负；它不估计第一张表中被排除位的总高度。
输入 `Q≤h≤ℓ²`、`ℓ` 的上界、`S≤D+N` 及 `h−Q` 的统一界以后，[d4_absorption](../tmp/sheaf/xif/paper/Mzk1G1D4BridgeActual.lean#L40) 把 C4 送到
`h/6 ≤ (1+C/√h)(D+N)+C√h·log(2Ch)+C`，其中 `C` 只依赖传入的界。[C 的显式式子](../tmp/sheaf/xif/paper/Mzk1G1D4BridgeActual.lean#L36)。
复用它要把 `Q` 和 `h` 都按未开根的 q 度计，并另证 `h/6` 与真实 `h̄_L(λ)` 的有界差；[旧 LocalHeightCriterion](../tmp/sheaf/xif/paper/Mzk1G1LocalHeightCriterionActual.lean#L68) 左侧还是总高度。
**LANA 在哪一行用它？** 对方不调用本地 `d4_absorption`，而是[先选素数](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/Corollary22.lean#L443)，[取得该点的数据和证书](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/Corollary22.lean#L530) 后才在 [h110](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/Corollary22.lean#L535) 使用 `h312`。
其中 [Tripod 的实际构造](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tripod/Main.lean#L107) 给 `D`、塔算术与 q 字典，[紧集上的高度比较](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tripod/Height.lean#L791) 已有证明；[有限例外](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Implication/Corollary23.lean#L78) 另计。
可对接的是选点后的域、q 度和遗漏界；不是从同名的 `InitialThetaData` 自动得到本地的 source 类型。[D4 历史 DONE](../dag/watchdog/watchdog.log#L263261)；[索引表历史 DONE](../dag/watchdog/watchdog.log#L282695)。

### C.4 R4、R5：从一个好函数到对全部共轭有效的一张映射
**R4 的直接消费者有两个。** R5 取 `φ` 的边界逆像用于避让；R6 用同一 `φ` 的分歧来比较线丛。只给逆像有限，不足以供第二个消费者。
设 `S,T` 为不交的 Galois 稳定有限几何点集。所求有限非恒定 `φ` 须同时满足 `φ(S)⊆{0,1,∞}`、`φ(T)∩{0,1,∞}=∅`、分歧值只在边界。
本地有实质的 Riemann–Roch（RR）计算：[zero_divisor_exists_proved](../tmp/sheaf/xif/paper/Mzk1GeomCoreRRProvedActual.lean#L204) 在给定的函数域及局部剩余等实例、代数闭常数域上，
对 `|T|≥2g+1` 给出非零函数 `g₀`，其正阶的位恰是 `T`，且在每个 `t∈T` 阶恰为一。这控制整个零纤维，不只是让函数在若干点消失。
证明[实际调用 RR](../tmp/sheaf/xif/paper/Mzk1GeomCoreRRProvedActual.lean#L209)，由负次数使两个对偶空间消失，再[比较截面空间](../tmp/sheaf/xif/paper/Mzk1GeomCoreRRProvedActual.lean#L237)。
这一步给选择初始映射的零纤维；还要把函数域实例接到实际曲线，处理有理性、下降以及几何点的保护条件。
不要反过来要求任意除子都非特殊：正亏格曲线取 `D=0` 就不成立。[旧接口](../tmp/sheaf/xif/paper/Mzk1G1F2H1VanishingDataActual.lean#L52) 与[只需所选大除子的修正](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L138)。
在固定有理点集上还有[实际两图实例及其零纤维](../tmp/sheaf/xif/paper/Mzk1G1PsiGeneralRRInstanceActual.lean#L35)，输入是 `Finset ℚ`；不可拿它涵盖一切闭几何点。
递归的后半段也有可用的强度：[belyiProtected_final](../tmp/sheaf/xif/paper/Mzk1G1BelyiProtectedConsumerFinalActual.lean#L12) 将有限个代数值送进 `{0,1}`，并控制多项式的临界值；它没有另一个避开的 `T` 参数。
[有理直线上的 noncritical 定理](../Belyi/NoncriticalP1/Main.lean#L114) 更进一步：对稳定有限集及集外一个有理 `τ`，以 Möbius 变换和多项式的复合同时控制分歧、送入点和避开点。
这给 R4 在 `ℙ¹` 上可直接使用的后处理；一般曲线上的首张映射、全部保护点及其复合仍需识别。[本地多项式消费者历史 DONE](../dag/watchdog/watchdog.log#L253737)。
**LANA 对应的已用步骤：** `Genl` 的 [nonempty_belyiDescent](../Genl/Curves/BelyiDescent.lean#L248) 对无标记除子的双曲曲线作反证；
它先提取必须避开的有限个极限位 `T`，再[实际取出 `φ`、Belyi 证明及避让证明](../Genl/Curves/BelyiDescent.lean#L269)。结果由 [Tripod 的一般位置接口](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tripod/GeneralPosition.lean#L269) 使用。

**R5 给 D1 的是固定的紧性条件 `K_V`。** 先控制次数 `≤d` 的局部域，再把每个点的全部局部共轭送进同一份紧性条件，次序不能倒。
第一步的输入很具体：对每个 `M/ℚ_p` 给整生成元、首一极小多项式、其导数下界及共轭范数界。[逐域所需数据](../tmp/sheaf/xif/paper/Mzk1G1SeparationInputActual.lean#L28)。
由 `f′(x)=∏(x−x′)` 和各距离 `≤1`，得到共轭分离；[separationInput_of_differentBound](../tmp/sheaf/xif/paper/Mzk1G1SeparationInputActual.lean#L45) 把这组输入变成 `B=d(d+2)` 的统一版本。
[Krasner 路线的出口](../tmp/sheaf/xif/paper/Mzk1G1SeparationToUFLEConsumerActual.lean#L23) 消费的是该分离界，输出一个足以容纳次数有界局部域的域，不是由一个形式实数生成所有完备化。
证据强弱在此可分辨：上述消费者有 [2026-11-17 的 DONE](../dag/watchdog/watchdog.log#L282386)，而[基域 different 为零的源码](../tmp/sheaf/xif/paper/Mzk1G1BaseDifferentTopActual.lean#L54) 对应文件有[当天的 FAIL](../dag/watchdog/watchdog.log#L284620)。
后者不抹去前者，也不能据此声称已为每个 `M` 构造完整的 `SeparationInput`。
第二步从 R4 要 `d·|V|+1` 张边界逆像两两不交的实际映射；对给定 `y`，先对所有 `v,σ` 取最小边界距离，再对映射取最大。
若下界 `ρ₀>0` 与 `y` 无关，同一张 `φᵢ` 对该 `y` 的全部共轭都有效，包括 2 处和无穷处；逐位另选 `i` 不能送入 D1。[局部射影距离](../tmp/sheaf/xif/paper/Mzk1G1GKRhoP1Actual.lean#L49)；[R5 验收](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L139)。
LANA 的 `Genl` 取另一条路：[在 2 和无穷处取有界子列](../Genl/Curves/BelyiDescent.lean#L263)，对上述同一 `φ` [得到子列尾部的统一界](../Genl/Curves/BelyiDescent.lean#L281)。
可拿 `K_V` 与 [cbsOf 和点的归属条件](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tripod/GeneralPosition.lean#L162) 比较；LANA 不因此需要导入本地 `UniversalLocalFieldExists` 或采用相同的映射族。

### C.5 R6、R7：在同一点上比较高度，再对全部三元组选常数
**R6 把 D1 交给 F6。** 对 R5 选中的 `φᵢ`，置 `Eᵢ=(φᵢ^*{0,1,∞})red`。分歧只在边界，才有对数微分的 `ω_Y(Eᵢ)≃φᵢ^*O(1)`。
这说明为什么必须把 `φᵢ(y)` 的高度、`Eᵢ` 的高度、导子和 `h_ω(y)` 都放回同一 `L,y`；分别找四个数满足标量不等式不识别这四种量。
本地 [completeToDegreeFamily](../tmp/sheaf/xif/paper/Mzk1HTF4R6CrosswalkActual.lean#L23) 用全部坐标 `X_k` 将生成元补成同次数 `P_j X_k^(m−d_j)`，不是只用 `X₀`。
任一射影点总有某个 `X_k≠0`；[baseDiv_completion_eq](../tmp/sheaf/xif/paper/Mzk1HTF4R6CrosswalkActual.lean#L63) 因此双向识别共同零点，不引入坐标超平面上的伪零点。
这可直接用于实际边界的方程；它是点集结论，不是理想茎相等、DVR 交重数相同或逐位度量相同的结论。
[局部 λ 之和](../tmp/sheaf/xif/paper/Mzk1HTF4R6CrosswalkActual.lean#L95) 已把坐标项、生成元项、度量项分开；待填的是来自 `Eᵢ` 的逐位项及其统一界。
[IV 勘误](IUT-TEXT/IV.txt#L3172) 要 `h_E ≤ 2(deg E/deg ω)h_ω+O(1)`，不是两种高度成比例的等式。
[hE_le 的证明](../tmp/sheaf/xif/paper/Mzk1HTF4R6HeightBoundActual.lean#L30) 是用已给 `hE_eq` 和非负余项作估计；[所需字段](../tmp/sheaf/xif/paper/Mzk1HTF4R6HeightBoundActual.lean#L23) 说明真实度量的构造没有被这一步消掉。
若只供给 F6，有限映射族上一致的较粗 `κ=max κᵢ` 也够；用 `h_λ=h_ω+h_E+O(1)`、`N≤h_E+O(1)` 后移项。
[实际 ε 分配](../tmp/sheaf/xif/paper/Mzk1G1F6EtaChoiceActual.lean#L11) 取 `η=δ/[2(1+(1+δ)κ)]`，[系数不超过 `1+δ`](../tmp/sheaf/xif/paper/Mzk1G1F6EtaChoiceActual.lean#L42)，不必再证明一遍吸收。
LANA 的 `Genl` 已有[同一 Belyi 函数的 cusp 高度与 tuple 高度比较](../Genl/Curves/BelyiDescent.lean#L215)，并[将它代入所选点列](../Genl/Curves/BelyiDescent.lean#L376)。
可以逐项比对 `Eᵢ`、高度归一化和有界差，不必要求 LANA 重写一般位置定理；本地[生成元](../dag/watchdog/watchdog.log#L282433)和[条件高度界](../dag/watchdog/watchdog.log#L282679) 各有历史 DONE。

**R7 的消费者是 P8 的统一高度界，最后才是整数 ABC。** 给定 `ε>0`，令 `δ=min(1,ε/3)`，先固定 `n≥4` 使 `n/(n−3)≤1+δ`，然后固定 `d=n²`、映射族与全部常数。
现在才取任一本原 `a+b=c`。令 `uⁿ=a/c`、`vⁿ=1−a/c=b/c`；[实际生成域](../tmp/sheaf/xif/paper/Mzk1G1F7LiftActual.lean#L42) 是同一代数闭包里的 `L=ℚ(u,v)`，不是一个只知道次数够小的辅助域。
[fermatLiftL_finrank_le_sq](../tmp/sheaf/xif/paper/Mzk1G1F7LiftDegreeBasicActual.lean#L56) 分两次添加根，给出 `[L:ℚ]≤n²`；所以 R3 的次数界可以在见到三元组前确定。
F7 接着需要这一个 `L` 的 `D(L)≤log rad(abc)+C₇`。逐素数贡献是 `Σ_{w|p} f_w δ_w log p/[L:ℚ]`，不是去掉 `f_w` 后数有几个坏位。
`p∤nabc` 要在实际提升域中证明不分歧；`p∤n, p|abc` 要证明驯分歧而得到 `δ_w=e_w−1`；`p|n` 的野分歧由仅依赖 `n` 的常数支付。
可复用[不整除 n 时 n 为局部单位](../tmp/sheaf/xif/paper/Mzk1G1F7PNotDvdActual.lean#L43)及[给定局部指数界后的野贡献](../tmp/sheaf/xif/paper/Mzk1G1F7PrimeClassesActual.lean#L23)。
[逐素数界求和](../tmp/sheaf/xif/paper/Mzk1G1F7PrimeClassesActual.lean#L38) 消费 `hclass`、`hDL`，不产生它们；[次数界](../dag/watchdog/watchdog.log#L281124)和[分类求和](../dag/watchdog/watchdog.log#L282437) 均是历史 DONE。
F8 不能丢掉点 `y=[u:v:1]`。在标准射影度量中，逐坐标取 n 次幂，`n h̄_L(y)=h̄_ℚ([a:b:c])=log c`；这是要与纸面投影及 `ω_Y≃O(n−3)` 接通的锚点。
本地[投影在 chart 0 上的高度比较](../tmp/sheaf/xif/paper/Mzk1G1F8PiActual.lean#L207) 已给总高度误差 `≤ n[L:ℚ]log 2`；
[标架高度的合成](../tmp/sheaf/xif/paper/Mzk1G1F8ChainActual.lean#L26) 已出现 `n/(n−3)`。两者都针对具体坐标，接入前须除以次数并识别为 R6 所用的同一度量。
若实际投影确为 `[a:c]` 且用标准度量，本原坐标给 `h_Π=log c`，故 `C₉=0`；用别的度量则把已证的一致有界差计入 `C₉`。[交接 §6 的投影判据](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L147)。
[routeF9_of_F6_to_F8](../tmp/sheaf/xif/paper/Mzk1HT87F7F8F9InterfaceActual.lean#L122) 要求每个三元组给同组 `h_ω,D(L),h_Π`：
`h_ω≤(1+δ)D(L)+C₆`、`D(L)≤log rad(abc)+C₇`、`|h_Π−n h_ω/(n−3)|≤C₈`，以及 `log c≤h_Π+C₉`。
该 Lean 入口只量化三个实数；把它们认作同一个提升点的高度和域判别式，是调用者的几何义务，不是 `routeF9` 检查过的字段。
由 `(1+δ)²≤1+ε`，结果中的加法常数正是 `(1+ε)C₇+(1+δ)C₆+C₈+C₉`。[逐点证明](../tmp/sheaf/xif/paper/Mzk1HT87F7F8F9InterfaceActual.lean#L83)；[对数界到 ABC](../tmp/sheaf/xif/paper/Mzk1HT87F7F8F9InterfaceActual.lean#L142)。
若只证出 F8 的上界方向，可以另证同一个 `RouteF9Statement` 再用后一消费者；不应报告双向 F8 已证。[P8 接受统一产物](../tmp/sheaf/xif/paper/P8ProducerAssemblyActual.lean#L33)，并没有替每个三元组产生这些量。
**LANA 的整数出口不同。** 它用 `StatementI` 的次数一情形，在[有理点上计算判别式、导子与高度](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tripod/ClassicalAbc.lean#L226)，先证 `ClassicalABCInt`，
再用 [classicalABC_of_statementI](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tripod/ClassicalAbc.lean#L286) 取正整数形式。这里消费的是全局 `StatementI`，不是本地某个 `n` 上的 F7/F8 结构。
反过来，若已经有本地统一的 F9，不必先移植 LANA 的一般位置出口；只须用本地的对数/幂等价。两条路可核对相同的 radical 及常数约定。

### C.6 Node09：历史检查保留，但不能据此承诺能构造 cards
Node09 留下了两个不同的条件定理。其一，[final_paper312_conditional](../tmp/sheaf/xif/paper/Node09FinalConditionalActual.lean#L27) 在 `N8NativeInput`、指定 `p` 及其上方各位的 `b` 下，
用 `Node09Paper312Inputs` 产生 `ExplicitPaper312Inequality`；左项含 `qVWeight/Fdeg` 与 `1/(2ℓ)`。它不是对所有原始输入构造 paper hull 的定理。
[该文件的余项](../tmp/sheaf/xif/paper/Node09FinalConditionalActual.lean#L41) 把阶与系数比较、`logMu` 的符号、局部剩余次数、基域归一化分别列出；没有从这个逐位式到高度/区域双比较的直接箭头。
其二，[Node09ComparisonCards](../tmp/sheaf/xif/paper/Node09ComparisonCardsActual.lean#L15) 固定一个载体 `X`、hull 数据 `W` 和三元组到点的映射。
`hweightvol` 要 `a/c` 的算术权重不超过实际比较区域的体积；`hpoint` 要移位后的单点体积不超过 `(1+ε)·weight+D₁`。这是两个方向、两个集合。
[toEpsilonComparison](../tmp/sheaf/xif/paper/Node09ComparisonCardsActual.lean#L37) 将它们与单位区域、分拆、有限性及 `hval` 合用，产生固定 ε 的两条比较。
原接口第一条控制[高度相对区域体积](../LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean#L236)，第二条控制[区域体积相对权重](../LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean#L248)，后者的加法常数先于三元组。
[直接的高度消费者](../tmp/sheaf/xif/paper/Node09FinalABCBridgeActual.lean#L12) 使用固定 `D₀` 和 `D₁=Aeps ε`；[经 ABCFrontier 的版本](../tmp/sheaf/xif/paper/Node09CardsToFrontierActual.lean#L31) 允许每个正 `ε` 先选 `D₀,D₁`。
二者都从 cards 出发，不是“逐位 paper312 已经产生了 cards”。LANA 的[三步合成](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/MainTheorem.lean#L36) 则直接用其 `Cor312VariantHolds`，并不导入 Node09。
历史证据可追到 2026-11-15（UTC）：[05:00:17 逐位 conditional](../dag/watchdog/watchdog.log#L245389)、[05:09:05 高度消费者](../dag/watchdog/watchdog.log#L245442)、[05:16:23 frontier 消费者](../dag/watchdog/watchdog.log#L245489) 均为 `DONE EXIT=0`。
该次[公理探针日志](../dag/watchdog/logs/tmp_sheaf_xif_paper_Node09CardsToFrontierAxiomProbe.lean.log#L1) 对 `frontier_of_cards`、`abcConjecture_of_cards` 只列 `propext`、`Classical.choice`、`Quot.sound`；检查对象是带前提的定理。
不只缺一个实现：旧 cards 的 [hval 字段](../tmp/sheaf/xif/paper/Node09ComparisonCardsActual.lean#L19) 要求所有支集素数上 `max(0,−v_p(a/c))≤1+ε`。
例如 `1+7=8`、`ε=1`，在 `p=2` 左边是 3 而右边是 2。更一般地 `1+(2ᵏ−1)=2ᵏ` 使左边为 `k`；[no_oneAdd_valuation_bound](../tmp/estimates-rec8-h1-review-20261016/H1UniformValuationBoundCounterexampleProbe.lean#L93) 正是否定同一全称式。
所以旧族不仅未构造，而且照原量词不能构造。此反例不反驳 ABC、实际点的 `hweightvol` 或一般的区域比较，也不取消历史条件证明。
其中仍可保留不依赖 `hval` 的两段：[权重字典与拆出缩放量的等价式](../tmp/sheaf/xif/paper/Node09WeightDictionaryScalingActual.lean#L23)，以及[由加权 q 度承接区域上界](../tmp/sheaf/xif/paper/Node09PM7SNamedActual.lean#L18)。
后一段要求先证区域体积不超过加权 q 度，再证该度不超过算术权重项加常数；这两个比较不能由日志中的 `DONE` 补出。
可用的新出口是[带全局加法常数的体积消费者](../LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean#L348)；它不靠逐素数 `hval`。
但所需全局高度界[与 ABC 等强](../LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean#L167)，仍须从独立算术得到。类似地，[旧桥非空 ↔ ABC](../LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean#L605) 不能当作构造桥的捷径。

### C.7 只求整数 ABC：可以不用原 III，但不能丢掉一致性
**保留域塔，删掉两列 Θ。** [交接 §17.1](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1580) 让每个足够高的 Legendre 点选择至少一组合格数据，而不要求为每组原 III 输入作比较。
固定紧性条件 `𝒞` 和次数界 `d`，令 `h` 为全部有限位的 q 高度，`Q` 为剔除 2、ℓ 后选中的 q 高度，`B=ℚ(λ)`、`K=F(E[ℓ])`。
窗口给 `√h≤ℓ≤C_d√h·log(2C_d h)`，还要 `h−Q=o(h)`；两类误差都对给定 `d,𝒞` 的所有高点一致，不是逐点取极限。
一个足够而尚未普遍取得的估计是 `Q/6 ≤ D_K+o_{d,𝒞}(h)`。`K` 必须是这个点的扭点域，不能挑一个判别式很大的无关数域。
为什么只剩这一边？LANA 的[塔上界](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tower/Different.lean#L390) 在实际分歧事实与有限支集下已给 `D_K≤D_B+N_S+2log ℓ+21`，不调用 `h312`；
再用[入选导子不超过 tripod 导子](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tripod/LogCond.lean#L196)及 R3 的紧集高度比较，可得 `h/6≤log-diff+log-cond+ηh+C`。
给定 `ε` 先取 `6η≤ε/(1+ε)`，移项后目标高度的系数至多 `1+ε`。这要对每个固定 `d,𝒞` 做，才能接 [StatementII → StatementI](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Tripod/GeneralPosition.lean#L269)，只做一个有理紧集不够。
上界中的 `N_S` 只算支集。若 `k_v=−v(j)>0` 为入选极点深度，`ω_v=log N(v)/[B:ℚ]`，则 `Q=Σk_vω_v`、`N_S=Σω_v`。
交接用根的赋值和 different 推出下界 `D_K≥D_B+(1−1/ℓ)N_S`，与上界合看，[式 (17.3)](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1618) 精确给出尚未支付的量：
记 `P=Σ(k_v−6)₊ω_v/6`、`L₀=Σ(6−k_v)₊ω_v/6`。在此窗口，所缺的是 `(P−L₀−D_B)₊=o(h)`；若 `P≤L₀+D_B`，该子族已够用。
仅在同一窗口改选 `ℓ` 不会把有正比例的深度损失变没。对有理 Frey 点，[奇素数的 j 分母深度](../LeanFormal/IUT/ABCBridge/Arithmetic/ABCInvariantLocalValuations.lean#L228) 就是 `2v_p(abc)`，能直接定位这项余量。
若已有具体张量估计而不想走 different 捷径，[§17.1 的最高行版本](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1626) 给出另一个可比较的强度：
对 `j=(ℓ−1)/2` 的固定槽行，若有 `R_j≥−j²M/3`，现有逐行上界给出的 `Q` 系数为 `(1−(3ℓ−1)/(ℓ(ℓ+1)))/6`，损失只有 `O(Q/ℓ)`。
这不是从原 III 的全行平均推出指定行下界；给每个高点选出满足它的一行是新前提。[全行版本](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1641) 也只要求适当可选数据上负部为 `o(ℓh)`，尚无全局构造。

**连辅助数域也不留：从平方端点到全部三元组。** 取互素 `0<u<v`，考察 `u²+(v²−u²)=v²`，其乘积的 radical 等于 `rad(uv(v−u)(v+u))`。
若这些平方三元组上对每个 `η>0` 统一有 `2log v ≤ (1+η)log rad(uv(v−u)(v+u))+Cη`，给任意 `a+b=c` 取 `u=a,v=c`。
新增因子 `a+c<2c`；把其贡献移到左边，得 `(1−η)log c ≤ (1+η)log rad(abc)+Oη(1)`。
取 `η=ε/(2+ε)` 正好得到指数 `1+ε`。反向只是把 ABC 用在平方三元组上；这缩小了输入族，没有降低剩余估计的强度。[§17.2 推导](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1663)。
若希望使用椭圆曲线，受限族带指定四阶点；本地[真实 Frey 的 j 高度判据](../LeanFormal/IUT/ABCBridge/Bridge/ABCEllipticHeightCriterion.lean#L61) 和[奇导子判据](../LeanFormal/IUT/ABCBridge/Bridge/FreyOddConductorHeightCriterion.lean#L358) 都已能消费统一高度界。
前者甚至给回程常数：若 `h(j)≤6(1+ε)log rad(abc)+Bε`，则对数 ABC 常数可取 `(Bε−log(27/64))/6`。它没有证明所代入的高度上界。
Frey 的[实际 c₆ 分解](../LeanFormal/IUT/ABCBridge/Geometry/FreyWeierstrassCurve.lean#L86) 解释了 `2a+b,a+2b,b−a` 三个因子的来源；计重数的 `log|c₆|` 不是不同素数的对数和。
[§18.4 的分类](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1853) 只在“保留三尖点、至多新增一点”的二次有理换元内穷尽搜索；应结束的是寻找第四种此类换元，并非所有 Frey 路线。

### C.8 重复素幂与连分数：每组可以算完，全族仍缺一个界
这是[交接 §18 的独立路线](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1771)：不调用 R1、R2、`hCor312` 或 LANA 的变体，也不产生原 III 的 Θ。
记 `D(m)` 为 `m` 中所有指数至少二的素数的**完整素幂**之积。固定 `A=D(a), B=D(b), D=D(c)`，写 `a=Ax,b=By,c=Dz`。
本原性使余因子 `x,y,z` 平方自由、两两互素且与 `ABD` 互素。令 `P=rad(ABD)`、`R=rad(abc)`；于是 `R=Pxyz`，`c/R=D/(Pxy)`。
当 `D≤P` 时整组已有 `c≤R`。否则 `P≥2`，取 `1≤k<D` 且 `k≡−AB⁻¹ (mod D)`；余数条件是 `y≡kx (mod D)`。
所有 `c>R` 的候选都满足 `Pxy<D`。写 `t=(kx−y)/D`，则 `t/x` 既约，且 `0<k/D−t/x=y/(Dx)<1/(2x²)`。
因此 `t/x` 必是从下方逼近 `k/D` 的渐近分数；可复用的是 Mathlib 的 [Real.exists_convs_eq_rat](../.lake/packages/mathlib/Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean#L56)，而非一个“已形式化的 ABC 算法”。
对 `k/D` 做一次欧几里得算法，逐项还原 `y`、`a,b,c`，并重查互素和三项的 `D(m)`。反向筛选防止把不属于本组的渐近分数算成例外。
由于分母每两步至少翻倍，每组至多检查 `2⌈log₂D⌉+2` 个候选；对保留项的 `c/R^(1+ε)` 和 1 取最大值，就是该组最小的 `K≥1`。[完备性及停止界](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1784)。
例如 `A=1,B=125,D=128` 给 `k/D=43/128`，下方渐近分数 `0/1` 被 `Pxy<D` 筛掉，`1/3` 恢复 `3+125=128`、`R=30`。
这是此组**所有高度**中唯一的 `c>R`，故每个 `ε` 的常数是 `max(1,128/30^(1+ε))`，不是在截断样本上取出的猜测。[逐项计算](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1797)。
跨组也有正面结果：若 `uB≡vA (mod D)` 且 `u,v>0`，则 `D|ux+vy`，得 `c/R≤(u+v)/P`。
例如 `A≡B (mod D)` 且 `D>P` 时可取 `u=v=1`，整族 `c≤R`；与 `D≤P` 的平凡情形合起来，素数及深度都可变化。[跨组同余界](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1801)。
另有一类不需要任何逼近：如果重复素因子只出现在三项中的一项，便有 `c≤R`。[式 (18.1)](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1822) 还能容许两项出现受控的重复部分。
若重复素数全在**预先固定**的有限集 `S` 内，[式 (18.2)](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1828) 用含有限位的经典子空间定理给每个 `1+ε`；此处是文字推导，常数依赖 `S`，不是本地 Lean 的无条件证明。
若要由下一商得到完整 ABC，令 `h_next` 是合格下方渐近分数的下一部分商。相邻渐近分数的行列式给 `h_next≤D/(xy)<h_next+2`。
故需要在所有组上证明 `h_next≤Cε·P·c^(ε/(1+ε))`，其中**同一个** `Cε` 适用于全部通过筛选的候选；由 `c/R=D/(Pxy)` 即得指数 `1+ε`。
反之 ABC 也给此界；已知每组候选很少，不能推出其最大商跨组受控。[下一商的双向归约](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1809)。
在固定素数集的写法中，相同困难是把 `S` 的依赖显式限制为 `U_S≤Cδ·ab·c^δ·P_S^(1+δ)`；这里 `P_S` 是 `S` 中不同素数之积。
取 `S` 为 `abc` 的全支集、`δ=ε/(2+ε)`，便得所需指数；仅有逐 `S` 的子空间定理常数做不到。[式 (18.3) 的量词与移项](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1843)。
评估新估计时，可先问它是否能在无穷多个奇素数指数 `ℓ` 上给出一个 `p` 恰整除 `2^ℓ−1` 一次。
这是 ABC 的必要后果而非充分条件；固定指数的有限检查只解决该指数，不提供无穷性。[§18.5 检验](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1878)。
§17 的平方归约、§18 的有限清单、样本交叉核对以及上列跨组推导，都按[研究交接的证据等级](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1884)记录；没有把它们写成新运行过的 Lean 定理。

### C.9 对接时应当交付哪一个命题
| 对方手上现有的证据 | 最短的有用交付 | 停在哪里 |
| --- | --- | --- |
| 同一固定 III 输入的原输出及其读数 | 给 R1 所需方向的原下界，并给全部允许像的有限性；需用 IV 时再与 R2 共用同一 Θ | 一个固定输入不足以调用对所有 `D` 的 LANA 主定理 |
| 高点上的算术 C4，或 §17.1 的扭点域界 | 给出对 `d,𝒞,ε` 一致、对点不变的常数，接 R3 或现成的 `StatementII` 出口 | 允许中间量不同；没有由此回推原 III 的步骤 |
| 同一 Fermat 点上的 F6、F7 和投影比较 | 交 F9 的显式 `Cε`，再转到本地 [ABCConjecture](../LeanFormal/IUT/ABCBridge/Statement.lean#L28) | 不需要 Node09 旧 cards，也不等于两仓类型已经互转 |
| 整数组上的例外清单或固定 `S` 估计 | 交范围、停止界和常数的依赖；要称完整 ABC，交跨组下一商界 | 无法控制 `A,B,D` 或 `S` 时就按子族结题，不转报原 III |

最容易核对的终端差别是常数：LANA 的 [ClassicalABC](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Abc/Classical.lean#L38) 不单列 `C>0`，本地则要求 `K>0`。
radical 并无额外数论猜想：本地 [natRadical 的定义](../LeanFormal/IUT/Foundations/Arithmetic/Radical.lean#L17) 就是 LANA 使用的 `UniqueFactorizationMonoid.radical`；两者都对每个素因子只计一次。
从前者送往后者时可取 `K=max(1,C)`，用 radical 正性放宽常数，再按[本原三元组的定义](../LeanFormal/IUT/Foundations/Arithmetic/PrimitiveAdditive.lean#L15)对齐输入。
这项转换只解决正性和量词，不提供高度估计。选择哪一条路线，取决于能独立产生哪份输入，而不取决于哪个仓库已有 `ABC` 名字的定理。

<a id="overlap"></a>

## D. 给 LANA 的客观差分与可复现交付

2026-11-20，本附篇供双方维护者选取固定例的复核材料。先回答「哪些源码已经相同」，再回答「哪些本地材料不能只发一个提交号」。
本仓根：`D:/lean`，本地 HEAD `a997af4b1cb2339d1e7403ef0781a16f809f4476`；所读的是工作树，不是该提交的归档。
LANA 根：`D:/lana-iut-latest-20261120`，本地 HEAD `553076af459e7a401bfee63a4607814d1c854477`；本节比较磁盘文本；远端同日复核另见 §1。
下文 `路径:行` 从该列所指仓库的根起算；共用文件的同一行号适用于两边。文件数、Git 状态和形式验收是三种不同的证据。

### D.1　只比较两个磁盘上的 `Iut/`

取各自 `Iut/` 下扩展名严格为 `.lean` 的磁盘文件，含隐藏、未跟踪和被忽略的文件。键为仓库相对路径，分隔符统一为 `/`，按 ordinal 区分大小写。
不含根部 `Iut.lean`、`Iut4Sec1/`、`LeanFormal/`、`tmp/`、依赖缓存、文档或其他扩展名；不查跨路径搬移、改名、同义声明或历史来源。
共有键逐文件严格解码 UTF-8，只将 CRLF、孤立 CR 转为 LF；保留 BOM（若有）、尾随空白、最后一个换行、注释及 Unicode 码位。解码失败就停止。

| 磁盘口径 | 文件数 | 如何重算 |
|---|---:|---|
| 本仓 / LANA | 950 / 694 | 各自路径集合大小 |
| 并集 / 交集 | 950 / 694 | 交集 = 换行归一相同 + 换行归一有差 |
| 同路径，归一后相同 | 694 | 两份完整文本按 ordinal 相等 |
| 同路径，归一后有差 | 0 | 路径相同，但归一后的文本不等 |
| 仅本仓 | 256 | 在本仓集合，不在 LANA 集合 |
| 仅 LANA | 0 | 在 LANA 集合，不在本仓集合 |
| 共有文件的原字节相同 / 不同 | 0 / 694 | 不转换换行；本快照共有文件本仓用 LF，LANA 用 CRLF |

校验：本仓 `694 + 0 + 256 = 950`，LANA `694 + 0 + 0 = 694`。仅本仓的 256 个键都在 `Iut/Foundations/`。
例如 `Iut/Foundations/ContinuousH1.lean:409` 定义 `ContinuousH1`；`Iut/Foundations/SourceFiniteSheetUniversalLift.lean:34` 定义 `liftIncidenceNode`。LANA 均无此路径。
这些计数不判断谁先写、作品归属、数学新颖性或证明完成度；尤其不能把 256 当成原创数量，把 694 当成两个仓库的全部关系。

### D.2　只读复算（PowerShell 7，在同一会话依次执行）

下列命令不写文件或 Git 索引。先建路径集合；遇到重解析点即停止，不让链接把比较带出指定目录。
```powershell
$ErrorActionPreference = 'Stop'
$hereRoot = 'D:/lean'
$lanaRoot = 'D:/lana-iut-latest-20261120'
$ordinal = [StringComparer]::Ordinal
$utf8 = [Text.UTF8Encoding]::new($false,$true)
function LeanPaths([string]$root) {
  $keys = [Collections.Generic.SortedSet[string]]::new($ordinal)
  foreach ($entry in (Get-ChildItem -LiteralPath (Join-Path $root 'Iut') -Force -Recurse)) {
    if ($entry.Attributes -band [IO.FileAttributes]::ReparsePoint) { throw "reparse: $entry" }
    if ($entry.PSIsContainer -or $entry.Extension -cne '.lean') { continue }
    $rel = [IO.Path]::GetRelativePath($root,$entry.FullName).Replace('\','/')
    if (!$keys.Add($rel)) { throw "duplicate: $rel" }
  }
  return ,$keys
}
function WorkText([string]$root,[string]$rel) {
  $utf8.GetString([IO.File]::ReadAllBytes((Join-Path $root $rel)))
}
function AsLF([string]$text) { $text.Replace("`r`n","`n").Replace("`r","`n") }
$hereSet = LeanPaths $hereRoot
$lanaSet = LeanPaths $lanaRoot
$union = [Collections.Generic.SortedSet[string]]::new($hereSet,$ordinal)
$union.UnionWith($lanaSet)
$rows = foreach ($rel in $union) {
  $rawSame = $null
  if (!$lanaSet.Contains($rel)) { $kind = 'here-only' }
  elseif (!$hereSet.Contains($rel)) { $kind = 'lana-only' }
  else {
    $left = WorkText $hereRoot $rel
    $right = WorkText $lanaRoot $rel
    $rawSame = $ordinal.Equals($left,$right)
    $kind = if ($ordinal.Equals((AsLF $left),(AsLF $right))) { 'same' } else { 'different' }
  }
  [pscustomobject]@{Path=$rel; Kind=$kind; RawSame=$rawSame}
}
'here={0} lana={1} union={2}' -f $hereSet.Count,$lanaSet.Count,$union.Count
foreach ($kind in 'same','different','here-only','lana-only') {
  '{0}={1}' -f $kind,@($rows | Where-Object Kind -eq $kind).Count
}
'raw-equal={0}' -f @($rows | Where-Object RawSame -eq $true).Count
$rows | Where-Object Kind -eq 'here-only' | Group-Object { $_.Path.Split('/')[1] } | Select-Object Name,Count
```
需要差分清单时，运行 `$rows | Where-Object Kind -ne 'same' | Select-Object Path,Kind`。`RawSame` 对单方路径无值，不算作「共有有差」。

### D.3　七份交接源码，另验两份直接供体

七份来自本仓 `coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1433`；另两份的实际用途见同文件第 1907、1917 行。下表是本次重读磁盘的结果。

| 来源 | 两边相同的路径:行 | 行上的声明 | 原字节数：本仓 / LANA | LF 后 |
|---|---|---|---:|---|
| 交接 | `Iut/Concrete/ThetaRegion.lean:170` | `thetaFiniteOn` | 20650 / 21036 | 相同 |
| 交接 | `Iut/Concrete/Literal.lean:115` | `cor312Literal_of_variant` | 6693 / 6811 | 相同 |
| 交接 | `Iut/Concrete/LocalConstruct/IndAut.lean:54` | `latticeAut` | 17017 / 17343 | 相同 |
| 交接 | `Iut/WallEquiv/VcI.lean:93` | `orderVol` | 47240 / 48141 | 相同 |
| 交接 | `Iut/Wall/QPilotRegion.lean:314` | `qRegion` | 17698 / 18068 | 相同 |
| 交接 | `Iut/Wall/Ind3.lean:213` | `Ind3` | 15065 / 15358 | 相同 |
| 交接 | `Iut/Cor312/Statement.lean:89` | `Corollary312Variant` | 4511 / 4610 | 相同 |
| 另验 | `Iut/Concrete/Ind1Invariance.lean:592` | `image_thetaFiniteOn_ind1Reindex` | 35969 / 36681 | 相同 |
| 另验 | `Iut/Concrete/LocalConstruct/LogLattice.lean:361` | `exists_padicLog_eq_of_norm_le_rpow` | 23878 / 24342 | 相同 |

以下两组是**原字节 SHA-256**，不是 Git blob ID，也不是 LF 后的哈希。不同摘要与上表的文本相同并不矛盾。

| 文件 | 本仓 SHA-256 | LANA SHA-256 |
|---|---|---|
| `Iut/Concrete/ThetaRegion.lean:170` | `F7A9F18F07C0C69491BD3FBB12EC48C9C6324DC19820FDE8B0346C8E1AD797FF` | `0044CE3EB231462389147C9B70B9CE7EFD5335F83DC8526211C30820C85A3157` |
| `Iut/Concrete/LocalConstruct/LogLattice.lean:361` | `6E205A769F290EC3A7C95F60C1869299BD4BC1A8372C3E2A0C6B61602F1DA209` | `7B7AB8E188E24B8D1990D5B1D78E2712BB5D1274DDC9887033F8B2E0FCF72D56` |

```powershell
$nine = @(
  'Concrete/ThetaRegion','Concrete/Literal','Concrete/LocalConstruct/IndAut'
  'WallEquiv/VcI','Wall/QPilotRegion','Wall/Ind3','Cor312/Statement'
  'Concrete/Ind1Invariance','Concrete/LocalConstruct/LogLattice'
) | ForEach-Object { 'Iut/{0}.lean' -f $_ }
foreach ($rel in $nine) {
  $pair = $rows | Where-Object { $ordinal.Equals($_.Path,$rel) }
  foreach ($root in $hereRoot,$lanaRoot) {
    $path = Join-Path $root $rel
    '{0} {1} {2} {3} {4}' -f $root,$rel,$pair.Kind,(Get-Item -LiteralPath $path).Length,(Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash
  }
}
```
LANA 的九个路径均已跟踪，`git --no-optional-locks -C $lanaRoot diff --quiet HEAD -- $nine` 返回 0。这是 Git 意义下与该本地 HEAD 一致，不是原字节哈希一致。
区域重排与普通单位见证可引用 LANA 原声明；两者均不提供原 evaluation 到该区域的映射。本仓交接已明确这一区别：`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1965`。

### D.4　六份本地核心源码：接收方从 HEAD 能取得什么

这六份文件都在 D.1 的比较域**之外**。这里只查各自的本仓磁盘、Git 索引、HEAD 与 ignore 规则；不据此称 LANA 没有相应数学。
`␠M` 表示 porcelain 的首列是空格（索引未改）、次列是 `M`（工作树修改）；`??` 是未跟踪且未忽略；`!!` 是未跟踪且被忽略。

| 本仓相对路径:行 | 索引 / 状态 | 工作树原字节 SHA-256 | 交接时用于核对 |
|---|---|---|---|
| `LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean:41` | 已跟踪 `␠M` | `D021033FF7DB772B2DBDF01D2056A8DDB31F4F1B3E1C2D94A6E309ACCD75198F` | `OriginalInput` 的输入字段，不是 evaluation 输出 |
| `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean:379` | 未跟踪 `??` | `8171F4C6F3BBE3D08E4D5119238222D57FF519DB68FDB5BFD9B600646512A355` | 指定值层模型及假设下的无界性 |
| `tmp/sheaf/xif/paper/S3138SourceProcessionProfileActual.lean:59` | 已忽略 `!!` | `9345784E173E4B35F1B8006496A4E3374734F9306E850E8E980DCA634618FE8F` | source choices 间的标量读数相同 |
| `tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean:56` | 已忽略 `!!` | `4481D181557B7E91D012978F307928373B1AEA6E40171A9E1A658D9669A258C9` | `SourceMultiradialCarrier`；BPS 到此商的构造仍缺 |
| `tmp/sheaf/xif/paper/S1447ReportFMarkedTraceActual.lean:354` | 已忽略 `!!` | `D2D1BDD00BECB5C7ABD8C438D18A5AD1438C4C53F1DABD33562F2434D8BFA025` | 从 output/readout 投影推出比较的条件消费者 |
| `tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:124` | 已忽略 `!!` | `056BF18EC5E7B20C5F10E699404F21FC2ED9487DC129CFABC318F80CC04F1937` | 待构造的 `S2452PaperOutputFamily` 字段 |

合计：已跟踪且已修改 1，`??` 1，`!!` 4，已跟踪且干净 0。四份 `!!` 均命中本仓 `.gitignore:2` 的 `/tmp`；常规 `git diff` 不含这五份未跟踪文件。
例一：`SourceOriginalInput` 在 HEAD 和索引中的 blob 均为 `5dacc810cf3ca70c8e3f9e4755975943ef554cba`；当前工作树相对 HEAD 为增 0 行、删 6 行。只发 HEAD 得到旧正文。
例二：`SourceImageHullVolume` 和 `S2452XiFCoverageActual` 在 HEAD 里都无条目；前者可见为 `??`，后者要显式显示 ignored 才见 `!!`。两者都要单独交付。
另列、不计入六份：`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1943` 为 `??`；全文原字节 SHA-256 为 `D90A54D81ED152C66C2657D204EB49E488574A79DCCEEA25F58767DC18C2D549`。

```powershell
$paper = 'tmp/sheaf/xif/paper'
$core = @(
  'LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean'
  'LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean'
  "$paper/S3138SourceProcessionProfileActual.lean", "$paper/S3139SourceMultiradialQuotientActual.lean"
  "$paper/S1447ReportFMarkedTraceActual.lean", "$paper/S2452XiFCoverageActual.lean"
)
$handoff = 'coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md'
$auditPaths = $core + $handoff
git --no-optional-locks -C $hereRoot ls-tree -r HEAD -- $auditPaths
git --no-optional-locks -C $hereRoot ls-files --stage -- $auditPaths
git --no-optional-locks -C $hereRoot status --porcelain=v1 --untracked-files=all --ignored -- $auditPaths
git --no-optional-locks -C $hereRoot check-ignore -v -- $auditPaths
git --no-optional-locks -C $hereRoot diff --no-ext-diff --numstat HEAD -- $core
foreach ($rel in $auditPaths) { '{0} {1}' -f (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $hereRoot $rel)).Hash,$rel }
```

### D.5　工具链与 mathlib：按各自工作树的锁复原

| 仓库 | `lean-toolchain:1` 的完整值 | Mathlib `inputRev` | Mathlib 已解析 `rev` | 该仓定位 |
|---|---|---|---|---|
| 本仓 | `leanprover/lean4:v4.32.2` | `v4.32.2` | `905b95818eb32af7874a58b427f50c1711a5e96c` | `lakefile.toml:15`；`lake-manifest.json:8`、`lake-manifest.json:11` |
| LANA | `leanprover/lean4:v4.32.0` | `v4.32.0` | `81a5d257c8e410db227a6665ed08f64fea08e997` | `lakefile.toml:16`；`lake-manifest.json:158`、`lake-manifest.json:161` |

本仓 `docs/rigid-analytic-interface.md:91` 的调研写的是 `v4.32.0`；本仓 `SETUP.md:10` 与当前锁是 `v4.32.2`。前者不是复现本仓的 pin。LANA 自己的 `README.md:1061` 则与其 `v4.32.0` 相符。
文档用于解释；Lean 取 `lean-toolchain`，依赖按 `lake-manifest.json` 中 **name 为 mathlib** 的 `rev` 及整份锁复原，不猜首条记录，不用 tag 代替提交，不把缓存当作核验。
尤其本仓 `lakefile.toml` 本身为 `␠M`，原字节 SHA-256 为 `B4F4E910473F2C7D66F72AF41B3CD62E4B365000040891F664EB7E6973C0597A`；即使 mathlib pin 不变，只发 HEAD 仍会漏掉工程配置差异。

```powershell
$configPaths = 'lean-toolchain','lakefile.toml','lake-manifest.json'
foreach ($root in $hereRoot,$lanaRoot) {
  git --no-optional-locks -C $root rev-parse --verify HEAD
  git --no-optional-locks -C $root status --porcelain=v1 -- $configPaths
  $toolchain = (Get-Content -LiteralPath (Join-Path $root 'lean-toolchain') -Raw).Trim()
  $lock = Get-Content -LiteralPath (Join-Path $root 'lake-manifest.json') -Raw | ConvertFrom-Json
  $mathlib = @($lock.packages | Where-Object name -ceq 'mathlib')
  if ($mathlib.Count -ne 1) { throw "mathlib entry count: $root" }
  '{0} {1} {2} {3}' -f $root,$toolchain,$mathlib[0].inputRev,$mathlib[0].rev
  foreach ($rel in $configPaths) { '{0} {1}' -f (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $root $rel)).Hash,$rel }
}
```

### D.6　交给维护者的最小包：先能复读，再谈构建

1. 在 `TARGET.md` 固定 `p=3, ℓ=5, d=3`，源 `(B,B,G)`、目标 `(G,B,B)`、`τ=(2,0)`。请对方审的是原 III.3.10.2 的映射及 `E_τ(1) ∈ U_{2,3}`，不是重做九份供体，也不是声称已证全称命题。依据：本仓 `coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1943`；LANA 的接收字段是 `Iut/Cor312/RightHandSide.lean:88`。
2. 在 `SNAPSHOT.tsv` 逐件写明仓库、基准提交、相对路径、声明/行、Git 状态、字节数、原字节 SHA-256、来源与改动。LANA 的九份只给该提交的路径和声明；本仓六份及交接正文按原字节给出。归一指纹只用于比对，不用作收件校验。
3. 本仓单独附工作树版本的 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json`；LANA 环境保留自己的三件套。明确接收方能否取得两个基准提交；若本仓基准不可取得，就附所需源文件，不让私有本机路径变成隐含依赖。
4. 若承诺的是**可构建包**，从实际入口逐层追 import，只补基准提交和依赖锁不能提供的源码，保留模块路径。例如 `tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean:1` 还引 `S3138SourceStepXIActual`，`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:2` 还引 `S2362MainlineReadoutActual`。六份是审阅入口，不是已验证的依赖闭包。
5. 接收方在隔离目录按清单逐件验原字节与行锚；不符先报告路径、预期值和实得值。不同平台的检出换行可以作 D.2 文本复核，但不能伪报字节校验通过。不发 `.olean`、`.lake/`、整棵 `tmp/`，不混用两仓环境。
6. 署名逐文件：九份共同源码头第 2–4 行均注明 LANA Project 与 Apache 2.0（例：`Iut/Concrete/ThetaRegion.lean:2`、`Iut/Concrete/LocalConstruct/LogLattice.lean:2`）。引用写 `lana-agents/iut@553076af…`、路径和声明；若随包带源码，保留原文件头、许可证及适用的 NOTICE，标清实际修改者与改动。
7. 本地接口、条件证明、反例和固定例分析分列；仅按文件头、提交记录或贡献者确认署名，未确认则标「来源待核」。双方 `LICENSE:2` 均标 Apache 2.0；分发说明各见本仓 `LICENSE:81`、LANA `LICENSE:89`。不由相同文本或单方路径推断权属，不替未来合并、许可或接收作保证。

本次仅核对磁盘、Git 状态和依赖锁，未移植、未打包、未编译。此固定例的 `statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 各为 `NOT_RUN`；与本仓 `coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1972` 分项口径相同。

<a id="source-contract"></a>

## E. 来源侧第一批可并入的文件：一次求值究竟能带走什么

固定一个问题：同一组初始 Θ 数据、同一次 III.3.10.2 求值，能否把有标记的源张量点送进原允许区域？
原文要求的是**能解释为 prime-strip 的区域族**，不是存在某个同值实数（[III.txt:10416](IUT-TEXT/III.txt#L10416)）。
LANA 端接收的是逐 capsule 的 `RHSData.thetaPilot`，还另要 `thetaPilot_hullAdmissible`；二者都不是产生区域的算法（[RightHandSide.lean:84](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Cor312/RightHandSide.lean#L84)）。
本批建议先并入可单独复用的单位商、箭头合成和张量投影；两套输入记录用于比对字段，特化方块用于核对方向，旧输出记录只作缺口对照。
证据取自 2026-11-20 工作树。入口是[总索引:24](LEAN-INDEX.md#L24)和[交接 §19.3:1941](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1941)；下文的「已写出」指能定位定义或证明体，不指已跨仓构建。

### E.1　I：给定的是哪组数据，哪些字段确实能送到剧场
原文元组列出 `ℓ`；Lean 把它放在 `SourceNativeInitialThetaData (l : PrimeGeFive)` 的外层参数，不要在六项 tuple 内再找一个可以单独改变的 `l`（[Quantifiers:1681](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1681)）。
原 I.3.1 的量词是「满足条件的这组数据」（[I.txt:3125](IUT-TEXT/I.txt#L3125)）；坏位是指定集合，不保证其补集处处都是几何好约化（[I.txt:3144](IUT-TEXT/I.txt#L3144)）。
`SourceDefinition31Quantifiers.lean` 固定 `ℓ : PrimeGeFive` 和算术根 `A`。`SourceInitialThetaTuple A` 的六项是 `fbar, xF, cK, V, V_mod_bad, epsilon`。
`fbar` 是带 `F`-代数比较的扩张，不是代数闭包中的一个点；其余几项有与辅助 `source` 一致的等式，尖点的等式还沿 `cK` 的等式运输。
这不是读者须重造的同一性：`complete_source_recovery` 已把这些比较一起取出（[Quantifiers:1612](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1612)、[同文件:1668](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1668)）。
例如 `xF_geometry` 的类型以曲线和 `xF` 为参数，但 `SourceOncePuncturedGeometry` 本身只存 signature 等式；从这个字段不能读出给定两曲线之间的同构（[Quantifiers:368](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L368)、[同文件:580](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L580)）。

| 在同一个 `A, tuple.source` 上取字段 | 实际输入或可取出的对象；不应改写成什么 |
|---|---|
| 域模与曲线 | `jModuli : A.Fmod` 满足 `algebraMap A.Fmod A.F jModuli = A.curve.jInvariant`；这是下降值，不是不同局部域内 q 元素相等（[Quantifiers:405](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L405)）。 |
| (a) | 对 `F` 的每个有限位给稳定约化；最大可解中间域带性质及「包含每个合格中间域」的量词（[Quantifiers:889](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L889)）。 |
| (b) | 对每个限制到 `V_mod_bad` 的 **`F`-位**，有乘法约化、一个非空 Tate 见证及剩余特征与 ℓ 互素；见证带该位的 `FinitePlaceQCandidate`、曲线比较、`order_coprime`（[Quantifiers:952](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L952)）。 |
| (c) | 供给 2·3 扭点有理性、实际 ℓ 扭点的秩二基、表示与典范矩阵表示的等式、像含 `SL₂`，以及 `K` 到扭点核域的 `F`-代数同构（[Quantifiers:1007](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1007)）。 |
| (d) | `K` 上的符号商有商见证；有限 étale 覆盖的映射等于该商映射；另有 `x,c` 两条基本群序列向 `F` 侧的嵌入（[Quantifiers:1106](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1106)）。 |
| (e) | `V` 是 `K` 的位的子集；与 `Fmod` 的全体位等价，对每个选中位按有限／无限分别给局部对象。`comap` 与该等价的逆相合（[Quantifiers:617](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L617)、[同文件:1438](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1438)）。 |
| (f) | `boundary_origin` 的秩一商使用 (c) 所给出的 `K` 侧基；其 cusp 等于 `S.epsilon`，分解群所用的 cusp 也要等于它（[Quantifiers:1553](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1553)）。 |

`SourceNativeInitialThetaPredicate A T` 依次存在量化 (a) 到 (f) 的见证，后项的类型依赖前项；末尾自反等式并不提供这些见证（[Quantifiers:1708](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1708)）。
`sourceNativeInitialThetaExists_iff_packaged` 只把该存在式与非空数据包互换；`∀ A, ∃ T, T.arithmetic = A` 是另外定义的 gate，不是此等价的结论（[Quantifiers:1746](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1746)、[同文件:1772](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1772)）。
`SourceDefinition31Boundary.lean` 则是 III 真正读取的合同 `SourceDefinition31Data`，不是上述六元组的另一个名字（[Boundary:667](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L667)）。
它存 `arithmetic, selectedPlaces, badPlaces, reduction, torsion, orbicurve, sections, cusp`，以及五组「compatibility 命题及其证明」；字段名本身不识别算术对象。
`badIncluded : Bad → Selected` 附有坏位有限性、自然数标签相容性；`qParameter : Bad → ℝ` 非零且范数小于 1，不是 (b) 的完备域元素（[Boundary:39](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L39)、[同文件:101](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L101)）。
`q_log_abs_negative` 因此可直接证明这个实参数的对数为负，却不能从中恢复一个 Tate 参数或选定完备化（[Boundary:1519](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L1519)）。
同样，`splitMultiplicativeReduction` 的默认值就是 `multiplicativeReduction`。在未识别给定谓词前，投影其证明不能作为局部 Tate 模型已分裂的证明（[Boundary:89](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L89)）。
扭点字段是给定群间的满同态，`imageContainsSL2` 是另附证明的 `Prop`；不是 (c) 的典范 `GL₂` 表示满射（[Boundary:210](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L210)）。
覆盖合同带短正合条件及截面，局部群合同带逐位双射，`cusp.epsilon : ℝ` 为正；它不等于六元组的几何边界尖点（[Boundary:328](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L328)、[同文件:521](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L521)、[同文件:612](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L612)）。
一个真能移植的局部桥是 `NativeContractPartitionFragment.ofNative`：在原位子类型上，用 `V_mod_bijection` 将坏位送进选中位，`ofNative_badIncluded_injective` 给出单射（[NativeContractBridgeReduction:151](../LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean#L151)、[同文件:166](../LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean#L166)）。
它未装配整个 partition。反向看，`toInitialThetaInput` 是从已有 Boundary 投影出算术、位、约化、扭点像和实 cusp 参数，不是从弱输入还原原几何（[Boundary:831](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean#L831)）。
因此先固定 `I : OriginalInput ℓ V`：`initial` 指这份 Boundary，`family` 有 `index ≃ ℤ × ℤ`，每个剧场的算术都等于 `initial.arithmetic`（[SourceOriginalInput.lean:39](../LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean#L39)）。
此时可以用相同 `(n,m)` 取 `theaterAt`、用同一族取 `linkAt`；四个输入字段没有一个是求值结果（[SourceOriginalInput.lean:53](../LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean#L53)）。

### E.2　II：先移植能在单位上检验的求值，不预设全条带同构
这里有两个不同的目标群：单位求值可以先映到整个代数闭包的单位群，也可以把目标限制到它的算术像。两种陈述的满射性不同。
原 II.4.9(i) 在普遍覆盖 pro-object 上求值，再取单位、除以扭元，比较的是带作用的模的 `Ism` 轨道（[II.txt:10042](IUT-TEXT/II.txt#L10042)、[同文:10062](IUT-TEXT/II.txt#L10062)）。
到 II.4.10(ii) 才由 II.4.6(iv),(v) 的求值给出 **`F_env → F_gau`** 同构；这说明 III 方块的下排第一箭应匹配谁（[II.txt:10410](IUT-TEXT/II.txt#L10410)、[III.txt:9123](IUT-TEXT/III.txt#L9123)）。
`TimesMuQuotient U = U ⧸ torsion U` 的投影满且核恰为扭子群；`G →* MulAut U` 下降为商上的作用，并与投影交换（[TimesMuQuotient.lean:24](../LeanFormal/IUT/IUTII/Kummer/TimesMuQuotient.lean#L24)、[同文件:75](../LeanFormal/IUT/IUTII/Kummer/TimesMuQuotient.lean#L75)）。
给开子群 `H ≤ G`，`invariantImage` 是 **先取** `U` 的 `H`-不动单位，**再映到**商；成员要有实际不动代表，而非只知商类不动（[TimesMuIsm.lean:45](../LeanFormal/IUT/IUTII/Kummer/TimesMuIsm.lean#L45)）。
`TimesMuKummer.Isomorphism ρ σ` 要求商群同构、`G`-等变及每个 `H` 的不变像的像等式；`orbitOf_eq` 比较同一对作用上的两个给定同构，不构造它们（[TimesMuIsm.lean:156](../LeanFormal/IUT/IUTII/Kummer/TimesMuIsm.lean#L156)、[同文件:273](../LeanFormal/IUT/IUTII/Kummer/TimesMuIsm.lean#L273)）。
`IsKummerIsometry` 的判据也是与作用交换、逐 `H` 保持该像；它并没有一条「保持某个张量范数」的字段（[TimesMuIsm.lean:68](../LeanFormal/IUT/IUTII/Kummer/TimesMuIsm.lean#L68)）。

**正例：固定任一素数 `p`，不借用 III 的任何方块。**
`timesMuUnitEvaluation` 把非零整闭包幺半群的单位模扭，送往 `ℚ_p` 的代数闭包的单位模扭；在单位代表上等于先求值再取商（[LocalTimesMuEvaluation.lean:21](../LeanFormal/IUT/IUTII/Frobenioid/LocalTimesMuEvaluation.lean#L21)）。
该同态有局部绝对 Galois 等变性及单射性；此处余域是整个闭包单位商，并未证明对它满射（[LocalTimesMuEvaluation.lean:37](../LeanFormal/IUT/IUTII/Frobenioid/LocalTimesMuEvaluation.lean#L37)、[同文件:51](../LeanFormal/IUT/IUTII/Frobenioid/LocalTimesMuEvaluation.lean#L51)）。
要用同构，可把目标精确取为 `evaluatedUnitSubgroup p`：元素和逆元都在基赋值整数环上整。`unitEvaluationEquiv` 对**这个像**为双射（[LocalIntegralUnitEvaluationImage.lean:30](../LeanFormal/IUT/IUTII/Frobenioid/LocalIntegralUnitEvaluationImage.lean#L30)、[同文件:140](../LeanFormal/IUT/IUTII/Frobenioid/LocalIntegralUnitEvaluationImage.lean#L140)）。
同一次单位求值给 `timesMuEvaluationComparison p`：商上的映射来自上述同构，等变性和不变像的双向包含均有证明体（[LocalIntegralUnitEvaluationImage.lean:181](../LeanFormal/IUT/IUTII/Frobenioid/LocalIntegralUnitEvaluationImage.lean#L181)、[同文件:198](../LeanFormal/IUT/IUTII/Frobenioid/LocalIntegralUnitEvaluationImage.lean#L198)）。
这可供 III 核对一个纤维的 Kummer 层；仍须识别 `G` 与两端单位纤维。一个 `p` 的局部同构不产生全局 Frobenioid 的 `env → gau`，也不产生张量区域。

### E.3　III：同一横箭头的两条走法，先看端点再取逆
以下先选一条 `F`-层代表；原文的三个上横箭在这种写法里未拆出全部中间顶点。要保留它们，须用 E.4 的图（[Arrows:47](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L47)、[同文件:65](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L65)）。
在 `SourceKummerEvaluationArrows.lean`，令 `G` 为共用的拓扑群，`A,B : FPrimeStrip V`。每个 `v` 的 `sourceAction, targetAction` 作用在两端 `Mon v` 的单位群上。
竖箭 `SourceKummerArrow G A B` 带 `stripIso : A ≃ B`（条带同构）和逐位 `SourceTimesMuKummerLayer`；后者给出 `invariantImage_law` 与 `kummer_orbit_unique`（[Arrows:130](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L130)、[同文件:161](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L161)、[同文件:200](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L200)）。
横箭 `SourceEvaluationArrow G A B` 带一个条带代表，以及 `A → B` 方向的等变单位商同构；`unitPortion` 不要求开子群不变像律（[Arrows:249](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L249)、[同文件:290](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L290)）。
两条数据在这个 reduced 记录中没有「来自同一操作」的相干等式；`sourceEvaluationArrow_self` 用恒等和自明作用，只检验接口可满足（[Arrows:70](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L70)、[同文件:318](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L318)）。
记 `u: UL → UR`、`b: LL → LR`，竖箭是 **`kL: LL → UL`、`kR: LR → UR`**。以下 `;` 表示先左后右（[Arrows:347](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L347)）。
方块的字段是 `kL⁻¹ ; b = u ; kR⁻¹`，两边从 `UL` 到 `LR`；等价地，从 `LL` 出发的下横条带代表为 `kL ; u ; kR⁻¹`。
`domainExpression_eq_codomainExpression` 直接取该字段，是两条复合相等，不是两个剧场的算术全纯结构相等（[Arrows:372](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L372)、[同文件:385](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L385)）。
可复用的构造 `ofThreeArrows` 给定上横及两竖，用条带共轭补出下横及其单位层；若改用两侧的 **Kummer 单位层** 共轭，则 `ofKummerLayerConjugation` 显式要求两处衔接作用相等（[Conjugation:190](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceEvaluationUnitPortionConjugation.lean#L190)、[同文件:122](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceEvaluationUnitPortionConjugation.lean#L122)）。
`SourceLinkFactorization` 另把 IPL 路径写为 `intermediate → gau → env → coricEnv → qPilot`；头两步是下横取逆，末步打包上排三箭（[Arrows:418](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L418)）。
其 `inputLink = composite` 是合同内所给的等式，不是从 `I` 计算 evaluation；`sourceQPilotStrip` 也只取 `input.theater.primeStrip`（[Arrows:454](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L454)、[同文件:489](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L489)）。
逐列接口 `SourceVerticalKummerCard G I n` 要为**每个整数 `m`**给 `(n,m) → (n,0)` 的 Kummer 箭；它既未把箭定义为族的 link，也不包含 Ind3 的上半连续性（[Arrows:470](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L470)）。

### E.4　III：`F×μ` 代表、商类和八顶点图，哪些合成不必重写

`SourceFTimesMuPrimeStripPolyIsomorphism.lean` 给每个 `v` 真正指定一个交换群 `timesMu v`，并非给 `FPrimeStrip` 换个名字。
从条带单位群**向**这个群有满同态，核恰为有限阶单位；`Π_v` 的作用下降，实化 degree 则从商映向 `Multiplicative ℝ`（[FTimesMu:164](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L164)）。
`timesMuQuotientMap_eq_one_iff` 把核条件变成逐元素判据。`canonical F` 取各纤维为单位模扭，作用和 degree 都沿同一投影下降（[FTimesMu:189](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L189)、[同文件:236](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L236)）。
代表 `φ : S ≃ T` 有条带层 `toF` 和纤维层 `isoTimesMu`；这次 `compatQuotientMap` 真正要求先商后映与先映后商相同，另有 `compatAction`、`compatDegree`（[FTimesMu:256](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L256)）。
所以若 `e : FPrimeStripEquiv F F'` 已定，不必另选单位映射：`canonicalLift e : canonical F ≃ canonical F'` 在 `v` 取 `congr (Units.mapEquiv (e.isoMon v))`（[FTimesMu:343](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L343)）。
商前的关系 `NaturallyIsomorphic` 要求 `toF` 相等且 `isoTimesMu` 逐位相等；`FullPolyIsomorphism` 是按此关系的商，不是所有可能输出区域的集合（[FTimesMu:387](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L387)、[同文件:577](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L577)）。
`representative_exists` 可以从**已有商类**取代表；结合 `comp_assoc, comp_symm, symm_comp` 可无关括号地合成、消去逆元，不能凭空产生一条算法箭头（[FTimesMu:627](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L627)、[同文件:651](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L651)）。
`canonical_trans` 进一步保证「两条 `F` 代表分别提升再复合」等于「先复合再提升」的商类；这才是把条带层的路径等式送上去所用的定理（[FTimesMu:675](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L675)）。

区分同文件的两个图，再与 E.3 对照：
| 类型 | 横竖箭的读法 | 已给数据能做什么 |
|---|---|---|
| `…PolyIsomorphismSquare` | 横向左→右，**竖向上→下**；`left ; lower = upper ; right`。 | 给上横、两竖和指定逆及消去律，`ofUpperHorizontal` 取下横 `left⁻¹ ; upper ; right`（[FTimesMu:717](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L717)、[同文件:739](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L739)）。 |
| `…Rem3102Diagram` | 两排都是 `env → gau → LGP → lgp`；四条 Kummer 竖箭反而是**下→上**。 | 三个格各有 `lower ; verticalRight = verticalLeft ; upper`；这是六条横箭、四条竖箭及其相容性的合同（[FTimesMu:805](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L805)、[同文件:829](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L829)）。 |

这解释了两个方块的共轭公式为何外观相反：若同名顶点要对接，先对竖边取逆，并比较代表和商类，不能直接把一个 `commutes` 赋给另一个。
对于给定的八顶点图 `D`，`iplLink D` 的起点是 `bottomLGP`，终点是 `topLgp`，并非从下排的 `env` 出发。
按执行次序，它是 `lowerGau⁻¹ ; lowerEnv⁻¹ ; verticalEnv ; upperEnv ; upperGau ; upperLGP`（[FTimesMu:845](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L845)）。
前两个交换格分别允许消去一次回程，`iplLink_eq_verticalLGP_upperLGP` 将这六步化为 `verticalLGP ; upperLGP`，不是新加的等式字段（[FTimesMu:856](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L856)、[同文件:893](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L893)）。
另有两个有输入的方块构造，不只是一张空图：
- `processionInclusionSquare I P n i j` 把 `P.stage n` 的两标签送进下一 stage；横边是同层 link，竖边是包含态射在两个标签上的分量（[FTimesMu:982](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L982)）。
- `logThetaLatticeSquare I n m` 抬升 `n,n+1` 与 `m,m+1` 的四条 `fLinkAt`；两条复合相同由该族的 `fLinkAt_trans` 得到（[FTimesMu:1034](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L1034)、[同文件:1057](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L1057)）。
这两个方块的输入分别是 procession 和剧场格，不是操作的运行记录；文件明确把「由原算法操作产生」留在合同之外（[FTimesMu:799](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L799)）。
原 III.3.11.1 还给最后求值附上符号、乘积公式和直积区域逆系统的条件，不能只核对六步的路径顺序（[III.txt:9703](IUT-TEXT/III.txt#L9703)、[同文:9713](IUT-TEXT/III.txt#L9713)）。

### E.5　S1951：只取一个 `D`，三条边确实拼成哪一条边
分界恰在 `General` 之后：`v : V` 和作用群在[第 61 行](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L61)仍是变量；到[第 201 行](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L201)才固定位置类型。
`S1951KummerEvaluationSquareActual.lean` 的通用部分可以先拆出来复用，不必把特化输入搬进 LANA。
给条带同构 `φ : A → B` 和逐位作用因子 `f_v : G →* Π_A(v)`，`factorLowerOfEquiv` 取 `φ.isoPi(v) ∘ f_v`；两端因而用的是同一 `G`（[S1951:82](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L82)）。
`xMuQuotientEquiv φ v` 用 `φ.isoMon` 诱导的单位同构降到扭商；`kummerIsoOfFactors` 证明其等变并将每个开子群的不变像映满（[S1951:76](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L76)、[同文件:91](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L91)）。
`layerOfFactors` 保留 Kummer 层；`unitPortionOfFactors` 用 `ofKummerLayer` 忘掉较强的条件，底下的单位商映射不变（[S1951:179](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L179)、[Conjugation:109](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceEvaluationUnitPortionConjugation.lean#L109)）。
这正好与 `canonicalLift φ` 的代表公式相比较：在同一个单位 `a` 上，两者都把 `[a]` 送到 `[Units.mapEquiv (φ.isoMon v) a]`。
此逐代表公式可由两侧的商映射计算律核对（[S1951:70](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L70)、[FTimesMu:136](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L136)）；不是二者已共同识别了原文的 Frobenioid 顶点。

特化时，给 `D : S1895PaperInput`，令 `I = paperInput D`。这里的 `D` 要带 `S1280RemainingClauses D.l` 及五组相容命题和证明（[S1895:104](../tmp/sheaf/xif/paper/S1895OIdentificationsActual.lean#L104)）。
四个角各是**同一** `I.fPrimeStripAt` 的值（[S1951:204](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L204)）：
| 上左 `env` | 上右 `gau` | 下左 `LGP` | 下右 `lgp` |
|---|---|---|---|
| `(0,0)` | `(0,1)` | `(1,0)`，代码名 `lgpStrip` | `(1,1)`，代码名 `lgpLowerStrip` |

共同群取 `(1,0)` 核心条带的 `Π` 的积；`factorLGP` 是第 `v` 坐标投影，其余三个因子用该源的 `fLinkAt.isoPi` 从这里运输（[S1895:132](../tmp/sheaf/xif/paper/S1895OIdentificationsActual.lean#L132)、[S1951:228](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L228)、[同文件:259](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L259)）。
`upperEvaluation` 是 `env → gau`；`leftKummer` 是 `LGP → env`；`rightKummer` 是 `lgp → gau`，三者分别使用起点的作用因子（[S1951:279](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L279)）。
`lowerUnitPortion` 由 `LGP → lgp` 的实际 link 和 `factorLGP` 构造；这里没有假设一个未知的下横单位同构（[S1951:298](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L298)）。
`kummerEvaluationSquare` 调用的是 `ofThreeLegs`：上横、两竖、这份下横**单位部分**，共四个参数；下横的 **strip 代表** 才由三条边强制给出（[S1951:305](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L305)）。
`lowerHorizontal_stripIso` 展开 `LGP → env → gau → lgp`，以 `fLinkAt_symm` 和两次 `fLinkAt_trans` 得到精确的 `I.fLinkAt 1 0 1 1`（[S1951:313](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L313)、[同文件:243](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L243)）。
因此在这个 `D` 上，可对这个**已知代表等式**两边取 `canonicalLift` 的商类并使用 `canonical_trans`。所得仍是 `canonical LGP → canonical lgp`，没有任何 `Set (Tensor …)` 出现在余域。
于是有 `kummerEvaluationSquare_twoPath`。实际消费者 `s1927Square D` 的 `square` 就是这个构造，不需要再给一遍方块（[S1951:325](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L325)、[同文件:359](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L359)）。
但 `fullLogKummerUQ D h` 仍需 `h : S1927FirstMissing D`；源文件也不把这四角、这些 link 或所用的积群拓扑认作论文的对应对象（[S1951:32](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L32)、[同文件:395](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L395)、[同文件:406](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L406)）。

**`2/7` 与 `3/5` 不是两次给同一对变量赋值。**
`PaperV := FinitePrimePlace 2 7`；类型展开为 `{p : ℕ // 2 ≤ p ∧ p ≤ 7 ∧ Nat.Prime p}`，即区间里的有理素数（[S1951:201](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L201)、[LocalPrimePlaces.lean:21](../LeanFormal/IUT/IUTI/HodgeTheater/LocalPrimePlaces.lean#L21)、[PrimeIntervals.lean:14](../LeanFormal/IUT/Foundations/Arithmetic/PrimeIntervals.lean#L14)）。
`ℓ` 则是 `D.l : PrimeGeFive`，并未由 `7` 指定；`S1895PaperInput.I D` 的**位索引**才特化为上述区间（[S1895:121](../tmp/sheaf/xif/paper/S1895OIdentificationsActual.lean#L121)）。
即使取到该区间的素数 `3` 并另给 `D.l = 5`，也没有选出 `Fmod` 在 `3` 上方的 `G/B` 两个位、它们的 `K`-提升或深度 `d=3` 的张量。
把两个端点改写成 `FinitePrimePlace 3 5` 也只会得到另一个素数区间；本例需要的却是固定有理素数 `3` 上方的数域位纤维。
诊断例中的 `3` 是剩余素数、`5` 是扭阶素数；第二行有三个**槽**，不是有理素数区间的三个条目（[交接:1541](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1541)、[ThetaRegion.lean:170](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/ThetaRegion.lean#L170)）。
故可移植的是对任意 `V,G,φ` 的因子构造和共轭计算。特化的 `s1927Square D` 是有条件的实例，不是 `(p,ℓ,d)=(3,5,3)` 的区域求值。

### E.6　静态张量侧：区域有具体成员判据，但成员不是求值履历
这部分要区分三种操作：在同一张量空间重排因子，从整包投影到一个块，以及在条带的单位商上沿列比较；只有第二种改变成元组块。
`OrigXiFIndeterminaciesActual.lean` 的张量部分从已给的 `C3 : SourcePilotRegionData I` 和逐因子的有限位指标出发（[OrigXiF:95](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L95)）。
在行 `j` 上，索引是 `(i,t) : Fin (j+1) × C3.tensorIndex`；该坐标的位族只依赖 `t`，所以换 `i` 不改变对应完备化族（[OrigXiF:103](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L103)）。
载体是在 `ℚ_[C3.p]` 上取所有 `CompletionPacket` 的张量积；`OrigXiFPaperOutputRegion` **定义为** `arithmeticTensorLogRegion`，并不是所有 evaluation 值的 `Set.range`（[OrigXiF:119](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L119)）。
`OrigXiFPaperOutputRegion_mem_iff` 给出可操作的检验：找一族 `a(i,t)`，每项在对应 `completionPacketLogRegion`，且待测 `z` 恰是这一族的纯张量（[OrigXiF:152](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L152)）。
不要把此集合扩大为纯张量的所有线性组合；另一个定义 `arithmeticIQCarrier` 才取 `ℚ`-线性张成（[FinitePlaceArithmeticIQTensor.lean:32](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticIQTensor.lean#L32)）。

- **Ind1。** 对任意 `σ : Equiv.Perm (Fin (j+1))`，线性自同构重排 `(i,t) ↦ (σ i,t)`；作用于纯张量后，第 `(i,t)` 因子是原来的 `a(σ⁻¹ i,t)`（[OrigXiF:170](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L170)、[同文件:204](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L204)）。
  `OrigXiFInd1Equiv_region_fixed` 逐因子代入 `σ⁻¹` 证正向、代入 `σ` 证反向，结论是**整集合的像相等**，不是每个点不动（[OrigXiF:242](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L242)）。
- **Ind2。** 每一 `(i,t)` 的每个局部坐标有独立的 `u : ℚ_[p]ˣ`，要求 `‖u‖ = 1`；以标量乘法作用于该坐标，因子及逆都保持局部 log-shell（[OrigXiF:301](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L301)、[同文件:350](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L350)）。
  `OrigXiFInd2Equiv_region_fixed` 同样是指定张量区域的集合等式，不是任意 completion 自同构或任意原 Ism 都允许（[OrigXiF:443](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L443)）。
- **静态读数。** 两个 `…Equiv_logVolume` 对任意给定测度 `μ` 成立：证明把像集改写回同一个集合，不需要 `μ` 本身对所有变换不变（[OrigXiF:285](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L285)、[同文件:485](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L485)）。
  `haarLogVolume μ S : ENNReal` 在质量为 `⊤` 时仍为 `⊤`，有限时取 `ENNReal.ofReal (Real.log (μ S).toReal)`；它不能直接当作保留负号的 RHS 实数（[FinitePlaceIQHullInterface.lean:51](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullInterface.lean#L51)）。
- **Ind3 换了载体。** 固定 `I,v`，`(1,m)` 的单位模扭沿 `I.fLinkAt 1 m 1 0` 去 `(1,0)`；`…StageComparison_logVolume` 保的是 `timesMuDegreeOfUnits`，`…StageComparison_action` 则用同一 link 的 `isoPi` 运输作用（[OrigXiF:512](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L512)、[同文件:525](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L525)、[同文件:542](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L542)）。
  这里 `OrigXiFLogKummerRegion = Set.univ`；自同构把全体映满，不等于原允许输出族在竖直迭代下的上半连续体积比较（[OrigXiF:562](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L562)、[同文件:66](../tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean#L66)）。

**可以脱离旧 C3 拿走的定理**：直接给数域、素数、有限因子及相应的有限位族 `places`，以下证明不需要 Kummer 根系。
`isCompact_arithmeticTensorLogRegion` 给这一静态集合的紧性；`one_mem_arithmeticTensorLogRegion` 用各因子的 `1` 作纯张量见证（[FinitePlaceArithmeticIQTensor.lean:39](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticIQTensor.lean#L39)）。
`arithmeticTensorTupleProjection places tuple` 是从整包到指定位置元组块的 `ℚ_p`-线性映射，在纯张量上逐项取 `a i (tuple i)`；其连续性也已写出（[FinitePlaceArithmeticTensorBlocks.lean:46](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean#L46)）。
`arithmeticTensorTupleProjection_image_logRegion` 更给出投影像**等于**该块的 log-shell 区域。反向包含是在各指定坐标放入原元素，其余坐标补零（[FinitePlaceArithmeticTensorBlocks.lean:74](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean#L74)）。
`finrank_arithmeticTensorTupleBlock` 给该块的 `ℚ_p`-秩为所选局部完备域秩的乘积，可在识别同一块后核对体积归一化的分母（[FinitePlaceArithmeticTensorBlocks.lean:97](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean#L97)）。
这解决「已在整包里，怎样投到元组块」，没有解决「原 evaluation 怎样进入整包」。在固定标签行使用时，投影的指标也必须是本行实际选择的位族。

### E.7　旧输出尝试：构造器确实做了什么，`sorry` 在哪里
此处的 `SourceAllowedOutput` 专指 `P6Comparison` 的记录。它的类型不要求原 III 的算法选择，也没有把 `Q ≤ Θ` 藏进字段（[P6Comparison.lean:61](../tmp/sheaf/n8/closure/P6Comparison.lean#L61)）。
`SourceAllowedOutputActualAttempt.lean` 的起点不是一个任意 `OriginalInput`，而是 `X : N8NativeInput ℓ`。固定 `X` 再看数据怎样依赖彼此（[Attempt:48](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L48)）。
`actualBridge` 由 `donors : P6BridgeDonors X` 推出；donors 含该算术根上的 `inputDonors`，还含专属于其生成输入的 `bindingDonors`（[P6Bridge.lean:52](../tmp/sheaf/n8/closure/P6Bridge.lean#L52)、[Attempt:51](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L51)）。
其中一部分已有来源：`nativeC1ActualParts X` 的选中位属于 `V`，其 `comap` 正是这个 `X` 的 `badBasePlace`。这既不是任意选位，也还不是整组 donors（[C1BridgeProof.lean:59](../tmp/sheaf/n8/closure/C1BridgeProof.lean#L59)）。
令 `b = actualBridge donors`。`SourceAllowedActualData X` 在 `b` 上还要以下数据（[Attempt:57](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L57)）：
| 字段 | 它钉在哪个载体上 |
|---|---|
| `C2` | `SourceLogKummerData b.input b.binding`；有限位的 shell 和整单位对数核分别与指定 shell、扭子群比较（[SourceLogKummerRealization.lean:51](../tmp/sheaf/n8/closure/SourceLogKummerRealization.lean#L51)）。 |
| `C3` | `SourcePilotRegionData b.input`；固定 `p` 及 `Fmod` 上该特征的位，存完备域 q、有限 theta packet、根系和一组张量因子（[SourcePilotRegion.lean:59](../tmp/sheaf/n8/closure/SourcePilotRegion.lean#L59)）。 |
| `D`（C4） | `SourceWitnessedOutputData b.input (PaperLabel ℓ)`；给定 `v`、`SourceImageRealization v`、pilot 指标和作用，状态／输出是 `ThetaPilotPoint v`（[SourceWitnessedOutput.lean:60](../tmp/sheaf/n8/closure/SourceWitnessedOutput.lean#L60)、[同文件:90](../tmp/sheaf/n8/closure/SourceWitnessedOutput.lean#L90)）。 |
| `T`（T11） | `SourceThetaIQInterface C3`；`thetaImage n c` 落在 **C3 选定元组的 IQ 块**，不是 C4 的值点（[SourceThetaToIQ.lean:44](../tmp/sheaf/n8/closure/SourceThetaToIQ.lean#L44)、[同文件:64](../tmp/sheaf/n8/closure/SourceThetaToIQ.lean#L64)）。 |
| `mu, B`（C6） | 在同一 `ArithmeticTensorTupleBlock` 给可测结构、Borel 结构、加法 Haar 测度 `mu` 与 `C6ActualIQData … mu`；不是任取一个实数作体积（[Attempt:64](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L64)）。 |

`sourceAllowedOutputOfActualData A` 确实不用外给 `bridge` 或最终 witness。它取 `n := A.D.pilot.n`，取 `x := constantThetaPilotPoint … 1`，不是取张量中的 `1`。
`w := ⟨zeroSignedLabel, ⟨A.D.eval n x zeroSignedLabel, rfl⟩⟩` 记录**那个选择及其求值**（[Attempt:75](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L75)）。
这个 `rfl` 的两边都是 C4 值点；`D.eval` 用 `sourceThetaPilotPoint … n c`，不使用状态 `x`，`D.Witness n x` 是依赖对而非一份 Haar 区域证书（[SourceWitnessedOutput.lean:102](../tmp/sheaf/n8/closure/SourceWitnessedOutput.lean#L102)、[同文件:118](../tmp/sheaf/n8/closure/SourceWitnessedOutput.lean#L118)）。
展开 `ThetaPilotPoint v`，它是从 `ThetaPilotCarrier ℓ × SignedLabel ℓ.value` 到 `(I.primeStripAt 0 0).Mon v` 的函数。给定 `n,c` 的 `sourceThetaPilotPoint` 在这个函数的各输入处取同一 `thetaImageValue`（[SourceImageHull.lean:139](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean#L139)、[同文件:201](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean#L201)）。
`U_eq_range` 把 C4 的 `U n x` 写成这些见证输出的像；在此可以从见证回读所用标签，不能把带符号的零标签换读为 capsule 换位 `(2,0)`（[SourceWitnessedOutput.lean:141](../tmp/sheaf/n8/closure/SourceWitnessedOutput.lean#L141)）。
`SourceAllowedOutput.region` 到 IQ 侧却取**所有** `c : D.Choice n x` 的 `T.thetaImage n c`，没有用 `w.2` 选出一个张量成员（[P6Comparison.lean:96](../tmp/sheaf/n8/closure/P6Comparison.lean#L96)）。
能正向复用的那一小步是 `outputRegion_contains_witness`：按标签 `w.1` 取得的 **T11 像**在这片区域里。证明 `⟨w.1,rfl⟩`，不是 C4 值点与该张量像的识别（[C9ValuesPaper.lean:48](../tmp/sheaf/n8/closure/C9ValuesPaper.lean#L48)、[同文件:58](../tmp/sheaf/n8/closure/C9ValuesPaper.lean#L58)）。
给定这样的 `J` 后，`hullPoss` 的类型是 `J.region ⊆ J.B.hull`，`ellOut` 是 `J.B.normalizedLogVolume J.region`；字段可读取并不等于包含已经证明（[P6Comparison.lean:102](../tmp/sheaf/n8/closure/P6Comparison.lean#L102)）。
给定真实 `places,tuple,mu`，`C6ActualIQData.actual` 可生成规范 C6，`actual_isActual` 识别其读数及倒张量秩权重。任给记录 `B` 与这一个规范对象并非定义上相等（[C6ActualIQData.lean:45](../tmp/sheaf/n8/closure/C6ActualIQData.lean#L45)、[C6ActualIdentification.lean:31](../tmp/sheaf/n8/closure/C6ActualIdentification.lean#L31)）。

**准确的未证声明与调用者：**

```lean
theorem sourceAllowedActualData_nonempty :
    Nonempty (SourceAllowedActualData X) := by
  sorry
```

这是 [SourceAllowedOutputActualAttempt.lean:107](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L107) 的声明，[第 109 行](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L109) 是证明体。
`sourceAllowedOutput_nonempty_of_actualData` 有显式前提，拆包即可；无显式包参数的 `sourceAllowedOutput_nonempty_of_package` 正是调用这处 `sorry`（[Attempt:99](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L99)、[同文件:113](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L113)）。
旁路同样不能充证：旧 `P6Comparison.sourceAllowedOutput_nonempty` 自身也有 `sorry`（[P6Comparison.lean:142](../tmp/sheaf/n8/closure/P6Comparison.lean#L142)）。不是有两个名字就有一份独立构造。

### E.8　`tensorLanding_q`：能改写一个点，不能代替来源识别
先核对域：这里的位在 `I.initial.arithmetic.Fmod` 上，而 E.1(b) 的 Tate 见证在其上方的 `F`-位上。两个参数都写成 q，并不提供完备化之间的运输（[SourcePilotRegion.lean:65](../tmp/sheaf/n8/closure/SourcePilotRegion.lean#L65)、[Quantifiers:966](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L966)）。
设 `F_v = CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place`，`B_c = ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple`。
这里 `tensorUnit : B_cˣ`，`tensorLanding : F_v → B_c` 是普通函数。`tensorLanding_q` **只有以下一个方程**（[SourcePilotRegion.lean:93](../tmp/sheaf/n8/closure/SourcePilotRegion.lean#L93)）：

```text
C3.tensorLanding (C3.q.q : F_v) = (C3.tensorUnit : B_c)
```

`qPilotPoint_eq_tensorUnit` 的证明体就是这个字段；右侧是一枚给定的可逆元，未写成乘法幺元 `1`（[SourceThetaToIQ.lean:105](../tmp/sheaf/n8/closure/SourceThetaToIQ.lean#L105)）。
`qPilotMembership_iff_tensorUnit_mem` 只把目标改写为「该单位属于规范 hull」；等价式既没有生成 hull 成员，也没给 `tensorLanding 1 = 1`（[C7QPilotMembershipUnderconstrained.lean:45](../tmp/sheaf/n8/closure/C7QPilotMembershipUnderconstrained.lean#L45)）。
函数的类型不要求可加、保乘、保任意单位或连续。方程中无槽 `i`、无重排 `τ`、无第二个元组，故不能拿它充作整数据换位的交换图。
它也不是 T11 的识别。`T.thetaScale_eq` 钉住实数 `I.thetaValueAt (n.1 : Int) 0 c`，`T.thetaImage_eq` 钉住张量像 `tensorLanding (T.thetaCompletion n c)`；两条等式的余域不同（[SourceThetaToIQ.lean:66](../tmp/sheaf/n8/closure/SourceThetaToIQ.lean#L66)）。
现成的 `thetaIQInterfaceOfQUnit` 在 completion 取 `qUnit ^ (gaussExponent c.1).toNat`，这个表达式不使用 `n`；实数 scale 另从剧场读取。能填接口，不证明此幂来自同一次原 evaluation（[SourceThetaToIQ.lean:82](../tmp/sheaf/n8/closure/SourceThetaToIQ.lean#L82)、[同文件:94](../tmp/sheaf/n8/closure/SourceThetaToIQ.lean#L94)）。
即使只比实数 packet，也另有 `QIdentification := C3.thetaPacket.q = (I.theaterAt 0 0).thetaPacket.q`；由它可推全 packet 识别，前提并非完备域 q 的 landing 等式（[T11Reductions.lean:83](../tmp/sheaf/n8/closure/T11Reductions.lean#L83)、[同文件:98](../tmp/sheaf/n8/closure/T11Reductions.lean#L98)）。
反向只需检查零 procession 的 `oneSignedLabel`，该标签处两种 scale 分别还原为各自的 q；所以实际有 `thetaPacketIdentification_iff_q`，不是从 `tensorLanding_q` 推出的单向蕴含（[T11Reductions.lean:62](../tmp/sheaf/n8/closure/T11Reductions.lean#L62)、[同文件:127](../tmp/sheaf/n8/closure/T11Reductions.lean#L127)）。
若已有 `thetaPacket_eq` 的明确见证，`thetaPacketIdentification_of_witness` 才可直接消去这一项（[C3QPacketIdentificationAttempt.lean:46](../tmp/sheaf/n8/closure/C3QPacketIdentificationAttempt.lean#L46)、[同文件:58](../tmp/sheaf/n8/closure/C3QPacketIdentificationAttempt.lean#L58)）。

还有一个比「暂未构造」更强的理由不并入旧 C3 的存在断言：`roots : NatRootSystem qUnit` 被要求位于 **`F_v` 本身**，且 `qUnit_eq` 把它绑在这个 q 上（[SourcePilotRegion.lean:70](../tmp/sheaf/n8/closure/SourcePilotRegion.lean#L70)）。
设 `e = q.order > 0`。根系会给同一完备域中的 `(e+1)` 次根；在离散值群取整指数 `a`，得到 `(e+1)·a = −e`，不可能。
这个排除有证明体，不是对 `sorry` 的猜测（[S1429CompletionRootObstructionActual.lean:62](../tmp/sheaf/xif/paper/S1429CompletionRootObstructionActual.lean#L62)、[同文件:134](../tmp/sheaf/xif/paper/S1429CompletionRootObstructionActual.lean#L134)）。
`sourcePilotRegionData_isEmpty` 正是沿 `qUnit_eq` 运输 `D.roots` 得到矛盾（[S1429:167](../tmp/sheaf/xif/paper/S1429CompletionRootObstructionActual.lean#L167)）。
因而对旧 P6 所用 C3，E.7 那个无条件包不能靠补上一个遗忘的见证来实现；同理，E.6 以旧 C3 为参数的静态定理不能提供本例的实例。
障碍是**所有阶的根都在此离散完备域**，不排除某个指定阶的根，也不排除代数闭包内的根系，不是否定原文允许输出的定理。
修订接口 `SourcePilotRegionDataLGeneric` 把根系放在代数闭包，要求它与原 q 单位的代数映射相合；张量 landing 仍从原完备域出发，并仍只有 q 方程（[Mzk1SourcePilotLGenericActual.lean:45](../tmp/sheaf/xif/paper/Mzk1SourcePilotLGenericActual.lean#L45)、[同文件:73](../tmp/sheaf/xif/paper/Mzk1SourcePilotLGenericActual.lean#L73)）。
这是另一种类型，不可把它直接填在 `P6Comparison.lean:69` 的旧字段；移植 E.6 的纯张量论证只需有限位族，不必连这个旧根系假设一起移植。

### E.9　把各段接回一次求值：固定例的交付点
这里 `U₂,₃` 的两个下标依次是行 `j` 和有理位 `v_Q`，不是 `FinitePrimePlace` 的区间端点。`d` 是此例的深度，也不是索引类型的基数（[III.txt:10383](IUT-TEXT/III.txt#L10383)、[交接:1551](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1551)）。
固定 `p=3, ℓ=5, d=3`、第二行 `j=2`、第 1 列，令 `G` 表好位、`B` 表坏位；它们不是 E.3 的作用群。这里要判断的是原 `U₂,₃`，不是后来取的 hull（[III.txt:10376](IUT-TEXT/III.txt#L10376)、[同文:10404](IUT-TEXT/III.txt#L10404)）。
目标元组为 `c_t=(G,B,B)`，源取 `c_s=(B,B,G)`。`τ=(2,0)` 是换位且自逆，故 `c_s ∘ τ⁻¹ = c_t`，源标记槽 `2` 到目标槽 `0`。
模型一侧，`1 ∈ thetaFiniteOn({2}, c_s)` 是交接的点证据。其标记在好位；相同目标元组若仍标默认槽 `2`，投影绝对值是 `3^(−6/5)` 而非 `1`（[交接:1541](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1541)、[同文:1943](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1943)）。
`image_thetaFiniteOn_ind1Reindex` 同时把 `S,c` 送成 `τ '' S, c ∘ τ⁻¹`；因此已能把源的模型区域送到 **同一模型** 的 `thetaFiniteOn({0},c_t)`（[Ind1Invariance.lean:592](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/Ind1Invariance.lean#L592)）。
与之不同，E.6 的等式重排同一个静态整包；E.5 的两路等式在条带上。即使三边都写着 `1`，它们也分属张量、单位商或值点的不同类型。

**逐步对接时，如何认定始终是同一次 evaluation？**
1. 固定输入、坏位上方的 `F`-位和 `K`-截面，并把具体 q、源元组、标记槽及 capsule 嵌入一起记录。E.1 给可取字段；剧场算术根相等并不识别两次选择。
2. 从这次操作取出候选条带代表 `φ`，在局部单位代表上核对 `[a] ↦ [φ(a)]`。E.2 可检验局部单位像；E.4 的 `canonicalLift` 可将已识别的同一个 `φ` 提升到 `F×μ`。
3. 在同一组顶点上，E.3/E.5 的公式可计算下横代表，E.4 的公式可化简 IPL 路径。**到此输出仍是条带箭头。** 不能应用它到 `thetaFiniteOn` 的一个张量上，除非另给相应的载体映射。
4. 第一项待证：让这次原操作产生带积分数据的 `D_τ`，并在它的载体与来源张量之间给出 `E_τ`；换位须运输嵌入、因子和区域代表，而不只是交换两个数字（[交接:1915](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1915)、[同文:1945](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1945)）。
   一个可核对的自然性方程是 `E_t ∘ r_τ = r′_τ ∘ E_s`：`r_τ` 是模型重排，`r′_τ` 必须是同一求值在原输出侧诱导的运输，`E_s,E_t` 是相应两端的载体实现。这是待证方程，不是静态 Ind1 定理的改名。
5. 对同一 `D_τ` 证明它属于固定输入的原允许族 `P_C`，并证明 `E_τ(1) ∈ U₂,₃`；若能给 `E_τ '' thetaFiniteOn({2},c_s) ⊆ U₂,₃` 则保留整片区域（[交接:1948](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1948)、[同文:1955](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1955)）。
   E.6 的投影能在已识别的整包中计算该点的元组坐标；它的反向补零给的是静态区域原像，不是这次 III.3.10.2 操作的原像。
6. 最后比对同一输出的读数：第 1 列好槽的投影、张量秩归一化及 procession 权重一个也不能换；有限性与上界仍要对**全部**原允许输出证明（[交接:1956](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#L1956)）。

第一批交付的取舍由这个停止点决定：
| 给维护者的材料 | 在消费端如何使用 |
|---|---|
| `SourceDefinition31Quantifiers/Boundary` 与位的单射片段 | 对照 `InitialThetaData` 时分列几何输入、合同字段和需运输的等式，不把两个同名 q 合并。 |
| `LocalIntegralUnitEvaluationImage`、`TimesMuIsm` 与 `canonicalLift` | 从一个具体单位算到其商类和不变像；一旦给出纤维识别，即可比较两侧同一个代表的作用。 |
| `ofThreeArrows`、S1951 的 `General`、`iplLink_eq_verticalLGP_upperLGP` | 复用箭头和消去证明；`S1951` 的特化只作回归样例，不能给出 `p=3, ℓ=5` 的来源见证。 |
| `FinitePlaceArithmeticIQTensor`、`FinitePlaceArithmeticTensorBlocks` | 用明确 `places` 检验静态 `1`、紧性及逐元组投影，作为实际 `E_τ` 一旦给出后的计算工具。 |
| `SourceAllowedOutputActualAttempt`、旧 C3 与 T11 | 保留作字段和失败路线的证据；不并入旧非空断言，不把标签见证、q 方程或静态紧性充作 `D_τ ∈ P_C`。 |

下一项只验第 4–5 步的**固定输入点**；若载体映射无来源，就交付其精确缺口。不从这一点推出其他元组、全体 I.3.1 数据、原 III.3.12 或 ABC。
本附篇只核对源码和原文行号；`statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 四项均未运行。

<a id="dictionary"></a>

## F. LANA ↔ 本地：同一份输入，两个有方向的比较
原 III.3.12 要给**所有原允许像**的 hull 一个有限读数及下界；LANA 的 ABC 入口要给**指定标签**模型的实数读数一个下界。两者可以共用见证，不能先把两端定义成同一个数。
以下 `Iut/…` 指 LANA 工作树 `553076af459e7a401bfee63a4607814d1c854477`；`LeanFormal/…`、`tmp/…`、`coord/…` 指本地 2026-11-20 工作树（HEAD `a997af4b1cb2339d1e7403ef0781a16f809f4476`）。行号均自 1 起。
“现有”指所引源码中的定义或带证明体的定理；“建议”指待实现的映射或待证命题。两仓工具链分别为 4.32.0、4.32.2（各仓 `lean-toolchain:1`），本篇不作跨仓编译声明。

### F.1 先展开量词：谁给定数据，谁必须生成见证？
原文先固定一份合格的初始 Θ-data 和相对于它的、以整数对编号的不同 Hodge theaters（`coord/IUT-TEXT/III.txt:9153`）；3.12 沿用该情形（`coord/IUT-TEXT/III.txt:10326`）。
本地 `I : Theorem311Source.OriginalInput l V` 有 `initial`、`family`、`index_equiv : family.index ≃ Int × Int`、`arithmetic_alignment`（`LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean:41`）。
`family.distinct` 是对实际 theater 函数的单射性，`family.link` 连每一对下标（`LeanFormal/IUT/IUTI/HodgeTheater/SourceHodgeTheaterFamily.lean:32`）；`I` 不是一个已带 evaluation 或 q-coverage 的请求包。
LANA 的抽象 `X : Corollary312VariantData` 依次含 `data`、`qPilot : QPilotData data`、`rhsData : RHSData data`；`Corollary312Variant X` 只是后两个字段的实数不等式（`Iut/Cor312/Statement.lean:68`、`Iut/Cor312/Statement.lean:89`）。
ABC 前件并非 `∀ X, Corollary312Variant X`。令 `L(D) := D.qPilot.lhs`、`Hᵥ(D) := D.rhsData.rhs`、`Hₗ(D) := D.rhsDataLit.rhs`，则具体量词是：
- IV：`∀ D : Iut.InitialThetaData.{0}, L(D) ≤ Hᵥ(D)`；两个投影都由这个 `D` 生成（`Iut/Concrete/ThetaRegion.lean:359`、`Iut/Concrete/ThetaRegion.lean:375`）。
- literal：`∀ D : Iut.InitialThetaData.{0}, L(D) ≤ Hₗ(D)`；沿用同一 `D.qPilot`，只换 RHS（`Iut/Concrete/ThetaRegion.lean:367`、`Iut/Concrete/ThetaRegion.lean:383`）。
- `classicalABC_of_variant` 取前一条为假设，不取后一条（`Iut/MainTheorem.lean:36`）。在一个例子上算出两边，甚至对某个源构造的全部像证明它，都不等于覆盖每个 `D`。
若用格子路线，另有一层经常被略写为 `LL D` 的依赖量词。记 `LL := Iut.LogLink.LogThetaLattice`，这是本篇缩写，不是 `InitialThetaData` 的字段。
`LL D` 的字段是 `H : ℤ × ℤ → ThetaPmEllNFHT D`、相邻的 `vert` / `horiz` 和逐列、逐有限模域位的 `loc`（`Iut/LogLink/Lattice.lean:90`）。
`classicalABC_of_thm311` 取 `L : ∀ D, LL D`、`K : ∀ D, LatticeKummer (L D)`，再取逐 `D` 的 `Thm311` 与 `XiPrinciple`（`Iut/LogLink/Thm311.lean:234`）。
另一入口恰是 `∀ D, ∃ (L : LL D) (K : LatticeKummer L), XiPrinciple K`，不是 `∃ D`，也不要求每个 `L` 都由本地给出（`Iut/LogLink/Thm311.lean:241`）。
`LogThetaLattice.ofData` 的 `H _` 是同一模型，`loc` 是 tautological column（`Iut/LogLink/Lattice.lean:150`）；不能据此用常函数满足本地 `family.distinct`，或反推出原求值。
区别可写成 `∀ δ, ∀ Λ : PaperLL δ, Paper312 δ Λ` 与 `∀ D, Variant D`：前者的 `PaperLL` 表示原文给定的合格族，后者的 RHS 不以 `Λ` 为参数；`PaperLL` 是此处的数学记号，不是宣布新 Lean 声明。
有 `∀ D, LL D` 只是能为每个 `D` 选模型格子；有 `∀ D, ∀ L : LL D, …` 则能对任意模型格子使用该结论。两种签名均不自动识别给定的原 `Λ`。
需要真正 LGP 附加结构时，LANA 另有 `LGPLattice D`，增加无穷位的 `arc` 和坏位 Gaussian generator 的 `kum_gen`（`Iut/LogLink/Thm311LGP.lean:93`）。
对应的 ABC 定理要求 `L : ∀ D, LGPLattice D` 和逐 `D` 的 Kummer、`Thm311LGP`、`XiPrinciple`（`Iut/LogLink/Thm311LGP.lean:189`）；这不是 `Cor312VariantHolds` 的展开式。
因此本地若要消费 LANA，需要为给定原输入找到匹配的 `D`；LANA 若要消费本地，需要对**每一个给定的 `D`**找到匹配的原情形。两项覆盖义务不能交换。

### F.2 类型字段表：哪些可投影，哪些必须构造？
区分 `I.initial : SourceDefinition31Data l`（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:667`）与较强的 `T : SourceNativeInitialThetaData l`，后者带依赖的 tuple 和 A–F（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1681`）。
同一文件的 `InitialThetaData l : Prop` 缩写的是存在性（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1726`），也不是 LANA 的 `InitialThetaData : Type (u+1)`（`Iut/Cor312/ThetaData/Basic.lean:81`）。

| LANA 要求的字段或对象 | 本地能拿到什么 | 同一输入的验收义务 |
|---|---|---|
| `F`、`Field F`、`NumberField F`（`Iut/Cor312/ThetaData/Basic.lean:83`） | `A := I.initial.arithmetic` 或 `T.arithmetic` 的 `A.F`（`LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:62`） | 可投影；若两边选不同载体，要记录保 `ℚ` 的域同构。 |
| `Fbar`、`Algebra F Fbar`、`IsAlgClosure F Fbar`（`Iut/Cor312/ThetaData/Basic.lean:89`） | `T.tuple.fbar` 的域、代数性、代数闭性及到 `AlgebraicClosure A.F` 的 `≃ₐ`（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:187`） | 可沿该同构运输；连扭点和 Galois 作用一起运输，不另选不相干的闭包。 |
| `E : WeierstrassCurve F`、`E.IsElliptic` 和派生的 `X = E ∖ {0}`（`Iut/Cor312/ThetaData/Basic.lean:98`、`Iut/Cor312/ThetaData/Basic.lean:122`） | `A.curve.curve`、`isElliptic`，而 `puncture` 是显式射影点（`LeanFormal/IUT/Foundations/Geometry/PuncturedEllipticCurve.lean:17`） | 曲线可投影；带标记曲线另证尖点对应，不能遗忘标记后声称同一。 |
| `Fmod = ↥ℚ⟮E.j⟯`（`Iut/Cor312/ThetaData/GlobalField.lean:106`） | `A.Fmod` 是独立域；`field_of_moduli.jModuli` 映到 `j(E)`（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:405`） | 只知像含 `j` 不知由 `j` 生成；证明嵌入像是该中间域，或为所用读数给出真正的基变换公式。 |
| `VBad : Set (FinitePlace ↥(fieldOfModuli F E))`（`Iut/Cor312/ThetaData/Basic.lean:103`） | `I.initial.badPlaces` 仅是类型；`T.tuple.V_mod_bad` 确是 `FinitePlace A.Fmod` 的集合（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1624`） | 沿模域的位对应运输整集，核对非空、奇剩余特征、所有上方坏位；不是换成一个坏位。 |
| `global : IsInitialThetaGlobalData …`（`Iut/Cor312/ThetaData/GlobalField.lean:166`） | 源塔有 `sqrtNegOne`；native A/B/C 分别给稳定约化、坏位上的乘性约化及 2、3 扭点条件（`LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:35`、`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:891`、`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:962`、`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1011`） | 对每个 `w : FinitePlace F` 以及每个 `w` lying over `v ∈ VBad` 核对实际约化谓词；证明 `six_torsion_rational` 用的是同一 `E/Fbar`。 |
| `prime : AdmissiblePrimeData …`（`Iut/Cor312/ThetaData/AdmissiblePrime.lean:111`） | `l.value`；native 有基、标准表示等式、`SL₂` 像（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1012`） | LANA 的基从扭点到坐标，源基从坐标到扭点；识别扭点后取逆，验证 `rep_spec`、开核、互素次数及逐 Tate 参数/均匀化元的互素性（`Iut/Cor312/ThetaData/AdmissiblePrime.lean:130`、`Iut/Cor312/ThetaData/AdmissiblePrime.lean:138`、`Iut/Cor312/ThetaData/AdmissiblePrime.lean:154`）。 |
| `K := fixedField rep.ker`，`Kt := ↥K`（`Iut/Cor312/ThetaData/AdmissiblePrime.lean:165`、`Iut/Cor312/ThetaData/Basic.lean:132`） | native C 已给 `A.K ≃ₐ[A.F]` 本地表示的核域（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1027`） | 复用该同构，和闭包运输、两套表示的核相容；有限 Galois 扩张的类型类不决定这个核域。 |
| `orb : OrbicurveData … prime`，含 core、四条 cover、Cartesian 方块和 `epsilon = CKu.cuspOf q`（`Iut/Cor312/ThetaData/Orbicurve.lean:88`、`Iut/Cor312/ThetaData/Orbicurve.lean:111`、`Iut/Cor312/ThetaData/Orbicurve.lean:122`） | 弱记录的 `cusp.epsilon : Real`（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:612`）；native D/F 有带类型的边界来源（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1553`、`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1626`） | 运输 cover/秩一商及其非零元到真实的 cusp；正实数、签名或基数都不是 cusp。 |
| `V : ValuationSection …`，有 `sectFin`、`sectInf` 及各自 `liesOver`（`Iut/Cor312/ThetaData/LocalConditions.lean:140`） | 弱 `sections` 在两种抽象 carrier 间给双射（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:521`）；native 明有 `V_section`、`V_eq_section`（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:617`） | 比较**给定**截面的两个分支，逐位证明提升交换；不可换成另一条同样存在的截面。 |
| `localData : LocalThetaData … prime orb`（`Iut/Cor312/ThetaData/Basic.lean:113`） | native E 有有限/无限处的局部资料（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1438`） | 在所选完备化验证局部 Cartesian、`tateX/C`、`bad_type`、`bad_theta_model`、`epsilon_graph`（`Iut/Cor312/ThetaData/LocalConditions.lean:199`、`Iut/Cor312/ThetaData/LocalConditions.lean:211`、`Iut/Cor312/ThetaData/LocalConditions.lean:226`）。 |

弱记录还有 `qParameter : Bad → Real` 和抽象群表示（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:101`、`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:210`）；它们分别不是完备化中的 Tate 元和椭圆曲线的扭点作用。
旧字段清单 `tmp/sheaf/xif/paper/Mzk1InitialThetaDataMappingAuditActual.lean:23` 不能替代上表：native 并非没有闭包、坏位集或核域同构；缺的是与 LANA **指定对象**的识别及其相容性。
`ofExistence` 可以从既有 `global/prime/orb/sect` 填入 canonical Tate structures，但仍显式要求局部方块、型别、Θ-root 模型和尖点图（`Iut/Cor312/ThetaData/Basic.lean:220`）。这是可复用构造器，不是从 `I` 强转。
**建议的约束方式：**用依赖类型 `Match I D` 记录域塔、坏位集、给定截面、曲线和标记方块的相容证据；不要在 `Match` 里放任一目标不等式、输出覆盖或“存在所需 adapter”。
`matchOfSource I` 或 `sourceOver D` 若想消去调用者前提，必须返回依赖对及其 `Match` 证明。只实现 `(I) (D) (m : Match I D) → …` 可用于拆任务，不算完成任一方向的输入覆盖。
截面相容可以直接写成逐位等式。设 `β`、`κ` 是域塔识别诱导的模域位、扭点域位映射，则要求 `κ(σ_src b)=σ_D(β b)`，且 `β` 识别坏集、保持实/复重数。
本地 `SourceCompletion.ofSourceNative` 的 `arithmeticPrelude` 确实沿 `T.tuple.source.V_section` 构造（`LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean:1105`）；它可固定等式左端的来源。
反之，`SourcePlaceSelection.V_section` 通过 `NumberFieldPlace.restrictionSection` 选提升（`LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceSelection.lean:75`）。两个提升都限制为 `b`，不推出它们相等。
LANA 的容器级 `PlaceSection K k` 只记录 `fin`、`inf` 和有限处的剩余特征相容（`Iut/Concrete/Container.lean:196`）；在比较塔时，应回到 `D.V` 的 `liesOver` 字段，而不是从容器截面的类型反推它。
即使已知这些位对应，也不得额外要求 `Kt/Fmod` 为 Galois；LANA 的初始数据明确没有这一全局假设（`Iut/Cor312/ThetaData/Basic.lean:46`）。

### F.3 左端：一份 q，三个不同的局部数字
抽象 `QPilotData D` 取 `badFinset : Finset (FinitePlace D.F)`、枚举 `badPlacesOver` 的等式、`weight : FinitePlace D.F → ℝ` 及坏位权正性（`Iut/Cor312/LeftHandSide.lean:58`）。
“权为正”没有规定权是多少。具体 `D.qPilot` 才取坏集的 `toFinset` 与 `inertDeg D.F w / finrank ℚ D.F`（`Iut/Concrete/ThetaRegion.lean:348`）。
`D.tateParam w hw : TateParameter (localCompletion w)` 以同一曲线的 `j` 表征，`D.qOrder w hw : ℕ` 是整数阶，坏位严格为正（`Iut/Cor312/ThetaData/Basic.lean:156`、`Iut/Cor312/ThetaData/Basic.lean:166`、`Iut/Cor312/ThetaData/Basic.lean:173`、`Iut/Cor312/ThetaData/Basic.lean:180`）。
记 `w|b|p` 分属 `F,Fmod,ℚ`，`k_w = ord_w(q_w)`，`ord_w(π_w)=1`，`e_w=ord_w(p)`，`f_w` 为剩余次数，`d_w=e_w f_w`。LANA 具体左端为
\[
L(D)=-\frac{1}{2\ell[F:\mathbb Q]}\sum_{w\in\mathrm{bad}(F)} f_w k_w\log p_w .
\]
求和、除 `2ℓ`、取负号是三个定义（`Iut/Cor312/LeftHandSide.lean:81`、`Iut/Cor312/LeftHandSide.lean:88`、`Iut/Cor312/LeftHandSide.lean:93`）。这一步不求 `K` 上所选坏位的普通平均。
在默认 adic 范数下 `‖π_w‖ad=p^(−f_w)`，故 `−log‖q_w‖ad/log p=f_w k_w`；LANA 的 `ordp=-log‖·‖ad/(d_w log p)` 给 `k_w/e_w`（`Iut/Concrete/LocalTheory.lean:45`、`Iut/Concrete/LocalTheory.lean:59`）。
若改用延拓 `|p|=1/p` 的范数，则 `‖q_w‖ext=‖q_w‖ad^(1/d_w)`；本地对**同一个** `qVFamily T b` 有此幂公式（`tmp/sheaf/xif/paper/Mzk1P0QVFamNormBridgeDonorActual.lean:63`）。
所以乘归一绝对局部次数 `d_w/[F:ℚ]` 的是 `k_w/e_w`；乘 `f_w/[F:ℚ]` 的是 `k_w`。若对默认范数和读出的 `ordp` 都除局部次数，就多除了一次。
本地 `qVFamAt T w hw` 取自 native B 在该位的比较见证；`qPilotMagnitudePaper_v2` 对每个坏 `b` 的**完整** `primesOverFinset` 按惯性次数求和再除全局次数（`tmp/sheaf/xif/paper/Mzk1ULQPilotMagnitudeV2Actual.lean:36`、`tmp/sheaf/xif/paper/Mzk1ULQPilotMagnitudeV2Actual.lean:86`、`tmp/sheaf/xif/paper/Mzk1ULQPilotMagnitudeV2Actual.lean:94`）。
这是一个可对接的无符号、未除 `2ℓ` 的量。先运输 `b,w,p` 的索引、Tate `j` 身份和整数阶，再证明相同全纤维求和；不能因为两个求和外形相同就用 `rfl`。
若改从 `K` 侧的根读数，给定 `v|w`，LANA 有 `r_v^(2ℓ)=embedF(q_w)` 及 `ordp(r_v)=k_w/(2ℓ e_w)`（`Iut/Concrete/ThetaLocalConstruct/Data.lean:413`、`Iut/Concrete/ThetaLocalConstruct/Data.lean:420`）。
好 `v` 的根按 `¬ IsBadK D v` 分支取 `1`，即使同一 `p` 上另有坏 `v'`（`Iut/Concrete/ThetaLocalConstruct/Data.lean:281`、`Iut/Concrete/ThetaLocalConstruct/Data.lean:294`）。根在 `K_v`，不要求在 `F_w`。
可复用 `qOrder_div_ramIdx`、`ordp_qroot_sect` 和 `logQAt_eq_sect`：它们分别解决降到 `b`、在 `σ(b)` 开根、按 `Fmod` 的纤维权重重算该 `p` 的总和（`Iut/Concrete/SectionAverage.lean:174`、`Iut/Concrete/SectionAverage.lean:189`、`Iut/Concrete/SectionAverage.lean:284`）。
三条都是 LANA 内部对同一 `D` 的定理；跨仓还要把源 q 识别到它们的输入。`P.line.C3.q.q` 的一个默认范数对数不是上述全局和（`tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean:82`）。
具体可从 native 的 `SourceTateComparisonWitness` 着手：同一记录同时给 `parameter`、与 `A.curve` 的 `comparison` 及 `order_coprime`（`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:952`）。
先将该比较运输到同一 `F_w`，证输入曲线的 `tateJ` 等式，再用 LANA 的唯一性 `eq_tateParam`。若只需左端，认出 `k_w` 即可，不必声称两套任意选根相等。
若下一步要运带标记的区域，两个 `2ℓ` 次根可能差单位根；须证明该单位在真实允许作用下保区域或逐个标记运输。相同赋值足以算左端，但不足以构造右端的同一个点。
LANA 也已有区域版左端：`qRegion` 在每个 capsule 的标签 `1` 乘 `2ℓ` 次根的一次幂，无穷处取积分区域；`logVol_qRegion` 识别其全局读数为 `.qPilot.lhs`（`Iut/Wall/QPilotRegion.lean:314`、`Iut/Wall/QPilotRegion.lean:321`）。这是归一化测试，不是原 Θ 输出成员定理。

### F.4 右端：从带标记的张量点到 procession 读数
抽象 `R : RHSData.{u,v} D` 的 `container : LargeVolumeContainerData.{0,u,v} ℕ (ModPlace D.F D.E)`；`proc_standard` 固定长度，`toRational_finite/infinite` 固定底位（`Iut/Cor312/RightHandSide.lean:65`）。
它还要求 `vol : LogVolumeData container`、`hull : ContainerHullSystem container`、`thetaPilot : ∀ i, container.AdmissibleRegion i` 和逐行 `hull.IsAdmissible`（`Iut/Cor312/RightHandSide.lean:81`、`Iut/Cor312/RightHandSide.lean:88`、`Iut/Cor312/RightHandSide.lean:92`）。
`AdmissibleRegion.region vQ : Set (container.packet i vQ).Total`，几乎处处等于 integral region；这是有限支集条件，不等于 hull 系统逐包的可容许性（`Iut/Cor312/Container.lean:152`、`Iut/Cor312/ContainerHull.lean:64`）。
`rhsDataOn S hS` 在具体 `D` 上已生成这些字段，不给 PR 留任意替换 `thetaPilot` 的自由（`Iut/Concrete/ThetaRegion.lean:320`）。抽象 record 把区域当输入；具体函数构造模型区域，但不证明它是原文 evaluation 的像。
取 `n=(D.ℓ−1)/2`、`i : Fin n`、`j=i.val+1`；`Lab n i` 是 `{0,…,j}` 的标签类型，`distinguished n i` 是最后一个标签 `j`（`Iut/Cor312/Procession.lean:107`、`Iut/Concrete/ThetaRegion.lean:118`、`Iut/Concrete/ThetaRegion.lean:122`）。
取 `vQ : RationalPlace`，`B(vQ) := LocalTheory.Fiber D.Fmod vQ` 是映到 `vQ` 的模域位置子类型（`Iut/Concrete/Container.lean:65`）。一个元组是函数 `c : Lab n i → B(vQ)`，允许同一位置多次出现。
`σ := D.placeSect` 使用 `D.V.sectFin/sectInf`；`tuple σ vQ c` 才逐槽给出 `Kt` 的位（`Iut/Concrete/ThetaRegion.lean:109`、`Iut/Concrete/Container.lean:222`）。这不是任取 `K` 在 `p` 上方的一切元组。
记 `T_c := LocalTheory.Tensor D.Kt vQ (LocalTheory.tuple σ vQ c)`；它是对 `ℚ_p` 或 `ℝ` 的依赖张量积（`Iut/Concrete/LocalConstruct/Packet.lean:520`）。类型随 `c` 改变，重排不是同一 `Set ℝ` 上的置换。
在有限 `p` 及标记 `a : Lab n i`，`s_a := incl_a (r_{σ(c a)}^(j²)) : T_c`（`Iut/Concrete/ThetaRegion.lean:126`）；只有乘数占第 `a` 槽，其余因子仍在张量包里。
以 `J_c` 表示 `LocalTheory.shell …`、以 `S` 表示本行允许的标签集。实际有限分量（`Iut/Concrete/ThetaRegion.lean:170`）是
\[
U^S_{i,p,c}=\bigcup_{\phi\in\mathrm{indAut}(c)}\phi\!\left[\bigcup_{a\in S}s_a J_c\right]\ \subseteq T_c .
\]
因此一个成员证明的内容是 `∃ φ, ∃ a ∈ S, ∃ y ∈ J_c, x = φ(s_a • y)`（附 `φ ∈ indAut`）。其中 `x : T_c`；命题不是 `log ‖x‖ ≤ R.rhs`。
无穷位不走 `qroot` 或有限槽的分支：`thetaComponentOn` 取 `thetaInfinite`，是张量 Hermitian log-shell 在各因子符号、共轭作用下的并（`Iut/Concrete/ThetaRegion.lean:178`、`Iut/Concrete/Container.lean:499`、`Iut/Concrete/LocalConstruct/ArchIndAut.lean:81`）。
每个实/复因子的 log-shell 半径是 `π`，张量球由相应内积给出（`Iut/Concrete/LocalConstruct/ArchLogShell.lean:278`）；不能因 q 侧无无穷位项便将右端该球的读数设为零。
逐元组组成 packet 的 `productRegion`：成员是函数 `z : ∀ c, T_c`，须对每个 `c` 都有 `z c ∈ U_c`（`Iut/Concrete/Container.lean:259`、`Iut/Cor312/PacketPresentation.lean:108`）。
再对 `vQ` 组成 `thetaPilotOn`；它证明有限支集，对非空 `S` 另证各分量可容许（`Iut/Concrete/ThetaRegion.lean:273`、`Iut/Concrete/ThetaRegion.lean:186`）。单一元组的点没有其余元组坐标。
`thetaHull` 是 `hullFamily thetaPilot`，`rhs` 是 `vol.processionVol thetaHull`（`Iut/Cor312/RightHandSide.lean:99`、`Iut/Cor312/RightHandSide.lean:107`）；次序必须是先并、再按包取 hull、最后算量。
具体 `U` 是产品，least hull 可按各分量求（`Iut/Concrete/Container.lean:433`）。对其第 `c` 个 hull 分量 `B_c`，正、有限测度范围内的公式是
\[
v_c(B_c)=\frac{\log\big(\mu_c(B_c)/\mu_c(O_c)\big)}{\dim_{k_{v_\mathbb Q}}T_c},\qquad k_p=\mathbb Q_p,\ k_\infty=\mathbb R .
\]
`O_c` 是积分参考区域，未必是 `J_c`；分母是整个张量的秩，不是槽数（`Iut/Concrete/LocalConstruct/Volume.lean:196`）。在该参考上 `componentVol_integral = 0`，不是对所有 log-shell 都为零。
记 `d=[Fmod:ℚ]`。单个位权 `λ(b)` 在有限处为 `e_b f_b/d`，在无穷处为 `mult(b)/d`（实 1、复 2）；固定 `vQ` 时全部 `b` 的权和为 1（`Iut/Concrete/LocalTheory.lean:50`、`Iut/Concrete/LocalTheory.lean:54`、`Iut/Concrete/Container.lean:163`）。
元组权 `ω(c)=∏ₐ λ(c a)` 取自**模域**，不是取自提供 tensor 因子的 `Kt`；`packetVol` 对 `proj σ vQ c U` 的分量读数作加权和（`Iut/Concrete/Container.lean:338`、`Iut/Concrete/Container.lean:378`）。
`globalVol` 对全部有理位作有限支集和；`processionVol` 再对 `n` 行等权平均（`Iut/Cor312/LogVolume.lean:177`、`Iut/Cor312/LogVolume.lean:183`、`Iut/Cor312/LogVolume.lean:207`）。故模型右端为
\[
H_S(D)=\frac1n\sum_{i:\mathrm{Fin}\,n}\ \sum_{v_\mathbb Q}^{\mathrm{fin.supp.}}\ \sum_{c:\mathrm{Lab}_i\to B(v_\mathbb Q)}\omega(c)\,v_c\!\left(\operatorname{pr}_c\operatorname{Hull}(U^S_{i,v_\mathbb Q})\right).
\]
本地有三种容易相混的接口，分别验，不用一个常数“统一归一化”：
- `SourceArithmeticPlaceModel … I` 只给一个 `p`、`places : ∀ i, W i → FinitePlaceAtPrime … p`、`tuple`、`selection`；有 `block`，没有到所有 `Fiber Fmod vQ` 的截面或 arch 分量（`LeanFormal/IUT/IUTIII/Theorem311/SourceArithmeticPlaceModel.lean:55`、`LeanFormal/IUT/IUTIII/Theorem311/SourceArithmeticPlaceModel.lean:92`）。
- `globalPrimeWeight` 服务于模域上的实化除子：有限位取 `log(absNorm 𝔭)`、无限位恒取 `1`（`tmp/sheaf/xif/paper/GlobalRealifiedFrobenioidActual.lean:59`）。它不是 `λ`；要在除子系数中找回次数/重数，再推出同一加权和。
- `thetaPilotHullLogVolumeReal C3` 是单一 C3 区域的 `log μ(B)`（`tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean:97`、`tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean:128`）；在同一 `μ,B,O` 上才有 `log μ(B)=rank·v_c(B)+log μ(O)`。
若本地模型把所有 `K` 位都列入而 LANA 只用 `σ(b)`，需证明逐纤维读数可下降且权的推前正确，或直接给出所需方向的加权估计；单看纤维总权为 1 不够。
例如 `sum_placeWeight_placeUnder` 的输入是**底域位上的函数** `g`：它把 `∑ᵥ λ_K(v) g(v|k)` 化成 `∑ᵦ λ_k(b) g(b)`（`Iut/Concrete/SectionAverage.lean:51`）。它没有说任意 `g_K(v)` 等于 `g_K(σ(b))`。
若用模型读数给原文下界，非负权允许逐个 `b` 证明一个方向再求和；若只掌握上下波动的局部误差，则须对同一输入证明它们的**带权总和**具有所需符号。
取 `μ'=tμ`，参考格与被测集若同时运输，比值 `μ'(B)/μ'(O)` 不变；只运输 `B` 不运输 `O` 会留下常数。两边都叫 Haar 并不是测度校准。
同理，正秩相同只消去分母。若使用不同参考格，要给出相对格指数或 Jacobian 的对数，并说明该项如何进入这一行的元组权和。
若本地供体只算有限位，应逐项补 arch，或针对所求方向证明遗漏总项的符号。`λ(复位)=2/d` 不能从“arch 权正”推导，去掉 arch 也不能套乘积公式。
从点比较升到体积，至少运输一个满秩内格/正测度区域，或用所定义的最小 hull 的坐标半径定理。单点测度与它所约束的最小整格的测度不是一回事。

### F.5 Ind1–3：先选允许的像，再谈 hull 的方向
**Ind1（现有）。** `ivLabels n i = {distinguished n i}`；`litLabels n i = Set.univ`；LANA 已证前者包含在后者中（`Iut/Concrete/ThetaRegion.lean:237`、`Iut/Concrete/ThetaRegion.lean:241`、`Iut/Concrete/ThetaRegion.lean:248`）。
`thetaFiniteOn_mono` 给同一 `i,p,c` 下的集合包含；`hullAdmissible_mono` 还要求两侧可容许，逐包 volume 单调性在 hull regions 上使用（`Iut/Concrete/Literal.lean:64`、`Iut/Cor312/ContainerHull.lean:95`、`Iut/Concrete/LocalEstimate.lean:430`）。
因此确切的两个方向是 `Hᵥ(D) ≤ Hₗ(D)`，以及 `Cor312VariantHolds → Cor312LiteralHolds`（`Iut/Concrete/Literal.lean:84`、`Iut/Concrete/Literal.lean:115`）。RHS 越大，下界命题越弱。
换标签时实际定理是 `reindex(τ,c) '' U^S(c) = U^(τ '' S)(c ∘ τ.symm)`；它同时换元组、张量和标记，不固定 `c` 硬换下标（`Iut/Concrete/Ind1Invariance.lean:592`）。
同一重排保元组权；任何**单选**标记函数给同一全局 RHS（`Iut/Concrete/Ind1Invariance.lean:403`、`Iut/Concrete/Ind1Invariance.lean:680`、`Iut/Concrete/Ind1Invariance.lean:700`）。
这不允许将「每次固定一槽取 hull 再重排」交换成「每个元组先并掉所有槽再取 hull」；后者可以在不同元组利用不同槽。`Iut/Concrete/Literal.lean:23` 明说逆向步骤另待论证。
本地 `weightedSum_collectionChoiceBound_independent` 也只说两个固定槽的**加权和**相同，不给逐元组界（`LeanFormal/IUT/IUTIV/Estimates/StepVDistinguishedSlotAverage.lean:25`）。
若 `S` 是单点，重排 `τ` 在不同元组上必须来自所给的一次整数据操作；在每个目标元组各取最有利置换再拼成“同一次原求值”，并未给出这样的操作。
模型中 `productRegion` 允许分量取不同证人，不能反推出原 evaluation 逐元组独立。若只用投影半径，需给每个被采用的坐标一个真实全局输出的投影来源；未要求所有半径都由同一个输出达到。
**Ind2（模型选择）。** `factorAut` 取所有 `ℚ_p` 线性自同构中保持该因子 log-shell 格者；`tensorAut` 只取逐因子选择 `g_a` 后的张量积，不取任意线性混合（`Iut/Concrete/LocalConstruct/IndAut.lean:210`、`Iut/Concrete/LocalConstruct/IndAut.lean:219`）。
源码说明将原 `Ism` 的像放大到所有这类因子格自同构；这是建模的包含方向，不是已在那里给出了本地每条原群箭头的实现（`Iut/Concrete/LocalConstruct/IndAut.lean:206`）。
源码另有真正的 `tensorAut_subset_latticeAut`：保持**整张量格**的线性群可含非张量积映射（`Iut/Concrete/LocalConstruct/IndAut.lean:23`、`Iut/Concrete/LocalConstruct/IndAut.lean:233`）。有限处 `indAut` 选中间那一层，无穷处选 `archIndAut`（`Iut/Concrete/LocalConstruct/IndAut.lean:299`）。
本地 Step V 取参数 `Φ : Set (ArithmeticTensorTupleBlock … ≃ₗ[ℚ_[p]] …)`、一个标记乘数和 `x ∈ O_hol`，所得是集合（`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean:668`）。传 `Φ=全群` 不证明它是 `Ism`，传恒等也不证明覆盖全部像。
已有 `image_iUnion_tensorAut_packetReindex` 证明重指标共轭的是模型的 `tensorAut`（`Iut/Concrete/Ind1Invariance.lean:328`）。要改成 `Ism`，需从同一源群作用证明相应共轭，而非对该引理换一个群名。
**Ind3（模型选择）。** 具体有限区用 `s_a • J_c` 而非 `s_a • O_c`；这是把 log-Kummer 像落在 log-shell 的上半相容性用于建模（`Iut/Concrete/ThetaRegion.lean:37`、`Iut/Concrete/ThetaRegion.lean:173`）。
“落在壳内”不给壳中任一点的原像，也不给每个竖直迭代同一个双向等距。原全族的外界和一个有来源的内界应各自构造。
本地的生成商 `SourceMultiradialCarrier I` 有 Ind1/2 不变性和 Ind3 的单向性质；它的 possible image 是读数层的对象，而非 `Set T_c`（`tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean:56`、`tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean:75`、`tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean:115`、`tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean:126`、`tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean:136`）。
**建议。** 对真正要用的一条 `Ism`/置换箭头先给出带格的映射，并证明它作用于指定的源区域；直接使用 LANA 放大群可做外界，不能把放大群选出的内界证人倒送回原族。

### F.6 两个终点，各需要哪两个外侧不等式？
记 `Γ` 为固定的原 III.3.11 情形（含相对于初始数据的 theater 族）；`D` 为与 `Γ` 匹配的 LANA 数据。以下每行中的字母始终指同一匹配对，不随 `ε`、`p`、优化标签或比较方向换曲线。
`Qₒ(Γ) : ℝ` 是不再取 Ind1–3 的 q-pilot signed readout；`Θₒ(Γ) : ℝ ∪ {+∞}` 是全部原允许像在指定 holomorphic structure 上取 hull 后的 signed readout（`coord/IUT-TEXT/III.txt:10334`、`coord/IUT-TEXT/III.txt:10342`、`coord/IUT-TEXT/III.txt:10404`）。
原目标同时要求 `Θₒ` 有限及 `Qₒ ≤ Θₒ`；并非证明两者相等。`|log q|>0` 时，任一 `Θₒ ≤ CΘ·|log q|` 的实系数才推出 `CΘ ≥ −1`（`coord/IUT-TEXT/III.txt:10351`）。
**方向 A：从 LANA 的一次比较得到原 III.3.12（建议）。** 选定已知能提供中间不等式的 `S`（IV 或 literal），对任意 `Γ` 从其数据产生匹配的 `D`，所需一组充分条件是
\[
Q_o(\Gamma)\ \le\ L(D)\ \le\ H_S(D)\ \le\ \Theta_o(\Gamma),\qquad \Theta_o(\Gamma)<+\infty .
\]
第一箭头用符号化 q 的阶、权和 `2ℓ`；最后一箭头要把有来源的模型内区域或其读数放到**原** hull 下。两条不是同一侧语义的重命名。
中段可以由 `h : Cor312VariantHolds` 的 `h D` 假设给 IV，也可用专门证书给该 `D` 的 literal；`Corollary312Variant` 的定义自身不提供中段证明。
可用更小的内区域族 `B` 减少工作：直接证 `Qₒ ≤ v(B) ≤ Θₒ`，不要求整个 LANA 区域都是原像。例如仅选可追溯的整数据置换，无需证明每个 `factorAut` 来自 `Ism`。
`Θₒ < +∞` 是相反用途的上控制：要包住**全部**原允许像；少数 witness 的紧性、一个有限的 `H_S` 加上 `H_S ≤ Θₒ` 均不能推出它。
若另证 `Θₒ ≤ B_out < +∞`，才可在实数上继续；不得靠 `toReal` 抹去 `⊤`。原文明确单列这一步（`coord/IUT-TEXT/III.txt:10410`）。
已有本地标量供体同样只作单向运输：`Q_src ≤ Q_norm ≤ H_root ≤ H_tgt`，其中中段有证明体，外两段是参数（`tmp/sheaf/xif/paper/Mzk1ActualReadingTargetActual.lean:151`、`tmp/sheaf/xif/paper/Mzk1ActualReadingTargetActual.lean:159`）。它辨认的是该文件的 C3 读数，不自动辨认 `Θₒ`。
**方向 B：从原比较得到 LANA 的 ABC 前件（建议）。** 从任意给定 `D : InitialThetaData.{0}` 构造匹配的原情形 `Γ`，取该情形原比较的有限实值；足够的是
\[
L(D)\ \le\ Q_o(\Gamma)\ \le\ \Theta_o(\Gamma)\ \le\ H_{\rm IV}(D).
\]
左右两条外箭头都与方向 A 的用途相反。若原比较只控制 `Θₒ ≤ H_literal(D)`，则在这条链上只证明 literal；`H_IV ≤ H_literal` 无法接在其后。
若不打算证明完整原上界 `Θₒ ≤ H_IV`，也可直接从同源构造一个较小、足够的 `L₀`，证 `L(D) ≤ L₀ ≤ H_IV(D)`；这能供给 LANA，不因此给原 hull 有限性或原文定理。
从成员证明通到方向 A 时，记 `B_src` 为该源证人确实产生的分量区域；可证 `image e B_src ⊆ U_orig`，再比较送入原区域前后的归一化读数。抽象 `e` 连续并不保证它保 Haar 体积。
在方向 B，则要把用于下界的原区域送**入指定槽**的 hull，或直接比较那批允许输出与 `H_IV` 的读数；只能送入 literal 的全槽并，正好停在较弱终点。
只需要下界时无需局部同构：包含加单向的 Jacobian 控制也可以。反过来，即便局部向量空间恰好同维，若没有同一积分参考和权，`≤` 也没有确定的运输方向。
在依赖类型上，可将两个**待证**的覆盖分别写成如下签名草图；其中 `Same` 只承载 F.2 的对应，`Orig` 指原合格情形而非任意弱记录：
```text
forPaper : (Γ : Orig) → Σ D : InitialThetaData.{0}, Same Γ D
forLana  : (D : InitialThetaData.{0}) → Σ Γ : Orig, Same Γ D
```
不要求 `forPaper` 和 `forLana` 互逆；若只存在一个方向，在它所覆盖的范围报告结果。`∀ Γ, variant (forPaper Γ).1` 不是 `∀ D, variant D`。
若源字段居于更高宇宙，调用 LANA 的 `.{0}` 全称前须构造小模型并证明读数随同构运输；不可把 universe 限制误写成对原算术输入的限制。
本地的纯数值消费者可精确替代其中一段：对给定 `P : PaperSignedHull X Label`、`R : SourceTheorem311Realization l Label Choice`，`ActualOutput R` 是 `Theorem311Output R.input`（`tmp/sheaf/n8/closure/C9IUTBridgeOutput.lean:55`）。
`S2452PaperOutputFamily P R` 要以下同源对象，而不是一个 `q_le_hull` 证明（`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:124`）：
- `P_C : Set (ActualOutput R)` 非空，且为原最后 evaluation 的受限族。C9 的 `bridgePossibleOutputs` 按定义是单点集（`tmp/sheaf/n8/closure/C9IUTBridgeOutput.lean:60`）。
- `q : ℝ` 满足 `0 < q`、`q ≠ 1`，`Q_C = −|log q|`；必须识别为这次输入的 signed q 标量。这里不是把所有局部域的 q 元强转成一个实数。
- `ν_C : ActualOutput R → ℝ`，在 `P_C` 上与 `R.input.profile.logVolume z.source` 相等；每个 `z ∈ P_C` 满足 `ν_C(z) ≤ P.signedHullLogVolume`（`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:141`、`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:151`）。
- 覆盖是 `∃ z ∈ P_C, ν_C(z)=Q_C` 或 `∀ ε>0, ∃ z ∈ P_C, Q_C−ε ≤ ν_C(z)`（`tmp/sheaf/xif/paper/S1447ReportFMarkedTraceActual.lean:304`、`tmp/sheaf/xif/paper/S1447ReportFMarkedTraceActual.lean:308`、`tmp/sheaf/xif/paper/S1447ReportFMarkedTraceActual.lean:314`）。只许证人变，不许端点变。
加上逐输出上界后，用 `ε=(Q_C−H)/2` 排除 `H<Q_C`；现有消费者 `s2452_Q_C_le_of_upper_coverage` 与族上的 `Q_C_le_signedHull` 正做此事（`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:108`、`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:182`）。
此处 `Nonempty (S2452PaperOutputFamily P R)` 仍是接口，不是构造（`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:207`、`tmp/sheaf/xif/paper/S2452XiFCoverageActual.lean:216`）；还须证明 `P` 的读数与真实原 hull 同向相接，及 `R` 属于该 `Γ`。
原 (xi-e) 将 q 读数连到第 1 列的算术全纯结构；(xi-f) 才谈可能**输出读数**对该 q 的实现或逼近（`coord/IUT-TEXT/III.txt:10866`、`coord/IUT-TEXT/III.txt:10890`）。不能直接把输入标签写进输出集合。
若同一读数直接服务 LANA，足够证 `∀ D, ∀ ε>0, ∃ z∈P_C(Γ(D)), L(D)−ε ≤ ν_C(z) ≤ Hᵥ(D)`。改成原终点时则固定 `Γ`、用 `Qₒ(Γ)−ε` 与有限的 `Θₒ(Γ)` 夹住它；两个 `ε` 论证不要求两端相等。
若只构得一批可追溯的 `P₀ ⊆ P_C`，在 `P₀` 上构造 q 覆盖已经足以贡献下界；它仍不替代对整个原像并的有限性证明。这给小 PR 留出独立的验收点。
尤其不能把 `z`、`x ∈ U_c`、`ν_C(z)` 当成同一类型：第一项是结构化输出，第二项是其某个区域的张量点及成员证据，第三项才是一次完整求值的实数。

### F.7 一个失败例：混合元组丢掉标记后，读数不能恢复
沿用交接的曲线族 `k₀=ℚ(√13)`、`α=(1+√13)/2`、`E_d : y²+xy=x³+α^d`，这里 `d=3` 是族参数，不是模域次数。在分裂素数 3 上，`G` 是好位、`B` 是标记的坏位，各占模域权 `1/2`（`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1483`、`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1551`）。
固定 `ℓ=5`，故 `n=2`；第二行 `i.val=1, j=2` 有三个槽，默认标记 2。`ord₃(r_B)=3/10`，`r_G=1`；在延拓 `|3|=1/3` 的绝对值中 `|r_B^4|=3^(−6/5)`。
在**同一目标元组** `c_t=(G,B,B)` 上，取参考张量 `1` 和恒等作用。两种来源给如下对照（`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1541`）：

| 源元组、源标记 | 运到 `c_t` 的操作 | 在目标域因子投影所见的绝对值 |
|---|---|---|
| `(G,B,B)`，槽 2 即 `B` | 不动；乘 `incl₂(r_B⁴)` | `3^(−6/5)` |
| `c_s=(B,B,G)`，槽 2 即 `G` | `τ=(2,0)` 同时搬槽、元组和张量；目标标记为 0 | `1` |

第二行证据可以逐类型复述：由 `¬ IsBadK` 得好槽乘数为 `1`；积分元 `1` 进入 tensor log-shell；`id ∈ tensorAut`（`Iut/Concrete/ThetaLocalConstruct/Data.lean:294`、`Iut/Concrete/LocalConstruct/LogShell.lean:343`、`Iut/Concrete/LocalConstruct/IndAut.lean:253`）。
故在源 `c_s` 有 `1 ∈ U^{ {2} }(c_s)`。按 `image_thetaFiniteOn_ind1Reindex` 的正向，`c_t=c_s ∘ τ⁻¹`，目标上得到 `1 ∈ U^{ {0} }(c_t) ⊆ U^lit(c_t)`（`Iut/Concrete/Ind1Invariance.lean:592`）。
不能由此宣称目标指定坏槽区域没有别的点，也不能判断完整 IV 全球不等式为假。失败的是这样的函数：从一个不含槽和元组的标量，恢复两种有不同投影的指定来源。
本地 `sourceStepXILogVolume_eq` 说明任意两个 source choices 的标量相等，`sourceStepXIProfile.possibleImage` 是该标量的单点（`tmp/sheaf/xif/paper/S3138SourceProcessionProfileActual.lean:59`、`tmp/sheaf/xif/paper/S3138SourceProcessionProfileActual.lean:67`）。
若恢复函数 `f : ℝ → ℝ` 只通过该 profile 因子化，两次输入完全相同，输出必相同；但这里两个指定投影的对数相差 `(6/5) log 3 > 0`。加一次平均或取 Ind1/2 商都不能让 `f` 分辨它们。
这也解释为什么固定单槽重指标的等体积并不排除全槽并的局部增益：比较的不是同一对区域，`c_s` 的默认好槽不是 `c_t` 的默认坏槽。
可用同一算例复核归一化：第一、二行各占 `1/2`，每个元组分别占 `1/4`、`1/8`；不是把 `4+8` 个元组放在同一个均匀分布中。
按交接的整序见证，在一行全槽时只在所有可选位置皆坏时支付深度。两行的坏概率是 `1/4`、`1/8`，乘 `j²` 后才做行平均。
在该见证族上得到 `−(1/2)(x/4+4x/8) log 3 = −9/80 log 3`，其中 `x=3/10`；`q_s=−3/20 log 3`，余量 `3/80 log 3`（`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1551`、`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1565`）。
这些是有限算术证书的读数；它既没有算出原 `Θₒ`，也不是从一个已实例化的 LANA `D` 计算出包括所有壳、作用和无穷位的精确 `D.rhsData.rhs`。
精确缺口是把模型中的源点沿 III.3.10.2 的实际求值送进第 1 列原区域，而非再求这两个有理数的差（`coord/IUT-TEXT/III.txt:9069`、`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1943`）。

### F.8 建议给合作方的最小 PR：一条有来源的成员定理
**合并对象。** 固定 F.7 的一份合格输入，只交付一个 `τ=(2,0)` 的带标记求值，供本地 xi-e/xi-f 的输出族构造使用；LANA 一侧直接消费现有的 `thetaFiniteOn`。不改 `InitialThetaData`、`RHSData`、`OriginalInput` 或 ABC 主定理。
这个 PR 不需要先证一切模型的等价、不需要普遍地从任意弱 `I` 构造 LANA 的八个字段，也不需要先证明该固定输入已覆盖全部 q 读数。它需要以下可分别核对的交付：
1. **输入固定。** 提供同一算术样例的 `Γ₃`、`D₃` 及所用 `Match Γ₃ D₃` 的实际构造或精确已有声明；具体写出曲线、域塔、选位、坏位标签和 q 根身份。仅有交接中的数表，不算 Lean 实例。
2. **局部类型。** 定义源坐标 `(i,p,c_s,{2})` 与目标 `(i,p,c_t,{0})`；直接复用 LANA 的 `ind1Reindex`。在例上检查 `τ '' {2} = {0}`，且 `c_s ∘ τ.symm = c_t`，不以 `rfl` 假定两张量载体相同。
3. **原图。** 从这次初始数据和 theater 链给出实际的上/下 evaluation、左右 Kummer 箭头，标明源与靶的列、嵌入和标记，并在各自的结构上证明方块相容。
   现有 `SourceKummerEvaluationSquare` 接收这四箭头及 `commutes`，不是生成这一例的算法（`LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean:347`）；仅提交该结构体的参数化包装不通过。
4. **区域证人。** 从原图产生 `z_τ`，以及它是本次原允许 evaluation 的证明；从 `z_τ` 得到第 1 列的区域及带标记比较映射。不得将 `allowed` 定义为“满足所需半径”或指定点的单点集。
5. **输出判断。** 给出 `E_τ(1) ∈ U_{2,3}(Γ₃)` 的类型正确版本；若 `E_τ` 的余域只是一项分量，则提供一个原 packet 成员及其投影等式。固定一个坐标的类型不等于整个 `IQ` 的类型。
   一个可复核的签名草图如下；名字是建议的，`Z` 是包的点，`zτ` 是产生一族区域的原输出。`regionAt` 与 `coordinate` 的定义均须来自实际对象。
```text
zτ        : ActualOutput R₃                       -- 原求值生成
eligibleτ : IsAllowedEvaluation Γ₃ zτ            -- 由该求值的来源推出
Eτ        : T_src → OrigComponent Γ₃ 2 3 c_t     -- 带标记的比较；须与求值相容
Z         : OrigPacket Γ₃ 2 3                    -- 不是实数，也不是结构化输出 zτ
memZ      : Z ∈ regionAt zτ 2 3
coordZ    : coordinate c_t Z = Eτ (1 : T_src)
```
   其中 `T_src` 是 `c_s` 的张量载体。`memZ` 加 `eligibleτ` 给出并集成员；`coordZ` 把同一个成员连到源参考 `1`，并应校验所考域投影的绝对值至少为 1。
   若直接构造到原包的 `E_τ`，可取 `Z := E_τ 1`；若只得到 `E_τ 1 ∈ pr_{c_t}(U_{2,3})`，需保留该像成员的原包见证和允许输出来源，不能写成 `E_τ 1 ∈ U_{2,3}`。
6. **不改前件。** 固定例的公开回归定理不接收 `hmem`、`hcover`、`hupper`、`Hₗ ≤ Hᵥ`、`XiPrinciple` 或 `Cor312VariantHolds`；`Match` 也不许包含它打算证明的成员或数值结论。
   如尚不能产生 `z_τ`，可以提交精确的设计缺口；不能让调用者供应“已准许的求值且其像为该点”后把条件定理记为这个 PR 的通过结果。
评审可逐项做反向检查：把标记从目标好槽改回默认坏槽时，引用的源元组也必须改变；如果证明项丝毫不依赖这两者，应回查它比较的是不是标量常值。
再核一次余域：本地 `OrigXiFPaperOutputRegion j` 是预先定义的 tensor integral region（`tmp/sheaf/xif/paper/OrigXiFIndeterminaciesActual.lean:124`）。对这个静态集合证明不变性不够，必须连到 `regionAt zτ`。
如果选择验证一整个区域像的包含，保留源域的量词 `∀ x ∈ U^{ {2} }(c_s), …`；它能推出点级验收，但最小 PR 不反过来要求从单点推得整区域包含。
**验收的边界。** 固定例的 `memZ` 通过只算来源成员。交接还列有原读数识别、对全部实际输出作统一上界两项（`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1955`）；不列入最小 PR 的已证成果。
若下一批要验收固定输入的**整体下界**，才需补足其余获益元组、第一行、各域投影/参考格、arch 项和行平均，或给出同源的直接有向总量证书。不得用一个裸点宣告正测度或完成 `coverage`。
若要验收**原 III.3.12**，逐个合格 `Γ` 交 F.6 方向 A 的有向链或等强的原证据，另交全族的有限性。`sourceHullVolume_eq_top_of_degreeFaithful` 说明在其值层假设下有限性甚至会失败（`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean:428`）。
若要验收 **LANA 终点**，测试必须能按原类型 `intro D` 得 `Corollary312Variant (concreteVariantData D)`，不额外接受 `LL D`、同素数上方阶一致、单一模域位或“无 arch”之类前提；辅助格子若必需，应在证明内从该 `D` 得到。
一条独立核查路线是保留现有 `variant_of_thm311` 的真实前件 `Thm311 L K` 与 `XiPrinciple K`（`Iut/LogLink/Thm311.lean:214`）；`thm311_model` 有证明体，而 `xi_iff_ss` 的等价本身不给 Step (xi)（`Iut/LogLink/Thm311.lean:190`、`Iut/LogLink/Thm311.lean:219`）。
`Hₗ(D)` 的证书若没有通向指定槽的上界，提交时应命名为 literal 结果；不能把 `concreteVariantData` 改指 `concreteVariantDataLit` 来通过相同的文本测试。
正式验收须锁定目标及其引用定义的版本，按所在仓的构建规程验证，比较目标类型、检查传递公理，只允许 `propext`、`Classical.choice`、`Quot.sound`；由独立语义复核确认选位、标记、权重与原输入范围没有变。
本附篇交付的是字段与证明义务的设计；`statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 均未运行。固定例的第一步仍是构造上述 `z_τ` 和它的区域成员，而不是重新计算模型读数。

<a id="local-foundations"></a>

## G. 两个仅本地路径的实际用途：Kummer 芽的乘法与覆盖分支的粘合

这两例的证据都是另一个文件里的证明调用：一个把代表元的等式变成 Kummer 芽的乘法律；另一个把沿路径选出的页变成满足分支粘合的目标点。
2026-11-20 直接核对两个工作树；本仓 HEAD `a997af4b1cb2339d1e7403ef0781a16f809f4476`，LANA HEAD `553076af459e7a401bfee63a4607814d1c854477`。
下列 `路径:行` 默认指本仓，标「LANA」时从 LANA 根起算。两个供体都属于附篇 D 的 256 个单方路径；「仅本地」不表示原创，也不表示上游没有类似定理。

### G.1　连续 H¹：为什么两个单位的乘积给出两个芽的乘积？

**供体的结论。** `Iut/Foundations/ContinuousH1.lean:900` 的 `ContinuousH1GermRepresentative.Equivalent.of_equal_on` 给出一个充分条件：
两个代表元若限制到同一开子群 `U` 后逐点相等，则它们等价，因而在芽的商中给出同一个类。
这里 `G`、`A` 都是拓扑群，`G` 通过自同构联合连续地作用于 `A`（`Iut/Foundations/ContinuousH1.lean:27`）。
每个代表元含一个开子群和其上的连续 1-余循环；必须给出 `U` 含于两个定义域的证明（`Iut/Foundations/ContinuousH1.lean:595`）。
一般的等价只要求在某个这样的 `U` 上相差同一个余边界 `a`（`Iut/Foundations/ContinuousH1.lean:803`）。
在逐点相等的情形证明取 `a = 1`；声明明确移去了系数交换的假设（`Iut/Foundations/ContinuousH1.lean:895`、`Iut/Foundations/ContinuousH1.lean:911`）。

**实际消费者。** `LeanFormal/IUT/IUTII/Kummer/CanonicalKummerMap.lean:186` 的 `UnitKummerRootRealization.mul_germ` 证明 `(first.mul second).germ = first.germ * second.germ`。
这一层才用离散交换群 `B` 和 `G` 的连续自同构作用；两个值各被自己的开子群固定，并各自带一套相容有理根（`LeanFormal/IUT/IUTII/Kummer/ContinuousKummerGerm.lean:183`）。
证明在 `LeanFormal/IUT/IUTII/Kummer/CanonicalKummerMap.lean:194` 点名调用 `of_equal_on`，取 `U = firstSubgroup ⊓ secondSubgroup`。
`LeanFormal/IUT/IUTII/Kummer/CanonicalKummerMap.lean:210` 再用 `mul_ratioUnit` 验证交集上代表元逐点相等；`Quotient.sound` 将等价变为芽相等。
前一步处理根的乘法，供体处理如何过商，两者不能互换。`mul_germ` 本身只要给定两套根，不要求对 `B` 的所有元素选根。
进一步假设 `[RootableBy B ℕ]` 后，`CanonicalKummerMap.germ_mul` 在 `LeanFormal/IUT/IUTII/Kummer/CanonicalKummerMap.lean:244` 调用 `mul_germ`；
`LeanFormal/IUT/IUTII/Kummer/CanonicalKummerMap.lean:257` 据此装配从 `B` 到以 `Hom(ℚ/ℤ,B)` 为系数的连续 H¹ 芽的乘法同态。

**与 LANA 对照。** LANA `Iut/EtaleTheta/KummerClass.lean:173` 的 `decomposition_kummer_etaleThetaGerm` 比较的是给定 Tate 参数下的一个具体 θ 函数芽。
它固定非零层数 `n`、非零 θ 值、满足局部环与剩余映射相容条件的赋值子环，以及两侧 Kummer 根条件（LANA `Iut/EtaleTheta/KummerClass.lean:157`、`Iut/EtaleTheta/KummerClass.lean:164`）。
结论是在该分解群上，函数芽的 Kummer 类经限制及系数约化后，等于剩余值的 Kummer 类经分解映射拉回的类；两侧的 `ContH1.map` 见 LANA `Iut/EtaleTheta/KummerClass.lean:175`。
本仓的「芽」按缩小开子群取商，LANA 此处的「芽」是一个局部函数。要比较输出，得先固定同一分解群上的代表和系数映射；缩小后相等不能反推原群上相等。

**未证的原文步骤。** IUT II 例 1.8 的群侧构造不是定义 4.9(i) 的 Frobenioid 比较：后者对非平凡局部域群要求群侧与对象侧单位之间的同构轨道（`coord/IUT-TEXT/II.txt:10060`、`coord/IUT-TEXT/II.txt:10064`）。
上述同态既未在实际 Frobenioid 对象上求值，也未把求值与群侧 Kummer 类识别；消费者自身区分了这些义务（`LeanFormal/IUT/IUTII/Kummer/CanonicalKummerMap.lean:284`）。
群侧根比构造的来源还应保留消费者的说明：`LeanFormal/IUT/IUTII/Kummer/ContinuousKummerGerm.lean:12` 明记参考 `promachina/iut-lean@3de1d7c1`。

### G.2　覆盖的页：为什么边上选的点与顶点上选的点能粘合？

**供体的结论。** `Iut/Foundations/SourceFiniteSheetUniversalLift.lean:372` 的 `UniversalLift.vertexSheet_eq_transport_of_coincidence` 处理普适半图覆盖上的一次关联。
输入是半图 `base`、类型 `Sheet`、每个边分支的置换 `transport e b : Equiv.Perm Sheet`，以及根顶点和初始页（`Iut/Foundations/SourceFiniteSheetUniversalLift.lean:27`、`Iut/Foundations/SourceFiniteSheetUniversalLift.lean:354`）。
对提升后的边 `e`、分支 `b`、顶点 `v`，前提是覆盖中的 `coincidence e b = some v`；结论是 `v` 的页等于把置换 `transport e.edge b` 作用于 `e` 的页所得的页，其中 `e.edge` 是基底中的边。
这里没有 `[Finite Sheet]` 或 `[Fintype Sheet]` 假设；「有限层」是下面应用的背景，不是这条引理的额外前提。
页由约化关联路径逐步搬运（`Iut/Foundations/SourceFiniteSheetUniversalLift.lean:242`）。在边到分支这半步置换为恒等，分支到顶点那半步才施给定置换。
同一文件也用此等式验证覆盖态射 `UniversalLift.hom` 的关联条件（`Iut/Foundations/SourceFiniteSheetUniversalLift.lean:462`）；`projection_comp_hom` 证明再投影就是原普适投影（`Iut/Foundations/SourceFiniteSheetUniversalLift.lean:466`）。

**实际消费者。** `Iut/Foundations/SourceTemperedTargetSheetLift.lean:96` 取目标覆盖在根顶点的点集作 `Sheet`，再把目标的分支粘合写成这个集合上的置换。
该文件的 `TargetSheetLift.branchCarrierEquiv_edgePoint`（`Iut/Foundations/SourceTemperedTargetSheetLift.lean:346`）比较的是目标覆盖中的实际点：
代表元修正作用在所选顶点处的点上，所得结果等于把所选边上的点沿目标的分支粘合等价传过去的结果。这里没有假设代表元修正是恒等。
证明在 `Iut/Foundations/SourceTemperedTargetSheetLift.lean:389` 直接调用 `vertexSheet_eq_transport_of_coincidence`，随后用 `transport_apply_of_some` 展开实际置换（`Iut/Foundations/SourceTemperedTargetSheetLift.lean:405`）。
下一层 `GeometricDomination.correctedTargetPoints_at_branch` 在 `Iut/Foundations/SourceTemperedGeometricDomination.lean:542` 调用这个点等式；分支自然性据此逐侧拼合。
在基底顶点、边均可数，且给定能分裂目标的带点 Galois 层和根处目标点时，`GeometricDomination.hom` 给出从该层普适覆盖对象到目标的态射。
输入在 `Iut/Foundations/SourceTemperedGeometricDomination.lean:73`；态射及其自然性字段在 `Iut/Foundations/SourceTemperedGeometricDomination.lean:758`。分裂层是此步的输入，不是路径提升的输出。

**与 LANA 对照。** LANA `Iut/Anabelian/Tempered.lean:141` 对域上的模型 orbicurve 取其 presentation 的 `canonicalTemperedPi1`。
LANA `Iut/Anabelian/Tempered.lean:148` 给出 `Orbicurve.tempToEtale : X.temperedPi1 →* X.genuinePi1`；其连续性由两个连续映射复合而得（LANA `Iut/Anabelian/Tempered.lean:153`）。
本仓引理的输入是带分支置换的覆盖，LANA 同态连接的则是模型曲线的两个基本群。要把逐页构造接到这个 API，须指定同一覆盖的对象与纤维，并检验它们与分支粘合相容。

**未证的原文步骤。** 供体定位为《Semi-graphs of Anabelioids》命题 3.6(ii) 证明中的路径提升（`Iut/Foundations/SourceFiniteSheetUniversalLift.lean:15`），不是单凭一次提升就得到覆盖分类。
例如，从几何态射恢复作用态射是另外的论证，见本仓 `Iut/Foundations/SourceTemperedActionCoverEquivalence.lean:929` 的 `actionCoverFunctorFull`；不能把「本引理不证」写成「仓库没有」。
对 IUT III.3.10.2 的交接更具体：图上的 `Sheet` 不是带整结构的 θ 输出载体，`transport` 也未被识别为原允许 evaluation。
固定 `p=3, ℓ=5, d=3`、目标 `(G,B,B)`、换位 `(2,0)` 时，所缺仍是从同一输入构造 `E_τ` 并给出 `E_τ(1) ∈ U_{2,3}`（`coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md:1945`）。

### G.3　复核位置

| 仅本仓有此路径的供体 | 本次磁盘原字节 SHA-256 | 外部证明体的调用行（本仓） |
|---|---|---|
| `Iut/Foundations/ContinuousH1.lean:900` | `1D2964C84D957B03A7C51BA72924C315C9FBCADFBCB661FD5F35F3EB25C1A6EF` | `LeanFormal/IUT/IUTII/Kummer/CanonicalKummerMap.lean:194` |
| `Iut/Foundations/SourceFiniteSheetUniversalLift.lean:372` | `28715B2E6AC75E5AF17B9F274EFD6770DBDBCEB6636CB60C5BE52B000AE8C6B0` | `Iut/Foundations/SourceTemperedTargetSheetLift.lean:389` |

本轮只核对源文件中的声明、假设、证明体和调用点；未运行 Lean。`statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 本轮均为 `NOT_RUN`。
