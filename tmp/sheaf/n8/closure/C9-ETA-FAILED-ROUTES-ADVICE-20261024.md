# C9 / ETA 失败路线复核与下一步建议

日期：2026-10-24（Asia/Shanghai）。任务 ID：N8-C9-ETA-FAILED-ROUTES-ADVICE。owner：本 chat root，按用户要求单人研究、不写 Lean。本包只审查最近失败路线及其直接消费者；没有全仓重新审计，没有操作其他 owner 的代码或调度。

消费者：n8-c9-p6 / n8-p6-source-route / n8-s3-c9；当前具体文件为 P6L、EtaRssLogShellLine、EtaAnabAtFPlace、EtaRssComparisonReduction、EtaFPlaceSignedComparison、EtaQToFShellActual。SHEAF 阶段：1。集成/构建：本轮不适用。精确读取版本见同目录 C9-ETA-FAILED-ROUTES-EVIDENCE-20261024.json。

## 结论

最近已核的失败多数发生在论文对象被改写成 Lean 目标时，而不是已经准确实现论文对象后遭遇核心数学反例。应保留正确的局部域、商、Haar、log-shell 供体；撤下错误等式和弱接口，不继续通过换符号、换包装、补非零 guard 来抢救它们。

继续研究双构造比较的方向有意义，但当前若干 ETA 文件还没有实现 LANA 意义的两个 η。建议优先纠正三个基础对象：区域型 Adm、变化区域的体积商 Rss、原生 q 的区域表示。之后主攻实际 BPS→Kummer/evaluation→区域作用，而不是反复包装最终不等式。

本记录也澄清上一轮自己的措辞：不能“未经证明提前合并实直线”，不等于禁止用 ℝ 作坐标或禁止两个线使用同一底层类型。先各自构造、证明坐标/缩放关系，便可以在坐标中计算。类型名称不同不构成相容性证明。

## 1. Adm 的失败是量词与对象错误

P6L.lean:46 把 localLog 定义为元素的 log norm；:53–61 要求每个地方区域内 Haar 几乎处处满足 localLog=0。它强迫区域几乎落在单位球面及零点中，因而在 archimedean 地方与正质量冲突。已登记的 no-go 精确否定这个定义，不能推广为论文所需区域不存在。

III Prop.3.9(iii)，May 2020 PDF p.117 的原条件是：对全局区域族，除有限多个有理地方 v_Q 外，该分量的区域 log-volume 为零。正确形状为

    ∃ finite T ⊆ V_Q, ∀ v_Q ∉ T, g_vQ(R) = 0,

其中 g_vQ 是该有理地方完整 packet/procession 的正确局部读出；不是 ∀v ∀ᵐx, log‖x‖=0。把所有 tuple 贡献先行分别强制为零也可能更强，必须按原文的分量层级写。

对一个局部块，固定实际参考区域 O 后，可示意写为

    ν_O(R) = (log μ(R) − log μ(O)) / d.

这只是局部公式，完整 g_vQ 仍须原文 tuple/地方/procession 权重。源 direct-product/紧性/径向条件及正有限质量保留。参考 O 从源积分结构取得，不能随待测 R 选择。

建议：不再在“元素 log 几乎处处为常数/零”的方向寻找修补，也不通过删除 archimedean 地方回避问题。P6AdmRedesign 的正有限测度部分可复用，但 RelaxedP6Readout:129 的 support 还需要证明确实覆盖所有非零贡献，weight/dimension 必须绑定源对象且具有正确符号。任意选一个有限 support 不是全局有限支撑定理。

## 2. 最新两份 Rss 都是单点数据，不是实直线

EtaRssLogShellLine.lean:44 与 EtaAnabAtFPlace.lean:64 的结构均把所有数据字段固定：shell 等于一个指定 shell，volumeIndex 等于一个指定自然数，logVolume 等于该数的 log。

**本轮自然语言证明：** 固定 X，取两个这种结构的元素。shell_eq 给出 shell 相等；volumeIndex_eq 给出 index 相等；logVolume_eq 再给出 logVolume 相等。余下字段全是命题证明，proof irrelevance 消除差别。因此该类型为 Subsingleton；已有 canonical constructor 又使它非空。于是任何两个到该类型的函数都逐点相等，所有函数均常值。

所以 EtaRssComparisonReduction 中 ηQ=ηAnab 的比较即使无 sorry 完成，也可以完全没有算术内容；要求该 Rss 非平凡则与当前定义矛盾。更换 Fmod/F 地方不会改变这个结构性问题。

LANA 固定版本在 `sub:theMainGoal` 把 Rss 描述为 volume container 中 adelic measurable regions 按相同体积的等价关系取商，q-pilot 对应对角嵌入的 q_v O_v 区域类。该表述中的精确区域范围、实线运算和主文对应仍须展开，但足以排除“一个固定 shell 的记录”以及“shell 中的一个 p-adic 元素”作为 Rss 本身。

建议：把当前结构当作一个参考 shell 的计算记录；真正的 Rss 让合格区域 R 变化，再按源规定的同体积关系取商。要用实坐标，则构造读出并证明它下降到商、与目标实线结构相容；不得假定商自动是完整实直线，更不得借任意域上所有集合实现它。

## 3. 固定 shell 的体积差不应等于 q-pilot 的体积

EtaFPlaceComparisonProof 已用正确的符号计算否定

    log(index I) = q 的 signed log.

EtaFPlaceSignedComparison:44 改为 log(index I)=−Q。它消除了前一个符号矛盾，却没有建立任何源关系；不能因为两边现在同号就把等式当成新的源目标。本轮不声称改符号后的等式对所有源输入都假，判断是：尚无源依据，不能作为主攻比较。

已有生产 LogShellVolumeConsumer.lean:55、:64 明确给的是

    μ(I) = index(I) · μ(O),
    log(index I) = log μ(I) − log μ(O).

这是固定局部域的参考体积差。q 的赋值数据应进入 q 作用后的区域，而不是被要求等于该固定差。

### 可执行的正向小目标：区域缩放与参考校准

固定同一个实际非阿基米德局部域 K、正有限 Haar 质量的参考 O 与 shell I、非零 q。令 m_K(q)>0 为乘 q 的 additive Haar 缩放模，d>0 为已确定的归一化次数。设 μ(I)=N μ(O)。则

    ν_O(qO) = log m_K(q) / d,
    ν_O(qI) = log m_K(q) / d + log N / d,
    ν_I(qI) = log m_K(q) / d.

证明：μ(qA)=m_K(q)μ(A)，正有限性允许取实 log；展开 log 乘积并减去相同参考项。第二式再用 μ(I)=Nμ(O)，第三式减去 shell 自身的参考体积。所有等式都在一个已指定框架中，不涉及跨 Θ-link 的未证识别。

这把现有 logShellVolumeConsumer.index 放到了正确位置：**校准项**。后续再用独立的 norm/degree 定理把 log m_K(q)/d 与源 q signed readout 识别。若源 q 采用根、基变换或 tensor 对角嵌入，保留对应次数与权重，不直接用裸 q 范数代替。

复用候选：LogShellVolumeConsumer 的实际 Haar/index 公式；FinitePlaceNormalizedUnitScalingLogVolume 的 fractional-lattice/scaling 结果（它的具体 local-generator、valuation 和 common-exponent 假设仍需逐项满足）；既有 ArithmeticQPilotLogVolume 和基变换供体。现有文件被读取，未重新编译，本轮不声明已有一般 q 缩放 theorem 已接通。

这只是原生 q 一侧的区域校准，不是 Cor.3.12，更不能藉此预设 q 区域已经是算法允许输出。

## 4. 不应强求 q 的单位部分 log 非零

EtaQToFShellActual 实际分解 q=uπ^n，再对 u 取 log，并将非零性列为 named obligation。DVR 分解是有用供体，但只保留 log(u) 会丢掉 n；n 正是 q norm/degree 的重要数据。

局部反查：取 q=π^n，n>0，则 u=1，log(u)=0，然而 q 的赋值和对应区域体积并不平凡。这是局部模型对“仅凭 |q|<1 可推出 log(u)≠0”的反例，不是对全部合格 IUT 输入的反例。若某源步骤真的要求非零，必须给原文依据；不能把它作为排除常值实现的通用 guard。

建议：q 一侧优先保留 qO（完整 packet 中的对角表示）、分式理想类或实际乘法作用；完整 q=uπ^n 关系可以辅助计算。不要以 q→单个非零 shell 点作为强制中间目标。

另见 C9QPilotRegion.lean:39 仍为 singleton，:74 的 selected places 仍为单个 bad place。它们可以是局部候选数据，不是完整 global q-pilot 区域。新 ETA 文件引用它们，不会自动获得完整 source/global 含义。

## 5. “非退化”应由源结构保证，不增加无依据的新结论

EtaNondegeneracyGuards 中的 `LinesSeparated := ¬ Nonempty (Rval = Rss)` 不是跨框架相容性的表达。同一个底层 ℝ 可以携带不同指定构造/坐标；不同包装类型也可隐藏同一常函数。

同样，Theta≠0、reference≠region 不应作为每个源输入的强制条件。参考区域自身的归一化体积当然应为零；某个正确 hull 的读出也不能仅凭“怕退化”排除零。真正需要的是指定源区域、独立固定参考、正确缩放律、实际 q 校准，以及 η 的相应线性/同构性质。

若已证明 η 是非平凡一维实线间的线性同构，其非恒定性应作为后果。若两条独立线性映射定义在同一一维实线上，并且实际 pilot 非零，则在该 pilot 上相等可以足以推出全映射相等；不能笼统禁止 pilot-level 比较。错误在于未构造两条源映射，却把一个任意函数的固定点条件命名为比较。

## 6. 有名的存在性缺口仍可能过弱

EtaAnabAtFPlace.lean:104 的 `kummerVerticalAtFActual` 只是 `Nonempty VerticalLogKummerCorrespondence`，其正文不引用 X、选定地方或当地 shell。原结构中的 D、F_m、log、kummer 全为参数。

**本轮自然语言反查：** 取 D 和每个 F_m 都为单点有序集，所有映射取唯一映射，upperSemi 由自反性成立。这样即可满足抽象 Nonempty，但没有任何 IUT 源数据。这不是给项目提供实际实例，而是说明当前缺口不能代表指定地方的源构造。

此外，列出 Ind1/2/3 的 enum，或把一个有限模型的 Ind 等式放到同时带有 shell 的 record 中，不会建立这些 Ind 对该实际 shell/区域的作用。必须有实际作用及其与表示/读出的交换或单向控制定理。

建议将核心研究任务指向具体源复合：给定实际 BPS 和源允许的 realization，如何经 cyclotomic/Kummer/evaluation 构造 Gaussian monoid 的作用，并组装为 volume container 中的输出区域。然后比较两条构造；不要先求任意 VerticalLogKummerCorrespondence 的 inhabitant。

## 建议的执行顺序与停止边界

| 顺序 | 准确交付 | 验收出口 |
|---|---|---|
| 1 | 修正区域型 Adm 的量词，区分 point log 与 region log-volume；固定参考和真实有限支撑 | 原文逐项对应；archimedean 正质量区域可合法进入；不要求点上 log 常值 |
| 2 | 真正变化的区域类 Rss，现有固定 shell record 降为供体 | 不能由 proof irrelevance 得到所有 Rss 元素相等；读出下降及实线结构分别证明 |
| 3 | 原生 q 的 qO/packet 区域与 Haar 缩放、shell 校准 | 上述三个局部公式及源 q norm/degree 识别；清楚标为局部，不包装成 global |
| 4 | 固定源 BPS 的实际 Gaussian/Kummer/evaluation 作用与允许选择 J | 箭头载体、单位和值群部分、地方/列标签明确；不是自由 map 或无 X 的存在性 |
| 5 | 同一目标侧的 η 比较、实现区域属于允许族、hull 上界 | 原生与算法链独立定义；J 的允许性不以待证等式定义；最后回到 C9 |

1–3 消除的是现在反复出现的对象错误，不要求先重建整个 IUT。4 是真正的源构造研究；若缺少输入 theorem，应登记实际最小缺口，不再追加同义包装。5 未获得此前证据时只能作为正确陈述/待证目标，不能统计为闭合。

建议停止的具体尝试：旧元素级 a.e. log 条件、固定 shell discrepancy=±q 读出、互逆缩放冒充两条 η、单点 Rss 上的 η 比较、只从 q 的单位部分强求非零、无源依据的类型不等/Theta 非零 guard。保留源正有限测度、局部域比较、商、shell/index 及确切 no-go 作为供体和反查记录。

对未来每一个新证明目标先做一页数学检查：两边究竟是元素/区域/体积类/数值中的哪一层；每个量词在哪个集合；哪些数据随 q/允许选择变化；证据是否绑定实际 X。允许在精确前提上自顶向下试证，不设置全项目停工；只停止已经没有来源的目标。

## 文献、状态与版本

- IUT III，May 2020，Prop.3.9(i)–(iv)、Remark 3.9.5、Cor.3.12；本次定向核对 p.117 的全局条件。官网链接：https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf。
- LANA report，commit 293bdd89463473ae13d40834d70fb4b7ba81da1f，`subsub:actionOfTheta`、`sub:theMainGoal`、`sub:SSEtaStructure`；本次通过 GitHub 工具核回固定版本 2502–2541 行。链接：https://github.com/katobungen/LANA_report_202607/blob/293bdd89463473ae13d40834d70fb4b7ba81da1f/LANA_report_202607.tex。LANA 解释作为源字典，不能替代主文等价性和核心比较证明。
- 本轮给出的 Subsingleton、抽象单点 correspondence、局部 q=π^n 反查和缩放校准为 root 自行展开的自然语言数学；没有声称已被 Lean kernel 检查。
- statement_compiles、proof_body_checked、kernel_closed、comparator、Project build、独立审查：均未运行。target_accepted=false。
- 本包交付为具体诊断与可执行建议；不改其他 owner 的 Lean/路线文件，不宣布本 chat 以外的任务停工。后续由相应 owner 依据记录同步。
