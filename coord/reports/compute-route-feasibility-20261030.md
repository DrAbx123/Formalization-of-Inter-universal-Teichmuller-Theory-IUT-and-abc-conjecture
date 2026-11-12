**把当前缺口转成大规模逻辑搜索或相消计算：可行性调查**

2026-10-30；单线程；SHEAF 阶段 1；未启动证明搜索、求解器、训练或 Lean 构建。源路线沿用用户确认的 Formalization of IUT（2026）§4 与 Essential Logical Structure（2024）Stp1–8。本文承接[补充路径取舍报告](D:/lean/coord/reports/supplement-gap-priorities-20261030.md)，专门评估新的计算入口。

**有值得试的计算路线，但目前最有针对性的并不是盲目展开更多高阶项。优先评估“完整读数的关系消元与正性证书”和“源算法不变量的机器搜索”。** 两者有机会绕开某些过强的中间构造要求；前提是把真实源对象及其已知关系正确送入计算。当前尚未完成这个转化，不能宣布核心缺口已经变成一个只差算力的题。

用户所说的“断点被扩展成峡谷”在现有记录中确有对应：很多正确的条件定理把同一责任转交给新字段；证明树增长，但源输入到最终比较之间的未证条件没有消失。这不证明所有路线都无效，却足以要求新的计算方案提供一项此前没有的证据：**一个从更早源数据得到、可以直接代入当前消费者的证明或见证。**

以下文献说明算法本身的能力；将它们用于 IUT 是本报告提出的研究方案，不是这些论文已经给出的 IUT 结果。

**一、AI 改变了什么，哪些事情原本就能计算。**

大规模符号相消并非大模型出现后才可能。Koutschan、Kauers、Zeilberger 的 q-TSPP 证明在 2011 年已经用猜测递推、非交换算子消元和可核验恒等式证书完成困难的行列式求值。这里真正可借鉴的是“搜索可以复杂，结果必须有精确证书”。[原论文](https://arxiv.org/html/1002.4384v2)

AI 增加的是选择引理、发现表示、提出辅助函数和搜索策略的能力。AlphaProof 使用 Lean 环境和围绕目标生成的变式进行强化学习；其竞赛评价仍由专家确定正式题面。它提供了扩大证明搜索的实例，不提供“自然语言源语义自动正确”或“IUT 困难只是搜索量不足”的结论。[AlphaProof 原论文](https://www.nature.com/articles/s41586-025-09833-y) LeanDojo 则给出从数学库检索前提并与 Lean 交互的公开研究路线。[LeanDojo](https://arxiv.org/abs/2306.15626)

因此，不宜预设“必须找到 AI 以前不可能的方法”。更实用的标准是：以前人工不愿或无力搜索的表示、证书和中间引理，现在能否通过 AI 提案、符号计算及内核验证组合起来获得。这里的可行性不等于已具备 AlphaProof 的训练系统或算力。

**二、计算要接走的具体困难。**

固定同一合格源数据 C，用 Q_C、H_C 分别指锁定目标中的有符号 q 读数与 hull 读数；这里只写示意目标 Q_C ≤ H_C，不重新定义它们。直接消费者 [ThetaLinkActual](D:/lean/tmp/sheaf/xif/paper/ThetaLinkActual.lean:166) 仍要求 link_implies_inclusion；[最终入口](D:/lean/tmp/sheaf/xif/paper/PaperXiFCompileGate.lean:69) 消费这份数据。

目前应区分三种困难：

| 困难 | 计算可能承担的部分 | 计算不能凭空补出的部分 |
|---|---|---|
| 实际算法输出与固定 gluing 的来源 | 搜索源操作的复合、辅助引理、正确的关系表示 | 一个任意 strip 或 Prop 字段不是实际源输出。 |
| HDD、determinant、权重、参考项与 log-shift 的读数 | 消去大量中间变量；搜索线性、代数、递推或不变量证书 | 不同标签、测度或归一化的值不能因名字相同就合并。 |
| 允许像族扩大之后的最终有符号比较 | 从真实源约束直接推出比较，或构造合格输出/逼近见证 | 有限样本、任意独立 q/Theta 模型、强行假定 hull 身份不能替代源条件。 |

没有必要把“构造一个指定的完整 q→hull 映射”或“找到 exact output”当唯一途径。已有 [FinalEvaluationQMark 审查](D:/lean/tmp/sheaf/n8/closure/C9-FINALEVALUATIONQMARK-DEPENDENCY-AUDIT-20261026.md:17)明确允许单侧逼近或同一 C 的直接有符号证书。因此，新方法可以只构造最终比较真正需要的不变量；但必须证明它读的是原先的 Q_C、H_C。

**三、优先候选 A：把完整读数比较变成关系消元与正性证书。**

设能从源对象提取一组读数 x(C)，以及有独立依据的关系

\[
 r_i(x(C))=0,\qquad s_j(x(C))\ge0.
\]

尝试搜索并核验一个恒等式

\[
 H_C-Q_C
 =\sum_i a_i\,r_i(x(C))
  +\sum_j b_j\,s_j(x(C))+c,
 \qquad b_j\ge0,\quad c\ge0.
\]

线性情形是精确线性代数/线性规划的证书问题；多项式情形可以寻找理想成员表示，或用平方和作为非负乘子。系数和证书应恢复为精确数并核验，浮点优化结果只作为候选。这个公式是候选证明形式，**本轮没有求出本项目的 a_i、b_j 或证书**。

它的潜在价值在于：许多中间参考项、局部缩放、determinant 项可以一起消去；最终只保留目标差值和已有非负项。若成功，不必先证明每个中间对象的一个过强的逐点等式，也不必额外构造并非目标所必需的 exact witness。若整个求和只证明原有的“假设最终比较，则最终比较”，则没有价值。

本地已有具体基础：

- [linarith 的实现说明](D:/lean/.lake/packages/mathlib/Mathlib/Tactic/Linarith/Frontend.lean:37)采用不受信的证书搜索，再通过规范化和有序环推理验证；默认使用稀疏 simplex。无需重新发明线性收尾。
- [Farkas/分离定理](D:/lean/.lake/packages/mathlib/Mathlib/Analysis/Convex/Cone/Dual.lean:116)提供几何基础；这是定理，不能与一个现成的通用优化服务混为一谈。
- [grobner 用例](D:/lean/.lake/packages/mathlib/MathlibTest/Tactic/Grind/Grobner.lean)和 [linear_combination](D:/lean/.lake/packages/mathlib/Mathlib/Tactic/LinearCombination.lean)可用于代数证书检查。旧 [polyrith](D:/lean/.lake/packages/mathlib/Mathlib/Tactic/Polyrith.lean:15) 已因外部服务停止而不可用，不能按旧教程当作现成后端。
- [IsSumSq](D:/lean/.lake/packages/mathlib/Mathlib/Algebra/Ring/SumsOfSquares.lean:15)有形式化基础，但这个文件不是自动 SDP 求解器。外部数值搜索、内部验证平方和证书已有成熟先例；未找到低阶证书不代表不等式为假。[Harrison 原论文](https://www.cl.cam.ac.uk/~jrh13/papers/sos.pdf)

**眼下能转化到哪里？** [ProcessionNormalizedLogVolumeActual](D:/lean/tmp/sheaf/xif/paper/ProcessionNormalizedLogVolumeActual.lean:70)已有给定数据下的加权和公式，适合进入消元器。但它没有因此证明该数据就是最终源 hull 的规定读数。[PaperProcessionNormalization](D:/lean/tmp/sheaf/xif/paper/PaperProcessionNormalization.lean:76)里的比较仍是条件；旧记录还已提醒不能把项目想要的 Haar=average 等式冒充源文结论。此等式不得作为自动搜索的“已知关系”。

可加入关系库的项目应逐条列明：来源、同一 C 的实例、符号/权重/参考项、证明状态、是否依赖目标。3.11 可以作为准确的显式条件探索；xi-f 本身或等价字段不能用于独立证明 xi-f。对 log、范数及零值分支也只使用已证明的变换规则；不能直接交给 ring 自动解释。

本轮已经对最小输入做了初步分级，尚未把它们冒充一张可求解的完整矩阵：

| 候选关系 | 本轮看到的依据 | 能否直接当作源约束 |
|---|---|---|
| procession 读数等于加权和 | 上述 value_eq_weighted_sum 有证明体 | 给定记录下可以；记录与实际源 hull 的身份另需证明。 |
| 全局主因子的总 degree 为零 | [实际 principal divisor 公式](D:/lean/tmp/sheaf/xif/paper/ThetaFunctionLineBundleActual.lean:93) | 只能用于已证明来自该全局元素的主因子；不能把任意各地方缩放拼成一个主因子。 |
| hull-approximant 替代保留体积 | EssLgc Stp5 的源陈述 | 可列显式源条件；它说全局 log-volume，不能擅自替换为每个地方逐项相等。 |
| determinant 与全列 log-link 的读数相容性 | EssLgc Stp6–8 的源说明 | 仍需实际对象、幂次、参考项和同步的实例；目前不是已构造的一组数值行。 |
| hull=glue(thetaHull) | S1136 的输入字段 | 不准当作已经供应的事实；这是旧路线转移的责任之一。 |
| link 推出最终比较 | ThetaLinkActual 的输入字段 | 对当前独立证明目标不可用作搜索前提。 |

这张表表明，当前“可计算”与“已转成计算”仍有距离。新增价值必须来自实际源关系的补充或较弱充分不变量的证明，而非重新证明加权和收尾。

还需处理量词：固定一个小 l 的矩阵证书只解决该实例；一般目标需要参数化证书或统一生成算法及其正确性证明。实际权重未证明为确定的有理数时，不能擅自按常系数线性规划处理。有限关系系统中的反例只说明当前关系不足，不自动是合法 IUT 数据的反例。

**判断：最值得先做一个小规模、针对真实消费者的预实验。** 首要产物应是一张有来源的关系表和精确目标表达式，随后才决定线性消元是否足够。这里尚未证明完整源困难已落入线性或半代数范围。

**四、优先候选 B：让 AI 搜索贯穿源算法的不变量，而不是不断改写缺口。**

把 Stp1–8 的每一步写成有类型、有标签的关系。对同一 C 保留共享选择及依赖，不能把“存在同一整包选择满足所有条件”改成“每个分量各自存在选择”。一个可探索的任务是寻找 P，使其从源初始状态成立，并由每个实际操作保持，最后足以给出需要的读数关系。

这里有两个互补的计算工具。其一是检索供体、AI 提出引理、Lean 搜索证明。其二是反例引导的抽象细化：先用保守的关系模型检查候选；遇到反例，判断它是否来自丢失的源关联，再只补有源依据的关系。CEGAR 文献明确区分抽象反例与真实反例。[原始 CEGAR 论文](https://www.cs.cmu.edu/~emc/papers/Conference%20Papers/Counterexample-guided%20Abstraction%20Refinement.pdf)

插值法可以从已经得到的不相容性证明中提取共享语言里的中间断言，有助于发现接口需要保留哪些信息；它不能在尚无证明时自动制造缺失的数学事实。[McMillan](https://mcmil.net/pubs/TACAS04.pdf) 大量等式改写可借鉴 e-graph 的等价饱和，但所有规则必须保留源标签和侧条件，并能回放证明。[egg](https://arxiv.org/abs/2004.03082)

**最贴近补充路径的子任务是 Stp7–8。** 源文用完整 1-column、m∈ℤ 的平移及同步不定性。可以尝试寻找一个读数不变量或势函数，令一步变换的误差写成可控差分，并用统一的一步定理处理全列。如果采用势函数相消方案，必须交付具体势函数、每一步的源公式、端点/同步条件及最终读数解释；只写“误差是 coboundary”仍然是在搬缺口。

这里不能用有限长度循环代替 ℤ，也不能仅因 shift 由一个生成元描述就省略与其他源操作的相容性。Ind1–3 若没有可用的生成定理，就不能抽样几个作用后宣布覆盖全部。若目标走存在输出/逼近见证路线，保持某个性质的安全性不变量也不能替代输出存在性：需要相应的源构造或见证策略。

当前直接入口是 [algorithmic-provenance](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialIplLinkWiring.lean:190)。它仍缺实际操作与 full-poly strip 箭头的联系。AI 搜索可以尝试补较弱但足够的读数关系，不必坚持完整映射重建；然而必须从实际操作证明这个较弱关系，而不是把它作为新的 compatible 字段。

**判断：这是更接近核心源断点的候选，但建模成本比候选 A 高。** 可以与 A 共用源关系表：A 发现残余关系，B 尝试由更早源操作证明它，再交回 A 核验。若 B 只不断提议与目标等价的前提，就停止这一轮搜索。

**五、候选 C：creative telescoping、递推和大规模恒等式证书。**

这与用户所说的大量项相消最接近。对于合适的求和项 F(n,k)，搜索递推算子 L 与辅助函数 G，使

\[
 L(F)(n,k)=G(n,k+1)-G(n,k).
\]

求和后内部项消去，剩边界项，再由递推与初值控制全体 n。D-finite/适当 q-差分框架允许把某些巨大恒等式化成算子和线性代数问题；并非任意函数、supremum、hull 或不定性集合都属于这些框架。[Brochet–Salvy](https://arxiv.org/html/2307.07216v2)

本地并非完全没有这种证明模式：[Catalan 的证明](D:/lean/.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Catalan/Basic.lean:72)已有具体 Gosper 辅助项及望远镜求和，再推出闭式。该辅助项是 private，适合作为模式参考；这不是通用 creative-telescoping 引擎。此次限定目录检索未定位到可直接处理当前 IUT 表达式的通用引擎，不据此断言整个生态没有。

q-差分的移位算子与系数通常不交换；上文的交换环 grobner 用例不能当作已经备齐的 Ore 算子引擎。若用外部系统搜索，需要核验正确的算子语义，或把证书展开成可以逐项核验的系数恒等式。

若需要的是非负性而非恒等式，还可考虑先推出递推，再用不变锥证明其解非负。已有研究在 Poincaré 型、唯一单主特征值及适当初值条件下产生正性证书，不能泛化成任意递推的自动判定器。[Ibrahim–Salvy](https://arxiv.org/abs/2306.05930)

可接入的对象应是**真实读数中已经出现的**参数化有限和、determinant 系数或 q-函数。须先指出其确切项、递推/消去理想、边界和初值；最后证明该表达式等于源所要求的量。对不定性取上确界、做 hull 或改变输入输出标签之后，递推是否仍成立也须证明。

当前 [ThetaFunctionLineBundleActual](D:/lean/tmp/sheaf/xif/paper/ThetaFunctionLineBundleActual.lean:99)供给的是 q^(j²) 数值族，且明确说明这不是源 theta divisor；其中还有 q=1/5 的具体示例。它不足以作为“展开源 theta 函数百万项”的输入。已有 j² 加权和若已能简单化简，就不值得换成大算力重算。

**判断：保留为条件性路线。** 找到一个直接承担缺口的、属于适用函数类的源公式之后才投入。当前没有定位到这样的完整公式，不能预判“大量高阶项会恰好相消”。

**六、候选 D：用有限确定性定理把无穷恒等式压成有限计算。**

这里有比“多算几项猜相等”更严格的办法。本地 [sturm_bound_levelOne_nat](D:/lean/.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean:284)已给出：level 1、整数权 k 的模形式，若 q 展开消失阶大于 ⌊k/12⌋，则为零。对已经证明属于相同空间的两个模形式，有限个精确系数可以决定恒等式。

这提供了真正的有限化机制。AI 可搜索候选恒等式，计算机算有限系数，数学定理保证覆盖所有后续系数。但它不是对任意 theta 表达式的通行证：theta 常涉及不同 level、character、半整数权或亚纯性；先取幂、乘分母、升降 level 都要核对对原目标的影响。

本地 [JacobiTheta](D:/lean/.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean:11)与 [q-expansion](D:/lean/.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean:15)主要是复上半平面上的对象。它们与本项目实际 Tate/非阿基米德 theta 取值之间仍需要源身份与基变换依据。即便一个解析恒等式成立，也不自动识别允许像族的 hull/log-volume。

**判断：方法和部分库基础都实在存在，当前源适用性未建立。** 只有出现符合上述类型的具体源恒等式，才升为活动任务；不先为试探而建设整个模形式理论。

**七、候选 E：先用赋值与过滤判断高阶项是否会影响目标。**

对于加性非阿基米德赋值，有限和若有唯一取得最小赋值的项，其和的赋值由该项决定；有并列最小项时才需进一步检查首项相消。mathlib 的乘性记法已有 [map_sum_eq_of_lt](D:/lean/.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:314)；形式幂级数已有 [order_add_of_order_ne](D:/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Order.lean:170)。

这启发一个便宜的筛选：如果目标读数只依赖某个确定的赋值，而源表达式的主项在全部合法输入下严格占优，继续计算大量高阶项不会改变该读数。若有并列、首系数抵消或特殊参数，就应计算残项及必要的更高阶信息。

形式幂级数的消失阶不等于任意 p-adic 代入后的赋值；代入、收敛、系数赋值和无限尾项都要控制。上述有限和定理也不能直接替代无限级数的尾项证明。这项分析只对已识别的实际源表达式有效，不对整个 IUT 作“高阶项无用”的判断。

**判断：适合作为候选 C/D 的入口筛选或局部引理工具。** 它可能省掉无效展开，但本身不是 fixed-gluing 比较的替代证明。

**八、已有歪路如何约束这些新方案。**

| 已有尝试/证据 | 不能重复的错误 | 新方案必须增加什么 |
|---|---|---|
| [S1136 的单调 gluing](D:/lean/tmp/sheaf/xif/paper/S1136SourceComparisonViaGluingActual.lean:17) | q 与 hull 的运输关系已作为字段输入；再消掉 j² 不能证明这些字段。 | 相消证书的每一行都要从源构造得到，不能预置 hull=glue(thetaHull)。 |
| [marked trace 更正](D:/lean/tmp/sheaf/n8/closure/C9-U2K2-SQ3-MARKED-TRACE-20261026.md:164) | 给定 Φ、t_ij 后验算 cocycle，不等于构造固定 C 的实际 Φ、t_ij。 | 提供实际源映射，或独立证明足够的源读数不变量。 |
| [SHEOutputActual](D:/lean/tmp/sheaf/xif/paper/SHEOutputActual.lean:238) | 单位截面读取有真实局部环，却未建立源 output→section 的联系。 | 证明实际源读取身份；不由 record 非空推断。 |
| 上轮 [F/K、Haar、范数审查](D:/lean/coord/reports/gap-exploration-20261030.md) | 在错误完备化无根、替代测度、默认范数或独立拼出的 q/Theta 上计算。 | 保留同一 C、指定地方、源区域、正确归一化及全部合法选择。 |
| 10-26 的 exact/approximate 区分 | 把某个充分构造当作唯一必要形式，因其失败就否定所有路径。 | 允许直接比较证书、单侧逼近及较弱的充分不变量；逐个证明转移。 |
| 只扩大有限样本/模型搜索 | 小模型通过被当作全称证明；小模型失败被当作源反例。 | 提供有限确定性/归纳/抽象正确性定理，并核对量词与见证范围。 |

这些新方法最容易重犯的错误是：让 AI 在不忠实或过弱的模型里找到很漂亮的证明，再把“正确编码真实源对象”留成一个包含原结论的新假设。为避免此事，证书检查之外必须保留两个接口：源实例确实满足计算约束；计算结论确实是锁定目标。它们不能只登记名字，必须有证据。

**九、建议的取舍与最小可行性实验。**

| 路线 | 算法基础 | 当前源转化程度 | 决定 |
|---|---|---|---|
| A：完整读数的消元/正性证书 | 成熟；本地有核验工具 | 加权和等叶子可用，关键源关系尚未供应 | **先做有限预实验**，先关系表后求解。 |
| B：AI 搜索源不变量/必要中间引理 | 有研究与工具模式 | 实际步骤语义、共享选择和全列覆盖仍需建模 | **重点探索**，与 A 的残余关系衔接。 |
| C：creative telescoping/递推 | 成熟，复杂证书有先例 | 尚未定位承担核心 gap 的合格求和公式 | **有条件保留**。 |
| D：Sturm 等有限确定性 | 本地有 level 1 结果 | 未证明当前源表达式属于适用模形式空间 | **等待具体公式**。 |
| E：赋值/过滤/尾项控制 | 本地有相关定理 | 只对明确局部表达式适用 | **筛选工具/按需叶子**。 |

下一包建议是**一个直接对消费者的关系与证书预实验**，而不是训练模型或铺开五条证明工程：

1. 固定 Q_C、H_C 的源版本；只取直接通往 link_implies_inclusion 的读数和源步骤。给每条候选关系登记来源、量词、同一 C 的实例和证明状态。已有数学库定理、给定记录的条件定理、尚待构造的源身份分开标记。
2. 从已有来源中提取一个最小的真实关系系统。先判断是否已经是线性/代数问题；如果模型必须先加入 Q_C≤H_C 的等价条件才成立，就把该行退回源证明，不能启动伪“求解”。
3. 在此系统上搜索精确消元/正性证书；若剩下一项具体源关系，则让 AI 搜索它的较早供体或一步不变量证明。只在发现实际求和公式时转入 C/D/E。
4. 成功标准是供应一个此前缺失的源引理/证书，并让当前消费者少一个未证责任。若只得到新接口、相同残差或无源反例，记录为该表示/该预算内未推进，不当作数学不可能性。

对于无限族，预实验必须说明之后怎样推广：参数化恒等式、归纳、生成元验证加生成定理、或明确的有限确定性界。测试几个 l、几个 m、几个数值点只用于发现候选。

这轮还不宜给“需要多少 GPU 天”的估计：输入表示和搜索空间尚未确定。当前 Python 环境可发现 sympy/scipy，未发现 z3/cvxpy/sageall 模块或 z3/sage/maple 命令；这是环境发现，不是完整安装审计，也没有运行求解器。有限的精确线性证书核验可先利用现有基础；大规模模型训练不是起点。

**十、本轮交付和结论边界。**

本轮已完成网上原始资料调查、本地 mathlib 的针对性检索、相关源码追踪和旧失败路线比对。新增的具体认识包括：本地已存在 level 1 Sturm 界、Gosper 相消证明模式和线性证书核验；polyrith 已不可用；当前直接源消费者仍未供应可将整体比较立即交给上述算法的完整关系系统。

我建议改变的是研究入口：**尝试让机器找一个直接消掉源比较责任的证书或不变量，而不再用增加中间对象的数量衡量进度。** 这保留了绕过过强中间构造的可能；没有把编码真实源对象的困难宣布为已解决。当前不判这些路线必成，也不以尚未找到源公式断言它们不可行。

版本：workspace HEAD 9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee；mathlib HEAD 905b95818eb32af7874a58b427f50c1711a5e96c；实际文件另按 SHA256 冻结，不能仅凭 HEAD 代表 dirty workspace。文献核对日为 2026-10-30；未使用搜索结果中的第三方突破传闻支持判断。

statement_compiles=not_run；proof_body_checked=not_run；kernel_closed=not_run；target_accepted=false。未运行 Lean、Project build、比较器、公理检查、独立审查或任何候选求解。完整记录见[证据](D:/lean/tmp/sheaf/compute-route-feasibility-20261030/evidence.json)、[机械核对](D:/lean/tmp/sheaf/compute-route-feasibility-20261030/verification.json)、[本地检索](D:/lean/tmp/sheaf/compute-route-feasibility-20261030/local-searches.json)及[文献与适用范围](D:/lean/tmp/sheaf/compute-route-feasibility-20261030/literature.json)。
