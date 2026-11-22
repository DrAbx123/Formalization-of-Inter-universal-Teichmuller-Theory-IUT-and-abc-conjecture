# C9：结合后续说明的源对象分解与实施路线

日期：2026-10-23。owner：当前 chat root，单人研究。用户明确要求路线/阶段 1，不写 Lean。本记录接续 VALUESPAPER-SEMANTICS-REVIEW-20261023.md，修正过强的路线要求，不覆盖历史结论。

## 执行决定：对象路线已定，不再等待用户选择

用户随后指出研究者必须下判断，不能以双方都不清楚为由停止推进。本节给出经 2026-10-23 一致性复核后的执行决定；修订前全文保存在同目录 *.pre-consistency.md。已经读取另一个工作流的 C9-TARGET-V3.md 和 C9-P0-P1-SOURCE-TABLE.md，复用其清单，不重复创建同类 inventory。实质更正及外部讨论的来源见 C9-ROUTE-CONSISTENCY-REVIEW-20261023.md。这里决定研究路线，不把尚未证明的源定理标为通过。

1. **拒绝当前点值型 C9 定义作为论文目标。** singleton 和有限 SignedLabel 点像都不承担 output region 的角色；增加 named sorry 不能修正这个对象错误。旧 C4 的 eval/witness 作为分量层数学保留，退出“完整源输出”的职责。后续以区域族重建 C4 的对外输出边界，C9 消费这份区域输出。
2. **固定一份源配置，再变化允许选择。** 配置包含合格 S、其实际 log-theta-lattice L、当前 Θ-link、所需完整列及各计算框架。固定配置不删除 Stp7 对所有 m 的移位/同步数据。新的 C9 规格不保留语义未识别的旧 x 参数，也不以“证明旧 x 不变性”为前置任务；将确实需要的源状态直接放入配置。若旧消费者将来需要适配，再证明该适配的识别。不得混合不同源配置的 Values。
3. **采用整包区域族和表示关系。** 一次选择 α 必须覆盖源允许且相互兼容的整包数据；j 只标记分量。固定局部框架后可以用具体函数构造区域，跨 holomorphic structure 的整体层采用源规定的表示/下降关系。停止寻找没有源依据的全 value-monoid→IQ 单值 lift。明确区分 lattice 的整数坐标 (n,m)、有限 procession/label 索引及 tensor tuple；不能把它们统一成旧 ThetaPilotCarrier。
4. **Values 采用源 hull 内的合格区域读出。** 先由源算法定义 RawPoss，再按分量 i 取 U_i=⋃αRα,i 和 H_i=Hull(U_i)。保留整包选择 α 的相关性，不能默认为各分量独立选择。以 III Remark 3.1.1(iii)、3.9.5(ii) 的 direct-product region 类作为本轮主体区域类；原始 pre-region、分量并 U 与可取有限体积的 region 分开。全局条件是局部归一化 log-volume 几乎处处为零，不能加强为几乎处处等于参考区域。Stp4 给合法扩大，不能另外加入一个自由的“被允许”谓词。一般 Borel 的 E-weighted 扩展不作为本轮前置；若某个实际源步骤需要它，再沿源定义扩展，而不缩小该源步骤的范围。
5. **读出先分框架定义，再证明比较。** 对各带标签的框架 f 独立定义实际全局读出 ℓ_f，包含选定地方/tuple 权重、procession 平均、参考项及无穷地方。C6 局部 actual normalization 是供体，不能作为自由 B 输入进入最终源定理。Prop.3.9(ii),(iv) 的参考项校准和 log-link 相容性是定理；不能提前视为同一函数。最终比较在目标侧完成，不要求 Θ-link 保持两边原生 degree。采用 Ob3-3 的数值 determinant 路线，独立证明 degree 读出比较，不先建设无消费者的完整 determinant API。
6. **Q 和 Θ 独立构造。** Q 来自原始 q-pilot 的全局区域/线丛读出；Θ 来自源 H。禁止先把 q region 放进 H 来取得比较，也禁止用 singleton region 配一个独立 q 标量宣称构造完成。Values:Set ℝ，Q:ℝ，Θ:WithTop ℝ，有限性单独证明。structure 可以用于缓存这些构造及其识别等式，不再保留自由数值字段。
7. **P6 的主任务是两种实际构造的比较。** 独立构造原生 q 读出与 multiradial 算法经下降、hull/degree 校准及 log-shift 后的读出，证明存在源允许的整包选择/积分结构，使它们在实际 q-pilot 上一致，并证明对应输出区域属于 HullPoss。由此推出 Q∈Values，再导出上界传递及旧 epsilon 接口。LANA 的 η^q 与 η^anab_J 比较可作为展开这项任务的字典；必须先核对其类型、算法与主文对象，不能直接采纳一个自由的 η 或相容性字段。上界传递保留为数值消费者，不再把它作为核心分解的终点。

上界传递与 Alien §3.7(ii)(10est) 的 hull 上界表述相容，但 P4 已给出 max Values=θ 时，它与 Q≤θ 等价。因此它不是比目标更细的证明步骤。主任务改为上述带源构造的比较；若将来只证明一侧近似，仍可供 P7 消费，但那只能记为较弱的数值结果，不能冒充原文所说的两种读出的实现。

### 现在可以完成的局部自然语言证明

**P4 的条件数值部分。** 固定同一配置。设 H 是该配置的合格全局区域；各体积分量及参考项正有限；归一化系数为正；全局读出只有有限个非零贡献。定义 Values 为所有合格 R⊆H 的 ℓ_out(R)。对于 v∈Values，取其区域 R。局部测度的单调性给 μR≤μH；正有限性允许转为实数并取对数；减去同一参考项、乘同一正权重、对所有相关地方/tuple/procession 求和，得到 v=ℓ_out(R)≤ℓ_out(H)=Θ。取全局有限支撑的并可使两边在同一有限索引上求和。H 自身合格且 H⊆H，故 Θ∈Values。因此对任意实 b，UpperBound(Values,b) 当且仅当 Θ≤b。没有使用 Q，也没有把 q 的比较偷偷放入这个证明。

**数值接口与原 QPaperApproximated 的等价。** 对任意 V⊆ℝ 和 Q∈ℝ，以下两式等价：

- 上界传递：∀b∈ℝ，(∀v∈V，v≤b) → Q≤b。
- 一侧逼近：∀ε>0，∃v∈V，Q−ε≤v。

从上界传递到一侧逼近：若对某 ε>0 不存在这样的 v，则每个 v∈V 都小于 Q−ε，从而 Q−ε 是 V 的上界。传递得到 Q≤Q−ε，矛盾。

从一侧逼近到上界传递：给定上界 b，若 b<Q，则取 ε=(Q−b)/2。逼近给 v≥Q−ε>b，而上界给 v≤b，矛盾。这项等价不要求 V 闭、最大值存在或局部格子体积稠密，也不需要单独假设 V 非空。

**P7 的有限数值部分。** P3 给 Θ=θ∈ℝ；P4 给 θ 是 Values 上界；P6 上界传递立即给 Q≤θ。完整源结论还消费 P3 的有限性。上述三段证明在相应准确对象定义后可进入陈述阶段；本轮不写 Lean。

### 下一步的准确证明任务

已有 P0/P1 表不再作为下一次重复交付。继续阶段 1 时，直接展开 P6 在源对象上的三段证明责任：

1. 固定原始 q 输入及实际 Θ-link，逐步写出 III Remark 3.10.2/3.11.1 中被使用的 Kummer/evaluation 复合，证明原始 Θ 表示被允许输出族覆盖。保留单位部分和值群部分；不能仅以三个抽象同构的存在性代替源箭头。
2. 对每个允许下降、Ind 扩大、hull 扩大、全局等体积替代，证明原始 gluing 关联继续有效；将 Ind1/2 的读出不变、Ind3 的单向控制、hull 的包含扩大和全局替代的等体积分开。保留替代区域位于当前 hull 内的证明，不以全局等体积代替包含。中间不要求与 q 的数值相等，也不识别两边环结构。
3. 展开目标侧 log-Kummer 的列内移位相容，构造两条独立读出链并证明它们在实际 q-pilot 上的比较；同时交付实现区域的合格性与包含性。局部数值等式、全局汇总和移位识别分别写出，不能以“由 SHE/APT”或“同一抽象 BPS”结束。

这是已经选定的工作方向。仍开放的是这些具体源命题的证明，不是用户需要选择的建模方案。P4/P7 及上界传递等价的自然语言证明本轮已补齐；P1/P5/P6 的源证明不据此虚报完成。

## 任务、范围与验收边界

- 任务 ID：N8-C9-SOURCE-ROUTE；父节点 n8-s3-c9；规划记录节点 n8-c9-output-region-source-route。
- 实际消费者：C9 的 ValuesBounded、q-pilot 数值实现/近似，以及 C10 的源 Corollary 3.12（Q ≤ Θ 且 Θ 有限）。不是给旧任意接口上的 sorry 找 inhabitant。
- 输入范围：沿 coord/N8-TARGET-INPUT-DECISION-20261023.md，采用原文合格初始 Θ-data S 及其上的实际 log-theta-lattice L；选定地方 V(S) 是到 Fmod 地方的 section。不能把任意旧 OriginalInput 自动当作这一输入。S 的候选已有 SourceNativeInitialThetaData；L 的完整源类型仍是陈述缺口。
- 数学目标：对每份上述合格输入，构造同一源配置的 Q∈ℝ、Θ∈ℝ∪{+∞} 和真实输出语义的 Values⊆ℝ，证明 Values 有 Θ 上界、原始 q 输入在允许的输出构造中的数值实现/足够的一侧近似，以及 Θ 有限；推出 Q≤Θ。固定该输入后才量化允许的输出选择，不把不同输入/状态的 Values 混成一组。
- 写入：本 Markdown、新研究节点；向 AUDIT_LEDGER、STATE、queue、父节点追加本轮证据。没有更改任何 Lean、共同数学定义或他人 owner。
- 精确文件版本：原审查四个 Lean 文件 hash 见上轮记录；本轮读取的供体和文献见同目录 C9-STAGE1-SUPPLEMENT-EVIDENCE-20261023.json。工作树非干净，不把 HEAD 当作 tmp 文件版本。
- 集成/构建：不适用本轮；后续由既有实现 owner 接入。本轮没有消掉一个源数学证明前提。
- 阶段状态：原文路线与失败路线的定向调查已交付；C9 整体 stage 1 仍未完成。下述 P1、P5、P6 还有必须细化的源构造/自然语言证明缺口，不能把“补充文献说有 AND 关系”直接变成可消费的假设。

## 文献与实际读取范围

所有页码指本地 PDF 页内页码；这些文件在本次所用区间与物理页码一致。完整路径、SHA256 和 PDF 元数据在证据 JSON；版本以文件内容为准，PDF 创建日期不代替数学版本说明。

| 文献 | 版本/范围 | 对本任务的用途 |
|---|---|---|
| IUT III | May 2020；Remark 3.1.1、Prop.3.9、Remark 3.9.5、Remark 3.11.1、Cor.3.12 | 区域、加权体积、hull-approximant、determinant、算法及最终数值目标 |
| Essential Logical Structure（EssLgc） | March 2024 修订，167 页；核对全篇结构，细读 §3.6 的 ExtInd、§3.10 Stp1–8 及 §3.11 的相关解释，结合 §3.9 结尾 | 最直接的步骤表；扩大可能性、全局等体积替代、log-shift、最后数值化的先后关系 |
| Cmt2018-05 | 8 页全文；重点 C16–18，pp.5–7 | 区分抽象 pilot 与具体表示；同一个容器上的同一个 log-volume |
| Cmt2018-08 | 5 页全文；重点 C10、C12、C14，pp.3–4 | 一个 Θ-pilot 的 j 分量；不能把各标签当成独立完整 pilot |
| Report on a certain series of preprints (2024-03) | 12 页全文；重点 §2，pp.6–9 | 区分同构类与带兼容性的结构；全局性与 hull 的必要性 |
| Alien Copies, Gaussians, and IUT | 本地 170 页，PDF 元数据 2020-12-23；§3.7(i)(ii)、§3.11(v) | 把 q、Θ、hull、degree、两侧 log-Kummer 串起；说明为何省略 hull 不得到所需比较 |
| Rpt2018 | February 2019 修订，45 页；§12 的 LbLV/MlLV/LVEx，pp.23–26 | 区域几何引入的变化不能替换成任意标量或简单 j² 缩放 |
| On the Formalization of IUT | April 2026，14 页；正文 pp.1–11，重点 §4 pp.9–11 | 区分 dsc、hull+det 与 SHE；“3.11.5”是含额外工作的重组，不能直接当作 Th.3.11 |
| LANA interim report | revision 1.0.1，commit 293bdd89463473ae13d40834d70fb4b7ba81da1f；定向细读算法/比较/待澄清/SS 分析诸节 | 两条独立 η 构造及实际 pilot 比较；报告承认尚无该比较的证明，不作为完成证据 |
| Scholze–Stix, Why abc is still a conjecture | July 16, 2018，10 页；全文，重点 pp.7–10 | 追踪抽象 pilot、具体 degree、j²/平均缩放；检验任何提前标量化路线 |
| Dupuy–Hilado, arXiv:2004.13228 | v1 (2020) 35 页的 §1、§3.10；另核对 v2 (2025) 20 页的引言和范围 | v1 有 selected-place/degree-volume 的可展开计算；v2 已改为 initial theta data，不能误引为 UΘ 构造/核心比较的证明 |

长文的“纳入调研”指上表的定向读取，不声称逐页审完全部历史讨论、类比或所有引用论文。SS/Joshi 评论中的论争性结论是作者的判断，本记录只提取与本路线有关的具体数学说明，不据此宣布争论已解决。

官网原文：

- https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf
- https://www.kurims.kyoto-u.ac.jp/~motizuki/Essential%20Logical%20Structure%20of%20Inter-universal%20Teichmuller%20Theory.pdf
- https://www.kurims.kyoto-u.ac.jp/~motizuki/Cmt2018-05.pdf
- https://www.kurims.kyoto-u.ac.jp/~motizuki/Cmt2018-08.pdf
- https://www.kurims.kyoto-u.ac.jp/~motizuki/Report%20on%20a%20certain%20series%20of%20preprints%20(2024-03).pdf
- https://www.kurims.kyoto-u.ac.jp/~motizuki/Alien%20Copies,%20Gaussians,%20and%20Inter-universal%20Teichmuller%20Theory.pdf
- https://www.kurims.kyoto-u.ac.jp/~motizuki/Rpt2018.pdf

本轮另渲染并目视核对 EssLgc pp.150,153,154；May 评论 p.6；Aug 评论 p.3；Alien p.108；2024 Report pp.8,9；Rpt2018 p.24；IUT III pp.133,162。图像及 manifest 在 tmp/pdfs/valuespaper-stage1-sources-20261023。上轮已目视 IUT III pp.173–175,182–184。

## 五项应修正的路线判断

### 1. 原始输出与扩大后的允许输出必须分开

EssLgc p.150 Stp4 明确从 Stp3 的 possible output regions，扩大到这些区域之并的 holomorphic hull 内的 regions。它是 ExtInd1：增加可能性并保留原有关联。因此，“Values 只能枚举原始 eval 的输出，不能包含其他区域”过强。

正确区别是：原始源输出族 RawPoss；其 hull H；经过此步许可扩大的区域族 HullPoss；最后读出的 Values。扩大后的每个 region 不必来自一个旧 C4 点 witness，但扩大操作本身必须来自同一源 RawPoss 和 H，并保持输入输出关联。不能用无关 provenance 替代 H，也不能对任意 Set 使用 Real.log 的全函数值冒充合格区域体积。

所以当前 C9Paper 的“取子集”形状并非原则上错误；问题是 provenance 自由、未绑定源 hull、没有区域有效性条件、归一化未识别、与源构造链没有关系。C9ValuesPaper 的 singleton 形状则没有因这项澄清得到支持。

### 2. 不把整个 C4→IQ 单值映射作为必经起点

IUT III p.162 APT 明确说明，所讨论的是两侧结构下同时有效的构造算法，不是沿一个集合函数搬运区域。固定一个局部 realization 后，可以有落点、理想或区域的具体函数；但不能据此要求全 value monoid 跨结构有一个指定的单值 IQ lift。

较合适的源边界是：带 theater/列/行标签、单位部分和值群部分的实际输出数据，以及它在指定结构下的区域表示关系；商或多值表示也可使用。随后分别证明相应表示变换保持读出、或只给规定方向的上界。特别是 III Cor.3.12 proof (x) 区分 Ind1/2 的不变性与 Ind3 的不等式，不能笼统要求所有允许选择给同一个数。函数模型若能证明是该关系的忠实实现，当然可以使用。

### 3. 单个 j 不是完整 Θ-pilot

Cmt2018-08 p.3 C10 特别区分整个 pilot 和 j 分量。C4 的 SignedLabel 选择与整包输出之间需要“分量组装＋procession 归一化”，不能把每个 j 的一个点读数作为完整 possible pilot-object log-volume。

这不意味着现有 label 接口必须全部删除：它仍可能是分量计算接口。必须证明如何从实际允许的整包选择产生各分量、如何同步这些选择，再按原文计算一个总数。不能把对 j 的求和/平均与“在所有 j 中任选一个”的存在量词混用。

### 4. determinant 有数值捷径，但不能省略识别责任

IUT III p.133 Ob3-3 允许在只计算 log-volume 时省略显式 determinant 中间操作。故路线不必先建完全部 determinant Frobenioid API 才能探索 C9。

可选的短路线是证明：带正确权重、单位参考项及正 tensor power 校准的区域读出，等于独立定义的算术 degree 读出。之后在数值消费者中使用该等式。不能定义 degree := volume，再用 rfl 冒充这项比较；也不能因此删除全局线丛、同构类或 log-Kummer 相容性的源义务。

### 5. 全局匹配与局部计算是不同任务

EssLgc Stp5 要求相同的是 global log-volume。IUT III Remark 3.9.5(i)–(iv) 区分一般 hull-approximant 和恰好同体积的 Ξ；局部恰好同体积不一般成立，全局版本利用无穷地方。不能把每个 p-adic 块的格子体积当成稠密实数，再逐地方做 epsilon 逼近。

2024 Report §2 强调这里的全局性。这不禁止对正有限测度使用局部单调性，再求和证明 ValuesBounded；禁止的是未经源证明就把 q 与 Θ 的核心比较换成“各地方的同类 q≤Θ 不等式”。

## 建议冻结的数学对象（尚不是 Lean 定义）

固定原文合格输入 (S,L)，以及同一 Θ-link 的源端、目标端和所需完整列。目标端的 holomorphic structure 是最终计算框架；中间保留各列/行及 input/output 标签。以下 ℓ_f 指框架 f 的读出；不得因都以 ℝ 为值域就把这些函数及其构造等同。

1. α 表示源算法实际允许的一次完整选择，包含所需的地方、tensor packet、procession 分量及 Ind 数据之间的兼容。j 是 α 产生的整包数据的分量索引，不单独充当 α。
2. Rα 是在指定框架可解释的原始输出族，分量按有理地方、所选地方 tuple、procession 位置等索引。先定义源构造/表示关系，再识别其集合表示。Remark 3.1.1(iii) 的 pre-region 仅要求相应相对紧条件，不能自动认作可取有限体积的 region；也不是任取一个点后取 singleton。
3. 分量式定义 U_i=⋃αRα,i、H_i=Hull_f(U_i)。这是 Cor.3.12 所用的区域族记号，不能误作一个没有权重的大集合的 Haar 体积。证明源允许的整包选择到各分量的投影；任意独立拼接分量只能在已证明的扩大步骤中引入。若某分量不相对紧，原文允许全空间 hull；先证明非退化及扩展读出的适用条件，再保留 +∞ 上界，随后对源输入证明有限性。
4. Adm_f(R) 是该步骤使用的原文区域条件：指定直积形式及各地方相应的紧/开/径向条件；有限 log 值所需的正有限质量；全局在所有但有限个有理地方的局部归一化贡献为零；以及 source 步骤实际要求的可替代性条件。参考区域相等是保证零贡献的一种方式，不能作为等价定义。不能只写 nonempty，也不把每个 region 强制为积分模块。
5. ℓ_f(R) 是该框架的全局、有符号、procession-normalized log-volume。非空、零测集不是它的有限值对象；参考区域也须正有限。框架间校准须由 Prop.3.9 及实际源映射证明。原文允许的更一般 Borel 区域需用原文 E-weighted 构造扩展，不随意当成同一个乘积 Haar 测度。
6. HullPoss 在 Stp4 的源识别证明之后表示为 Adm_out(R) 且逐分量 R⊆H 的区域族，不再附加自由的 allowedStp4 字段。Values = {ℓ_out(R) | R∈HullPoss}。每个数的 provenance 是实际区域/构造路径，而不只是 SignedLabel。若只实现子族，须另证与这里完整扩大族的覆盖关系，不能静默改换目标。
7. Q = ℓ_native-q(Rq)，Rq 独立来自目标列 q-pilot 的原生表示；Θ = 扩展读出 ℓ_out(H)。这两个读出先各自定义，不能提前假设 Rq⊆H 或 Rq 已是输出框架中的同一区域。P5/P6 负责带参考校准和列内移位的比较，最后才能用共同的实数读出收尾。

这里的公式给出对象职责，不宣称 Adm、α 或原文区域表示已经在当前代码中被精确定义。P0/P1 就是消除这些剩余表示歧义的任务。尤其不能用一个任意字段 Rα 和一句“它是真实输出”的未展开谓词替代这些任务。

### 单点为何不能修补

在固定的 additive Haar 空间中，平移不变性给 μ({a})=μ({0})，所以当前 actual normalization 对每个 singleton 给同一个数。非离散局部域的 singleton 质量又为零；Real.log 0=0 是总函数约定，不能解释为论文的有限 log-volume。

一个局部说明是 μ(ℤp)=1 时：L(p^kℤp)=−k log p，随 k 改变；L 的当前全函数公式代入 {p^k} 却均给 0。这里的 p^kℤp 只是说明正确“区域”与“点”的区别，不宣称论文全部输出都是此类主理想。

### x 与 witness 的处理

旧 w.2.1=eval n x w.1 已由 witness 的等式给出。因此若先有真实区域解释，并证明 label 路线与 output 路线给出同一区域或相同读出，使用 w.1 可成为实现优化。

当前缺少这一因子分解，而且 Choice/eval 已经不使用 x。原文没有一个已经识别为该自造 x 的变量，不能凭变量未使用断言论文必然非平凡依赖 x。新 C9 直接采用上述 source configuration，不以研究旧 x 为前置。将来适配旧接口时，才分别处理冗余 presentation 的不变性与真实状态的依赖。不能把所有不同输入状态的输出并集压到一个固定 Θ 下。

## 自顶向下的 DAG 分解

下表 P0–P7 是本研究节点中的任务分解，尚未伪装成已形式化的新定理。S 表示 statement dependencies，P 表示 proof dependencies；边均为 planned source route，不标 verified_lean。

| 包 | 消费者与准确交付 | S 依赖 | P 依赖/状态 |
|---|---|---|---|
| P0：源输入与索引 | P1/P2；给 (S,L)、选定地方、全体所需 tuple/procession 的依赖索引；写清每个载体在哪列哪行 | n8-target-input-v2 的合法输入规格，原文 I Def.3.1、III 3.1/3.11 | native 选定地方数据可复用；L 及实际箭头的完整源绑定仍缺 |
| P1：整包输出与表示 | P3/P5/P6；对每个源允许 α 给出整包 Rα；保留初始 Θ-pilot 的允许表示，Ind1/2 的不变性及 Ind3 的单向区域控制 | P0；theta 特殊值、Kummer/Galois evaluation、tensor log-shell 的真实对象 | III Th.3.11(i)–(iii)、Remark 3.10.2/3.11.1；T11/C4-G4 及实际箭头供体未闭合 |
| P2：分框架归一化及比较 | P3/P4/P5/P7；在 Adm_f 上定义 ℓ_f，分别证明不变性、参考校准和正权重单调性 | P0；实际测度、积分参考结构、权重、无穷地方与全局有限支撑 | III Remark 3.1.1、Prop.3.9；局部与 E-weighted 引理可复用；实际权重代入和全局源识别缺 |
| P3：源 hull 与有限性 | P4/P5/P7；逐分量 H_i=hull(⋃αRα,i)，证明容纳性、各必要块正有限质量、全局有限读出 | P0/P1/P2 的对象 | 实际源输出的一致有界性、Ind 控制、hull 紧性、几乎处处零 log；不能从每个 Rα 紧推出其任意并紧 |
| P4：扩大区域与上界 | P5/P7；Stp4 的 HullPoss 和 Values；∀z∈Values，z≤Θ | P1/P2/P3 的定义 | 原始输出到扩大族的关系包含；有效区域单调性；此数值步骤证明路线明确 |
| P5：同体积替代与 degree 校准 | P6；每个所用合格全局区域有源允许的 hull-approximant，global ℓ_out 不变；相对 determinant/正有理 tensor power 的 degree 读出校准 | P0/P2/P3/P4 的区域、原文线丛/实化 Frobenioid | III 3.9.5(i)–(iv),(Ob1)–(Ob9)；EssLgc Stp5–6；局部矩阵恒等式可复用，完整源定理仍缺 |
| P6：实际 q-pilot 的双构造比较 | P7；独立构造 native-q 与算法输出读出，证明一个源允许整包选择在 q-pilot 上给相同类/读出，且实现区域合格并位于 H 内；推出 Q∈Values | P0–P5；独立 Rq/Q；具体 gluing、下降及读出链 | Stp1–8、III xi-a–f；2026 Formalization 四个三角形及 LANA η 比较作展开字典；不能新增相容性为输入假设 |
| P7：数值收尾 | C9/C10；Θ 有限且 Q≤Θ | Q、Θ、Values | P3 有限性＋P4 boundedness＋P6 realization/approximation；初等序论，无新的算术内容 |

主要边：P7→P3/P4/P6；P6→P1/P2/P5；P5→P2/P3/P4；P4→P2/P3；P3→P1/P2；各对象经 P0。类型依赖只要求上述对象已准确陈述，不把所有证明完成作为上层探索门槛。

## 各包的证明路线与不可偷换之处

### P2：先做归一化账目，不用一个 finrank 代替全部权重

IUT III Remark 3.1.1(ii)–(iv) 对选定地方 tuple t 使用来自局部扩张次数的 N_t，并有对应有理地方的归一化因子 Z；procession 又有自己的平均。直积区域上先用乘积测度公式取 log，再按这些正系数求和，减去同样权重的单位参考项，最后作 procession 归一化。一般区域使用其 E-weighted 构造。

具体交付须逐项列出 N_t、Z、procession 系数、determinant tensor power 和参考项，并证明它们来自同一输入。当前单 tensor block 的 1/finrank 可能是其中一个局部因子；它与论文完整 ℓ_f 是否相同需要计算，不能直接命名相同。单纯 Haar 测度常数在 log 差中消去，不等于地方权重和全局归一化也自动消去。

单调性的自然语言证明：R⊆H 给每个使用的质量项 μR≤μH；由 μR>0、μH<∞ 转为正有限实数；实对数单调；减去相同参考项，乘相同正权重并求有限和/有限支撑全局和；得到 ℓ_out(R)≤ℓ_out(H)。若使用 E-weighted 非直积版本，先证明其区域构造保持包含，再应用相同论证。

### P3/P4：来源、有限性和扩大关系分别证明

从 P1 的源输出和 Ind 控制建立各 U_i 的一致相对紧性/局部界，而非定义 U=canonicalHull。按原文构造 H。有限地方用实际积分模块 hull 的紧性、非空内部/非退化条件得到正有限质量；无穷地方使用相应径向区域。证明全局几乎处处局部 log 为零，才能从局部结论得到有限 Θ；区域逐点等于标准单位不是必要条件。

对于每个原始 Rα，先有 Rα⊆U⊆H；许可扩大只增加选项，所以保留原始输入输出的关联。对扩大族每个合格 R，用 P2 得上界。注意，这证明的是已有 output family 的 boundedness，尚未证明 q 输入被覆盖。

### P5：全局等体积，不要求不成立的逐地方密度

沿 Remark 3.9.5 定义原区域的 hull-approximants，区分有序上下界的 Φ 与同体积的 Ξ。先做有限地方的积分区域替代，再用源允许的无穷地方调整以匹配 global ℓ_out；实际适用条件和参考结构必须逐项展开。还须保留包含链：若 P⊆H，则 φ(P)⊆φ(H)=H，而源 approximant A 满足 A⊆φ(P)，所以 A⊆H。全局等体积本身不推出包含；无穷地方调整也必须满足这个约束。所得替代不必逐点等于 P，或在每个地方有相同体积。

在相同 arithmetic holomorphic structure 下，按 Ob3 的相对 determinant、单位结构 sheaf 校正及 tensor power，证明其 degree 与 P2 的相应 ℓ_f 一致。数值消费者可以用已证明的读出等式省去中间对象。现阶段缺少“实际全局区域→实际线丛/degree”的源实现，不能把这一段写成已完成的自然语言证明。

### P6：固定 gluing 后维持关联，最后才能取数值

这是仍需精细研究和构造的中心，不是给任意结构加一个 named sorry 即完成。

1. 固定实际 q-pilot 及 Θ-link 的原始 gluing。输入对象含单位部分和值群部分，不是一个已脱离结构的 Real。
2. Stp1 用实际 Kummer/Galois evaluation 重构 Θ-pilot 为允许表示的一种；需要具体源箭头和表示覆盖的证明。项目已有三腿方块构造仅能在这些腿和单位部分已经存在时复用。
3. Stp2–3 沿允许的忘却/下降扩大可能性，证明算法对这些操作相容，并保留固定 gluing 的关联。不能任意识别两边的环结构，也不能只保留一个标量相等式。
4. Stp4 使用 P4 的扩大，Stp5–6 使用 P5 的同全局值替代和 degree 校准。逐步保留关联的对象级含义。
5. Stp7 对所有 m 的 (1,m) 输入→(1,m+1) 输出作源给定的同步，应用目标侧 log-Kummer 的读出相容性修正移位。须证明它与实际 q 输入的读出一致；不是把下标重命名后 rfl。
6. Stp8 在最后共同读出中得到 q 的数值实现。当前选定路线是：先定义两个独立的实际构造，再证存在源允许选择 J，使其在实际 q-pilot 上的比较成立；由构造的合格性/包含性证明取得 R_J∈HullPoss 和 ℓ_out(R_J)=Q。可用 LANA 的 η^q(p_q)=η^anab_J(p_q) 描述待展开的比较，但 η 的类型与每条复合箭头必须先绑定主文。整条 η 映射相等是更强的可用结果，不必无依据地要求额外强度。单独的 epsilon/上界传递结论只记作数值后果，不替代这项源识别任务。

当前最大的未知是步骤 2 的实际表示覆盖，以及步骤 3–5 在项目完整源对象上的相容与读出识别。这些需要继续按 III Th.3.11 与相应 Kummer/evaluation 定理分解。EssLgc 提供清晰路线，但没有替项目构造这些对象，也没有把所有必要等式变成现成 Lean 供体。

不要走“Q∈Values 因为都在 ℝ 中”或“两个值群抽象同构所以 q 值相同”。也不要把 Stp7 的最终共同容器解释成一开始就有一个跨两边环结构的集合级恒等映射。所需的相容性发生在源规定的具体操作和读出上。

### P7：有限/无限分支

Values 保持 Set ℝ，Q 保持 ℝ；在已证明源 hull 非退化、全局扩展读出有定义的条件下，Θ 暂在 WithTop ℝ，比较时嵌入。零质量对象不属于该定义域，不能用 WithTop 掩盖可能的 −∞。Θ=+∞ 时上界和 Q≤Θ 平凡，但不因此得到 Q 的输出实现或 epsilon 逼近；源 Cor.3.12 还要求 Θ 有限，故必须完成 P3。不能把 top 分支的平凡不等式当最终结论。

有限分支设 Θ=θ。若 P6 给精确实现，直接应用 P4。若给一侧 epsilon 条件，反设 θ<Q，取 ε=(Q−θ)/2>0，得到 Q−ε≤z≤θ，与 θ<Q−ε 矛盾。这里无需 Values 自身闭集、无需 attained maximum，也无需先证明所有实数≤θ 都能出现。

若要把论文的整个 ℝ≤Θ 与本实现 Values 认作相等，另证可达性/饱和性；C9 上界推理本身只需上界加 q 的实现。不能通过把 Values 定义为 ℝ≤Θ，再把 q membership 当“源构造”来绕过 P6。

## 已调查的复用与适用边界

下列均是读取源码确认的候选复用，不是本轮重新编译/公理审查的结论。

| 已有供体 | 可复用内容 | 尚不能替代 |
|---|---|---|
| SourceDefinition31Quantifiers：SourceNativeInitialThetaData、V_mod_bijection | 正确的选定地方及算术塔输入 | 完整源 L 和实际表示的构造 |
| SourceEWeightedLogVolumeData：kappa_log_eWeightedVolume_eq_weightedSum | 非空有限索引、正 cardinality、σ-finite 测度及合格直积区域的加权乘积 log 公式 | 实际 N_t/Z/procession 数据的代入，任意区域扩展与全局算术识别 |
| FinitePlaceNormalizedUnitScalingLogVolume 的 normalizedLogVolume/mono | 单个实际 tensor block 的有符号参考归一化与正有限质量下单调性 | 选定地方权重、整个 procession 和全局 log-volume |
| C6ActualIdentification：IsActual、actual_isActual | 排除默认字段被覆盖导致的任意 B 函数 | canonical hull 等于源 hull，以及该局部读出等于论文 L |
| LocalFieldIntegralHull：exists_compact_integralModule_hull | 在其有限乘积、properness、相对紧及各坐标非退化条件下构造紧积分模块 hull | 源 Ind 后的 U 满足这些条件；无穷地方和全局部分 |
| LocalFractionalIdealUnitQuotient、FinitePlaceFractionalIdealUnitQuotient | 局部单位商到可逆分式理想的实际等价；代表元选择不影响理想 | C4 值幺半群识别为该商；完整 tensor packet 或跨结构输运 |
| SourceKummerEvaluationSquareExtension：ofThreeLegs、sourceKummerEvaluationSquare_nonempty_iff | 三条实际箭头和 lower unit portion 给定后的方块组装/共轭公式 | 实际三腿、单位部分的源存在性及全局 numeric q realization |
| SourceSHETransportObligations：sourceOneColumnLabelBinding | 已有模型中的一列算术字段一致 | 各 holomorphic/ring 层的忠实实现，P6 所需全部关系 |
| HullDeterminantLogVolumeReduction | 矩阵 determinant 和部分有限权重账目 | 实际算术线丛及相对 determinant 的源识别 |
| ArithmeticQPilotBaseChange/GlobalNormalization | 完成域范数/局部扩张 log 关系及全纤维求和公式 | 原文所选 section 与全上方地方之和不可未经证明互换 |
| Group6Normalization、C8 当前 rfl | raw log、参考 log、局部 normalized log 的定义等式 | 独立 arithmetic degree 的比较 |

Mathlib 查询已定位 Haar singleton 平移不变、Real.log_zero，以及生产 normalized monotonicity 所需的质量条件。无需为机械替换 w.1/w.2.1 写测试；本轮也没有重新构建这些供体。

## 推荐下一包：两条读出链与一个准确比较命题

已有 P0/P1 表继续复用；本轮补充研究已把下一包缩到 P6 的双构造比较。以主文 Th.3.11/Remark 3.10.2/3.11.1、2026 Formalization §4 和 LANA 对应构造为依据：

1. 独立写出 native-q 的 BPS→实际 divisor/region→degree 链，以及 BPS 的 étale-unit 部分→Kummer/evaluation→log-shell action→区域→hull/degree 的算法链；每条箭头写明列、行、单位和值群信息。
2. 给出完整选择 J 的源约束，并区分构造存在、对允许同构的相容、Ind3 的上半相容。不能用 connected groupoid 中任意两对象同构替代算法产生的 IPL。
3. 在同一个目标侧框架中陈述实际 pilot 上的比较，保留此前所需的 Prop.3.9 校准、所有 m 的移位及全局替代包含链。列出比较的 statement dependencies 与 proof dependencies；不能把比较本身装进输入结构。
4. 将望月的 dsc→hull+det→SHE 四个三角形逐个映射到这两条链。特别登记 “3.11→3.11.5” 的 APT/IPL 和 “3.11.5→3.12” 的 SHE/IPL 责任，禁止把后者条件偷偷命名为已经有的 Th.3.11。
5. 对缩放作数学反查：j²/平均、地方权重、参考项和符号必须可追踪；不允许为了交换而抹去 j²，也不允许任意扩大 H 获得一个后续 IUT IV 无法使用的上界。

验收物是两条可逐箭头核对的源构造链、一个带完整量词与类型的比较命题，以及其自然语言证明或精确剩余子命题。只有换名称、抽象同构存在性或 Q≤Θ 的重述不算完成。P2 的通用计算与实际构造可按依赖交错推进；本 chat 不派发 subagent，也不写 Lean。

## 本轮状态

### 研究期间的工作区版本变动

其他工作在本轮研究期间更新了 C9ValuesPaper/C9Paper。本记录没有参与这些 Lean 修改。旧 singleton 与旧自由 Q 的审查结论对应上轮冻结 hash，不能冒充对新文件逐项审查的结论。本轮结束时另读了两个新文件的相关定义，并在证据 JSON 记录观察版本：

- 新 C9ValuesPaper.outputRegion 是所有 c : D.Choice n x 的 T.thetaImage n c 的集合，参数 _w 未使用。Choice 仍是有限 SignedLabel，因此这只是有限点像；在实际非原子 Haar 场景下仍质量为零，不能因为不再是 singleton 就获得合格区域语义。它也仍未绑定 witness 的实际输出、源 Ind、整包组装及允许区域条件；B 参数仍未消费 IsActual。
- 新 C9Paper.QPaper 将 qPilotRegion 固定为 tensorUnit 的 singleton，而 qPilotLogVolume 直接绑定 localSignedLog C3.q；这使 scalar 等式可由字段推出，但没有证明该 singleton 的体积等于这个标量，更没有得到完整全局 q-pilot 的 log-volume。Theta 的 thetaToC6 与 Values 的 provenance 在本次所读版本仍自由。
- 新文件的非空/字段等式不能作为 P1/P2/P5/P6 的完成证据。这里是定向语义观察，未编译，也未覆盖其全部消费者。

- 交付：主文及六份补充说明的定向研究、五项路线修正、P0–P7 的两类依赖、局部证明步骤、供体边界和下一包。
- statement_compiles：未运行；未写 Lean。
- proof_body_checked：未运行。
- kernel_closed：未运行；源桥仍开放。
- target_accepted：false；旧 Values/C9 对象未因本记录获得验收。
- comparator、全 Project 构建、传递公理检查、独立审查：均未运行；本轮为 root 自审。
- 没有删除 imports/源码；逻辑上不再采用 singleton readout、弱常函数 C4→IQ、任意 provenance、各 j 独立 pilot、无条件局部 q≤Θ、强制全 value-monoid 单值 lift、先完成全部 determinant API 等错误或不必要的前置路线。
