# C9 路线一致性复核：修正后的执行依据

2026-10-23；owner：本 chat root。用户要求自行研究、吸收外部讨论、核对路线后只改实质冲突；本轮不写 Lean、不派发 agent。实际消费者为 C9 的源 Values/Q/Θ 构造、P6 比较以及 C10 Cor.3.12；阶段为 SHEAF stage 1。

## 判断

保留“完整源输出族 → 目标侧逐分量 hull → 合格区域的实际全局读出 → q 比较”的主方向。这比 singleton、有限 label 点像或自由 theta map 忠实。复核确实发现需要改动的语义与证明组织问题，已同步修改主路线 C9-STAGE1-SUPPLEMENT-ROUTE-20261023.md。原文件按字节保存在 *.pre-consistency.md，SHA256 为 4d6256789c99648f9de14d8ef7c434e730e8014d006522b0f356356252c3136b。

本次没有发现足以否定这条带完整源结构路线的矛盾；这不是该路线已通的证明。核心待证点已进一步明确为两条实际构造在 q-pilot 上的相容性。我们选择研究这个具体命题，不把用户的正确性倾向写成假设，也不以争论尚存为由停止工作。

## 实质修正及理由

| 旧路线中的问题 | 修正 | 依据/检验 |
|---|---|---|
| Adm 要求几乎处处等于参考单位区域 | 改为几乎处处局部归一化 log-volume 为零；前者仅为充分条件 | III Prop.3.9(iii)，PDF p.117。不同区域可能具有同一体积；加强为集合相等会缩小量词 |
| 一开始就用同一个 L 读 q、输出与 hull | 分框架 ℓ_f；原生 q、输出先独立定义，参考校准/列内移位后才比较 | III Prop.3.9(ii),(iv)，EssLgc Stp7；S-S 对 degree 缩放的检查、LANA 双 η 构造 |
| 所有允许表示变化都要求读出不变 | Ind1/2 的对应规范化读出不变；Ind3 单向控制；hull 为包含扩大；Ξ 为全局等体积，各自独立 | III Cor.3.12 proof (x)，PDF p.180–181 的相关段落 |
| 把 RawPoss、U 和合格 region 视为同一类型；并记号容易丢失相关性 | 分开 pre-region、分量并 U_i、hull H_i、合格读出区域；α 保留整包兼容 | III Remark 3.1.1(iii)，Cor.3.12 pp.174–175；不能由各输出紧推出其任意并紧，也不能从逐分量存在推出整包存在 |
| 全局等体积替代没有明确保留 hull 内包含 | 同时证明 A⊆φ(P)⊆φ(H)=H；无穷地方调整也受此约束 | III Remark 3.9.5 的 hull-approximant 条件；等体积本身不蕴含包含 |
| 把上界传递作为 P6 的主要细化 | 保留为数值 corollary；主任务改为源允许选择下的双构造比较及实现区域证明 | 当 H 合格时 max Values=θ，所以 Transfer(Values,Q) 等价 Q≤θ。原路线的等价证明有效，但没有减少源缺口 |
| 前部宣布不再重做 inventory，末尾仍以 inventory 为下一包；旧 x 任务仍阻塞 | 复用现有表，下一包为两条读出链和一个精确比较命题；源配置直接替代未识别 x | 内部任务冲突；不改原数学量词 |

另外补齐两个边界：固定配置仍包含 Stp7 所需完整列及所有 m；WithTop 只能在排除零质量/−∞并建立扩展读出后使用。+∞ 自动给数值上界，不自动给 q 的输出实现，最终仍须证明 Θ 有限。

## 外部讨论如何改变实际路线

### Scholze–Stix：保留缩放信息，不拿抽象同构代替具体比较

读取 July 16, 2018 的十页原文，重点 pp.7–10。其具体警报是：抽象 pilot 的识别与具体 divisor 的 degree 读出之间有 j²（或 procession 平均）缩放；把所有实直线提前平凡化，再要求各路径同时保持 degree，会产生不相容。

对本项目的结论：若 Lean 路线依赖那个直接标量比较，必须修改。我们不要求 Θ-link 保持两边原生 degree；改为保留单位部分、值群部分、构造路径，最后在目标侧比较。反过来，仅保留标签也不能证明相容，仍要交付实际比较定理。S-S 对完整 IUT 的否定判断与这里已经验证的“某种标量化会失败”分开记录。

来源：[Why abc is still a conjecture](https://www.math.uni-bonn.de/people/scholze/WhyABCisStillaConjecture.pdf)。

### 望月 April 2026：不能把加强后的 3.11.5 当作原来的 3.11

读取十四页报告的正文 pp.1–11，重点 §4 pp.9–11。其图明确分出 dsc、hull+det、SHE，并把 3.11→3.11.5 的 APT/IPL 与最后 3.11.5→3.12 的 SHE/IPL 分开。“3.11.5”是报告使用的重组名称，不是主文现成定理。

对本项目的结论：允许沿这个分解研究，但每个三角形都要有实际数据和证明；不能给黑箱加入已经含 q 比较的字段，再把后面的短证明当作 Cor.3.12 的源闭合。报告描述的是 skeletal 工作，不能当作我们已有可调用且源实现完成的 Lean 供体。

来源：[On the Formalization of IUT, April 2026](https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf)。

### LANA July 2026：用两个实际 η 构造定位比较，而不是停在口号

读取 revision 1.0.1（2026-07-20，commit 293bdd89463473ae13d40834d70fb4b7ba81da1f）的算法、3.11→3.12、Points to be clarified 和 S-S examination 各节。报告把原生 q 的构造与从 BPS 经 anabelian/Kummer/log-shell 过程得到的构造分开，提出寻找合适积分结构使两者相容。其判断仍保留，明确说尚无该比较的证明。

本项目采纳它作为更具体的研究字典：构造 η^q 与 η^anab_J，核对源对象后比较它们在实际 pilot p_q 上的值，并交付合格输出区域。完整映射相等可以充分推出该比较，但若实际消费者只需 pilot 上相等，不擅自增加强度。J 是源允许的整包积分结构选择，不是可以任意调体积的参数。

这不等于认定 LANA 的再表述已经与主文等价；下一包须逐箭头核对。报告也同意 S-S 图的非交换，但不同意仅凭该图就否定预期的同侧比较；我们因此将它用作模型反查，而不把它的立场当作数学结论。

来源：[LANA report，固定版本](https://github.com/katobungen/LANA_report_202607/blob/293bdd89463473ae13d40834d70fb4b7ba81da1f/LANA_report_202607.tex)，重点 labels `sub:theMainGoal`、`sub:SSEtaStructure`、`sub:SSActualComparison`、`sub:SSAssessmentNew`。

### Dupuy–Hilado：数值计算可借鉴，版本必须分清

arXiv:2004.13228v1 (2020) §3.10 给出 selected-place、tensor/average 与 divisor-degree 的具体转换，适合逐行核对 P2/P5 的符号和权重。该处明确限于其所列条件，不能直接覆盖任意输出区域、无穷地方替代或 P6。

2025 的 v2 已缩为 Initial Theta Data，正文明确不处理 UΘ 的复杂构造。不能把新版已发表文章的身份用于担保旧版全部区域构造，更不能引用它作为核心比较已证的依据。

来源：[v1](https://arxiv.org/pdf/2004.13228v1)、[v2](https://arxiv.org/pdf/2004.13228v2)、[作者论文列表](https://tdupu.github.io/papers.html)。读取为 v1 引言/§3.10 与 v2 引言及范围核对，不声称精读两版全文。

## 修订后的唯一主路线

固定合格源输入 (S,L) 及实际 link/列数据。

1. **P0/P1：实际构造。** 从完整源选择 α 产生各框架的整包输出；保留单位和值群、Kummer/evaluation 复合、允许 Ind 及相互兼容。旧 C4 点 witness 只能作为待识别的分量供体。
2. **P2：带框架的读出。** 定义各 ℓ_f；明确地方、tuple、procession、参考项及 degree 符号。证明每种实际映射对应的等式或单向不等式。
3. **P3/P4：源 hull 与 Values。** 逐分量 U_i=⋃αRα,i，H_i=Hull(U_i)；证明统一局部控制、非退化、全局有限性。实现 Stp4 后，HullPoss={R | Adm_out(R) ∧ R⊆H}，Values=ℓ_out '' HullPoss。通过单调性得到 boundedness。
4. **P5：全局替代和 degree。** 构造源允许的同体积 hull-approximant，同时保留包含链；独立证明其数值 degree 识别。Ob3-3 允许省去显式 determinant 中间对象，不能省掉这个比较。
5. **P6：双构造比较。** 原生 q 链独立给 Q；算法链从同一固定 gluing 数据构造输出。证明存在源允许 J，使实际 q-pilot 在两条链的校准读出一致，且相应 R_J∈HullPoss。因此 ℓ_out(R_J)=Q，得到 Q∈Values。
6. **P7：数值收尾。** 由 membership 和 boundedness 得 Q≤Θ，加上 P3 的有限性。Transfer 与 epsilon 近似保留为推论/旧接口适配。

P6 不能被简化为“两个对象同构”“两边都在 ℝ”“选一个 inhabitant”或“它们有共同容器”。其声明中，两个构造必须独立于待证等式定义；J 的范围不能引用 Q≤Θ 或相等本身筛选。后者只是在定义中藏入目标。

## 可以确定的数学结论与尚缺工作

已有 P4 条件单调性、Transfer↔一侧 epsilon、P7 初等收尾的自然语言证明保留，未发现错误。进一步有：若 θ 是 Values 的最大值，则 Transfer(Values,Q)↔Q≤θ。正向取 b=θ；反向任意上界 b 满足 θ≤b，再传递 Q≤b。

因此，单有区域有界/体积规范化不会产生 q 比较。例如纯数值模型 Values=(-∞,-2]、θ=-2、Q=-1 满足所有上界/最大值条件但不满足 q 比较。这是对弱数值接口的反例，不是对源 IUT 输入的反例；它说明缺失的工作必须落在源 q 与输出构造之间。

下一包的验收不是再写库存表，而是交两条带完整类型的构造链和一个实际 pilot 比较命题，并将未证明的每一复合相容性挂到源定理。当前源 P1/P5/P6 仍开放；尚不能宣称 C9 整体 stage 1 已完成。

## 与其他工作流的衔接及检查

- C9-TARGET-V3.md 是另一工作流的旧锁定候选，尚未接受。本次未覆盖其文件；它的 almost-everywhere reference unit、统一 L、自由 allowedStp4 和旧 next task 必须按本记录同步后才能接受。C9-P0-P1-SOURCE-TABLE.md 的索引也应继续区分 lattice 整数坐标与有限 procession 索引。
- root 所有的主路线及研究节点已更新；STATE、queue、AUDIT_LEDGER 和父节点追加本复核证据。既有 P0–P7 节点沿用，不复制一套 DAG，也不宣称其他 owner 已完成同步。
- 本轮文献扩展为上述直接相关原始讨论；没有声称“看完网络所有讨论”。新文件与版本见 C9-ROUTE-CONSISTENCY-EVIDENCE-20261023.json。
- 新 PDF 另以 PDFium 渲染并目视核对：望月 2026 pp.10–11 的四个三角形与两段推导图、S-S p.10 的六边形、Dupuy–Hilado v1 p.16 的 degree/volume 公式。图像保存在 tmp/pdfs/valuespaper-consistency-20261023。
- statement_compiles、proof_body_checked、kernel_closed、comparator、Project build、独立审查：未运行。target_accepted=false。只有 root 自审、文档一致性与证据文件校验；未更改 Lean 源码。
