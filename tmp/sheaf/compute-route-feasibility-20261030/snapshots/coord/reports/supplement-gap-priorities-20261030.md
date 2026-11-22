**按照望月后续补充路径，围绕当前缺口决定做什么、不做什么**

2026-10-30；单线程；root 自审。用户已确认依据是 Formalization of IUT（April 2026）§4 和 Essential Logical Structure（March 2024）的 Stp1–8。本次是对[上一份探索报告](D:/lean/coord/reports/gap-exploration-20261030.md)的优先级修正，不是又一轮全库盘点。没有新增数学证明。

**要修改上一份报告的排序：先攻固定 gluing 下的源比较；K 侧根、通用张量、Haar character 等暂列为按需调用的支撑工作。** 上一份报告证明了它们值得复用、值得纠正，却没有证明“先做它们”就能解除当前核心阻塞。数学上正确、与 IUT 有关、甚至将来必须完成，都不足以说明现在该优先做。

这里有两个不同的目标：一是弄清补充路径的条件推理，二是让我们的实际源对象满足其条件。只完成前者，或把后者放进新接口字段，不能算缩小独立证明的缺口。

**两份补充说明给出的工作边界。**

2026 报告将 3.11→3.12 拆成两段：前段以 APT/IPL 处理 descent 和 hull+det，称其结果为重组后的“3.11.5”；后段以 SHE/IPL 做同时比较。第四个三角形是在 q-pilot+etHT 的特例上限制同一个 HDD。报告也说明，前两阶段不必先完成抽象 ZFC/species/mutations 的一般形式化。[Formalization，§2 pp.4–5、§4 pp.9–11](https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf)

EssLgc 的 Stp1–8 保留固定 q-pilot 与原 Θ-link gluing，在 Θ 侧逐步引入允许的不定性，经过 hull、全局体积替代、determinant 和 1-column log-shift 后读取数值。pp.154–156 明确区分这条路径与“先取两个独立映射、再比较它们”的做法。[EssLgc，§3.10 pp.148–156](https://www.kurims.kyoto-u.ac.jp/~motizuki/Essential%20Logical%20Structure%20of%20Inter-universal%20Teichmuller%20Theory.pdf)

据此，本项目应当研究的是：**同一组固定输入之间的关联，能否由实际构造一直保留到最终读数。** 不应擅自把“两个任意独立的完整映射相等”升为唯一目标；也不能因为源文称关联始终固定，就省略在 Lean 中表达和证明该关联。2026 图中本来就有交换三角形；需要避免的是改成另一种独立选择问题，并非取消所有相容性验证。

**先定位真正阻塞消费者的地方。**

当前 [PaperXiFCompileGate](D:/lean/tmp/sheaf/xif/paper/PaperXiFCompileGate.lean:69) 的最终入口仍消费 ThetaLinkActual 和 hlink。[ThetaLinkActual](D:/lean/tmp/sheaf/xif/paper/ThetaLinkActual.lean:166) 则含：

\[
  \mathrm{link\_identification}
  \longrightarrow
  O.\mathrm{qPilotLogVolume}
  \in \mathrm{hullLogVolumeRay}(P.\mathrm{signedHullLogVolume}).
\]

这个字段就是源 link 如何给出最终数值比较的责任。[PaperXiFProof](D:/lean/tmp/sheaf/xif/paper/PaperXiFProof.lean) 把它传给最终消费者，没有在该文件构造它。因此，增加一个正确的局部域引理后，如果这里仍原样要求这个字段，并且没有新构造能供应它，核心缺口没有因此减少。

以下直接消费者有助于把责任定位得更具体：

| 当前消费者/实现 | 实际提供了什么 | 还没有因此得到什么 |
|---|---|---|
| [SourceMultiradialIplLinkWiring](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialIplLinkWiring.lean:190) | reduced wiring；明确登记 algorithmic provenance 的源义务 | 实际算法的输出/操作与对应 full-poly prime-strip 箭头之间的源实现，以及它与固定 q 输入的关联。 |
| [IPLAPTActual](D:/lean/tmp/sheaf/xif/paper/IPLAPTActual.lean) | 给定 Kummer/evaluation/link 等数据后的 factorization 与运输包装 | 算法实例、完整源层、SHE landing、Ind3 和列间移位由这些包装自动产生。 |
| [SHEOutputActual](D:/lean/tmp/sheaf/xif/paper/SHEOutputActual.lean) | 真实局部环中的单位截面读取，以及输出记录的字段一致性 | 其读取不依赖输出 o；文件末尾自己保留实际 output→section 的义务。仅凭此实例不能推出待证 q 读数关联。 |
| [SourceArithmeticHolomorphicLanding](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/SourceArithmeticHolomorphicLanding.lean:555) | 完备化上的系数对象与条件化 landing 入口 | 实际源输出的 operation-level 表达仍须供应。 |

这些是所检查的直接消费者的现状，不是全库不存在其他构造的声明。已有 [10-26 FinalEvaluationQMark 审查](D:/lean/tmp/sheaf/n8/closure/C9-FINALEVALUATIONQMARK-DEPENDENCY-AUDIT-20261026.md)和[marked trace 的更正](D:/lean/tmp/sheaf/n8/closure/C9-U2K2-SQ3-MARKED-TRACE-20261026.md)已经指出相同边界；本次复用它们，不把重新命名或再次发现这个缺口当新进展。

**当前应保留一条主线，但不能把缺口藏在 3.11.5 内。**

工作链为：

\[
 \text{同一合格源输入与固定 gluing}
 \ \xrightarrow[\text{APT、IPL}]{\text{dsc；hull+det}}
 \text{带源关联的 HDD/3.11.5}
 \ \xrightarrow[\text{IPL、log-shift/readout}]{\text{SHE 特例}}
 \text{规定的 q 与 hull 比较}.
\]

这是任务依赖图，不是本轮证明。

前段与后段要各有可核对的义务。先把整个 3.11.5 当成包含最终比较的黑箱，然后证明后段很短，只是把缺口搬了位置。反过来，也不用等整个 IUT 的全部早期基础都重建后才研究后段：可以使用准确的源定理作显式条件进行探索，所有传递依赖继续标为未闭合。

尤其要核对：HDD 的区域和读数确由 3.11 的那个允许像族及规定 hull 产生；SHE 使用的是原先固定的 q，而不是把 q 重新定义为 HDD 的输出读取。仅按定义写出 HDD=(hull+det)∘dsc、再写 HDD∘SHE，会得到复合关系，却没有自动证明这两项源身份。

在我们当前的形式化中，直接工作应收敛到下面三项：

1. **实际输出的源身份与固定 BPS 关联。** 给实际算法输出一个有来源的 prime-strip/区域解释，证明其关联由该次算法操作及原 gluing 产生。一个任意同构、相同 carrier 或常值读取都不够。这里不预设所有不同输出必须有相同体积。
2. **HDD 对该关联的保留。** 区分允许像族的扩大、hull 包含、全局等体积替代与 determinant 归一化。各步骤需要什么，只证明什么；不得以“都在一个范畴”替代源输出身份，也不得把独立分量任意拼接成源允许的整包。
3. **q 特例与完整 1-column 的 log-shift/readout。** 将上一步同一构造用于规定 q 输入，处理各 m 的移位及同步关系，最后识别带参考区域、权重、符号的全局读数。不能把两边都映到实数，就认作同一个读数；也不能把 log-shift 换成有限循环或固定点问题。

前两项承担“3.11.5 到底包含了哪些已证内容”；第三项承担最后比较。若某个步骤仍无法从已列源输入推出，应停在该精确子命题上，不自动转去扩建另一块数学库。

**做与不做的具体清单。**

以下“暂不做”是本 chat 为当前缺口给出的取舍，不是宣布该数学永远无用，也不改变其他 chat 的 owner 或并行安排。

| 工作 | 当前决定 | 何时才值得做/恢复 |
|---|---|---|
| 固定 gluing 的实际输出解释与 IPL 来源 | **直接做** | 已有明确消费者：algorithmic-provenance、HDD 及最后 link 比较。每次完成须提供具体源构造，不能只填 predicate。 |
| APT 对允许不定性及 HDD 的相容性 | **直接做其实际缺失部分** | 必须指出哪次源操作、哪项关系被保留；已有条件 exchange/transport 引理直接复用。 |
| SHE 特例、Stp7–8 的读数与移位 | **直接做** | 必须消费前段同一源对象；逐项识别 q 读数和 hull 读数，避免再次写入结论字段。 |
| 有限 \(p\)-进 tensor/hull、Haar 正有限性 | **按实际前提调用** | 上述比较明确需要某个源区域的紧性/质量时，先实例化已有供体；不再为“更通用”而独立扩建。 |
| K 侧 q、\(2l\) 次根、地方运输 | **保留语义纠正，降低建设优先级** | 只有证明实际 evaluation/mark 关联时确实缺此根或参数比较，才开该小包。F/K 误用一旦出现立即纠正，但这不等于要先重建整条根论。 |
| 默认范数与 spectral 范数公式 | **按读数校准需求修复** | 某个确切 readout 等式调用它时，修到该消费者需要的范围并验证；不为无消费者的全域公式扩张任务。 |
| E=rootStackExtension 的一般 Haar character 公式 | **暂不作为主线** | 先证明 E 是此源比较所需的表示，并给出调用该公式的具体前提；否则保留已有 L 层模板即可。 |
| 更复杂的 root stack、泛化 line bundle、完整范畴机械设施 | **暂缓泛化建设** | 某条实际源箭头确实不可在已有准确接口中表达时，再补最小结构；不能仅凭对象名字相近推进。 |
| IUT IV 常数优化、ABC 数值收尾 | **不作为当前攻缺口任务** | 当前源比较闭合、或它明确要求一个特定数值叶子时再做。 |
| 一般 ZFC/species 基础；完整早期 anabelian 库重建 | **不先做** | 独立最终闭包可以需要早期定理；本轮条件路线分析不以先完成所有基础为门槛。 |
| 已有标量收尾、更多 Final/Card/Required 包装 | **停止重复** | 只有它们的输入类型因实际源构造发生必要变化时才维护。 |
| 新的 toy 数值模型、抽象闭环或批量“无路可走”反例 | **不继续扩张** | 只在检查一个正在消费的具体接口时使用，明确适用域；不能替代完整源对象的证明/反例。 |
| 其他作者替代路线或进一步争论综述 | **本轮不展开** | 当前依据已由用户固定为两份望月补充说明；除非特定供体直接解决已登记前提。 |

这也修正上一份六路线排序：原来的 F 应收敛成上面的固定-gluing 主线；A/B/C 是被具体源比较调用的支撑；D/E 只有出现明确调用才进入本包活动范围。不能把六条都持续作为“主线”。

**如何判定一个任务真的在攻缺口。**

开工前必须能填完这条句子：

> 当前消费者的某个具名前提 P，属于补充路径的某一步；本包用指定的更早源数据构造它，完成后消费者能够删除或由真实供体实例化 P。

随后检查三个条件：

- **来源没有换。** 同一 C、同一固定 gluing、源允许的选择范围与读数约定保持一致。只改变中间呈现方式时，附消费者可用的等价/运输证明。
- **责任没有藏。** P 没有变成 Q≤H、q membership、完整 readout comparison 的别名或新字段；也没有被换成另一个同样未展开的“compatible”。
- **退出点明确。** 本包要么供应具体见证/证明，要么交付一个比 P 更精确、非循环、可继续消解的源子命题和失败原因。第二种只是研究推进，不能报告为数学闭合。

这不是简单统计剩余字段个数。一个前提拆成几条可独立证明的具体等式可以有用；许多无消费者的绿色定理仍可能不改变目标。数学任务是否进入当前主线，取决于它在这条责任链上的作用。

**下一包只做什么。**

建议下一包固定为：**给当前实际 multiradial 输出补上源 prime-strip 解释及其固定-gluing 的 IPL 来源。** 精确消费者是 SourceMultiradialIplLinkWiring 中的 algorithmic-provenance 义务，并说明这个结果如何供给 HDD/SHE 的同一次构造。

本包使用同一个合格源 C 和已固定的 gluing；选择当前算法里实际出现的输出/最终 evaluation，逐项给出它的源对象、对应 strip、Kummer/evaluation 复合及输入端。先查已有 full-poly 供体；若 reduced Output 类型已经丢掉这些数据，就修改准确的中间陈述并同步消费者，不能向该弱类型硬填一个任意 strip。

交付只有两种合格结果：

1. 构造了这条实际联系，并证明它确由算法与固定 gluing 产生；列出后续 HDD/log-shift 仍需的条目，不能提前宣布最终读数已对齐。
2. 把第一个确实缺失的源引理精确到对象、量词、箭头及消费者；说明现有供体为什么不够，且不再自动开启不相关的根论、Haar 或范畴建设。

这项选择不是声称它必然能完成 IUT，而是因为它直接落在当前消费者已暴露的源身份缺口上。它比先完善一个尚无调用边的技术供体，更能判定这条补充路径在本项目中是否真的可以继续闭合。

旧 marked-map、完整双映射相等、exact output witness 均只保留为可能的充分实现方式；不把它们强加为补充路径的必要形式。[已有 scalar probe](D:/lean/tmp/sheaf/n8/closure/C9XiESourceConditionLogic.lean) 的 exact/单侧逼近收尾可以复用，但它的简化 executability 反例不是对完整 SHE 的反例。

**本轮结果与验收。**

已经完成的是优先级决定、两份补充材料与当前消费者的对应、以及做/不做和恢复条件。没有构造新的源箭头，没有减少已验收的数学 gap；这次工作用于避免把后续时间花在不能解除阻塞的分支。

statement_compiles、proof_body_checked、kernel_closed、comparator、Project build、独立审查均未运行；target_accepted=false。只进行了源文阅读、图像核对、代码文本追踪和文档/证据机械校验。完整版本记录见[证据清单](D:/lean/tmp/sheaf/supplement-gap-priorities-20261030/evidence.json)及[机械检查](D:/lean/tmp/sheaf/supplement-gap-priorities-20261030/verification.json)。
