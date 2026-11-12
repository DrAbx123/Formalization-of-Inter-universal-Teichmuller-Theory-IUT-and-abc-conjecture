七项 actual / exact 接口核对与下一包建议

日期：2026-10-30。单线程。范围是用户最新七项清单及其实际消费者 `iplAlgorithmicProvenanceCard`。此前四份报告保留原字节；本报告按新代码修正当前状态，不把历史“未找到”继续当作现在的结论。

**结论**

当前已有真实的 source-index→strip、索引操作、theta packet 的 logVolume 规律和有限 theta 标量像集。本包已把后两者接到 S1231 的 Core，得到通过 Lean 检查的 `Profile`。但这组操作与当前强 `Carrier` 不相容：`sourceInd3 1 = sourceInd1 (-1)`，前者被要求严格增层，后者被要求保持层数。这个冲突与选择哪一个 level 无关，已经形式化证明。它只否定这组明确操作与接口的组合，不否定其他源实现或 IUT。

相邻方形需要绑定实际箭头；当前“exact”类型还没有这样的绑定。Nontriviality 的现有命题则针对源作用，不是 evaluation 箭头本身非恒等。因而七项不能直接理解为“前四项齐了，只剩后三个证明体”。

**一、逐项状态与准确对象**

| 用户清单 | 当前证据 | 对应范围与未消除的责任 |
|---|---|---|
| Choice → strip：actual | [S1221](D:/lean/tmp/sheaf/xif/paper/S1221StripOfChoiceActual.lean:36) 构造 stripOfChoice；还证明等于 `(I.family.theater i).primeStrip`，并构造 linkOfChoice。正式 Output 文件也已有 stripOfChoice。 | 对每个合格 `I`，Choice 是 `I.family.index`。无需先构造一个具体 OriginalInput；不能据此把另一个有限 carrier 的 Choice 自动识别为它。 |
| source Ind operations：actual | [S1225](D:/lean/tmp/sheaf/xif/paper/S1225SourceChoiceCoreActual.lean:43) 给出水平/垂直置换幂和 translate；[S1231](D:/lean/tmp/sheaf/xif/paper/S1231SourceCoreActual.lean:76) 证明 Core 规律。 | 这些是实际定义的源索引操作。其与补充原文的 Ind1/2/3 算法操作、允许不定性及对应 strip 箭头的识别，不能由名称或群律推出。 |
| logVolume laws：actual | [S1232.sourceLogVolume_eq](D:/lean/tmp/sheaf/xif/paper/S1232LogVolumeShiftActual.lean:34) 由 family.link_q 证明整个索引族的 thetaPacket.logVolume 相等，继而得到 S1225 的全部 shift laws。 | 这是有限 theta packet 的标量读数，尚不是 HDD hull 的归一化 Haar/log-det 读数识别。Ind3 的上界在这里由相等推出。 |
| possibleImage：actual | [S1233.thetaPossibleImage](D:/lean/tmp/sheaf/xif/paper/S1233ThetaPossibleImageActual.lean:50) 是 `range (j ↦ log (thetaPacket.scale j))`；非空、索引不变和相应像规律已有证明。 | 真实存在的是有限 theta scale 的标量像。尚不能把它认作全部联合允许 Ind 选择经源算法得到的区域/读数像族；二者甚至未先证明是同一层次的对象。 |
| level / Core：exact | S1231 的弱 Core 已构造，level 恒为 0；本包 `thetaScalarProfile` 可消费它。 | [Carrier](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/ParametricCarrier.lean:25) 要求严格 `+n`。固定当前操作时不存在这样的 Carrier，详见下文的已核验证明。 |
| Adjacent square：exact | [S1212AdjacentKummerSquareData](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/Output/SourceOutputPrimeStripInterpretation.lean:130) 提供待构造 square 的类型。 | 没有构造其 inhabitant；类型也未规定其中某一条边等于 actualUpperEnv。按当前参数顺序，要绑定 `square.lowerHorizontal`。 |
| Nontriviality：exact | [S1212UpperEnvNontrivial](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/Output/SourceOutputPrimeStripInterpretation.lean:136) 是具体商群上的存在命题。 | 命题要求源作用移动一个商类。它不是 evaluation 单位映射非恒等的断言，也不能代替原文评价算法来源证明。 |

“actual”在上表表示当前定义或构造确实给出了所写对象；原文语义、下游目标身份和编译状态分别核对。本包没有把源码名称当作论文忠实性证书。

**二、已经实际核验的组合与冲突**

隔离文件：[SourceIndexBoundary.lean](D:/lean/tmp/sheaf/source-seven-interface-audit-20261030/SourceIndexBoundary.lean)。只添加本包文件，没有修改共享 Lean 源码。

1. [thetaScalarProfile](D:/lean/tmp/sheaf/source-seven-interface-audit-20261030/SourceIndexBoundary.lean:32) 使用 S1231.sourceCore、S1225.sourceLogVolume、S1232 的相等定理和 S1233.thetaPossibleImage，填满现有 `MultiradialKernel.Profile`。没有添加新假设，没有新增 sorry/axiom，没有使用 singleton 或 Set.univ 替代像集。
2. [sourceInd3_one_eq_sourceInd1_neg_one](D:/lean/tmp/sheaf/source-seven-interface-audit-20261030/SourceIndexBoundary.lean:49) 直接展开当前操作，得到：

   ```text
   sourceInd3 I 1 c = sourceInd1 I (-1) c
   ```

3. [noExactGradingWithSourceOperations](D:/lean/tmp/sheaf/source-seven-interface-audit-20261030/SourceIndexBoundary.lean:57) 对任意 `Core ℤ I.family.index` 证明：只要其 Ind1、Ind3 等于当前操作，就不能满足 Carrier 的严格增层律。证明取 `c = core.base`：

   ```text
   level (ind3 1 c) = level (ind1 (-1) c) = level c
   level (ind3 1 c) = level c + 1
   ```

   两式矛盾。因此只修改 level、profile 或 connector 都不能修复这一组合。
4. [noCarrierWithSourceOperations](D:/lean/tmp/sheaf/source-seven-interface-audit-20261030/SourceIndexBoundary.lean:71) 把此结论应用到当前 Carrier 类型。这个定理不要求新建具体 OriginalInput；它在原有合格 I 的参数下成立。

这是一条实现路径的精确排除证据。它没有证明“原文必须使用此 Carrier”，没有排除更丰富的真实算法状态，也没有排除直接使用已有较弱 route 接口。

**三、相邻方形应怎样写，才能真的接上**

当前 [actualUpperEnv](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/Output/SourceOutputPrimeStripInterpretation.lean:118) 来自 [S1195](D:/lean/tmp/sheaf/xif/paper/S1195ActualUpperEnv.lean:51)：底层 stripIso 是 `I.fLinkAt 1 0 1 1`；单位层是沿该 strip equivalence 构造的 graph-group Kummer 层。这是实际的 reduced arrow 构造。尚须证明它与原文源评价操作相符，不能仅靠 `SourceEvaluationArrow` 类型名完成该识别。

[SourceKummerEvaluationSquare](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean:347) 的参数顺序为 upperLeft、upperRight、lowerLeft、lowerRight。目前 wrapper 代入 S00、S01、S10、S11，所以 S10→S11 的 actualUpperEnv 实际占据 lowerHorizontal 槽位。

下一条准确的交换目标应先固定另三条**已有源来源的箭头** E00、Kleft、Kright，然后证明下式；这是建议目标，不是新增已证定理：

```text
Kleft.stripIso.symm.trans actualUpperEnv.stripIso
  = E00.stripIso.trans Kright.stripIso.symm
```

其中 E00 : S00→S01，Kleft : S10→S00，Kright : S11→S01。证明后再组装 square，并使 `lowerHorizontal := actualUpperEnv`。如果继续用已构造的 D，则至少要已有 `D.lowerHorizontal = actualUpperEnv` 的证明；将这条等式再放入未供应的 record 字段不算完成。

上式在 reduced strip 层成立也只是一个接口阶段。完整目标仍要关联原文 full-poly ×μ 箭头、相应单位层以及算法操作的来源。不得把另三条边任意指定为 family links，利用传递律完成一个图，就宣称原文评价/Kummer 相容已经完成。

**四、Nontriviality 的具体消费者与见证**

当前命题写的是

```text
∃ v g x, action (actualUpperEnv.unitPortion.sourceAction v) g x ≠ x
```

根据 [S1187](D:/lean/tmp/sheaf/xif/paper/S1187NonReflKummerCommonGroupActual.lean:28) 和 [S1188](D:/lean/tmp/sheaf/xif/paper/S1188NonReflKummerLayerActual.lean:27)，源作用来自 `S10.unitsAction v` 与 product group 的评价映射。因而此处合适的局部见证是：一个源地方 v、一个 `γ : S10.Pi v`，以及 `x : TimesMuQuotient ((S10.Mon v)ˣ)`，使该作用移动 x。随后可用在 v 处取 γ、其他分量取 1 的 product-group 元素得到现有命题的 g。这是明确的见证路线，当前没有供应这样的源见证。

这个条件检验的是作用。即使某个评价箭头是恒等箭头，其源作用也可能非平凡。若真正需要评价同构的非恒等性，必须先明确同域同陪域的比较映射/运输以及在哪个商层检测；不同 strip 上的元素不能未经识别就直接写成不相等。也不能把“非平凡”额外加到任意 OriginalInput 上来伪装原定理已完成。

优先核对下游到底消费哪种非平凡性。实际构造及来源验证不自动要求每一支箭头都非恒等；仅为排除空壳而添加的条件，不应转变成原目标没有要求的新全局难题。

**五、下一包的明确路线与分岔条件**

建议先复用现成的 [MultiradialKernel.Output](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/MultiradialProfileKernel.lean:326)。它只需要 Core、Profile、source、route 和源像非空。其 target 是 `applyRoute`，并已有 level 弱单调、logVolume 弱单调、possibleImage 上界定理。无需新造一种弱 wrapper，也无需强行构造不可能的 Carrier。

具体顺序如下：

1. 使用本包已核验的 `thetaScalarProfile` 做对象连接试验。对任意明确 route 和起点 i，以已有 Output 计算 target；用已有 stripOfChoice 读取起终点 strip。这部分仅整理已实现的索引/标量数据，不计为源 evaluation 或 HDD 缺口闭合。
2. 为一个真实源评价步骤固定算法输入、输出及其到上述索引的投影。证明该步骤导出的 strip 箭头与 actualUpperEnv 相符，再证明第三节绑定了同一箭头的相邻方形。`linkOfChoice` 只可作为已有 family-link 供体；“这就是该评价步骤”的等式必须有源证明。
3. 优先消费已有 `applyRoute_append` 和 Output 的三条弱规律，核实实际 provenance 消费者哪些结论真的用到严格 level。现有 [output_level](D:/lean/LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialPresentationWiring.lean:228) 明确需要严格 `+verticalBudget`，这条结论不能沿用到当前索引 Core。也不能把较弱 Output 谎称为原 Carrier/SourceRun 类型的 inhabitant。
4. 如果目标消费者确实必须用强 grading，则改从**实际源算法状态**提取 Choice 和 level。真实状态可有到 family.index 的投影，strip 沿投影读取；但额外状态必须来自源算法，且必须证明忘却关系和消费者结论。不得凭空加 `× Nat`，再以第二坐标递增冒充原文 Ind3。
5. 在原文允许的联合选择、像区域和 readout 识别证明后，再导出给消元/相消工具的标量关系。当前有限 theta scale range 不足以替代这一证明。计算可立即用于精确方形、运输和自然性引理；大规模搜索不应花在已经排除的 Carrier 组合上。

第 2 项是下一份源证明包的实际目标；第 1 项已有的 profile 组合在本包完成，其他装配只按下游需求使用。若第 2 项缺少实际评价步骤输入，就明确停在这个源定义/识别，而不是反复提交“存在一张图”的包装。

**六、新增代码与旧报告的纠正范围**

旧 source-compute-integration 报告把 SourceOutputPrimeStripInterpretation 列为拟建文件；当前已存在，不应继续这样描述。S1232 也消除了旧 S1225/S1229 报告所列的 theta 标量 logVolume shift laws 欠缺。本包没有重做这些证明。

核对过程中该正式 Output 文件又加入了 S1234 finiteKernelRun，已重读新增部分。它使用 `SourceFiniteParameterized.carrier l` 和 `AlgorithmInput.empty`，Choice 仍是有限模型的 ProcessionChoice；`I` 参数出现在 SourceRun 的 presentation 类型中。它不是已经构造了 `Carrier ℤ I.family.index`，也不与本包的不可能性定理冲突。

原文范围继续采用用户确认的 [Formalization 2026 §4](https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf) 与 [Essential Logical Structure §3.10 Stp1–8](https://www.kurims.kyoto-u.ac.jp/~motizuki/Essential%20Logical%20Structure%20of%20Inter-universal%20Teichmuller%20Theory.pdf)。后者 Stp1–3 明确讨论 anabelian 算法的候选像、Ind3 及随后 Ind1/2 的下降；仅有索引平移群律和一个有限标量 range，尚不能建立这些语义识别。对应本地文本与已读旧报告均纳入本包版本证据。本轮没有进行新的网上广搜，复用前两轮已调研的一手材料。

**七、验收与证据**

本包单次零模型自动化 `audit` 返回 green、exit=0、cached=false、stale_modules=[]。四个本包声明均经 `#print axioms` 检查，仅依赖 `propext`、`Classical.choice`、`Quot.sound`。证据见 [本次编译日志](D:/lean/tmp/sheaf/source-seven-interface-audit-20261030/automation/build-4443ea39472e48d3a5c29ccf326e7eaf.log)、[版本清单](D:/lean/tmp/sheaf/source-seven-interface-audit-20261030/evidence.json) 和 [核对结果](D:/lean/tmp/sheaf/source-seven-interface-audit-20261030/verification.json)。

| 验收项 | 本包局部 Profile/冲突引理 | 原文 IPL/HDD/SHE/xi-f |
|---|---|---|
| statement_compiles | pass，见本次精确文件和依赖指纹 | 本包未运行 |
| proof_body_checked | pass，无新增 sorry/axiom | open |
| kernel_closed | 四个本包声明通过，传递公理仅允许三项 | open |
| target_accepted | false，局部试验不是最终目标 | false |

没有全 Project 构建、目标 comparator、独立 reviewer 或大规模 solver 运行。共享源码未修改；历史报告不覆盖。后续接受源目标仍需对应版本的构建、目标比较、公理与原文语义审查。
