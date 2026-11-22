# ValuesPaper 定向语义复核（2026-10-23）

## 任务与证据版本

- 任务：回答用户关于 C4 witness / x / T11 / singleton / Q-Theta / +inf 的八项问题。
- owner：当前 chat root；用户纠正要求后已停止初次开启的 subagent，以下源码与原文核查由 root 完成，不称独立审查。
- 节点/阶段：n8-s3-c9，阶段 1 定义语义审查；消费者为 C9Paper.ValuesBounded、QPaperApproximated 与最终 Q <= Theta。
- 范围：只审查这些定义及直接接口，不修改 Lean 定义/定理，不启动证明或全 Project 构建。
- 量词：区分任意 D/T/B 接口实例与实际源构造；不把某个候选实例的性质用于任意接口参数。
- Git HEAD：9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee；工作区非干净，tmp 文件不能仅凭 HEAD 定版。
- C9ValuesPaper.lean SHA256：A61D7B53338E4913F67197AC1E68AB586A7896B28A8341F02743BB36FCFC9977。
- C9Paper.lean SHA256：67313E8E55831D05A792F817EC76853FFB4C24A5FF00BB69ABBCCA20F3D2DDCB。
- SourceWitnessedOutput.lean SHA256：97311E15C7B38FE539135C24FBF791C1D8731CF0483F661CBAA19CCF64EF786A。
- C6ActualIQData.lean SHA256：8F76571F273C0AB49BE4B462EB9CFA3927EE09E2050836585F93BC2CAFDB0C45。

原文为 `papers/motizuki_corpus/raw/Inter-universal Teichmuller Theory III.pdf`，May 2020，199 页，SHA256 `9A7EE3C77B1C7717210C0613EB39B6844649D0040DC3D9E1BE7D544F8F91A0B9`。直接渲染并逐页读取 pp.173–175、182–184；同时核对配套 txt 10323–10415、10809–10898。官网原始 PDF：https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf 。仓库旧 audit/plan 仅用于定位；网页博客搜索结果未采用。

## 原文核对

- pp.173–174 Corollary 3.12：Theta 起初在 R union {+inf}，是可能 Theta 图像之并的 holomorphic hull 的 procession-normalized mono-analytic log-volume，涉及 Kummer 和 Ind1/2/3；Q 在 R，是 q-pilot 图像的相应 log-volume，不受这三类 Ind 处理。
- p.174 的结论还要求 Theta 属于 R，不仅要求 Q <= Theta。p.175 由 compactness 等给出有限性。
- p.175 明确输出数据可解释为 regions 的集合及 F-prime-strip。
- pp.182–183 (xi-c)/(xi-d)：形成 hull 后解释为局部化算术向量丛；取 determinant 的适当正 tensor power，并按标签归一化 log-volume，方能比较。
- pp.183–184 (xi-d)–(xi-f)：数值范围写作 {lambda in R | lambda <= Theta}；Q 的构造/近似关系不是只由任何一组数的非空性推出。

## 八项结论

1. `w.2.1` 是 C4 输出；SourceWitnessedOutput:129–132 已给出 `witnessOutput = eval n x w.1`，因此只用 label 并非语法上必错。但 C9ValuesPaper:50–53 用的是另一个接口 T 的 thetaImage，缺少与 eval 输出及实际 output region 的对应定理。改成对 w.2.1 的点度数读出也不自动得到原文的区域体积。
2. SourceWitnessedOutput:102–110 的 Choice 与 eval 本身都不依赖 x；故当前 U、Witness 的实际评估也抹掉 x。原文没有与这个自定义 x 已确认相同的变量，不能声称论文一定非平凡依赖它；正确义务是证明忠实的输出数据建模或状态不变性，目前未见。C4-STAGE1 的 G4 也明确完整输出载体尚未识别。
3. SourceThetaToIQ:64–78 只约束 thetaScale 与 source 实数一致，以及 thetaImage 为 thetaCompletion 的 landing；没有连接 thetaCompletion 与该 thetaScale。qUnit 候选实例及 interface 非空证明存在，但不能填补这一语义缺口。T11Native:126–136 的 packet identification / ValueMonoid-to-IQ 仍是 sorry。
4. C9ValuesPaper 的 singleton 不符合已核对的 region/hull/determinant 路线。更强地，当 B=actual 时，Haar 平移不变性使所有 singleton 测度相同，归一化值也相同，完全丢失输出变化。复用依据是 Mathlib/MeasureTheory/Group/Measure.lean:781–784 的 haar_singleton 及其 to_additive 版本；本次未提交 Lean 证明。通常非离散场景 singleton 质量为 0；Real.log 0=0 的全函数约定会产生有限伪读数，不能作为真实 log-volume 解释。生产 normalization 的单调定理明确要求小集合质量正、大集合质量有限（FinitePlaceNormalizedUnitScalingLogVolume:107 起）。
5. 当前有两个不同 ValuesPaper：C9ValuesPaper 的 witness/label singleton 定义；C9Paper:106–117 的任意 provenance 子集体积定义。后者不导入前者，没有接线。ValuesBounded、QPaperApproximated 分别在 C9Paper:176–182、196–203 仍为任意弱接口对象上的 sorry。需要实际区域构造、有效 normalization 比较、q 输入输出兼容/近似证明；当前定义不足。
6. 当前 C9Paper 已不同于用户引用的早期纯自由字段版本，但约束仍不足：qPilotRegion 只要求包含于 C6.hull；thetaHull 虽绑定旧 sourceHull，thetaToC6 完全自由；provenance 完全自由，且 values 遍历所有子集（包括空集）。`kummer := C2`、`ind := D.ind` 只是默认值。structure 可以保留，但须以实际构造或识别等式约束数据。对任意弱对象宣称源定理的 sorry 不是正确的源构造义务。
7. 更正旧 C9-COMPLEX-VALUES-PLAN 的 P7 泛化说法：Values 不因 Theta 允许 top 就必须改为 WithTop Real。原文 Values subset R，Q in R；可用 Values:Set Real、Q:Real、Theta:WithTop Real，并在比较时嵌入。Theta=top 时上界和 Q<=Theta 平凡，但 Cor.3.12 的有限性仍须证明；有限分支可由 forall eps>0, exists v in Values, Q-eps<=v 与 boundedness 推 Q<=Theta。这只是数值推理，不能替代源 approximation。当前 C9Paper:99–100 令 Theta 等于一个 Real 的嵌入，实际上已排除 top，并未处理它。
8. C4IQAlignment 的已见结果仅在 DegreeFaithful 条件下比较 log-degree 和 log thetaScale。C8 SourceDegreeComparisonIQ:71–82 只对 B=actual 给出 canonical hull 的定义恒等式，未消费某个 witness 的 output region。C7DonorProof:72–74 的 sourceUToIQDonor_weak 甚至用常函数 1 实现弱条件，不能作为 source map；不能将旧 plan 所称 P1 的该弱接口视为充分。

## 额外的接口漏洞

C6ActualIQData:32–43 全部是有默认值的字段，不是识别等式；任意 `B : C6ActualIQData ...` 不等于 `C6ActualIQData.actual`。因此 C9ValuesPaper 对任意 B 的 `normalizedLogVolume` 甚至可以是任意 Set→Real 函数。必须固定 actual 或证明识别后，才能调用上述 Haar 语义。即便固定 actual，singleton 退化仍存在。

当前 C9Paper 的自由子集语义在单位参考质量归一到 1 时总包含空集的伪值 0，而原文需要处理 Theta<0 的分支；所以不能把任意子集的全函数 log 读数当作所有允许输出区域的 log-volume。缺的是允许区域条件和实际 source construction。

## 验收与下一步

- statement_compiles：未运行（不沿用旧 hash 的编译结论）。
- proof_body_checked：未运行。
- kernel_closed：未运行，当前依赖仍含已知 sorry。
- target_accepted：否；当前 Values 语义未通过本次自审，comparator 未运行。
- 独立审查：未运行；这是 root 自审。未运行零模型编译、全 Project 构建或传递公理检查。
- 本次没有消掉数学证明前提，没有更改目标/Lean 源码/其他 owner 实现；所得为准确缺口和旧计划修正。
- 下一可执行项：先固定论文允许的完整 output-region 数据及其与当前 C4 候选载体的关系，再陈述 eval/witness 到该区域的兼容性和 valid-region 归一化读出；不能预设整个 value monoid 到 IQ 的单值映射必然是正确模型，也不能只把 w.1 换成 w.2.1。
