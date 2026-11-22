# C9：目标列回接中的 image/tag 区分与相容性检验

任务 ID：C9-MARKED-IMAGE-DESCENT-20261024。owner：当前 chat root；2026-10-24。用户目标：继续攻击关键部分；单线程自然语言研究，无 Lean、无 subagent。

节点/消费者：n8-c9-output-region-source-route，SHEAF stage1；原 P6 fixed-native-q 输出覆盖，以及最大坏容器的源 escape 责任。

目标量词：原文全部合格完整 initial Theta-data 和实际 log-theta-lattice；固定 native q、原 gluing、原 global normalization。不得把额外的 global descent、非单位 Kummer 相容或正补偿作为新输入。

本包目标：展开 III Remark3.10.2→Remark3.11.1(iii)→(sQ3)/(sQ4)。分别保留 local structure map 的实际 image 和由 IPL 携带的 global pilot tag，检验二者之间的实际下降；核查单位 Kummer 数据是否真能校准非单位 valuation。

冻结复用：C9-EVALUATION-DEFECT-ATTACK-20261024.md，SHA256 bfdad69825b86a4f1372f822117b03a0451a01af8bb404c0c4ee3f4657098912；C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024.md，SHA256 ec0bbb35abb1d28128a958ecbdaad27d600dfe81e1738af70ec28c0bb439e704。前轮为 progress：实际文件/哈希和队列已重新读取，有新证明、计算证据及改变后的下一动作；非等待/空转。

statement_dependencies：给定目标 frame 的局部/全局 Frobenioids、实际 region/hull、local-global ⊼-collections、原 q-pilot 标记；nonunit Kummer class 只用于诊断明确提出的加强路线。
proof_dependencies：前包实化下降判据；FrdI 模型与实化；III cQ3/cQ4、Prop3.9 与 Rss 校准；局部 Kummer/惯性赋值公式（本包展开）。

精确写文件：本记录、C9-MARKED-IMAGE-DESCENT-EVIDENCE-20261024.json、必要的同名前缀计算脚本/证书；root-owned DAG 节点追加研究字段；AUDIT_LEDGER、STATE、queue 仅追加。其他 owner 的源码及独立编译记录不改、不据此宣称本包被独立审查。

来源：IUT I May2020 Ex3.5、Def5.2；II December2020 Def4.9/Cor4.10；III May2020 Rmk2.4.2、3.9.5(ix)、3.11.1(iii)、Cor3.12(xi)；FrdI June2008 Prop5.5/Thm6.4，FrdII June2008 Ex5.6；外部 Kummer 供体限实际核对的原文。

验收：完整自然语言辅助证明、准确源适用性和失败/成功证据。statement_compiles/proof_body_checked/kernel_closed/comparator/Project/独立审查均未运行；target_accepted=false。主目标未闭合则保持 goal active，不以本包局部结论代替完整目标。

状态：研究中。

## 2026-10-24 用户纠偏：恢复反证的原对象

用户指出：“你看清楚我们是在反证法，你要搞清楚我们要证明的对象”。本节优先于上述研究中计划；保留已做计算，不将其记为原目标的关键进展。

### 1. 固定的对象和准确否定

任取原文允许的完整配置 C，固定其 native q-pilot、原 Θ-gluing、目标列和原 normalization。不能在推导中另换 C、q、gluing 或规范化。令 A_C 为这份 C 的完整源允许分支族，R_chi 为其实际原始输出区域，U_C 为这些区域的并，H_C 为其目标 holomorphic hull。Q_C 是独立从 native q 读出的原数值。

另记 E_C 为带源构造证据的最终允许输出：它包括原文允许的 hull 内扩大、同全局体积 hull-approximants、正确的 weighted determinant/reference 处理和目标列 log-shift。这里的 E_C 不是任意负实数的集合，也不由自由 BPS 字段定义。其读出集合记为 V_C。

P6 要求原指定 q 的体积类由这个最终过程覆盖；采用原文允许的近似版本时，数值责任是

    对每个 eps>0，存在 E∈E_C，使 ν(E)>Q_C−eps。

这个单侧逼近还须连同源关联交付；只有数值并不足以替代构造。若要由逼近转成恰好 Q_C 的一个输出，还须使用已核的源允许向下扩大/调节和闭性，不把一般集合的 sup 等于 Q 当成 Q 属于该集合。

其准确否定是：存在一份合格 C 和 eps0>0，使该 C 的每个最终源允许输出都满足 ν(E)≤Q_C−eps0。它不只是“某条路径的值小于 Q”，也不只是“恰好 Q 没有被取到”。

在已建立原文 Stp4–Stp6 的 hull 扩大和读出接口的情况下，数值核心可写成 Q_C≤ν(H_C)。对此反证固定同一 C，假设 h_C=ν(H_C)<Q_C，置 Delta=Q_C−h_C>0。对于源允许的同全局体积 approximants，使用的是数值上界 ν(E)≤h_C；不要误称每个 approximant 都逐点包含于 H_C。

### 2. 哪些证书真正击中反面假设

在 h_C<Q_C 下，以下任一项连同真实源构造即足够：

- 构造最终允许输出 E，证明 ν(E)>h_C。选择原目标逼近精度 eps<Delta 就能达到这一点，但不能把逼近本身作为输入假设。
- 构造有限个实际分支，其共同 hull 的体积大于 h_C。无需其中任何单条原始分支独自达到 Q_C。
- 对一个包含 H_C、仍有 ν(B)<Q_C 的坏容器 B，构造实际原始分支中的点 z∉B。该点必须来自 R_chi；仅有一个重新分配了各处体积的 hull-approximant 在 B 外，不构成这个矛盾。
- 从同一 C 的实际数据与反面假设推出其他矛盾；允许采用任何数学方法，但必须给出反面假设实际参与的推导。

有限模型中的不可能性、额外加强条件的失败、另一个 C 的坏例子，都不是上述证书。不能把任意有限多层的检查外推成完整输出族的全称结论。

### 3. 撤下不必要的强要求

前包的精确公式 h−Q=S−kappa（linear 比较，S≥0）继续有效。反面假设给出 kappa>S。因而充分的矛盾方向是：从实际源构造证明某个相关比较的 kappa≤S，或直接找到其他实际输出越界。没有理由预先要求所有比较的 kappa=0。

“给定局部比较下降为全局 linear 态射”所需的 kappa=0 是一条更强的充分路线，不是原目标的必要条件。一个简单标准算术例子说明区别：F=Q，L_3=3Z_3，H_3=Z_3，其余有限处取单位格，无穷处均取单位球。则 Q=−log3、h=0，目标不等式成立。局部比较在3处乘3、其余处恒等，具有 kappa=log3、S=2log3；给定局部比较并不全局下降，但 h−Q=S−kappa=log3>0。此例只反驳“零障碍是必要的”，不充当 IUT 例子。

本包已经执行的 marked-image/非单位 Kummer 阶计算没有用到 h_C<Q_C。它们检验了额外要求，未构造原源 escape，退出当前主攻链。尤其不能把“不能把所有非单位 Kummer 类以某种更强方式同一化”登记成原 P6 的反证或关键进展。

### 4. 重新核对的原文位置

III Cor3.12 proof(xi-c)–(xi-f)，pp182–184：先取完整可能输出，再取 hull、determinant 及目标列 log-Kummer 校准；最后宣称同一固定 q 值被输出可能性覆盖或逼近。它没有要求逐条原始路径等体积。

Essential Logical Structure §3.10，Stp4–Stp8，pp150–154：Stp4 明确增大可能性族；Stp5 保持全局 log-volume 而不承诺每处区域不变；Stp6 处理 determinant；Stp7 的对角复合标签和纵向校准必须在同一个目标列内执行。不能把上游 poly-isomorphisms 可逆直接当成下游输出关系可逆。

III Rmk3.11.1(iii)，pp160–161，给出实际 IPL 复合及最终由 evaluation 构造进一步刚化的位置。II Cor4.8(iii)/Rmk4.8.1，pp151–152，和 III Prop3.7(v)，pp111–112，确实给出 Gaussian/局部理想到全局 Frobenioid 的构造及其自身局部化相容。后者不能单独替代经过目标列回接后的原规范化比较。

III Rmk2.4.2(vi)，p91，明确允许在共同实化 Frobenioid 中比较不同负 pilot 所对应的进一步刚化。因此仅凭“对象落在同一个全局类别”不能抹掉反证中的严格数值差。反过来，这也没有证明原源输出不能补偿该差。

### 5. 当前结论、剪枝与下一步

本轮完成的是反证对象和量词的纠正，并核对了原文的具体出口；没有得到原反面假设下的新矛盾，也没有证明原 P6。不要将这种纠正记作关键数学突破。

继续工作的唯一主线：固定坏的 C、h_C<Q_C，沿 III Rmk3.11.1(iii) 指定的实际复合，追踪 ELS Stp7 的输入/输出复合标记 ↱(1,m)↱ 和 III Rmk3.9.5(Ob9)/(cQ4) 的实际读出；检验它在原规范化下是否强制一个源允许输出越过 h_C。精确接受项是实际输出/见证族及其严格数值界，或由同一源数据得到矛盾；不新增校准、下降、非单位 Kummer 同一化或补偿存在的假设。

已运行的辅助 Python 证书保留为离线诊断：380 对固定标记比较、19 条算术模型边、2176 组 Kummer 参数检查通过。它们都不是完整 initial Theta-data，也不是反证证书。无 Lean 修改；statement_compiles、proof_body_checked、kernel_closed、comparator、Project build、独立审查均未运行；target_accepted=false。

来源：[IUT III](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf)，[IUT II](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf)，[Essential Logical Structure](https://www.kurims.kyoto-u.ac.jp/~motizuki/Essential%20Logical%20Structure%20of%20Inter-universal%20Teichmuller%20Theory.pdf)。本文核对的是本地记录的 May2020 / December2020 / March2024 版本。

本包最新状态：纠偏记录完成；原目标 open；标记/非单位 Kummer 支线退出主攻，历史计算保留。
