# C9：固定 q 的坏容器反证，实际源闭环攻击

任务：C9-CONTRADICTION-ATTACK-20261024；owner：本 chat root；2026-10-24。用户指令：开始攻击；只做自然语言研究，不写 Lean，不使用 subagent。

节点/阶段：n8-c9-output-region-source-route，SHEAF 阶段 1。实际消费者：P6 固定 native q 的输出体积类覆盖；前包最大坏容器反证的 escape 责任。

目标量词：任取原文合格完整配置 C，固定 native q-pilot、Θ-gluing 和原 normalization；令 H_C 为完整源输出区域并集的 holomorphic hull，Q_C 为 native q 读出。在 ν(H_C)<Q_C 的假设下，针对含 H_C 的坏容器 B 尝试构造真实源越界输出，或在取粗体积之前的源闭环中导出矛盾。不缩小输入范围；不把待证覆盖当新假设。

精确写文件：本记录、同目录 C9-CONTRADICTION-ATTACK-EVIDENCE-20261024.json，以及 root-owned dag/nodes/n8-c9-output-region-source-route.json 的新研究字段；只追加 AUDIT_LEDGER.md、coord/STATE.md、coord/queue.md。不覆盖其他 chat 的 Lean 文件。集成：root；Lean 构建：不适用。

冻结复用：C9-CONTRADICTION-CONTAINERS-20261024.md，SHA256 6a0f21aa14f7044150edcab9bd753716b1e4858bcfec8a92cb9c262fbf701e9d。该包仅证明有限坏容器/网格约化，未证明源 escape。

源：IUT III May2020 Remark3.9.5(v)–(ix)、Cor3.12 proof(xi)；Essential Logical Structure March2024 §3.10 Stp7–8；Formalization of IUT April2026 §4。版本哈希在证据文件记录。

statement_dependencies：源输出族与 native q 的原语义、有限读出情形；完整源配置尚未形式化。
proof_dependencies：前包坏容器准则（自然语言已证）；实际 closed-loop 对指定 pilot 的作用（本包攻击对象，未证）；Ind2 最终线性块标量化（此前自然语言已证，可剪枝）。

方法：追踪 closed loop 经过的对象、标记、有效包含和 quotient；先找导致 ν(H_C)≥Q_C 的第一条源约束，再考虑展开深度。绝不把形式商中的相等直接当作原对象相等。

验收：实际源推导及可核验的成功/失败条件；区分条件引理、源构造和完整结论。statement_compiles/proof_body_checked/kernel_closed/comparator/Project build/independent_review 均未运行；target_accepted=false。停止边界：得到新的实质源约束或定位确切未构造箭头；不以复制层数代替数学。

状态：首轮实际源攻击完成；得到下列源内标记保持、校准障碍及局部反例。没有构造原 IUT 坏容器的 escape；P6 未闭合。

## 1. 第一个可证明的源结论：抽象 pilot 标记确实随 BPS 同构保留

原文 II Definition4.9(viii)，p158，不是仅定义一套无标记的容器：在每个 bad place，分裂单子 O▶ 抽象同构于 N；其生成元连同 localization 数据 ρ_v 决定全局实化 Frobenioid 中的 pilot 对象，精确到同构。BPS 态射是这整个 collection of data 的同构。

因此，若 f:B→B′ 是这种 BPS 同构，则

    Pic(f)([pilot(B)]) = [pilot(B′)].

证明：N 的单子同构必须把唯一非零不可分解生成元送到生成元；BPS 同构又与各 ρ_v 相容，所以把这些生成元确定的全局对象送到目标侧相同构造所得的全局对象。此构造不需要另添一个自由的 pointed-compatibility 假设。

这是本轮对既有缺口描述的修正：不能再笼统地说“IPL 没有携带指定 pilot”。它携带了抽象 pilot 的同构类。需要展开的是这个同构类在实际输出区域、hull/determinant 和目标原生度量中的实现。

这条结论没有证明数值读出相等。两个带标记的有序 Picard 群可以由一个带正比例因子的同构关联，尽管该同构保持各自的抽象标记。

## 2. 把反面假设变成明确的校准障碍

任取原源配置 C。假定 H_C⊂B 且

    b := ν(B) < Q := Q_C < 0.

此处 Q<0 是原 q-pilot 的情形。若 H_C=+∞ 则不可能有这个坏容器；本攻击只处理严格偏小的有限情形。

在取 ⊼ 商之前，III Remark2.4.2(v) 将相关 Picard 群描述为抽象有序加法群 M≅R。固定各自原生 normalization 后，一个有序加法群同构 F:R→R 必有

    F(t)=a t，a>0。

证明：令 a=F(1)。加法性先给整数、再给有理数上的等式；对任意实数以有理数上下夹逼，保序性给出 F(t)=at。不需要另外假定连续性。

若一项实际输出给出的负 pilot 读出是 v≤b，且其 IPL 同构在这些尚未取商的 Picard 群上把输入 pilot 送到输出 pilot，则第1节给出

    a Q=v，故 a=v/Q ≥ b/Q = 1+(Q-b)/|Q| > 1。

因此，只要在对应的实际比较上独立证明 a≤1，就能反证该坏容器。若证明 a=1，则更强。这是对一项真正源比较的诊断，不是把整个区域构造声称降成一个实变量，也不是假设完整输出族都是 BPS 同构的数值像。

## 3. 原文自身允许的重建说明：抽象同构、符号和比例不能独自消掉 a

III Remark2.4.2(iii)–(vi)，pp89–91，给出从有序群 M 以及负 pilot 元素 η 重建 prime-strip 数值部分的构造。用其记号固定 r▶_v，局部生成元的 localization 为

    ρ_η,v(nη)=r▶_v nη。

对任何 c>0，取 η′=cη，整体映射 x↦cx，局部映射 nη↦nη′。则

    c·ρ_η,v(nη)=c r▶_v nη=r▶_v nη′=ρ_η′,v(nη′)。

它保持加法、顺序、各局部抽象 N 生成元、localization 的交换关系、以及全部 r▶_v 比例。因而符号检查与 product-formula 转换比例都不能单独排除 c>1。原文在2.4.2(vi)也明确将不同负 η 视为同一全局容器上的不同进一步刚化。

精确范围：这里确实使用了原文的 Picard/局部 divisor/localization 重建，不只是任意给几行数字。没有由此声称任意 c 都能实现为同一固定 C 的完整 Kummer/evaluation/积分区域输出；也没有证明这些缩放可与全部 Galois、log、holomorphic 数据同时实现。它排除的是仅靠这些已展开的数值部分即可完成反证的推理。

已核对的其他操作也不自动消掉 c：

- 正整数 tensor power 把 η 和 η′ 同乘 M；按原 M 除回后比例仍 c。
- inverse-reference determinant 必须保留；相对 determinant 与同一原 reference 的正确正规化不能被任意平移替换。它校准读出，但不是一条未证明的跨 Θ 等式。
- product formula 的零关系在整体正比例缩放下仍成立。单用全局主除子作为“非零校准探针”无效，因为其全局 degree 正好为零。
- Ob9/Rss 的 log-link 保体积证明校准了相邻纵向箭头；把它拼在未知横向比较两边，不会仅凭纵向校准便证明横向比例为1。

## 4. 一条能导致矛盾的校准判据，以及实际攻击它的结果

条件引理：若第2节的 F 还保持某个已知非零的度量类 d，即 F(d)=d，则 a=1。

证明：ad=d 且 d≠0，故 a=1；于是 v=Q，与 v≤b<Q 矛盾。它只要求一个独立于 q 数值的非零校准类，不需要逐个比较所有 pilot 值。

本轮尝试的具体校准类来自深单位邻域。一般地，对任意实际有限扩张 K/Q_p（p 为奇素数），令 d=[K:Q_p]，取 k≥1，则 log/exp 给出 1+p^k O_K 与 p^k O_K 的双射。理由是 log 级数首项以后的各项赋值严格更高，exp 在这个范围内收敛并互逆。以 μ(O_K)=1 并令 ν=d^(−1)log μ，则二者读出都是 −k log p；源额外正权重只会把这个等式同乘固定正数。因此下面的障碍适用于任意这样的真实局部块，不依赖 Q_3 能否单独扩展成一份完整 Θ-data。

将实际有限计算取在 Q_3 中，令

    U_k=1+3^k Z_3，L_k=3^k Z_3，k≥1。

p-adic log/exp 互逆给出 log(U_k)=L_k，且局部导数 1/u 的绝对值为1。故在 μ(Z_3)=1 的原加法 Haar measure 下

    ν(U_k)=ν(L_k)=−k log3。

相邻 k 的差是非零的 −log3，亦可用有限指数 [3^k Z_3:3^(k+1)Z_3]=3 表达。这与 III Remark3.9.4(iii) 及3.9.6 的 sufficiently-small-region 校准一致。

但是这条探针不能被无证明地穿过实际 hull 步骤：

    Hull(U_k)=Z_3，   Hull(log U_k)=3^k Z_3。

证明：U_k 全在 Z_3 中且含单位1，因此其最小 fractional ideal 是 Z_3；log U_k 本身就是 fractional ideal。因此 U_k 与 U_(k+1) 的体积差非零，而其 hull 的体积差为0；先 log 再 hull 则体积差仍非零。

这不仅是“不确定是否可交换”，而是一个确切反例。取 U_k 和 L_k，还说明两个等体积区域可以有不同体积的 hull，因此 hull 不能仅由区域的 Rss/体积类决定。先把区域压成体积类，再通过某个未定义的“hull on volume classes”运输探针，是错误步骤。

另一个确切限制：log(U_k)=3^k Z_3 与下一次普通 log-link 的单位定义域 Z_3^× 不相交。III Remark1.1.1(i)，p28，明确要求迭代 log-link 只在局部单位上定义。因此不能将这一对具体区域沿任意多次 pointwise log 迭代，宣称获得任意深度的同一探针。原文的 Rss 比较与形式空交处理是另一种构造；它不声称这条点集路径存在。

机器核验：c9_log_hull_probe_20261024.py 在模3^6=729上，用有尾项赋值界的精确对数级数，分别遍历 U_2 的81个剩余类和 U_3 的27个剩余类；log像分别恰为9Z/729与27Z/729，且与下一单位域的交为空。所有断言通过。无限层结论由上述 log/exp 和 fractional-ideal 证明给出，不由有限枚举外推。

结论：这个非零校准策略有明确的成功条件，但本轮选取的实际小单位探针不能自动通过 hull/任意 log 迭代。不能据此填写 a=1。

## 5. 反查“逆向几十层逼出矛盾”：⊼ 商的精确障碍

设 b<0，把 S_b=R_{≤b} 压成一个点 ★，其余实数保持各自不同，得到 III Remark3.9.5(v) 类型的集合商 E_b。

首先，Q>b 时 [Q]≠★。因此，如果真实源构造给出固定 q 类在这个同一校准商中等于 ★，坏容器立即被排除。这个出口不要求恢复所有点集，也不把单点的 Haar measure 当 pilot 体积。

但该集合商不是加法群商。例如 b=−2，−3与−2已被识别；同时加2以后得到−1与0，未被识别。所以不得把第2节的有序群同构分类直接应用到 E_b 上。

更精确地，正比例映射 f_a(t)=at 能在 E_b 上诱导自映射，当且仅当 a≥1：

- a≥1 时，aS_b=S_(ab)⊂S_b，故被压成一点的整块仍映入同一点。
- 0<a<1 时，S_b 中有些点映到 b 之上，有些仍在 b 以下，不能给 ★ 赋予单一像。

当 a>1 时，所诱导自映射不是单射：任何 t∈(b,b/a] 原先在压缩块之外，但 at≤b，因此它的像落到 ★。相应的逆比例 a^(−1) 不能作为同一个 E_b 的自映射。

所以一种貌似有力的反证——反复取正比例环路的逆，把负体积向0推，从而越过固定坏上界——在这里有一个确定的非法步骤：逆映射不下降到同一 ⊼ 商。不能仅从上游 full poly-isomorphisms 可逆就推出下游扩大/取商后的区域关系也可逆。

若确实证明某个源比较给出保持同一个负 cut 的双向有序群同构，则 ab=b，故 a=1；这可作为可核验的充分条件。但 III 的 upper semi-compatibility、包含/满射及 formal quotient 不是默认的双向 cut 同构。本包不把后者加成新假设，再声称原命题已证。

## 6. 实际闭环核查到哪里，尚未通过哪条箭头

逐项读取后的链条是：

1. II Def4.9(viii) / III Def3.8(i)：指定 abstract pilot 从局部分裂单子生成元产生，BPS 同构保持它。第1节已展开。
2. III Remark3.11.1(iii)，pp160–161：IPL linking maps 是 Remark3.10.2 图中两个下方箭头的逆、首个 Kummer 竖箭头、再三个上方 evaluation 箭头的复合。其末端把 evaluation 产生的可能区域解释为全局实化 Frobenioid 的可能进一步刚化；明确引用2.4.2(iv)–(vi)、3.9.6、3.9.7。
3. III Remark3.9.5(Ob3)：weighted determinant 要连同 inverse-reference determinant，按 M 处理；这确实能将最终 hull 变成原目标局部/全局 Frobenioid 中可比较的对象。
4. 同 Remark(ix)(cQ3)：local-global ⊼-collections 保留 Galois、单位作用、局部化，以及映向 det^M(H) 的 structure poly-morphism。这比裸实数模型强，不能略去。
5. (cQ4)/Ob9/3.9.4：纵向 log-Kummer 和 Rss 校准；不会把点集上的任意 log 变成全定义、保体积映射。
6. Essential Logical Structure Stp7–8，pp151–155：对角复合标签/同步使最后比较发生在同一容器；同文随后解释 closed loop 在数学对象层不是两条独立映射，固定的是 q 与原 gluing。不能把本包的 scalar 诊断误当作要求额外一对独立 Θ/q 映射交换。

仍未展开成功的精确责任是第2→4→5的接合：同一固定 q 所携带的 pilot 类，在由实际 evaluation 区域构造的 local-global ⊼-collection 中，经过原 normalization 后，必须被送入输出 cut，而非仅被某个改变数值刻度的抽象 BPS 同构送到一个负 pilot 类。

可用更几何的方式检验这一责任：对于同一个固定目标 holomorphic frame，要从源复合构造将 q 的 M 次方对象放进 (cQ3) 的相关 slice/structure-poly-morphism 数据，连同实际 degree 比较。若得到的是规范化的有效包含 q^M→det^M(H)，其 degree 差为 M(ν(H)−Q)，在反面假设下为负，便与有效性矛盾。这里的 degree 符号按区域包含使 ν 增大的约定取；不能把 Frobenioid 类别之间的等价函子直接当成两个对象之间的内部有效态射。

这项内部态射/商中 membership 尚未由本轮读到的具体步骤构造出来。原文 Remark3.9.5(ix) 和 Cor3.12 proof(xi-e)–(xi-f) 宣称整套构造完成了它；本记录没有将该宣称重复登记为新的独立证明，也没有据未完成的重建断言原文不存在证明。

2026年4月 Formalization 报告§4，pp10–11，将 hull+det 移入“3.11.5”，并把3.11→3.11.5中的 APT 与最后比较区分开。这个分解与本轮定位一致；该报告不替代上述具体对象/态射的源实现。

## 7. 明确判断与下一项

已证明/核实：抽象指定 pilot 对 BPS 同构的自然性；未取商 Picard 比较的正比例形式；坏容器下的明确下界 a≥1+(Q−b)/|Q|；原文负 η 重建保留缩放的计算；非零 anchor 判据；实际 Q_3 hull/log 校准探针失效；负 cut 商只允许单向比例自映射的分类。

没有证明：任意合格 C 的 native q 体积类属于完整源输出；任意坏容器都有真实 escape；源 IPL 的完整输出关系具有 a≤1 或保持同一 cut 的双向性质。没有原 IUT 反例。Q_3 局部证书也不构成完整 Θ-data。

对路线的判断：继续反证有明确对象；目前不能靠增加纵向层数推进。下一项应只攻击 Remark3.11.1(iii)所指定的 evaluation→进一步刚化→(cQ3) structure-poly-morphism：保留固定 BPS/pilot、实际区域及原 reference，检查所得对象和态射是否在同一 holomorphic realization 中给出 q 的 cut membership。输出应是这个态射/相容性等式的实际构造，或一个源允许配置下其无法成立的具体证据。不得以 free `calibration_preserved`、裸 positive scalar、默认逆映射或新 source 输入代替它。

本轮不启动大规模多层搜索：已确切证明仅沿数值重建/纵向校准复制多层不能排除比例，且 pointwise log 探针会遇到空定义域。只有新的源约束实质限制该比较或给出真实 escape 后，才值得扩展计算。

statement_compiles：未运行；proof_body_checked：未运行；kernel_closed：未运行；comparator/Project build：未运行；独立审查：未运行；root 自然语言自审；target_accepted=false。

原文链接：

- [IUT II](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf)，December2020，Def4.9(viii)。
- [IUT III](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf)，May2020，Rmk1.1.1、2.4.2、3.9.4–7、3.11.1；Rmk3.9.5(ix)及Cor3.12 proof(xi)。
- [Essential Logical Structure](https://www.kurims.kyoto-u.ac.jp/~motizuki/Essential%20Logical%20Structure%20of%20Inter-universal%20Teichmuller%20Theory.pdf)，March2024，§3.10。
- [Formalization of IUT April2026](https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf)，§4。
