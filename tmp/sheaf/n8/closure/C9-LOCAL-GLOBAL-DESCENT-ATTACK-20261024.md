# C9：evaluation 输出的局部结构态射与全局 degree 障碍

任务 ID：C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024。owner：当前 chat root，单线程，无 subagent。用户要求继续攻击直到有关键结果；自然语言研究，不写 Lean。

节点/消费者：n8-c9-output-region-source-route，SHEAF 阶段1，P6固定native-q输出覆盖，以及前包提出的(cQ3) structure poly-morphism反证出口。

目标量词：对原文任意合格完整C、固定native q和gluing，核查实际evaluation→pilot刚化→local-global upper-collection能否构造排除ν(H)<Q的全局比较。先严格区分局部结构箭头、localization同构和一条全局有效态射；不得把局部存在拼接为未证明的全局存在。

精确写文件：本记录、同目录C9-LOCAL-GLOBAL-DESCENT-EVIDENCE-20261024.json及必要的本包精确计算文件；root-owned节点的新研究字段；只追加AUDIT_LEDGER.md、coord/STATE.md、coord/queue.md。其他owner源码不改。集成root；Lean构建不适用。

冻结复用：C9-CONTRADICTION-ATTACK-20261024.md，SHA256 bf2f92bc3e99497c1291e608cb9f6f499c4f36314a9eefb470ece529d80714ad。已有BPS抽象pilot自然性、Picard缩放及cut商分析有效；本包重点检验它提出的结构态射出口。

来源：IUT III May2020 Remark3.9.5(ix)(cQ3)、3.10.2、3.11.1(iii)；The Geometry of Frobenioids I Example6.3/Theorem6.4及model Frobenioid；II Example1.1/5.6。精确版本记录于EVIDENCE。

statement_dependencies：原q算术线对象、最终weighted normalized determinant对象、(cQ3)局部/全局集合定义。
proof_dependencies：原源pilot自然性（前包已证）；从实际evaluation得到全局有效比较（未证，本包攻击）；局部线束/范数和product formula（须按对象展开）。

本包验收：得到源构造中的新有效约束，或对目前具体接合准则给出严格反例及修正。仅再写一个等价于目标的条件，不计关键结果。当前所有形式化检查未运行，target_accepted=false。

状态：本包自然语言证明完成。得到严格的局部—全局接合反例、给定局部比较的实化下降充要判据及有限构造；原 fixed-native-q 输出覆盖仍未证明。

## 1. 结果及其准确作用

上一包提出检查 (cQ3) structure poly-morphism 是合理的，但其中“将 q 放进相关 local-global collection 就足够”的候选接合必须修正：

> (cQ3) 的对象数据，包括每处的局部 linear structure poly-morphism、一个全局对象和 localization 同构，并不自动给出由同一条全局 linear 有效态射诱导的结构 poly-morphism。

下面在原文引用的标准算术 Frobenioid 模型中证明这一点，反例在任意有限数域扩张后仍成立，并且可以带上自然的局部单位/Galois 作用和各层局部 Kummer 自然性。它不是只给裸实数任意赋值。

进一步，固定同一全局算术 realization、原 reference 和一组给定的局部比较后，定义其有限支撑局部乘子除子 A 和有效零除子 Z。令 κ=deg(A)、S=deg(Z)。对 linear 比较，证明精确恒等式

    h − Q = S − κ,        S ≥ 0.

在标准全局实化 Frobenioid 中，这组局部 structure poly-morphism 在实化后下降到一条全局 linear 态射，当且仅当 κ=0。证明还给出由有限多个理想主化数据及单位群线性方程构造该态射的方法。

这是一个接合定理和对错误充分条件的反例，不是原 P6 的证明。没有从实际 IUT evaluation 证明 κ=0 或 S≥κ；更不能把“κ=0”加成输入假设，冒充完成。全局 linear 态射是当前一条充分路线，不是原 P6 唯一可能的证明方式。

## 2. 原文实际上定义了什么

IUT III Remark3.9.5(ix)(cQ3)，pp141–142，先在每个局部 Frobenioid 中固定由 hull 的加权 determinant 得到的对象 H_v。局部对象带有到 H_v 的 **linear** 态射的 Aut(H_v)-轨道。随后定义 local-global ⊼-collection 的对象：

1. 每处一个上述局部对象；
2. 一个全局实化 Frobenioid 对象 L；
3. 各局部对象实化后与 L 的 localization 之间的同构。

这张对象清单没有再附加“一条全局 L→H 的 linear 态射，其 localization 正好是全部局部结构态射”。后者是另一个条件。原文称这里的构造为 formal/stack-theoretic quotient，保留范畴和态射信息；本包不把它擅自解释为对象集上的 membership 商，也不据此声称原文已经犯了这个错误。

在标准算术模型、固定同一 base object 的范围内，局部实化的秩一度量对象彼此同构：有限处用uniformizer的形式实数幂匹配两个divisor，无穷处用正实缩放匹配半径。因此，对任意全局实化对象 L，可以在每处取局部对象 H_v、结构态射 id_Hv，再选择 H_v 的实化到 L_v 的同构。这样就给出一个上述 collection；也满足“局部对象来自 hull-approximants”的可选限制，因为选择的正是 H_v 本身。有限支撑之外可取共同标准对象的恒等同构。

因此，单独取这个 collection 范畴到全局对象范畴的投影，其对象层的像不会自动限定全局 degree。所需约束若存在，必须由实际算法像及其相容态射携带；不能从对象存在推出。

这里使用的是标准算术 realization 的结论，不把所有抽象 BPS 的 localization 函子自动认作同一数域的标准 localization。它已经足以反驳“这些列出的对象条件本身蕴含数值下界”这一通用候选引理。

## 3. 符号约定与局部比较方程

固定数域 F、原算术 degree 和 reference。先不除以 [F:Q]；最后同时除回。有限处的除子系数 α_p 对应局部格子 p^(−α_p)，无穷处的系数 α_σ 对应半径 exp(α_σ)。于是相对 log-volume 等于

    deg α = Σ_p α_p log Np + Σ_σ [F_σ:R] α_σ.

非零全局函数 f 的 principal divisor 在有限处是 ord_p(f)，在无穷处是 −log|σf|；product formula 给 deg div(f)=0。这个约定与 FrdI Example6.3、III Proposition3.9(iii) 的算术 degree/区域读出方向一致。

设输入线对象由 α 表示，目标 determinant 线对象由 β 表示。局部乘子 a_v 给出 Frobenius 次数 d 的局部有效态射，当且仅当

    d α_v + Z_v = β_v + div_v(a_v),     Z_v ≥ 0.

这是 FrdI Theorem5.2(i)，p100 的模型态射公式。有限处它就是 a_v L_v^(⊗d)⊆H_v；无穷处它就是相应半径不等式。d=1 才是 linear。

注意：乘以非单位可以是两个不同格子之间的局部同构。例如乘3把3Z_3同构到9Z_3。这不意味着二者在固定环境 Haar measure 下等体积。把“局部对象同构”直接替换成“同一环境的原规范化体积相等”会遗漏这个乘子。

## 4. 一个在所有有限扩张后仍存在的反例

先取 F=Q，固定 p=3。这里的 L 是检验候选接合引理的算术线对象，不声称它已经是某份完整 Θ-data 的 native q-pilot。

    L_3 = 3 Z_3，H_3 = 9 Z_3；
    L_p = H_p = Z_p（p≠3）；
    L_∞ = H_∞ = [−1,1].

将各处标准单位格/球的相对 log-volume 取为0，则

    Q_0=ν(L)=−log3，h_0=ν(H)=−2log3<Q_0.

各处确实有局部 **linear isomorphism** L_v→H_v：在3处乘3，在其他有限处和无穷处取恒等。它们与局部单位作用、局部 Galois 作用相容；全局对象取 L，localization 同构取通常的同构，就得到第2节列出的数据。若要求局部对象自身为 H 的 hull-approximant，可改取 H_v/id，再以逆局部同构将其粘到 L_v。

但是，不存在全局 **linear** 有效态射 L→H。若它由 f∈Q×给出，有限处的条件要求 f∈3Z；无穷处要求 |f|≤1。这与非零 f∈3Z 矛盾。

这个论证不是有限枚举。对任意有限数域扩张 E/Q，若存在基变换后的全局 linear 有效态射，则 f∈3O_E 且所有嵌入满足 |σf|≤1。由前者

    |N_E/Q(f)| ≥ 3^[E:Q]，

由后者 |N_E/Q(f)|≤1，矛盾。因此任意有限 base-change 都不能修复它。对任意共同正 tensor power M，同理得到3^M而非3，仍矛盾。实化后的不存在性由第5节的 degree 公式直接给出，不以“实化有理函数仍是某个实际 f”这一错误说法证明。

局部 Kummer 自然性也不排除此反例：在3处，取实际元素3的各阶 Kummer 类及相容根；在其余处取1的类。每一处的 Kummer 边界映射与所有局部有限扩张的限制/范数相容，包含标准的次数因子：Norm_E/F(3)=3^[E:F]，不声称它等于3。这只是逐处的完整局部数据，不是全局 Kummer 类的存在声明。所有局部标量也与其局部 Galois/单位作用交换。故不断增加**仅逐处**的这些层数，不会凭空证明全局下降。

这里还有一个关键检查：L^(⊗2)=H，所以确实存在 Frobenius 次数2的全局态射 L→H。它只证明2Q_0≤h_0；绝不能拿它证明Q_0≤h_0。原文(cQ3)中的 linear 一词以及 Ob3 的共同 tensor/normalization 不能删。

这不是原 IUT 的反例：未构造初始 Θ-data、实际 theta evaluation、完整 source-output family，也未证明它们能产生上述 H。它严格否定的是前包拟用的弱接合准则，以及“任意多的局部相容性足以自动拼成全局 linear 态射”的推理。

## 5. 给定局部比较的精确下降障碍

假定全部数据已经放进同一个标准全局实化 arithmetic model；局部乘子除子和有效余量有有限支撑。令

    A=(div_v(a_v))_v，Z=(Z_v)_v；
    Q=deg α，h=deg β，κ=deg A，S=deg Z≥0.

对模型公式求 degree，得到

    dQ+S=h+κ，亦即 h−dQ=S−κ.                 (★)

当d=1且反面假设h<Q时，所有这样的局部比较都满足

    κ=Q−h+S ≥ Q−h > 0.                         (†)

如果它们来自一条全局实化 linear 态射，其乘子除子属于全局 principal divisors 的实线性张成，degree必须为0，和(†)矛盾。

反例中以log3为单位，α=(−1,0)，β=(−2,0)，Z=(0,0)，A=(1,0)，故κ=1。真正全局函数3的除子却是(1,−1)：不能把无穷处的−1漏掉。

κ是**给定比较数据**的不变量，不仅是端点的不变量。改选更收缩的局部态射会同时改变S和κ，只有κ−S=Q−h由端点决定。把κ另设为一个未实现的自由字段没有进展。

在指定数据范围内，以下操作不隐藏κ：

- 对局部目标的单位 automorphism 取轨道：其局部 divisor 为0。
- 由真正全局有理函数改变 source/target 的全局 trivialization：只加全局 principal divisor，其degree为0。
- 两端同时 tensor M，并按原M除回：κ与S同乘M，规范化后恢复原值。
- 标准有限数域 base-change：未规范化degree同乘扩张次数；除回原次数后不变。
- 两端减去同一 reference：差值不变。若只改一侧reference，差值及障碍必须一同记账，不能将其隐去。

不允许任意独立局部换框架后仍宣称κ不变；原gluing、局部坐标和reference的变化必须一起运输。这正是要核查的内容。

## 6. 实化后 κ=0 也是充分条件，而且有有限构造

准确陈述：固定有限支撑的局部比较数据和原gluing，在标准全局实化 Frobenioid 中，局部态射**实化后的**poly-morphism轨道可由一条全局相同次数d的态射诱导，当且仅当κ=0。

必要性已证。充分性不靠新增公理：FrdI Proposition5.5(iv)将实化的有理函数除子明确描述为R·Φ^birat；Theorem6.4(i)的证明说明这恰好是有限支撑degree-zero除子空间。因此κ=0给出一个实化全局有理函数乘子，其divisor正好是A，原等式 dα+Z=β+A 和Z≥0就构造了所需全局态射。相同局部divisor的乘子只差局部目标单位，故给出同一实化poly-morphism轨道。

还可以不把这一步当黑箱。下面给出构造：

1. 对A的有限支撑中的每个有限素理想p，取正整数m_p及实际f_p∈F×，使(p)^(m_p)=(f_p)。理想类群有限保证存在；可以通过理想运算产生并核验这个等式。
2. 若A在p处的系数是c_p，取实化有理函数的形式实线性组合 Σ_p(c_p/m_p)[f_p]。其principal divisor与A的全部有限处分量相同。
3. 相减后只剩无穷处向量r。因为κ=0，r的加权和为0。
4. 取单位群模torsion的基ε_1,…,ε_(r1+r2−1)。Dirichlet单位定理说明其对数divisor向量构成这个无穷处degree-zero实空间的基。解一个(r1+r2−1)维实线性方程，就得到r=Σ_i t_i div(ε_i)。
5. 合并前两组形式实线性组合，得到全局实化乘子。代回模型态射公式检验每个Z_v≥0，完成构造。

这是真实的有限数学构造，不是“给一个globalization字段”。它也不是对任意黑箱实数都能判定κ=0的计算机算法：一般实数的精确相等需要证明或精确表示。对有理指数的代数数/素数对数，可使用精确乘法恒等式；数值近似只能给带误差的界，不能把接近0当成0。

Schoof《Computing Arakelov class groups》(2008)，§2，Prop2.2及后面的算法部分，提供了理想类群、单位格、原始degree-zero Picard群的具体结构和计算背景。要特别区分：未实化时，degree0通常不等于principal；理想类及单位格的剩余障碍仍在。这里使用的是FrdI规定的实化，不是未经说明地对普通Arakelov类群做商。

一个严格例子：F=Q(√−5)，p=(2,1+√−5)，Np=2，p²=(2)。除子

    A=p−(log2)/2·[∞]

在唯一复处权重2下degree为0，但不可能由F中一个实际函数产生：这要求某个整数a+b√−5的范数a²+5b²=2，显然无解。因此原始类别中不能下降；在实化中A=(1/2)div(2)，则确实下降。这说明“realified”不能从定理陈述中省略。

## 7. 最小补偿、多层复合及机器该算什么

在第4节反例中，把H的无穷处半径从1扩大到3，得到H′，其除子为β′=(−2,1)。现在

    α=β′+div(3)，ν(H′)=Q_0.

因此全局乘3给出真正的linear同构L→H′。精确需要补回的log-volume是log3。一般若h<Q，要靠仅扩大无穷处半径修复“存在某条全局实化linear态射”，至少补回Q−h；补到相等后，第6节构造给出同构。此处只说明最小算术代价；并未证明这次扩大是IUT源输出允许的扩大。

对于任意长度的**真实、端点匹配**局部态射链，FrdI Theorem5.2(i)给出

    d_(ψφ)=d_ψ d_φ，
    A_(ψφ)=A_ψ+d_ψ A_φ，
    Z_(ψφ)=Z_ψ+d_ψ Z_φ。

同一base上的degree满足相同递推；有base-change时先保留对应pullback和原扩张次数，再正规化。于是n层复合的κ、S都是各层κ_i、S_i乘以后续Frobenius次数的加权和。任意层数都能由这个递推核算，而不必只检查两三层。

这给出严格剪枝规则：在同一固定frame和原normalization中，已经验证d=1、κ=0、S=0的全局同构层可从数值账本消去；其前后的非零κ不会因为多复制几层同构而消失。但是κ=0、S>0的真实有效扩大不能删，它确实增加体积，可能抵偿已有亏损。实际hull扩大/Ind3的正余量正是仍值得研究的部分。

对精确覆盖，可从真实源得到某组比较且S≥κ；对ε-覆盖，可得到S≥κ−ε。后者给h≥Q−ε。只是重写(★)当然不算证明；价值在于A、Z及d必须由真实箭头计算，哪些层为0、哪些层产生正余量均可独立检验。不得用目标不等式反过来定义这些数据。

本包脚本 c9_local_global_descent_20261024.py 使用有理数/整数，核验反例、全局principal divisor的对偶阻碍、Frobenius次数2的区别、无穷处精确修复、真实模型复合的加权公式及20组共同tensor/base-change正规化。没有浮点近似，没有按“人类算不完”人为堆20层；无限塔结论来自第4节证明，不从20组有限检查外推。

## 8. 回到实际 evaluation：哪些源步骤已经够，哪些还不够

IUT III Example3.6(i)–(iii)，pp107–108，给出尤其有用的准确区分：

- 任意符合有限支撑条件的局部fractional ideals可定义一个全局算术线对象。
- 该全局范畴中的linear态射必须来自**同一个**f∈F_mod×，并在所有处同时积分。

因此，Prop3.7(v)，p112，从实际局部fractional ideals构造全球对象的算法，不仅因其输出是global object，就自动给出native q到该对象的全局linear态射。需要实际态射/余量计算。这一判断是从原定义直接得到，不是一般性的怀疑。

III Remark3.10.2、3.11.1(iii)中的evaluation/Kummer/BPS同构仍保持前包已核实的abstract pilot；本包没有推翻它。新的定位是：在传到同一目标frame、处理Ob3加权determinant与inverse reference之后，必须保留具体局部比较及其globalization，或者通过真正的区域扩大证明相应S足够。局部算术线同构、BPS同构及collection对象存在，分别都不自动给出这一步。

FrdII Remark5.6.3，pp65–66，确有很强的供体：标准算术poly-Frobenioids的等价，在全部局部整数型条件下诱导的全局degree比例为1，即使global部分实化。不能因此直接宣称此处比例为1：还需证明实际返回比较提升到这种**带标准全局—局部化函子**的等价。IUT的局部分裂q单子、随pilot重建的localization及formal quotient不能未检验就替换成该定理的输入。

补充文 Essential Logical Structure §3.8.2(iii)–(iv)，pp122–123，明确讨论LGIsl：相关局部G_v需与全局Galois群嵌入相隔离，以支持要求的同步。故“把所有局部Kummer比较默认当作同一全局Galois类的localization”不是原文允许的省略。这里的隔离不证明目标不成立；它说明真正的全局相容性必须由后续源构造恢复/实现，不能事先强加。

本包没有读到一个独立于 Cor3.12(xi-e)–(xi-f)结论、可直接应用于这些实际局部乘子并令κ=0的现成定理；这不是断言全部文献中不存在任何这种证明。下一动作是具体计算III Remark3.10.2的实际evaluation在Prop3.7(v)输出的两组fractional ideals之间产生的A、Z，并保留Ob3的全部reference、权重和共同M。最有价值的证据是：一个真实全局torsor态射/实化principal-divisor等式，或一个真实源扩大产生S≥κ的证明；仅再证明“能构造global对象”不再列为突破。

## 9. 与原目标、并集及无限值的关系

所有端点必须来自原任意合格完整C，固定native q和gluing。这里可以把H取为完整输出族并集的hull及其determinant；不要求一条primitive branch独自达到Q，也不把(cQ3)的整个对象范畴当成实际输出族。

若最终Θ=+∞，反面假设Θ<Q不能发生，本包的有限degree反证不需要构造一个“degree=+∞的算术线对象”。但Θ=+∞本身也不证明原Values实际ε-覆盖Q；那是另一个源构造结论，仍须给出。

本包真正剪掉的证明依赖是：从local-global collection对象存在直接推出原native-q cut membership；从不记次数的全局Frobenioid态射推出所需linear体积比较；靠任意多次纯局部相容检查自动获得全局principal关系。没有修改目标、缩小C的量词或改Values定义。

## 10. 验收与来源

自然语言结果：上述局部—全局接合反例、全有限扩张稳定性、局部比较公式、实化下降充要判据和有限构造、多层带次数递推均已完成root自审。未完成：实际IUT源输出的κ/S计算及P6覆盖。无原IUT反例。

statement_compiles、proof_body_checked、kernel_closed、comparator、Project build：未运行（本包无Lean）。独立审查：未运行；只有root自审。target_accepted=false。精确计算结果及文件哈希记录于同目录EVIDENCE JSON。

主要来源及适用处：

- [IUT III](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf)，May2020，Ex3.6，Prop3.7(v)，Rmk3.9.5(ix)(cQ3)、3.10.2、3.11.1及Cor3.12 proof(xi)。
- [The Geometry of Frobenioids I](https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Geometry%20of%20Frobenioids%20I.pdf)，June2008，Thm5.2(i)模型态射/复合、**Prop5.5(iv)**实化模型、Ex6.3、Thm6.4(i)。注意不是Prop5.3(iv)。
- [The Geometry of Frobenioids II](https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Geometry%20of%20Frobenioids%20II.pdf)，June2008，Ex1.1、3.3、5.6及Rmk5.6.3。
- [Essential Logical Structure](https://www.kurims.kyoto-u.ac.jp/~motizuki/Essential%20Logical%20Structure%20of%20Inter-universal%20Teichmuller%20Theory.pdf)，March2024，§3.8.2(iii)–(iv)的LGIsl。
- [Schoof, Computing Arakelov class groups](https://library.slmath.org/books/Book44/files/14schoof.pdf)，MSRI Publications44(2008)，pp447–495，§2及Prop2.2；算法背景不替代源输入的构造。
