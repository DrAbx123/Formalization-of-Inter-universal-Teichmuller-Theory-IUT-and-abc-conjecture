**任务与结论状态**

任务 N8-C9-ALLOWED-REGIONS；owner 为当前 chat root；2026-10-24；SHEAF 阶段 1。用户要求自然语言研究，不写 Lean、不派 subagent。本包是上一份 C9-BPS-THETA-REGION-NATURAL-RESEARCH-20261024.md 的继续，不替换其历史结论。

实际消费者：n8-c9-output-region-source-route、n8-c9-p6、n8-s3-c9 中的完整输出族、Values/Theta 构造、q-pilot 比较。精确写入本记录、同名 EVIDENCE JSON、root 所有的 DAG 节点，并向 AUDIT_LEDGER、STATE、queue 追加。其他 owner 的 Lean、目标定义和调度不改。构建负责人不适用。

固定量词范围：一个原文合格的 initial Theta-data、实际 log-theta-lattice、指定的 Theta-link、目标侧 q-pilot 与完整 BPS gluing。只变化原文允许的表示、Kummer/log 分支和 indeterminacies。不把任意具有同构弱 BPS 的其他算术输入加入同一个输出族。以下用 C 表示这份固定配置，B 表示其中指定 BPS。

本轮结论：原先“构造 A，然后寻找 suitable S”的表述不够准确。原始分支中的积分数据和 A 必须共同生成；最终允许输出还包括源明确授权的 hull 内扩大，并不要求每个最终输出都是某个原始 S 的精确像。可以展开区域生成的操作规则、外逼近方向、全局 hull-approximant 和目标侧 log-shift 的体积类校准。尚未证明的是：这些操作保持与固定 q-pilot 的关联，强到足以保证其指定体积类属于最后的允许族。不能把此点改名为 existence of suitable S 后认为完成。

**一、先把三个层次分开**

1. 原生 holomorphic 区域：在一个实际 realization 中，由实际 Gaussian/LGP generator 和指定积分结构得到。
2. 表示族：将原生数据放入原文 log-Kummer 对应，加入 Ind1/2 及 Ind3 所描述的包含/覆盖，得到带来源和 pilot 关联的可能表示。分支可能只给 pre-region 或外区域的逆系统。
3. hull 内扩大族：先取第 2 层所有分支的各分量之并，再在指定目标 holomorphic structure 中取 hull；随后允许其中的合格区域及源允许的 hull-approximants。

第 3 层是 Essential Logical Structure (March 2024), §3.10 Stp4–5 明确使用的扩大。因而，要求第 3 层每个元素都有一个第 1 层精确 realization，是额外的、未获来源支持的要求。反过来，第 3 层的自由度也不能提前放进第 1 层。

这是对前一记录第七、九、十部分的细化：保留实际 action、区域、来源的要求；撤下“最终 q 比较必须找到一个原始 S 的精确像”的强解释。所需比较可以在授权扩大后的全局体积类上进行。

**二、积分数据的起点有具体来源，不能成为独立自由变量**

在非阿基米德实际局部域 k 中，原生积分对象是 O_k 或 O_k 去掉零的乘法版本；采用加性区域时补回零。在实际有限 tensor block

    E = tensor_{i=0}^j k_i

中，holomorphic 积分结构 O_E 是有限 étale 代数各 field summand 的整数环之积。III Prop.3.1(ii)、Remark 3.1.1(i)、Remark 3.9.4(v) 指明了这种结构。O_E 不应未经证明替换成 tensor_i O_{k_i}；后者与前者的差由 ramification/different 控制。

另一个对象是 mono-analytic log-shell 及其 tensor lattice：

    I_k = (p*)^(-1) log(O_k^×),
    p*=p (p odd), p*=p^2 (p=2).

它满足 O_k ⊂ I_k、log(O_k^×) ⊂ I_k，但通常不是 O_k-submodule。无穷处的具体 holomorphic 表示中相应控制球为半径 π 的球；在 mono-analytic 坐标中可呈为 unit ball，必须带上两者的实际比较。不能丢掉这个校准。

固定实际 Gaussian profile 的分量 g_j 后，pilot generator 在该 block 的作用为

    A = id tensor ... tensor multiplication(g_j).

因此一个原生 holomorphic 区域模型是 A(O_E)，经后续表示得到 A(S) 型表达。这里 S 的改变来自积分对象的实际运输及对应，不是反解所需体积差。源 monoid action 的所有幂可以作为结构保存；pilot 输出用被标记的 generator，不能把任意幂、特别是幂 0，都混为同一个 pilot 的输出。

**三、如何生成 log 对应中的积分数据**

原文 III Remark 1.1.1、Remark 1.2.2、Prop.3.5(ii) 给出的规则比“所有 log 迭代”精确。

非阿基米德地方，在固定一条源允许的 log sequence 和其中的 Kummer 表示后，使用两类资料：

- 不经过 log-link 的原生整数/单位对象的 Kummer 像；
- 从某行开始，沿有限个相邻 log-link，再接终点 Kummer 表示所得的像。

第二类的定义域是原生单位中那些在每一步都落入下一条 log-link 定义域的元素。若以 L_{m,h} 表示从第 m 行开始的 h 次复合，就必须同步保留 D_{m,h}=Dom(L_{m,h})。不能把它写成定义在整个 k 上的 log^h。原文在每一步只让 local units 进入 log-link。

各步的域、像和关系均来自固定配置中的实际 monoids、maps 和 Kummer identifications。这给出普通集合/关系意义上的构造：取指定域、取指定映射的像、再按源指定的 tensor maps 组装。源的 O_E 是整数结构；纯张量集合、它生成的 tensor lattice、以及 O_E 三者也不能任意互换。

控制为何成立？零次路径的整数部分落在 I_k；非零路径的最后一步是某个单位域上的 log，其像也落在相应 I_k。Prop.3.5(ii)(a) 将此控制推广到全部指定 tensor/Kummer 分支。对原文大定理的完整同步与重建仍是引用依赖；本段没有从弱 BPS 重新证明它。

无穷处要反过来保留覆盖关系。单位 u=exp(i t) 可取 |t|≤π 的提升 i t，这解释了有界球为何能覆盖单位。对迭代，使用 Prop.3.5(ii)(b) 对实际定义域的覆盖结论；不能取所有复对数提升 i t+2π i n 的无界并，也不能声称任意单位可在所有迭代中无条件继续。

在经过原生整数/单位比较后，以 tensor packets 为单位组装这些资料；同一分支中的 Gaussian profile、零标签 splitting、根单位、局部域识别和 global Frobenioid 必须一致。log 只作用于指定的单位部分；不能把非单位 Gaussian generator 乘进去后再取 log，或把 A 随意移过 log 箭头。Prop.3.5(ii)(c) 给的是 splitting monoid 的特定相容性，不是 log 与乘 g 交换。

所以，完整分支的索引不是一个孤立 S，而是完整相容数据 χ：realization、指定 Kummer maps、单位域上的 log 路径/覆盖、Gaussian generator、tensor/全局同步、表示到目标容器的识别。固定 χ 时可将其当地输出写作

    R_{χ,j,p} = transport_χ(A_χ(S_χ))

或相应的关系像/外区域逆系统。这里 S_χ 由上述程序生成。所有 χ 的范围是源允许的完整图数据；不要求每个当地分量独立选 χ，也不把所有与数字目标相容的 S 作为 χ。

这是一份用原文实际对象和映射作输入的关系式描述；完整形式化仍要实现这些对象并证明覆盖与原文一致。本轮没有把“源允许”作为任意 predicate 假设来证明最终不等式。

**四、Ind1/2 要作用于完整表示；Ind3 不是第三个任意群作用**

Ind1 来自 procession 的源 automorphisms。Ind2 是源规定的各 factor/direct summand 上的 Ism-orbits（无穷处为指定的有限 automorphisms）。对这些变换，action、integral region 和识别必须一起运输：若 σ 是一条允许的表示同构，则作用变为 σ A σ^(-1)，区域变为 σ(S)，输出变为 σ(A(S))。不能只替换 A 或只替换 S。

在一个有限非阿基米德 block 中，若 σ 保持某个正有限质量的 lattice I，则 Haar 缩放因子必须为 1：把变换公式用于 I，利用 σ(I)=I 即得。tensor、procession 权重及其置换兼容性仍按源处理。此处不需要“任意可逆矩阵 determinant=1”这种错误命题；正确结论是相应 determinant 的 p-adic 绝对值为 1。

Ind3 是前节实际局部对应的上方控制。III Remark 1.2.2(iv) 并没有给出一份在所有 log/Kummer 比较下精确互送的共同积分核心。应停止将这种共同核心当作本路线必须证明的中间命题；这不是对所有特殊情形作不存在断言。

也不要把源规定的单向 log 路径和同构选择，替换成“在所有这些操作下任意反复闭包”。尤其不能无条件加入 log 的逆映射、任意非单位缩放、各分量独立的字段识别。源所需的包含/覆盖与自由生成群轨道是不同对象。

**五、外逼近是逆系统，不能作为新的任意扩大分支取并**

若某分支只给 pre-region E，III Remark 3.9.7 使用的对象是所有合格外区域 E*⊃E 的逆系统，其读出是 inf ν(E*)。它不是将所有外区域当作新的原始输出，再取它们的并。

反查：在 Q_p 中，E=Z_p 的外区域包含全部 p^(-n)Z_p，n≥0。它们的 log-volume 下确界是 0，但它们的并是 Q_p。把逆系统改成并，会把一个有界问题直接改成无界问题。

若已知一个合格有界外区域 M，可将外逼近限制在 M 内：用 E*∩M 替换 E*，仍覆盖 E，且不增大体积。对 direct-product compact positive-mass 情形这给出共尾的外逼近；零质量极限按源逆系统处理。因此可以控制外逼近而不让它制造无限 hull。不能要求每个逆系统都由一个正质量极限区域表示。

同样，Remark 3.9.5(v) 的形式空交不是 Nonempty 的点见证。可以保留形式逆系统，但不能从它在某个商对象中有像推导其集合论交集非空。

**六、全局原始输出、总 hull 与可计算上界**

先把每个 χ 的完整 packet 记录下来。之后，按 Cor.3.12 的定义在每个 (j,p) 分量取可能像的并 U_{j,p}，再相对于指定目标 holomorphic structure 取

    H_{j,p} = Hull(U_{j,p}).

这一步允许忘掉部分分支相关性，因为它在构造包络；不能倒过来宣称任意拼出的各分量原本来自同一个 χ。整个 H 是这些当地 hull 的全局集合族，读出 ν 是源 prescribed weighted component log-volumes、procession 平均和 rational-place 求和。

hull 的顺序有实质影响。一个 elementary diagnostic：在 E=Q_p^2 中取 R=pZ_p × Z_p，取 σ(x,y)=(x+y,y)。σ 保持 Z_p^2 且保体积，但 σ(R) 是满足 a-b∈pZ_p 的真子 lattice；其 holomorphic product hull 是 Z_p^2，而 σ(Hull(R))=σ(R)。所以一般不能交换 hull 与 mono-analytic 线性变换。这只是一般线性模型，未声称它本身是完整 IUT 输入或特定源 Ism 元素。

同样，“每个分支紧”不推出“所有分支的并有界”。需要一个统一 majorant。IV Prop.1.2、1.4 及 Th.1.10 proof (iv)–(vii) 提供了相关实际控制：

- 非阿基米德部分，用 tensor-log lattice、tensor 整数环的 normalization 以及 different/ramification 常数作统一夹逼；
- 除有限个特殊 rational places 外，使用等于其自身 hull 的标准积分区域；
- 无穷处使用相应 π^(j+1) 倍球。

其中典型的局部夹逼（使用 IV Prop.1.2 的记号）是

    φ(p^λ (R_I)^~) ⊂ p^floor(λ-d_I-a_I) log_p(R_I^×)
                     ⊂ p^(floor(λ-d_I-a_I)-b_I) (R_I)^~.

其 elementary 原理是：固定两个 full Z_p-lattices 总能用 p 的整数幂相互夹住；保持中间 lattice 的 automorphisms 同时保持这些 p 的整数幂。源将全部允许像放入相应控制中这一事实仍按 IV 所引用的 III 结构解释，本轮不以任意局部 action 替代它。

据此，在合格源输入上，可独立于 q≤Theta 的比较建立一个有限 global upper readout；再由实际原生正质量区域提供下方有限读出，得到有限的 ν(H)。这是 finiteness 的明确来源，不能仅用“每支紧”代替。采用 IV proof (iv)–(vii) 的包络部分不必使用其后从 Cor.3.12 推 Diophantine estimate 的部分；后者不能反过来证明前者或 C9。

因此 WithTop 可以保留为一般 hull 构造的总化边界，但目标合格输入应另证有限性。若一般输入发生 +∞，上界包含关系虽平凡，它不自动产生所需 q 关联或任何有效有限估计。

**七、最终扩大族及全局 hull-approximant 可以具体构造**

暂假设 H 是合格、正有限体积的全局 hull，θ=ν(H)∈R。考虑几何扩大族

    G(H) = {R : 合格的全局 direct-product region，且各分量 R⊂H}.

这里合格包括源全局有限支撑条件：除了有限个 rational places，局部总读出为零。不是区域内部“几乎处处 log=0”。保持输入 B 与来源标记另是一项任务；G(H) 在这里首先是明确的几何包络族。

可以完全展开证明：G(H) 的全局读出集合恰为 {t∈R : t≤θ}。

上包含由体积单调性。对反包含，给定 t≤θ，保持所有分量不变，只选一个无穷处、正权重的 field/radial 分量。若将其 hull ball 的半径乘 s，其对全局 ν 的改变为 c log(s)，其中 c>0 是该分量的源权重和 normalization 系数。取

    s = exp((t-θ)/c) ∈ (0,1].

所得 R_t 仍在 H 内，具有正有限体积，只改变一个地方，因此保持全局合格性，且 ν(R_t)=t。实际上 R_t 本身就是 hull 型区域。这里既未用 q，也未求解任何 Kummer/eta 等式。

同理，对任意合格有限读出的 P，令 H0=Hull(P)，δ=ν(H0)-ν(P)≥0。只在一个无穷分量将 H0 缩小 exp(-δ/c) 倍，得到 H'⊂H0 且 ν(H')=ν(P)。这展开了 III Remark 3.9.5(iv)(Ξ2) 的全局机制。H' 不必包含 P；源 Ξ(P) 要求的是 H'⊂Hull(P) 及同体积，不是 P⊂H'。不能把它误写为当地每处分量同体积，或要求当地离散的 ideal 体积实现任意实数。

关于 pilot 的符号：上述是几何读出命题。III Remark 2.4.2(iv)–(vi) 对重建带 pilot 的 prime-strip 使用负 pilot；Cor.3.12 在 θ<0 的非平凡情形使用该比较。θ≥0 时 q 的负读出已给出数值不等式，但不能据此宣布正数或零也具有同样的 pointed prime-strip 解释。

在 θ<0 情形，还可以按 Remark 2.4.2 的 converse construction，为每个 t≤θ 构造相应的 value-group prime-strip：以全局有序体积线和负 pilot t 为起点，配上源固定的各处 local-to-global conversion ratios，再取规定的局部非负 monoids。这说明同体积类确实能产生相应类型的带 pilot 对象。它仍不证明这个对象与输入 BPS 的关联就是原始 Θ-link 经算法所得的关联；不能另选一个抽象 pointed isomorphism 代替该关联。

这表明最终层不需要寻找一个神秘 S。若在固定坐标中硬要写成 A(S)，可以对最终 R 取 S=A^(-1)(R)；这只是扩大后区域的反向坐标表达，绝不证明该 S 是原始 Kummer/log 分支允许的积分区域。

**八、目标侧 log-shift 的体积校准可由小单位邻域展开**

这里进一步减少一个此前笼统列出的 gap。III Remark 3.9.4(iii)–(vi)、3.9.6 的相容性不是“任意区域 E 与 log(E) 有相同体积”。

在 k/Q_p 有限时，取足够深的 principal-unit 邻域 S=1+p^N O_k，使 log 和 exp 在 S 与 p^N O_k 间互逆。log(1+x) 的线性项为 x，较高项在这个小域中严格更小；因此它给出保 Haar 体积的局部对应。更一般的小单位域同样由单位导数得到绝对 Jacobian 1。

源的 Rss 先对可积非负函数的积分作实化/半单化；它不限于一份固定 shell，也不是给孤立 set quotient 无证明加上线性结构。任何正有限质量小域都能在这个实化层面给出整个体积半直线。于是

    k ← S → log(S) → k

在体积实化层面给出保持积分的同构；以积分读出来就是恒等映射。取更深的 N 不改变它，因为所有箭头都用实际 Haar 校准。对任意 t 直接手设“映射为恒等”不是这份构造的替代。

无穷处同样可看小弧：长度 ε 的单位圆小弧，平移一个端点到零后，其径向长度为 2 sin(ε/2)，与 ε 之比趋于 1。源的取极限/实化程序给出相应 angular/radial 校准。再按实际 field summands、tensor degrees 和源权重组装；局部相等和 product-formula conversion ratios 给出全局 degree 相等。

q 非单位并不进入 log 的定义域。被比较的是 [qO_k] 的体积类，经已经校准的 Rss 同构运输；III Remark 3.9.4(iv) 正是在这个层次保留 q^N 的读出。因而不必计算 log(q)，也不丢失 q 的赋值。

这展开了目标侧 log-shift 的数值机制；仍不是跨 Theta-link 的 q 与 Gaussian 比较。源完整构造及其与原图的绑定仍须在项目中实现。

**九、剩下的核心比较究竟是什么**

到此，一旦源分支图已给定，我们有实际作用、对应生成的积分资料、共同容器里的可能像、总 hull、明确的几何扩大族，以及目标侧 q 读出 Q。不能再把剩余问题说成“随便找一个 suitable S”。

必须保留完整输出关系：

    固定 BPS 的输入 pilot
      —实际 Θ-link / Kummer / evaluation 的关联—
    可能输出的带 pilot 区域/向量丛/行列式对象。

放宽区域时，应放宽这条关系的输出端，固定输入端；不能把关系投影成一个裸区域集合后，再任意配回一个输入 pilot。保持原分支的集合包含只说明旧输出仍存在，并不独自说明目标侧 native q 的指定体积类已存在。

原文声称的实质要求可以准确表为：在固定 q-pilot 的源配置上，经上述 descent、hull-approximants、带 reference correction 的 determinant 及目标侧 log-shift 后，输出体积族包含 native q 的指定体积类；若使用源允许的逼近解释，则任意 ε>0 有一个输出读出 v≥Q-ε。

这个要求应从实际 prime-strip、global Frobenioid、pilot 标记的运输推导。它不要求 qO 按当地集合逐项包含在原始输出中，也不要求两侧环结构成为同一个环；只需要在正确的最终全局体积类中实现比较。

本轮检查了 III Cor.3.12 proof (xi-b)–(xi-f)、Remark 3.9.5(vii)–(ix)、EssLgc Stp7–8、Alien §3.11(v)、April 2026 Formalization §4。它们把保持固定 gluing、同时 holomorphic 表达及 hull/determinant/log-shift 后的比较作为关键；本轮未给出把前述具体积分关系逐对象推到 native q 体积类的完整证明。因此不能报告这一核心已闭合。

为什么其余已完成计算不能替代它？一个仅作逻辑检查的局部模型足够：在 Q_p 取固定 integral reference Z_p，让算法 action 为乘 p^2，而 native q-region 为 pZ_p。两者都真实可测，所有 Haar/determinant、同一容器和各自 monoid action 都正确；前者的 hull 为 p^2Z_p，ν=-2log p，后者 ν=-log p。前者 hull 内区域不能实现后者读出。此模型不是合格 IUT 配置，也不是对原文反例；它只排除“有实际 action、同一容器、正常体积函数就自动完成比较”的弱接口。

同样，在第七节已证明 G(H) 的读出为 (-∞,θ] 后，存在 R∈G(H) 且 ν(R)=Q，与 Q≤θ 完全等价。若先按差值 θ-Q 调 S，或把 suitable 定义为能满足 eta equality，就把待证不等式放进选择条件了。正确的源证明必须在这一步之前证明固定输入关联的保留。

**十、对路线的具体修订及可执行的下一研究项**

保留：实际 cyclotomic/Kummer/evaluation、Gaussian generator、指定因子的 action、全局权重、hull、determinant 与 reference correction。

修改：把单个“允许 S”接口改理解为生成 action 和积分资料的相容分支关系；将原始分支、Ind3 控制包络、外区域逆系统、hull 内授权扩大分别命名；仅在最后层讨论同体积 hull-approximants 和 q 的全局读出。

剪除本路线的错误证明需求：所有行共同的精确积分核心；任意 outer covers 取并；全部 monoid 幂混为 pilot；hull 与 mono-analytic automorphism 无条件交换；每个最终 output 都必须有原始 S 精确 realization；单点或 abstract Nonempty 作为输出区域的替代。

下一研究项不是再定义一个 η：以 III Remark 3.10.2 的实际复合为起点，将其输入 pilot 标记写入每个局部/全局对象，逐项核对从源表示关系到 III Remark 3.9.5 的 hull/determinant 关系的箭头，证明这些箭头在固定输入 BPS 上保持所需的全局 pilot 体积类。特别区分：determinant 的数值公式已经可算；该 determinant 对象携带的 pilot 与 fixed input 绑定尚未由此公式证明。April 2026 §4 的 HDD 与 SHE 应用于同一实际源对象，是核对位置，不能用新增“compatible”字段充当证明。

**来源、复用与验收**

- IUT III，May 2020：Remark 1.1.1、1.2.2；Prop.3.1、3.5；Remark 2.4.2、3.1.1、3.9.4–3.9.7；Th.3.11；Cor.3.12 proof 尤其 (xi)。本轮定向读取上述段落，不声称通读全篇。官方 PDF：https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf 。
- IUT IV：Prop.1.2 的 lattice 夹逼；Th.1.10 proof (iv)–(vii) 的统一容器。官方 PDF：https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf 。
- Essential Logical Structure，March 2024：§3.10 Stp1–8、§3.11。官方 PDF：https://www.kurims.kyoto-u.ac.jp/~motizuki/Essential%20Logical%20Structure%20of%20Inter-universal%20Teichmuller%20Theory.pdf 。
- Alien Copies：§3.7(ii)、§3.11(v)。官方 PDF：https://www.kurims.kyoto-u.ac.jp/~motizuki/Alien%20Copies,%20Gaussians,%20and%20Inter-universal%20Teichmuller%20Theory.pdf 。
- On the Formalization of IUT，April 2026：§4 pp.9–11。官方 PDF：https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf 。
- Dupuy–Hilado arXiv:2004.13228v1，§3.9、4.8–4.11：其 coarse UTheta 公式用于反查对象层次；作者说明 Ind3 不是简单的 set function application，且该文并不证明 Cor.3.12。未把引用中的未取得续篇作为已核实供体。https://arxiv.org/pdf/2004.13228v1 。
- LANA report 固定 commit 293bdd89463473ae13d40834d70fb4b7ba81da1f：本轮重核 main goal 2500–2528 行及本地 η construction；suitable S 的等式在该报告是研究目标，不是供体证明。https://github.com/katobungen/LANA_report_202607/blob/293bdd89463473ae13d40834d70fb4b7ba81da1f/LANA_report_202607.tex 。
- Cmt2018-05 C11–18 的局部文本作为校准与标签解释的反查；复用前次冻结来源，不把评论当作缺口的独立证明。

复用：前一 BPS 研究的固定-realization Gaussian/action/determinant 计算；既有 P0/P1 source table。没有重新全仓审查，没有新增 Mathlib 搜索，没有宣称现有代码已接入这些自然语言证明。

本轮展开证明：外逼近 inf 与 union 的区别；允许 isometry 的 Haar 模数；hull 与一般 integral linear map 不交换的模型；全局半直线读出及同体积 hull-approximant；小单位域到 Rss 的目标侧 log-shift 校准；suitable-region existence 与最终不等式的循环风险。

仍属源引用或未闭合：完整 anabelian/Ind3 分支图的实现与覆盖；统一源 majorant 的全体系接入；带 fixed-input pilot 的下降、扩大、determinant、log-shift 关联保持。前述 elementary 证明不替代这些源定理。

statement_compiles=未运行；proof_body_checked=未运行；kernel_closed=未运行；comparator=未运行；Project build=未运行；independent_review=未运行（root 自审）；target_accepted=false。阶段 1 的局部研究取得具体结果，整个 source q 比较节点仍开放。
