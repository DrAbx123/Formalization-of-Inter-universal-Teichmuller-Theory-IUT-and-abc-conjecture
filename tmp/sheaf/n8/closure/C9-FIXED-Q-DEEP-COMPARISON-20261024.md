# 固定 q-pilot 体积类：外部供体与多层比较研究

任务 ID：n8-c9-fixed-q-deep-comparison-20261024；owner：当前 chat root；日期：2026-10-24。

范围：自然语言数学研究，不写 Lean，不启用 subagent。用户要求直接攻击 fixed-q-pilot 体积类的保留，并从其他论文中寻找可供机器核算的复杂比较路线。

消费者：`dag/nodes/n8-c9-output-region-source-route.json` 的 P6；实际 C9 `QPaperApproximated` / source q coverage 的语义缺口。保留完整原输入、源允许 realization、原 Θ-link、native q、原权重与原 hull。不得用另一个理论中更大的输出集合代替。

目标：固定原文合格 Θ-data 及实际 log-theta-lattice、指定 Θ-link 和 native q-pilot。记 Q 为 native q-region 的全局校准 log-volume，H 为完整源输出族的 holomorphic hull，θ=ν(H)。研究并证明原输入关联经过 Kummer/evaluation、下降、授权区域扩大、determinant 和目标 log-shift 后，仍能在最终输出体积类中实现 Q（或源允许的一侧任意精度逼近）。在先前已经分析的有限 hull 几何层，这与 Q≤θ 等价；不以该等价作为证明。

既有证据：`C9-ALLOWED-REGIONS-NATURAL-RESEARCH-20261024.md` SHA256 `03aad091be1773147a64abd1388f494cd8c947604d2d5b3ca86d295c9dce7ac5`；复用其完整对象区分与目标侧 log 校准，不重新全仓审查。

读文件：IUT II Cor.4.10、III Prop.3.7/3.10、Remark 3.9.5/3.10.2/3.11.1、Cor.3.12；Essential Logical Structure §3.10；外部论文将逐项登记准确版本和适用条件。

写文件：本记录、同目录专用计算脚本/证据、root 所属上述 DAG 节点；向 AUDIT_LEDGER、STATE、queue 追加本包结果。不改其他 owner 文件、生产定义、目标或调度。

证明方法：把复杂比较的每个箭头分成实际构造、可核算的 determinant/度数缺陷、源允许性；先证明适用的精确辅助结果，再尝试在真实源链上消去缺陷。外部理论的输出覆盖、度量归一化和输入绑定必须分别核对，不能凭术语相似接入。

验收：自然语言证明/明确反例或缺口，加版本固定的原文来源与可复核计算。代码计算仅检验指定代数模型，不冒充对所有源输入的证明。Lean 编译、公理、comparator、独立审查均未运行；target_accepted=false。

状态：本次有界文献/数学筛选完成；fixed-q-pilot 比较仍未证明。外部技术尚无一条获准作为已经接通的主证明路线。下述计算是供体和诊断证书，不是合格 IUT 输入上的验证。

## 1. 最新用户要求与研究判断

用户要求多找其他作者的论文，研究可交给机器的大规模、多层比较；随后明确要求先确信路线成立再投入，避免重复人类很可能已经试过的浅层方案。本包因此把“供体数学成立”“可计算”“确实接入原目标”分开判断，不因二十层模型算通就推进 Lean 或大规模搜索。

本次结论：

- 相对 determinant、canonical metric、图能量和动机积分各有可复用的严格技术，但没有任何一个自动完成 fixed-q-pilot 比较。
- 可以证明一个针对原 hull 定义的有限见证压缩命题。它减少计算量，不提供缺失的体积下界。
- 已验证的高度跳跃平方和能处理任意多层，但同一图/同一标记的成比例重复严格给出零；这类“多加几层”的路线退出主线。
- canonical metric 的二次修正、周期比较中的参考 lattice、局部相对 determinant 都必须计回原读出。仅换度量/换表示不能获得所需增量。
- 原 Ind2 不是任意 GL 群。有限层中心化子还需无限层相容和全部规定 lattice 的保持；没有提升证明的矩阵只可用于外包络，不能充当下界见证。
- 尚未得到一份原源分支的输出证书，其在原 normalization 下足以覆盖 native q。因此本包不把任何候选路线标记为 stage1 已完成。

这不是完整 IUT 命题的反例或不可能性结论。以下被否决的是具体简化方式，不是全源输入上的路线。

## 2. 外部论文：准确使用位置、适用条件与决定

阅读方式是针对性核对定理、定义和相关证明，不声称逐页读完所有论文。PDF 固定版本及 SHA256 见 `tmp/pdfs/fixed-q-deep-comparison-20261024/manifest.json` 和 `additional-manifest.json`；网页版本另在下表写明。

| 论文 | 本包实际核对 | 能提供的东西 | 不能据此声称的东西 |
|---|---|---|---|
| Osipov–Zhu, *A categorical proof of the Parshin reciprocity laws on algebraic surfaces*, [1002.4848v3](https://arxiv.org/html/1002.4848v3) | §3.2、§4.2 式(4.5)、§5.1 Prop.5.1/Remark5.1 | 相对 determinant torsor、复合的相容性；真正全局有理函数的互反消去 | 任意地方独立的缩放有 product formula；任意 Θ-link 自动成为同一全局对象上的映射 |
| Braunling–Groechenig–Wolfson, *A Generalized Contou-Carrère Symbol and its Reciprocity Laws in Higher Dimensions*, [1410.3451v3](https://arxiv.org/html/1410.3451v3) | §4.3、Th.6.5/6.7 | 通过真正 localization diagrams 证明高阶边界复合为零 | log-theta-lattice 的二维外形本身给出代数曲面/2-Tate 对象或所需交换图 |
| de Jong–Shokrieh, *Faltings height and Néron–Tate height of a theta divisor*, [1810.02637v3](https://arxiv.org/html/1810.02637v3) | §5、§8.3、§9 Prop.9.1、§14.5 | theta 的 canonical metric 与 tropical 二次项的精确比较；全局 rigidification 的校准 | canonical metric 可以直接替换 IQ-hull 的 Haar/degree 读出 |
| Foster–Rabinoff–Shokrieh–Soto, *Non-Archimedean and tropical theta functions*, [1705.08212v2](https://arxiv.org/abs/1705.08212v2) | Prop.3.19、Cor.3.21、Prop.3.24；Th.4.9 在上一论文中的用法 | theta Fourier 系数、下降 cocycle、tropical theta 与实际度量之间的关系 | 改用 tropical theta 后原 q-pilot 的校准可以丢掉 |
| Biesel–Holmes–de Jong, *Néron models and the height jump divisor*, [1412.8207v2](https://arxiv.org/html/1412.8207v2) | Def.3.3、Th.4.1/4.2、Th.7.8、§8–9、Appendix A | 半稳定曲线的 admissible pairing 在基变换下的缺陷；自配对时有效；图 Green 函数可计算 | 任意体积差都是该 height jump；混合配对有相同符号；一参数重复能产生非零增益 |
| Burgos Gil–Holmes–de Jong, *Positivity of the height jump divisor*, [1701.00370v2](https://arxiv.org/html/1701.00370v2) | Th.1.1–1.4、3.2、4.7 的假设 | semipositive hermitian line/Lear extension 条件下的正性 | 原 IQ volume 已具有这些几何结构 |
| van Bommel–Holmes–Müller, *Explicit arithmetic intersection theory and computation of Néron–Tate heights*, [1809.06791v2](https://arxiv.org/html/1809.06791v2) | §2、Alg.2.3、§3 的范围 | 从有限展示计算交点长度；解 vertical correction 的线性系统 | 其数值 archimedean 实现或 BSD 数值实例是 IUT 比较的严格证书 |
| Česnavičius–Koshikawa, *The A_inf-cohomology in the semistable case*, [1710.06145v3](https://arxiv.org/html/1710.06145v3) | 引言、Th.8.7 及证明 | 实际 proper semistable 对象、相关 log-de Rham 群无 torsion 等条件下的 integral comparison | 任意跨 Θ-link 识别；只取 determinant 还保有 Tate extension 的 q 标记 |
| Hales, *Orbital Integrals are Motivic*, [math/0212236v1](https://arxiv.org/html/math/0212236) | Th.2、§5、Th.8、Lemma10 及证明 | 在其定义域/稳定性条件下，有效计算有限 double coset 界、截断层、Galois stratification 和虚 Chow motive | 任意 IUT 输出关系已可定义；得到 motive 就自动判定所需不等式 |
| Hales, *Can p-adic integrals be computed?*, [math/0205207v2](https://webusers.imj-prg.fr/~francois.loeser/hales.pdf) | §2–5、轨道积分例子 | 应计算参数族背后的代数对象，而非仅逐实例浮点积分；不同曲线可借实际 isogeny 比较 | 只靠算更多样本就证明全称命题 |
| Cluckers–Gordon–Halupczok, *Integrability of oscillatory functions on local fields: transfer principles*, [1111.4405v2](https://arxiv.org/html/1111.4405v2) | Th.3.1.1、3.1.3、3.3.2、4.4.1/2 的范围 | 可定义族的积分仍 constructible；cell decomposition；大剩余特征的 integrability/boundedness transfer | 全部 Galois/Ism 塔和无界 log 迭代自动可定义；transfer 自动给 volume inequality |
| Bartel–de Smit, *Index formulae for integral Galois modules*, [1105.3876v4](https://arxiv.org/html/1105.3876) | Lemma3.1、Prop.3.2、Cor.3.4/3.5 | 有实际 Brauer relation 和 permutation-module injection 时，fixed-submodule indices 可转成 determinant/kernel/cokernel 数据 | 源 procession 权重已经是一条 Brauer relation，或其 regulator 就是原 log-volume |
| Streng, *Generators of the group of modular units for Γ¹(N) over the rationals*, [1503.08127v3](https://arxiv.org/html/1503.08127) | Th.1.1/1.2、§2.1–2.2 的定义、division-polynomial recurrence | 给定 level 的全部 modular units 有明确生成元与整数指数约束；可以真正做格子计算 | 改用某个 modular unit 等于保留指定 theta generator；负指数关系可作为输出区域扩大 |

Cluckers–Loeser 的 *Constructible motivic functions and motivic integration* 已检索到，但本包没有取得足够稳定的具体定理正文；详细积分结论采用已核对的 CGH 版本。Kato 2004 原文 PDF 的 web 获取因大小失败；检索到的二手说明不作为本包证明依据。Elder 的局部 integral Galois module 论文仅作检索线索，未用于结论。

Joshi 的 2303.01662v3 本包也核对过 §7–10，但其 period-ring theta set 的下界不是原 IQ-hull 下界，未接为供体；本次答复不把它充作“其他领域新路线”。

## 3. 已证明：有限输出见证可以压缩原 hull，不能产生下界

以下为本包自行展开的初等命题。源定义位置：IUT III Remark3.9.5(i)，PDF p.127；hull 为指定 holomorphic field decomposition 中 λO 型最小包络。此处严格沿用该定义。

### 3.1 非阿基米德精确压缩

设 E=∏_{a=1}^s K_a 为固定目标 holomorphic structure 的有限 étale Q_p-algebra。U⊂E 有界，且包含一个正有限体积区域 R₀。对每个 a 令

    m_a = min {v_a(u_a) : u∈U, u_a≠0}.

最小值存在：有界性给赋值下界；非零投影由正体积保证；赋值属于离散的 Z。选一个 u^(a)∈U 达到 m_a。于是

    Hull(U) = ∏_a π_a^(m_a) O_(K_a)
            = Hull(R₀ ∪ {u^(1), …, u^(s)}).

证明：每个 u 的第 a 分量在 π_a^(m_a)O 中，给一个包含 U 的候选 hull；任何包含 U 的 λO 必须包含 u^(a)，故该分量至少如此大。两边夹逼即得。

必须保留 R₀：源的 hull 定义以含正体积区域为前提，不能直接把 finite singleton 当成该定义中的正体积输入。即使通过理想生成把有限点写成 λO，体积也是 λO 的体积，绝非有限点的 Haar 体积。

对于 R₀⊂U 和任何有限 W⊂U，同样有 K_W=Hull(R₀∪W)⊂Hull(U)。因此一份带来源的有限 W，若直接算出 ν(K_W)≥Q，就真的足以给出所需数值下界。这里没有反解 S 或以 Q 定义允许性。

若选出的当地见证属于不同分支，每个见证都必须附上一份完整合法的全局 χ。允许合并的是源已经授权的 componentwise union/hull；不能把彼此无关的当地选项伪装成同一个 χ。

### 3.2 无穷处与全局近似

在源的有限维 ball/radial 分量，hull 半径是投影模长的上确界。有界且正半径时，给定 ε>0，可在每个相关分量选有限个实际点，使所得半径从下方逼近该上确界，因 log 连续而让 weighted readout 误差小于 ε。

若已证明一个共同的有限 exceptional-place 集合、且 R₀ 和 H 在其外均为规定 reference hull，则合并有限个非阿基米德精确见证和无穷处近似见证，可得

    ν(H)-ε < ν(K_W) ≤ ν(H).

这里的共同有限支撑是实质输入；不可从“每个分支各自有有限支撑”推出。实际源接入消费 IV 的 uniform-container/finite-support 结果。

于是严格下界 Q<ν(H) 若成立，在这些几何条件下有有限见证；临界相等时可能需要一列 ε 证书。命题没有证明存在一个有效可枚举、对全部真实 Ism 足够稠密的分支生成器，更没有证明搜索一定终止。

### 3.3 机器真正要核验的对象

有限线性分支 Rχ=AχLχ 可用 basis matrix 表示；在 split algebra 中，a 分量的 hull 指数就是各矩阵第 a 行全部非零 entry 赋值的最小值。一般有限扩域中，先用真正 field idempotents 和 π_a 赋值做相同计算。

标准 Haar 归一化 μ(O_(K_a))=1 时，log μ(π_a^m O_(K_a))=−f_a m log p；源的 degree/procession 权重需在此之后准确加入。不得把全部 packet 当成一个未校准的普通 Haar 空间。

涉及 log 的非线性分支必须先证明其实际定义域与像。只有满足可定义性/analytic-cell 条件的部分才可消费 cell-decomposition 技术。对输出并集应消去分支变量、计算“存在 χ”定义的像；积分时不能沿 χ 把同一个输出重复计数。

本命题是计算压缩工具，不是 P6 新证明。当前并没有一份原源 W 通过 ν(K_W)≥Q 的最后检验。

## 4. 原 Ind2 的精确限制与无限层提升

IUT II §4, p.39（本地 txt 约2192–2200行）定义 Ism(G)：G-equivariant automorphisms of O^{×μ}(G)，并对每个 open H⊂G 保持 M^H 中由 O^×(G)^H 的像给出的 lattice。IUT III Th.3.11(i)(Ind2), p.154 要求其分别作用于每个 tensor factor 的每个 direct summand。

这比 GL_d(Z_p) 严格。一个明确诊断：p=3，G=C₂ 在 Q₃² 上由 diag(1,−1) 作用，L=3Z₃×Z₃。与 G 交换的矩阵必须对角，因此其 integral automorphism orbit 保持 L；而任意 GL₂(Z₃) 的轨道并覆盖 Z₃²，hull 体积虚增 log3。该例只否定放松 G-equivariance 的推理，不是对 IUT Ism 的分类或反例。

### 4.1 可以怎样把真正约束交给机器

在一个实际 realization 中，取穷尽有限 Galois 扩张的嵌套塔。逐层保留：有限维 M_n、相关有限 Galois action、该层及其中全部 intermediate fields 对应的 lattices、各层 inclusion matrices。源给定这些有限维结构；本包没有声称单靠裸群标签已实现其有效重建。

一族矩阵 T_n 真正给出 Ism 元素，必须同时满足：

1. T_n 可逆，G-equivariant，保持每个规定 lattice；
2. T_(n+1) 与 T_n 在实际 inclusion 上相容；
3. 以上条件对全部层成立，而非只验证前二十层。

反之，若这些条件确实成立，则 T(ι_n x)=ι_n T_n x 在 ind-limit 上良定义；逐层逆映射同样相容，因此 T 是 ind-topological automorphism，且逐个 open subgroup 的规定 lattice 被保持。这直接给出一个实际 Ism 元素。

在每个有限层/有限精度，条件可写成有限环上的中心化方程、det 为 unit、lattice 包含与 inverse 包含。全部相容有限解形成逆系统。如果对于每个有限截断都存在满足该截断所有条件的解，且所选离散截断确实描述这些 compact lattice constraints，则 compactness/König 引理给一条无限相容解。

但该存在论不提供计算终止界。前二十层有解不能保证后一层仍有解。有效内见证应有显式的全塔构造或提升规则；仅有限截断解属于外近似。一个已知源允许的显式 σ 可以直接用，无需先分类全部 Ism。

### 4.2 内外双向计算的用途

- 内侧只收实际可提升的源分支和积分区域，用于下界证书。
- 外侧可放松部分有限条件，用于给上界并剪掉不可能的候选。
- 若内外未相遇，结果是未知；不以外包络的大体积替代内侧见证。

这一区分决定了复杂计算能否提供正确方向的证据。目前完整源分支到有效有限/无限证书的接入仍开放。

## 5. 高度跳跃：任意多层的真实平方和，以及一个决定性的零结果

这是从 Biesel–Holmes–de Jong 的 Green-function 公式提取的计算机制；以下平方和证明由本包独立展开，未声称论文直接写出同一形式。

令 Γ 为有限连通有向图，B 为 incidence matrix，d 为总和为零的 vertex charge。给每边 resistance r_e≥0，定义

    E_r(d) = min_{Bf=d} Σ_e r_e f_e².

零 resistance 可按论文收缩边，也可在半正定二次最小化中处理。取 N 个 resistance vectors r^(a)，令 r*=Σ_a r^(a)，选各自 minimizers f_a 和 f*。由于 f*−f_a 是 cycle，且最小值的一阶条件给 R_a f_a∈im Bᵀ，交叉项为零：

    E_(r*)(d) − Σ_a E_(r^(a))(d)
      = Σ_(a,e) r_e^(a) (f*_e−f_(a,e))² ≥ 0.       (★)

这对任意 N 成立。机器无需相信浮点优化：输出 rational f_a、potentials u_a，逐项核验 Bf_a=d、R_a f_a=Bᵀu_a，再验证 (★) 即可。大图、大量边与层使搜索和证书生成昂贵，但验证仍是精确线性/二次算术。

两条平行边时，若第 a 层长度为 (a_a,b_a)，s_a=a_a+b_a>0，S=Σs_a，则

    (Σa_a)(Σb_a)/S − Σ(a_a b_a/s_a)
      = (1/S) Σ_(a<b) (a_a b_b−a_b b_a)²/(s_a s_b).

证明是 weighted variance identity：写 x_a=a_a/s_a，将左边化为 Σs_a x_a²−(Σs_a x_a)²/S。N=20 时右边有190项。

但若所有 r^(a)=c_a r₀，且 charge d 不变，则所有最优 flow 相同，(★) 严格等于0。只把同一个一参数退化复制、重新缩放、串接二十层，不能得到任何正修正。BHDJ Th.4.2 也明确给出只有一个 boundary divisor 时 jump 为零。

这不排除真正多参数 degeneration、不同 graph/charge、实际高阶覆盖产生新现象；这些情形必须重新建立实际 pullback/pushforward 与标记的比较。改变 charge 后不能无证明照用固定 d 的有效性公式；mixed pairing 没有一般正号。

接入原目标所需的等式若写作

    ν(H)−Q = (positive height jump) + 其他已知非负项，

则左边的实际源对象与右边 admissible pairing 的 identification 是关键新数学，不是可新增的字段。本次没有建立该等式，所以不把图能量列为已选主路线。

## 6. 多层 comparison 的三个否决检验

### 6.1 相对体积在可逆同步运输下不变

同一局部向量空间的正有限体积对象 R 和 reference lattice L，定义

    v_L(R)=log μ(R)−log μ(L).

任意可逆线性 T 的 Jacobian 在分子分母同时出现，故 v_(TL)(TR)=v_L(R)。连续做二十次、二百次仍成立。相对 determinant 的 transitivity 给同一个结论，不能靠复杂复合把原来的差值消掉。

非可逆 lattice inclusion 会给 torsion quotient length，可计算且有方向；hull 可增体积。真正的路线必须从这些非可逆步骤或真实全局互反关系取得增量。对 arbitrary local rescalings 并无 product formula。

### 6.2 改 metric 消去 j² 后，换回原 normalization 必须补回

de Jong–Shokrieh Prop.9.1 在规定的 symmetric rigidification 条件下给

    −log||s(x)|| = ½[trop(z),trop(z)] − log||f(z)||.

二次项是两个度量读出之差。若源 Gaussian g_j=a^(j²)，直接用 a^(j²−1)O 作为新 reference 会使相对读出看似只有 log|a|；换回 O 时仍需加回 (j²−1)log|a|。只有证明该修正来自源允许的区域扩大，或来自真的全局 principal relation，才能用于 P6。

因此“加 canonical metric 后二次项消失”本身没有通过原 normalization 检验。这里未否定 canonical metric 在一个完整几何比较中的作用；否定的是省掉 reference correction 的具体做法。

### 6.3 只取 Tate representation 的 determinant 会丢掉 q

Tate curve 的标记 extension 在一个相容 basis 中有（Kummer 描述可核对 Brinon–Conrad, [CMI notes](https://math.stanford.edu/~conrad/papers/notes.pdf), §9.2 Example9.2.9, pp.142–143；下面 determinant 结论为直接线性代数）

    ρ_q(g) = [[χ_p(g), c_q(g)], [0,1]].

q 的 Kummer extension 信息在 c_q 中，而 detρ_q=χ_p 与 q 无关。因此只用 det H¹ 或其 rational period comparison，不能重建指定 q 的体积类。必须至少带 extension class、端点标记和 integral data；不能先遗忘这些再要求 determinant 自然性恢复它们。

该观察不否定带额外 theta line/metric/integral structure 的比较，只排除仅有裸 rational determinant 的路线。

### 6.4 参数斜率先于大规模枚举

在一个确实存在的参数族中，若 native q 的读出为 −b t+c，而某候选完整包络的上界为 −a t+C，a>b>0 且 C,c 独立于 t，则对足够大 t 必然不能覆盖 native q。证明只需比较两条直线。

这个测试适合检查“只增加与 q 赋值无关的有限误差”的候选方案。不能未经证明把源中随 q 变化的 ramification、log-shell、全局字段或量词当成常数，因此它不是完整 IUT 的反例。它是要求机器先保留 q 参数并提取斜率，而不是只算若干具体 q 的理由。

## 7. 若可行性通过，真正的二十层计算应是什么

这是候选计算规格，不是已部署程序或已证明路线。只为满足用户关于机器承担人类难以手算工作量的要求而描述；在源允许性、增量、原归一化三项未过关前，不展开全规模搜索。

| 层 | 具体对象/运算 | 必须交出的证据 |
|---|---|---|
| 1 | 固定完整 Θ-data、Θ-link、native q 的同一份配置 | 输入标记；不能替换 q 或另选弱 BPS realization |
| 2 | 实际 torsion/cover、局部字段及 embeddings | defining equations、选定根、兼容关系 |
| 3 | cyclotomic coefficient identifications | inertia/根单位尺度，不只抽象同构 |
| 4 | theta 的实际 Kummer class | cocycle 和选定 source monoid 中的 image |
| 5 | 同步 evaluation，得到整组 Gaussian profile | 与函数值的自然性、零标签 splitting |
| 6 | 原生 O_E 与 tensor/log lattices | integral basis、different/index correction |
| 7 | Galois action 和全部相关 invariant lattices | 矩阵与 lattice 数据，不以 GL 代替 Ism |
| 8 | finite-level congruence constraints | centralizer、integrality、transition equations |
| 9 | 从候选矩阵提升为真正源 isometry | 实际全塔规则或完整提升证明；有限层解不足 |
| 10 | 同步 Ind1、Ind2 和 global gluing | 完整分支 χ，非各地方任意拼接 |
| 11 | 每条源 log 路径的定义域 | 每一步 units 条件、路径方向 |
| 12 | 相应积分区域/对应的像 | analytic cell、Jacobian 或准确的包含/覆盖 |
| 13 | distinguished tensor factor 的 Gaussian action | action matrix 和实际 generator 标记 |
| 14 | 向目标 IQ container 运输整个分支 | action 与积分区域一起运输 |
| 15 | 从该分支提取实际输出点与 R₀ | 内见证，不能取控制外包络中的任意点 |
| 16 | 目标 holomorphic field decomposition | 实际 idempotents/field valuations |
| 17 | 计算有限见证的 λO hull | 每个极值分量的来源与赋值证书 |
| 18 | 读出相对 determinant，补齐 reference corrections | Smith/index/norm 计算，所有符号和次数 |
| 19 | 原权重的 global assembly、archimedean 校准 | finite-support 证明和严格误差界 |
| 20 | 直接比较 ν(K_W) 与独立构造的 Q | 精确符号证明或一侧 ε 证书；失败就不通过 |

其中 9、10–12、15 不是已经解决的工程细节。它们控制候选是否真的落在原输出族。第20层不能用具名“兼容性”假设代替，必须检查具体算出的数或符号公式。

可接的外部机器技术：Hales/CGH 用于已经证明可定义的分支；van Bommel–Holmes–Müller 用于已经识别为真实 intersection 的校准项；Osipov–Zhu 用于相对 determinant 的合成。BHDJ 正性只在识别了真实 height-jump 对象后接入。它们不是同一条已证二十层 theorem 的现成拼装件。

若计算产生 modular-unit norm relations，可用 Streng 的生成元与指数约束做准确的格子检验；仍要保留函数/line 的 rigidification 及全部 cusp orders。一个全局 principal divisor 的 degree 为0，故不能把其他 cusp 的补偿项省掉。负指数的函数恒等式也不直接给出区域的正向包含。

## 8. 本轮实际运行了什么

脚本：`fixed_q_comparison_certificates_20261024.py`。只使用 Python/SymPy 的精确有理算术；运行命令：

    python -X utf8 -B tmp/sheaf/n8/closure/fixed_q_comparison_certificates_20261024.py

退出状态0；结果：`C9-FIXED-Q-EXACT-CERTIFICATES-20261024.json`，SHA256 `2b07d8399786670dfbd9d21be044b0df24ced222216aacc73bea8393dcaa528f`。

1. 8 vertices、16 edges、20 layers 的图模型：320个平方项；逐层保存 rational flows/potentials；从磁盘重读证书后独立于优化过程核对 Kirchhoff、potential 和能量恒等式。所得 jump 严格正。
2. 相同比较的 homothetic 20-layer 对照：jump 严格为0。
3. 两平行边的20层有理 specialization：190项平方差公式精确成立。任意参数的一般证明见第5节，不把此 specialization 当作全称证明。
4. C₂/GL₂(F₃) 诊断：中心化子4个元素，全 GL48个；相应有限轨道并分别3点和9点，显示放松约束会改变 hull。
5. split Q₃⁴ 的三份显式 lattice 输入：提取4个分量见证，hull exponents=[2,1,1,0]；核算的是整个 product lattice 的体积，未用 singleton volume。

这些输入不是原源 Θ-data，算通不算 P6 进度证明。没有执行原 Ism 全塔枚举、动机积分引擎、完整20层流水线或大规模 Lean 搜索。没有凭样本推断原命题真伪。

## 9. 当前出口与下一项

本包自然语言闭合：有限 hull 见证压缩（有明确假设）、相容全塔矩阵给真实 Ism 的构造、任意多层能量平方和、成比例层零增量、可逆同步运输保持相对体积、裸 Tate determinant 遗忘 q。

未闭合：没有实际源分支见证证明 ν(K_W)≥Q；没有证明 ν(H)−Q 是 height jump；没有完整源关系的有效可定义性/全塔提升界；没有以真实 global principal relation 消去剩余尺度差。

下一项只取一个可否决的数学任务：在一个非平凡、完整合格的源 packet 中，保留 q 参数，明确构造一条实际允许分支及其 integral-region image；把该分支连同 R₀ 的 holomorphic hull 读出写成带所有 reference corrections 的公式，检查它是否提供 baseline 之外的非零、方向正确的增量。若只给固定常数误差，先作第6.4节斜率检验；若来源或增量失败，则退回该候选，不启动二十层大规模计算。这个局部结果即使成功仍需原全局量词的证明，不算整体闭合。

`statement_compiles=not_run`；`proof_body_checked=not_run`；`kernel_closed=not_run`；`comparator=not_run`；`project_build=not_run`；`independent_review=not_run (root self-review only)`；`target_accepted=false`。
