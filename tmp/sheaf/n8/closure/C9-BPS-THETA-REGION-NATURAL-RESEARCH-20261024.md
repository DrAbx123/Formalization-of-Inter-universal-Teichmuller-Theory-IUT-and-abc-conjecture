# 从指定 BPS 到 theta 作用及输出区域：自然语言研究

日期：2026-10-24，Asia/Shanghai。任务 ID：N8-C9-BPS-THETA-REGION。owner：当前 chat root；用户要求单人、自然语言研究，不写 Lean。

目标节点：n8-c9-output-region-source-route；SHEAF 阶段 1。实际消费者：C9 的完整 output-region 构造、n8-p6-source-route 的实际 source action，以及后续独立 q/算法读出比较。减少的缺口是“cyclotomic/Kummer/evaluation 到底构造什么、作用在哪、区域如何出现”，不是关闭 Corollary 3.12。

输入量词：固定原文合格初始 Θ-data 及其实际 Hodge-theater/log-theta 配置、指定输入 prime-strip（下文借用补充说明的 BPS 名称）；在该配置允许的实现和相容选择中工作。不是从任意抽象 Galois group/monoid 构造全部 IUT 输入。记 r 为整体 realization，避免与 cohomology direct limit 的开子群 J、procession 的 j、lattice 的 (n,m) 混淆。

精确读写：只新增本记录及同名 EVIDENCE JSON，向 root-owned 节点和 AUDIT_LEDGER、STATE、queue 追加记录；不改任何 Lean、他人路线或任务 owner。集成/构建不适用。来源版本与读取范围在 EVIDENCE JSON。复用已有 C9-P0-P1-SOURCE-TABLE 与前次失败路线诊断，不重做全仓 inventory。

**判断与交付边界。** 固定一个真实 realization 后，theta monoid → Gaussian monoid → 有理化 tensor packet 上的作用，这一段有明确的原文构造，可以展开为自然语言论证。最重要的桥是 IUT II Cor.3.5–3.6 与 IUT III Prop.3.4–3.5，不是任意 `Nonempty VerticalLogKummerCorrespondence`。但作用本身还不是一个唯一的输出区域；区域还消费源允许的积分结构/单位区域及对应的 log-Kummer 选择。完整允许区域族的下降、global comparison 与 q 的匹配仍须单独证明。

下文用 [源] 标明依赖原文定理的步骤，用 [展开] 标明本轮自行写出的初等证明，用 [未闭合] 标明没有由本轮得到的结论。这里没有重新证明完整 tempered anabelian reconstruction。

**一、先区分给定的数据和 realization 增加的数据。**

BPS 是说明性简称。LANA 自己明确说它是原 F^{⊩▶×μ}-prime-strip 的简化替代，不能把该简化的等价性当作已证。工作时仍以原文完整对象为准。

其 étale-unit 部分记录当地 Galois 群、单位模 torsion 的作用及 compact/Kummer structure；value 部分记录带 pilot 的度/值群数据。单有前者不包含整个 punctured Tate curve 的 tempered fundamental group，也不自带一个 theta function。

一次完整 r 将这些输入数据通过源允许的同构接到指定的 Hodge theater，并提供/选定使用其已有的 tempered 基本群 Π_v、相关覆盖、mono-theta environments、标签和 decomposition groups、Frobenioid 与 log-link 资料。不是额外把待证的 q/Θ 体积相等加入 r。

各标签共享的环境、基点/共轭资料、常数 monoid 和 F_l 的对称性必须相容。不能把每个 j、每个地方、每个 tensor factor 的值独立选取，再声称这些选择自动来自一次原文 realization。

对照：IUT II Prop.1.4–1.5、Cor.2.8、Cor.3.5；III Th.3.11(i)–(iii)、Remark 3.11.1(ii)–(v)。LANA 的 theta-value-action Step 1 与 eta Step 1 分别强调 étale-unit realization 和带 value 部分的 BPS realization；这两种表述不能被用来偷偷丢掉输入 pilot 的关联。

**二、在一次 holomorphic realization 中，实际 theta 值可以算出来。**

固定一个坏约化地方，记所需实际局部域为 k（按源是相应 K_v，而不是默认 F、Fmod 或 Q_l）。以下计算允许在源已给的有限扩张/覆盖中进行。令 q 为该 realization 的 Tate 参数，0<|q|<1，并采用源所需的根与 i=√(-1)。

在双覆盖坐标 U 中，经典 theta 写成

    θ(U) = Σ_{n∈Z} (-1)^n q^{n(n+1)/2} U^{2n+1}.

令 P_j 对应 U_j=i q^{j/2}。对不落在 divisor 上的这些点，以 P_0 归一化。直接计算得到

    θ(U_j)/θ(U_0) = q^{-j²/2}.

[展开] 代入后 (-1)^n i^{2n+1}=i，q 的指数为

    (n(n+1)+(2n+1)j)/2
      = ((n+j)(n+j+1)-j²)/2.

将求和指标换成 n+j，提取 q^{-j²/2} 即得。双向级数在这些点收敛，因为指数的二次项使两端项趋于零；非零分母由点避开 theta divisor 保证。EtTh Prop.1.4(i)–(ii) 给出 divisor 和相同的变换公式。

IUT 使用的是规定归一化后的倒数之 ℓ 次根。若 a^{2ℓ}=q，则其特殊值写成

    g_{r,v,j} = ζ_{r,v,j} a^{j²},    j=1,…,(ℓ−1)/2,

其中 ζ 表示源规定的有限根单位歧义；确切 μ_ℓ/μ_{2ℓ}、覆盖、符号和反演选择保留在 r 中，不能以这条简写删除。此处 q 是 realization r 内的 q，不能无证明地等同于 Θ-link 另一侧输入 q 的同一实数坐标。

**三、Kummer evaluation 的内容可用 cocycle 直接说明。**

设 f 是相关覆盖上、在所选 evaluation 点非零的 theta 单位/函数；在可能的有限覆盖上选相容 N 次根 f^{1/N}。其 Kummer cocycle 为

    γ ↦ γ(f^{1/N})/f^{1/N} ∈ μ_N.

[展开] 对点 P 的 decomposition group D_P 作 restriction。该群保持相应几何点，函数根在该点的值就是 f(P) 的 N 次根。于是受限 cocycle 正是 f(P) 的 Kummer cocycle。改变根或 lift 改变代表，而不改变对应 cohomology class。对 N 的兼容系统和允许有限覆盖传递，得到相应 inverse/direct-limit 版本。

因此有真实的交换关系

    restriction_P(Kummer(f)) = Kummer(f(P)).

它不是“两个任意箭头可以填一个 commutativity 字段”。EtTh Prop.1.4(iii) 明确把 étale theta 的 restriction 与 classical theta values 识别；IUT II Cor.2.8 给出适合其 mono-theta environments、标签及共轭选择的版本。

也不能把任意 cohomology class 送入一个自由 `Kummer inverse`：必须证明它落在指定 monoid 的 Kummer image，并使用源提供的同构/带 torsion 的表示。固定真实 r 时，上面的自然性与实际 f(P) 给出这项 image-membership 的见证；源重建版本与它的识别消费 EtTh/IUT II 的定理。

**四、cyclotomic rigidity 固定的是上述等式的系数识别。**

这里有不同来源的 cyclotomes：函数/monoid 的根单位 Tate module，tempered 群的内部 subquotient，以及 evaluation 点当地 monoid 的 cyclotome。仅知道它们抽象同构，不能说明 Kummer 类采用同一指数尺度。

[源] EtTh Cor.2.19(i) 从 mono-theta environment 构造两个指定 splitting，由其差得到内部到外部的 cyclotomic isomorphism；其在实际几何 realization 中对应 algebraic section 和 theta section。IUT II Prop.1.3(iii) 证明 mono-theta 与 base-field/Galois 构造的 cyclotomic identifications 相容；Prop.1.5(iii)–(iv) 给出 projective system 及 Frobenioid Kummer 的兼容版本。

局部检查可这样理解：函数在 cusp 附近形如 t^d u，Kummer 类限制到 inertia 时记录 d；任意更换 cyclotome 坐标会更改这一识别。源的覆盖、ℓ 次根、倒数及上述 splitting 固定所需的尺度。这个局部解释不替代整个 cyclotomic rigidity 定理。

因此应当先按源识别系数，再作 restriction 并和当地 Kummer map 比较。不要依次随便挑三个同构，再要求它们满足预想数值式。

**五、evaluation 得到的是整组 Gaussian monoid；零标签负责分离常数。**

令 ξ_{r,v}=(g_{r,v,j})_j 为一次相容选择的 value-profile。示意地，Gaussian monoid 为

    Γ_{r,v} = Δ(U_v) · ξ_{r,v}^{N},

其中 U_v 是相关常数单位 monoid，Δ 是由 symmetrizing isomorphisms 确定的对角嵌入；根扩张版本另有有理非负幂及 torsion 条件。

[展开] 同一个函数乘以常数单位 u，在所有 evaluation 点都乘以同一个 u。经相容的当地识别，这正是对角单位部分，不是每个 j 独立的任意单位。以零标签 evaluation 的归一化分离出常数部分，留下 Gaussian 生成元及源规定的 torsion 歧义。

[源] IUT II Cor.3.5(i) 给出 symmetrizing/conjugate synchronization；(ii) 定义 value-profile 与 Gaussian monoids，并给出 theta → Gaussian restriction isomorphisms；(iii) 给出零标签 splitting。Cor.3.6 把这些与实际 Frobenioid-theoretic theta/Gaussian monoids 连接。不能只保留 θ 的点列表，删掉常数部分、共同指数、共轭同步或 splitting。

特别是，Γ 中有所有自然数幂，并不意味着“每个幂都是同一个 pilot 的允许输出”。Θ-pilot 使用源指定的生成元（up to torsion）；幂参数 k、lattice 的 n/m 和分量标签 j 是不同参数。

**六、Gaussian 生成元如何变成作用。**

IUT III Def.1.1 的 log-link 为 perfected units 所形成的加性对象赋予相应重建的 field structure。III Prop.3.4 将上述 Gaussian 数据沿实际 log-link 与 procession 组装成 LGP-monoids。原文明确的作用空间是 tensor packet 的 Q-span I_Q；不要额外要求全部操作保持固定 I。

在一个 holomorphic realization 的坐标中，这个作用就是乘法。对第 j 个 packet 和一个地方 tuple (v_0,…,v_j)，在有限维层可以写

    E_{r,j,tuple} = k_{r,v_0} ⊗_{Q_p} ··· ⊗_{Q_p} k_{r,v_j},
    A_{r,j,tuple} = id ⊗ ··· ⊗ multiplication(g_{r,v_j,j}).

也就是把 g 放进指定的 j 因子，其余因子放 1；原文 III Prop.3.1(ii)、3.4(ii) 正是这样的嵌入。不要在每个 packet 的所有因子再分别乘上全部 g_t，这会改变指数和体积权重。

对非负整数 k 使用 A^k，满足 A^0=id 与 A^{k+h}=A^k A^h。[展开] 这直接来自乘法结合律和 g^{k+h}=g^k g^h，因而确实构造了一个 monoid action。根单位/共轭变化仍按源处理。

转到 mono-analytic 容器时，保留该作用及其允许坐标表示，不假定容器已经带有一个跨 Θ-link 共享的环乘法。此处也不是把非单位 q 送进 p-adic log、再以 log(q) 作为乘法标量。q 的赋值信息始终保留在 Gaussian/LGP 乘法作用中。

[源] III Prop.3.5(i) 给出各 row 的 Frobenioid 版本和 vertically coric 版本的 Kummer isomorphisms；(ii)(c) 处理 splitting monoid 的作用；Th.3.11(i)(b) 在 mono-analytic I_Q 上保留该作用。不能从“g 和 I 都嵌入同一集合”推导 action；需要这里的乘法结构及实际运输。

**七、从作用到区域，必须保留积分结构 S。**

最基本的一个当地实例是

    A(x)=g x,      R=A(O_k)=g O_k.

g≠0 时，这就是非空紧开区域，并有正有限 Haar 质量。它包含无穷多个点；singleton {g} 不承担这个角色。[展开] 乘 g 是当地加性空间的拓扑自同构，故保持紧开性、可测性和正有限性。更一般的合格 S 同样产生 A(S)。

对 packet，先在实际 holomorphic structure 中取得规定 integral structure（需要时是 tensor algebra 各 field summand 的 integral closure，并非一概等于裸 tensor of integer rings），得到原生 pilot 区域；然后经源允许的 Kummer/mono-analytic 表示和 log-correspondence 记录它的可能区域。S 可以是具体 integral region，也可以是源要求的单位区域的像/相容 cover。不能无证明把每种原始输出都写成同一个 g·I。

于是，在固定完整选择后，可以概括为

    R_{r,S}=A_r(S) ⊂ V_Q(B).

这条式子说明输出层次，不定义任意 S 都合法。BPS+r 先给出作用；若“realization”一词尚未包含积分结构及 log-Kummer 分支，单凭它还没有唯一 R。LANA 的 eta_S 恰好也显式依赖 S。

完整源允许选择至少分别记录：

1. r 中的 Hodge/prime-strip 识别、mono-theta、同一 value-profile 及其同步；
2. 原文的 procession automorphisms 与逐因子的 Ind2 isometries；
3. 实际单位与 log-link 迭代所产生的表示/对应，以及 III Prop.3.5(ii)(a)(b) 的包含或覆盖；
4. 指定 integral reference 和区域在哪个 holomorphic frame 中解释；
5. 若原始像只是 pre-region，III Remark 3.9.7 所需的合格外区域 inverse system。

Ind3 不是第三个任意群作用。它来自沿 log sequence 比较 integral/unit regions 的 upper semi-compatibility。在非阿基米德地方是指定像的包含；无穷地方还涉及指定球内集合对单位区域的覆盖。必须以这些实际关系生成允许族。

原始区域、所有可能区域之并、holomorphic hull，以及 Stp4 允许扩大的 hull 内区域，保持不同层次。不能从“某上界区域容纳所有输出”反推其中每个区域本来就是原始输出。

**八、全局组装与体积：已经能得到一个有用的自然语言校准。**

按实际 rational place、procession j 和 tuple 组装当地数据；good places 的生成元部分是平凡的，仍保留相应 integral regions；archimedean 部分使用源规定的 radial/ball 数据，不能删除。Outside finitely many rational places 的零局部 log-volume 来自实际参考结构和源有限支撑；III Remark 3.9.7(i) 指出适当未分歧地方有 I=O 且读出为零。

III Remark 3.1.1 与 Prop.3.9 的读出是 prescribed weighted sums of component log-volumes，加上 procession 平均和全球求和；不能把整个大容器上任意集合的一种普通 Haar log 当作全部定义。

[展开：一个固定 finite local block 的计算。] 令 E=⊗_{i=0}^j k_i，d_i=[k_i:Q_p]，D=∏d_i，A 只在 j 因子乘 g。选取其余 tensor factors 的 Q_p 基，则 E 作为 Q_p 空间是 D/d_j 个 k_j 的直和，A 在每份上都是 multiplication(g)。所以

    det_{Q_p}(A) = Norm_{k_j/Q_p}(g)^{D/d_j}.

对正有限 Haar 质量的 S，令 ν 为本 block 的、除以 D 的相对 log-volume，则

    ν(A S) − ν(S) = log|Norm(g)|_p / d_j.

根单位 ζ 的 norm 绝对值为 1，故在这个固定 frame 的体积计算中没有贡献；这不表示任意 S 在乘 ζ 后逐点不变，也不能替代跨 log-link 的 torsion 处理。

代入 g=ζ a^{j²}，该差为

    j² · log|Norm(a)|_p / d_j.

这是 C4 分量输出数据与 C6 类型 normalized volume 之间一个真正有内容的桥：需要实际 A 和实际 S，而不是 label 的自由 thetaImage。完整 global formula 还必须使用源 selected-place、tuple、procession 权重，不能直接把本 block 的 D 归一化当作全局公式。

**九、何处已经具体，何处仍是核心责任。**

本轮给出了在原文重建定理作为输入时的一条具体链：

    指定 BPS 与合法 r
      → 实际 theta/Frobenioid monoid
      → cyclotomic identifications 下的 Kummer classes
      → decomposition-group restriction
      → 同步的 Gaussian value-profile/monoid
      → log-link 与 procession 上的 LGP action A_r
      → 源允许积分区域 S 的像 R_{r,S}
      → framed weighted log-volume.

其中 evaluation 自然性、特殊值 j²、作用律、区域正有限性、有限 tensor block 的 determinant-volume 计算都有本轮展开的自然语言证明。Anabelian reconstruction、cyclotomic rigidity、完整同步与 log-Kummer 相容性明确依赖列出的源定理，不因把它们画成箭头就视为重新证明。

允许 choices 改变时，不应期待 A_r 变成一条与所有 r 无关的裸单值函数。目标是源规定的带相容关系的表示族及其控制；III Remark 3.11.1(iv) 也明确不把 APT 当成由一个跨 Θ-link set function 搬运区域。

III Remark 3.10.2 提供了可逐箭头追踪的原始方形：两行都是 env → gau → LGP → lgp，竖箭头是 Kummer。它的局部 evaluation/Kummer 部分正由上述交换关系支撑。接下来必须保持这整个 prime-strip 方形（包括 value/pilot/gluing 和 global Frobenioid），不能只保存局部 point 的交换。

[未闭合] 从这条链还不能得到：存在源允许 S，使算法输出与另一侧 independently constructed q-pilot 的规定读出相同；或该比较自动通过整体 Ind/hull/degree 操作。LANA 的 eta^q=eta^anab_S 正是在表述这项比较。Mochizuki April 2026 §4 也把 descent、hull+det、SHE 分成不同步骤；没有把最后比较降为普通 Kummer 自然性。

一个反查：在同一简单 local frame 中，ℓ=5 的 profile 是 (a,a^4)，若两份 reference region 都为 O，平均 log-volume 为 (1+4)/2 倍 a 的当地 log-volume。这仅是单一 frame 的校准模型，不是全 IUT 合格输入/全局反例，却足以说明“已经算出 Gaussian action”不会自动给出“与 q 的读出相等”。若任意调大 S 以抵消差值，恰好会把待证比较塞进 allowed-S 的定义。

**十、后续研究的准确落点。**

建议保留本轮链，停止抽象 correspondence 的 inhabitant 和单个 shell 点值路线。下一包自然语言研究只追一个对象：固定输入 q-BPS，在 III Remark 3.10.2 的完整 square 中逐步记录哪份 integral region 被实际带到哪里，并将 III Prop.3.5 的 log-iterate/upper-semi 关系作用在这些区域上，列出不依赖待证 q equality 的允许 S 范围。对每条箭头同步记录其 value/pilot 关联；随后才检验是否足以得到 q realization 或原文允许的 hull-approximant。

这一步不能以“任意 S⊂I”替代，也不要求先重建全库。已有明确的 local construction 和体积校准可以独立复用。

**来源和验收。**

- EtTh，December 2008：Prop.1.4(i)–(iii)、Cor.2.19(i)，实际读取相应正文；https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Etale%20Theta%20Function%20and%20its%20Frobenioid-theoretic%20Manifestations.pdf 。
- IUT II，December 2020：Prop.1.3–1.5、Cor.2.8、Prop.3.1/3.3/3.4、Cor.3.5–3.6；https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf 。
- IUT III，May 2020：Def.1.1、Prop.3.1/3.4/3.5/3.9、Def.3.8、Remark 3.9.5/3.9.7/3.10.2/3.11.1/3.11.2、Th.3.11 的相关正文；https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf 。
- IUT IV：Theorem 1.10 proof Steps (iv)–(vii)（PDF pp.26–30）用于反查 action 的 distinguished factor、weights 及 region upper-bound 层次；https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf 。
- On the Formalization of IUT，April 2026，§4 pp.9–11；https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf 。
- LANA report，commit 293bdd89463473ae13d40834d70fb4b7ba81da1f；BPS、four log-shells、volume containers、theta-value-action Steps 1–8、eta algorithm 与 main goal。GitHub 工具再次核对 1853–2027 行，blob SHA 35a2507a5bc5bfc1835067dbdb6776e4bc4a3152；本地读了所列其他节。https://github.com/katobungen/LANA_report_202607/blob/293bdd89463473ae13d40834d70fb4b7ba81da1f/LANA_report_202607.tex 。此说明的简化不直接替代原文；尤其 action on I 改按原文表述为 action on I_Q。

状态：定向自然语言构造研究已交付；完整源对象和 q 比较仍开放。没有写 Lean，没有运行编译、proof-body check、kernel/axiom check、comparator、Project build 或独立审查。target_accepted=false。Mathlib/代码复用调查沿用前次记录的 Haar/index/tensor scaling 供体；本轮没有新增 Lean lemma 搜索或声称供体已接入。
