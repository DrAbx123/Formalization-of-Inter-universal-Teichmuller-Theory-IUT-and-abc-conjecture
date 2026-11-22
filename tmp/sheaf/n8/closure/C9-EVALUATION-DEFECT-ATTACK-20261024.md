# C9：实际 evaluation、相对 determinant 与扩大余量

任务 ID：C9-EVALUATION-DEFECT-ATTACK-20261024。owner：当前 chat root；单线程、无 subagent、自然语言研究，不写 Lean。用户要求继续攻击。

节点/消费者：n8-c9-output-region-source-route，SHEAF阶段1；原P6固定native-q的输出覆盖。原量词：任意合格完整初始Θ-data及实际log-theta-lattice，固定native q、gluing和原normalization；不能把新globalization条件加到输入。

本包目标：沿III Remark3.10.2/Prop3.7(v)及II Cor4.6/4.8/4.10展开实际evaluation后的fractional ideals；计算能够源实现的局部乘子除子、determinant与reference修正、hull/Ind3有效余量。交付真实约束/证明或精确失败证据；不以重写h−Q=S−κ为进展。

冻结复用：C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024.md，SHA256 ec0bbb35abb1d28128a958ecbdaad27d600dfe81e1738af70ec28c0bb439e704；及其EVIDENCE。局部—全局下降判据已自然语言自审；完整IUT接入未闭合。

statement_dependencies：真实源evaluation、labelled local field/tensor packet、局部fractional ideals、weighted relative determinant、native-q与完整输出族hull。
proof_dependencies：II实际Gaussian evaluation；III Prop3.4/3.5的log-Kummer与上半相容；III Ob3/4的determinant/reference；实际源扩大或global principal关系（本包待研究）。

精确写文件：本记录、同目录C9-EVALUATION-DEFECT-EVIDENCE-20261024.json及必要本包计算文件；root-owned DAG节点追加字段；只追加AUDIT_LEDGER、STATE、queue。其他owner源码不改。集成root；Lean构建不适用。

验收：分清同一holomorphic frame内的真实计算与跨Θ回接；保持原输出族强度。statement_compiles/proof_body_checked/kernel_closed/comparator/独立审查未运行；target_accepted=false。

状态：本包自然语言证明与精确局部计算完成。证明了实际 evaluation 的数值亏损、非分歧块无增益、完整 lattice 自同构外轨道的精确消元，以及任意因子数的二次分歧 tensor 模型。原 P6 的全局输出覆盖仍开放；没有完整合格 IUT 输入的证明或反例。

## 1. 本包实际改变了什么

此前已知真实 Ind2 在固定最终线性块上不增大 hull；也已知不能靠换 reference 消掉 j²。此次不是重述这两点，而是：

1. 把 II 的实际 evaluation 接到 III 的 local fractional ideals、原权重和 Ob3/4 相对 determinant，算出未扩大前的精确系数 ell(ell+1)/12。与 IV 证明中的 (ell+1)/24 系数相互核对。
2. 对奇素数非分歧、整数赋值的块，连 IV 使用的全部 lattice 自同构外群和 log-shell 上容器也不能扩大 Gaussian 理想。
3. 对任意 full Z_p-lattice L，消去“遍历所有保持 L 的线性自同构”的量词。给定实际输入 lattice A，外轨道本身恰为 p^t L，其中 t 是 A 在 L 中的最小坐标赋值。这是上界计算工具，绝不把外群当真实 Ind2。
4. 对 K=Q_p(sqrt(p))、任意 r 个 tensor 因子，精确计算 R、积分闭包 O_E、log lattice L、log-shell I、实际 Gaussian 乘法、外轨道和最终 hull。r=20 给出维数 1,048,576 的局部例子；先 hull 后继续作用会虚增 9 log p。
5. 对这种二次局部配置的完整 procession 外容器，给出严格负的当地余量实例。即使把整套 IV 局部上容器都赠给它，该地仍不足以单独保住 native q 数值。其意义是排除当地补偿路线，不能据此否定全球目标。

“完整外群/完整当地上容器”与“完整初始 Θ-data/全局实际输出族”始终分开。下面不声称构造了一份完整全局 Θ-data。

## 2. 实际源链与 normalization

固定一份源允许的 realization 和其中一个 holomorphic frame。II Remark2.5.1(i)、Cor2.5 给出：在 cyclotomic rigidity/Kummer identification 下，指定 theta evaluation 值属于

    g_(v,j) ∈ μ_(2ell) · qhat_v^(j²),       qhat_v^(2ell)=q_Tate,v.

沿 II Cor4.6/4.8/4.10、III Remark3.10.2，evaluation 进入 Gaussian/LGP/lgp 对象；III Prop3.4、Prop3.5 给出指定 tensor factor 上的乘法作用，Prop3.7(v) 给出由这些局部 monoid 生成元产生的 fractional ideals。这一局部原生理想是 g_(v,j) O_E；并非 singleton 的 Haar 体积。

III Prop3.5(ii)(c)、Thm3.11(ii) 把 nonunit splitting monoid action 与进入 log 的 unit-domain 资料分开。不能把 qhat 的非单位乘法擅自改成普通 log(qhat)，也不能把任意普通 log 复合认作源分支。

设 E=⊗_(i=1)^r K_i，D=[E:Q_p]，指定 factor 为 K_j、d_j=[K_j:Q_p]。真实乘法算子满足

    det_Qp(m_g)=Norm_(K_j/Q_p)(g)^(D/d_j).

这是上一包已证的 determinant 公式；这里将它接入真实 g。相对 reference 为 O_E，取 packet normalization：

    ν(O_E)=0,
    ν(g O_E)=D^(-1) log|det(m_g)|_p
            =-ord_p(g) log p
            =-j² ord_p(qhat_v) log p.                         (2.1)

III Remark3.1.1(ii) 的全局局部域权重会抵消人为引入的 [K_v:(Fmod)_v]。对 tensor tuples 加权求和时，指定 factor 的边缘分布正是相应 Fmod 地方次数分布：其他 factor 的权重求和为 1。因此 tensor 维数没有把 j² 消掉。不同 tuple 有不同 q 赋值时须按原权重求和，不能换成独立的最大值。

III Remark3.9.5(vii)(Ob3/4) 的参考修正是 tensor inverse det(O_E)，再用共同正整数 M 清除有理权重/stack twists。对 g O_E 与 O_E 的相对 determinant，修正恰好保留 (2.1)；把两边同时取 M 次方再除以 M 亦不改变它。这个运算不能改成以 g/qhat 倍 O_E 为 reference。

令 b=(ell-1)/2。procession average 给

    A_ell=(1/b) Σ_(j=1)^b j² = ell(ell+1)/12.

若 Q=-|log(q)| 是由同一 initial data 的 native q 参数计算出的数值，则未扩大 Gaussian ideals 的相应全局 numerical readout 是

    theta_seed=A_ell Q,
    Q-theta_seed=(A_ell-1)|Q|.                               (2.2)

这里比较的是明确的数值：不是声称已构造从 target-column 的 q-pilot 到这些 seed ideals 的 calibrated arrow。那条回接正是 P6 的核心。III/IV 的 native-q formula 为 |Q|=log(q_raw)/(2ell)，所以 (2.2) 的 raw-q 系数是

    A_ell/(2ell)=(ell+1)/24.

这与 IV Theorem1.10 证明(v)–(viii) 实际出现的系数吻合。没有借用该定理最后调用 III Cor3.12 的步骤来证明 P6。

原文位置：II pp71–72、138–139、151–153、159–160；III pp94–95、102–106、110–117、131–134、152；IV pp27–31。

## 3. 非分歧块：全部线性外群也无补偿

设 p 奇，全部 K_i/Q_p 非分歧。记 R=⊗Z_p O_(K_i)，E=R⊗Q_p。

**命题。** 若 g 的所有 field components 都有相同整数赋值 m，则

    O_E=R,      L:=⊗ log(O_(K_i)^×)=p^r R,
    I:=⊗ p^(-1)log(O_(K_i)^×)=R,
    φ(g R)=p^m R

对每个 φ∈Aut_(Z_p)(L) 成立。

**证明。** 非分歧整数环有限 étale，tensor 后仍有限 étale，故 R 已经 integrally closed。对 p 奇的非分歧 K，Teichmuller 分解和 log/exp 在 1+pO 与 pO 间的互逆给 log(O^×)=pO。由此 L=p^r R、I=R。φ 为 Q_p-linear 且保持 p^r R，故保持 R，也保持每个 p^m R。相同整数赋值条件给 gR=p^m R。证毕。

这与 AbsTopIII Def5.4(iii)、III Prop1.2 及 IV Prop1.2(iv) 一致；不是对原文的修正。对于实际 g=qhat^(j²) 且 ord_p(qhat)=N∈Z，有 m=Nj²。

更重要的是，IV 证明(v) 在此情形的精确容器本身就化为 p^m R：d_I=0、a_I=r、b_I=-r，λ=m，所以 p^floor(λ-d_I-a_I)L=p^(m-r)p^rR。log-shell 上包含并不会在这里额外赠出一个 p^(-1)。一般粗上界中的“+log p”在这里可删除。

范围：固定 tensor tuple 上此结论完全成立。若要把它用到一个 prime p 的整个源输出并集，必须同时跟踪 Ind1 可移动到的 tuples；例如所有相关地方都同样非分歧且 qhat 赋值相同的 uniform 配置可直接使用。不能把某个好 tuple 的结论推广到不同 q 赋值/不同 ramification 的全部 tuples。

## 4. 全部 lattice 自同构的外轨道：一个可精确消元的量词

令 V 为有限维 Q_p 空间，L、A 为 full Z_p-lattices，G=Aut_(Z_p)(L)，并定义

    t(A;L)=max{a∈Z : A⊂p^a L}.

若 B_L、B_A 为基矩阵，则

    t(A;L)=min_(u,v : C_uv≠0) ord_p(C_uv),   C=B_L^(-1)B_A.   (4.1)

**定理。**

    ⋃_(φ∈G) φ(A)=p^t(A;L) L.                               (4.2)

**证明。** 包含于右侧由 A⊂p^tL 和 G 保持 L 得出。取 a∈A，使 p^(-t)a 为 L 的 primitive vector。每个非零 y∈p^tL 可写成 p^(t+k)v，k≥0，v primitive。primitive vectors 可以补成 Z_p-bases，故存在 φ∈G 把 p^(-t)a 送到 v。由于 p^k a∈A，得到 y=φ(p^k a)。0 也属于每个 φ(A)，故反包含成立。

若 V=E 为已固定 field decomposition 的 finite étale algebra，则

    Hull_E(⋃_φ φ(A))=p^t(A;L) Hull_E(L).                    (4.3)

这把一个无限群量词变成准确基矩阵中的一个最小赋值。一般任意不可计算 p-adic oracle 不会自动给出这个最小值；这里要求实际局部域/矩阵有可核验的精确表示或足够的非零精度证书。

若源实际群 Γ⊂G，仅得

    Hull_E(⋃_(φ∈Γ)φ(A)) ⊂ p^t Hull_E(L).

因此 (4.3) 给安全外界与“不能逃出坏容器”的判据，不能把 full-GL 的取等向量当作源允许下界见证。此前真实 Ind2 的标量分类继续有效。

### 4.1 任意多层的有限线性外过程

对于固定可逆线性箭头 T_k 和每层独立允许的全部 G_k=Aut(L_k)，若 P_0=p^e0 L_0，则

    P_k=⋃_(φ∈G_k) φ(T_k P_(k-1))=p^ek L_k,
    e_k=e_(k-1)+min ord_p(B_(L_k)^(-1) T_k B_(L_(k-1))).    (4.4)

证明是逐层应用 (4.2)。层数任意，且每层保留真实 lattice；不提前做 holomorphic hull。对于含源相容条件的原过程，允许所有独立 G_k 是放宽，故仍给外界，但未必等于原输出。对非线性 log、变动定义域、不同标记的 identification，不得套用 (4.4)。

因此“多层”不是问题；问题是每条实际箭头能否进入这个经过证明的线性外计算。外界太小即可剪枝，外界足够大仍不产生源内见证。

## 5. 任意 r：二次分歧 tensor、积分闭包与 log-shell 的准确计算

取 p≥5，K=Q_p(π)，π²=p，O=Z_p[π]。令

    R=O tensor_(Z_p) ... tensor_(Z_p) O   (r factors),
    E=K tensor_(Q_p) ... tensor_(Q_p) K,
    O_E=O^(2^(r-1)).

此为真实局部域及其 tensor algebra；并非任意选择的自由 volume 字段。令 X_i 是第 i 个 factor 的 π，β=∏X_i。由于 log(O^×)=πO，

    L=⊗log(O^×)=βR,
    I=⊗(p^(-1)log(O^×))=p^(-r)L.                           (5.1)

### 5.1 积分闭包的指数与 conductor

把第一个 K 当 coefficient field。其余 r-1 个 X_i 可分别取 ε_iπ，ε_i∈{±1}。R 的 O-basis 为 X_S，S⊂{2,…,r}。evaluation matrix 为

    H · diag(π^|S|),

其中 H_(ε,S)=∏_(i∈S)ε_i 是 Walsh-Hadamard matrix，H H^t=2^(r-1)Id。因 p 奇，H 在 O 上可逆。因此 R⊂O_E 的 O-Smith 指数是

    s，重数 binomial(r-1,s)，0≤s≤r-1.

于是最大的 conductor ideal 为 π^(r-1)O_E⊂R；π^(r-2)O_E 不包含于 R（r=1 时同样按指数解释）。各 projection R→O 都满射，故 Hull_E(R)=O_E。β 在每个 component 是 π^r 乘一个符号，因此

    Hull_E(L)=π^r O_E,
    π^(2r-1)O_E ⊂ L,
    π^(2r-2)O_E ⊄ L,
    Hull_E(I)=π^(-r)O_E.                                   (5.2)

用原 packet normalization ν(O_E)=0、ν(pO_E)=-log p，可进一步算出

    ν(R)=-(r-1)/4 ·log p,
    ν(L)=-(3r-1)/4 ·log p,
    ν(I)=(r+1)/4 ·log p,
    ν(Hull_E(I))=r/2 ·log p.                               (5.3)

这精确区分 tensor lattice 自身的体积与其 holomorphic hull 的体积；二者不是同一个东西。

### 5.2 实际 Gaussian 作用与完整外轨道

取指定 factor 上 g=uπ^m，u∈O^×；Gaussian 情形 m=Nj²，qhat=u_0π^N。因 R、L、I 是 R-modules，u 在该 factor 的乘法保持它们。

对原生 fractional ideal A_0=gO_E，由 (5.2)：

    t(A_0;L)=floor((m-2r+1)/2),
    Hull_E(G A_0)=π^[2 floor((m-2r+1)/2)+r] O_E.            (5.4)

另一方面，要控制 log-unit images，源的上半相容首先给出 I 容器。实际乘法作用于这个容器得到 A_1=gI。这里的 A_1 是用于控制源输出的容器；没有宣称源实际所有分支已经把它填满。

写 m=2a+ε，ε∈{0,1}。在 R 的 monomial Z_p-basis 中，X_1^m=p^aX_1^ε。X_1R⊂R 但 X_1R⊄pR，因此

    t(A_1;L)=floor(m/2)-r,
    ⋃_(φ∈G) φ(A_1)=p^[floor(m/2)-r]L,
    Hull_E(G A_1)=π^[2floor(m/2)-r]O_E.                    (5.5)

此外 Hull_E(A_1)=π^(m-r)O_E。于是 full-GL 外群在这个容器上的额外 hull 增量最多为 (m mod 2)/2 ·log p；其主要扩大 r/2 ·log p 已来自 log-shell 相对于 O_E 的大小。

IV Prop1.2/1.4、Theorem1.10 证明(v) 在此模型有 d_I=a_I=r/2、b_I=-r/2、λ=m/2，所用精确容器

    p^floor(λ-d_I-a_I)L = p^[floor(m/2)-r]L

正好是 (5.5)。这里只消费证明(v)前半的局部 lattice inclusion 与源 unit-domain 上包含；未消费其后使用(R4)的全球 ramification 估计，更未消费最后调用 Cor3.12 的目标不等式。这里同时核对了 Ind3 上容器的计入位置，没有把原文最后的粗正误差项当成实际可实现输出。

### 5.3 不能提前 hull：二十因子可核验证书

若先把 A_1 换成 Hull_E(A_1)=π^(m-r)O_E，再继续允许 G，得到

    Hull_E(G Hull_E(A_1))
      =π^[2floor((m-3r+1)/2)+r]O_E,                        (5.6)

一般严格大于 (5.5)。这是具体的运算次序错误；并非否定原文在规定最后步骤取 hull。

取 p=821、ell=41、r=20、j=19、N=1。821 为素数，821≡1 mod164，故 μ_(4ell)⊂Q_821；可取局部 Tate parameter q_Tate=821^41、qhat=π。该局部域/参数不是一份已验证的完整 global initial Θ-data；实际全球化问题未被省略。所有依赖赋值的公式对同赋值的 unit 倍参数同样成立。

此时 m=361，dim_Qp E=2^20=1,048,576，有 2^19=524,288 个 K-components。

| 对象 | 每个 K-component 的 π 指数 | packet log-volume / log p |
|---|---:|---:|
| 原生 Gaussian ideal gO_E | 361 | -361/2 |
| 对 source unit 容器 gI 直接取 hull | 341 | -341/2 |
| 保留 gI，再做全部 G，最后 hull | 340 | -170 |
| 提前把 gI 换成 hull，再做 G | 322 | -161 |

提前 hull 给出的较大集合仍是合法的较松上界；错误在于把它当成原过程的精确输出，或把多出的 9 log p 当成源内补偿。正确取值来自任意 r 的上述证明；没有实际枚举百万维的全部矩阵，也不以小样本代替任意 r 证明。

### 5.4 完整当地 procession 外界仍可严格低于 native q

若 p 上所有相关源 tuples 都属于这个 uniform quadratic 配置，且 qhat 的 π-valuation 同为 N，则对 j=1,…,b、r=j+1，(5.5) 给当地源输出的上界

    U_p = (1/(2b)) Σ_j[-Nj²+(j+1)+(Nj² mod2)] log p.        (5.7)

native q 的当地 contribution 是 Q_p=-(N/2)log p。对 ell=41、N=1，

    U_p=-(263/4)log p,
    Q_p=-(1/2)log p,
    Q_p-U_p=(261/4)log p > 0.                              (5.8)

实际源群可能小于 G，实际 unit images 可能小于 I，这只会使该外界更强；不能使 (5.8) 变成下界见证。当地配置必须在一份完整源输入中确实出现，才能把 (5.7) 带入那个输入的全球计算。本包未构造这样的完整输入，所以 (5.8) 不是 IUT 反例。

明确含义：试图只靠这个地方的 Ind1/2/3 容器扩大补足 native q，已被准确上界排除。若原全局结论在这种配置下成立，其他地方及完整 gluing 必须有真正的全局机制，不能由这里的“还有很多 automorphisms”补出。

## 6. 反证路线的具体推进与仍未证明的地方

令全局 h=Σ_p h_p，固定 native Q=Σ_p Q_p，保留真实地方次数权重；此处 p 泛指全部相关有限处和无穷处。只需讨论 h 有限且 h<Q 的反证分支，h=+∞ 时数值覆盖不等式本身成立。之前 maximal-bad-container 规约要求构造一个真实源输出家族，使某个坏容器无法同时容纳它们；外群大并不够。

本包使这一步有了准确剪枝：

* 对第3节的 uniform 非分歧块，整个源局部上容器就是 Gaussian 理想。若候选坏容器已包含它，继续搜索当地线性 indeterminacies 不会逃出。
* 对第5节的 uniform 二次块，候选坏容器只要包含 (5.5)，源当地输出就不会逃出。任意多个固定线性外步骤可以按 (4.4) 计算，而不是任意加深枚举。
* 若 S 是这些已解析地方的集合，P6 若成立，必有

      Σ_(p∉S)(h_p-Q_p) ≥ Σ_(p∈S)(Q_p-U_p).               (6.1)

  这是必要的剩余补偿量，不是新增输入假设，也不是已证明这种补偿存在。

III Remark3.9.7 的 inverse-system regions 使用外近似的体积下确界；不能挑一个很大的近似区域，就说该体积已被实际输出实现。IV Theorem1.10(vii) 的 archimedean π 容器同样是上界。两个方向都已核对；目前没有一个由这些引用直接提供的全局下界见证。

本包没有把 norm/determinant map 提前插入 Θ-link：III Remark3.9.5(x) 也指出这类下降会丢失 unit/Galois 资料。determinant 在这里仅用于原文规定最后的数值读出，局部矩阵计算在指定 frame 内进行。

**判断。** 当前不能继续把主要资源投到“放大一个局部线性对称群，叠二十层就会补齐差额”的路线：在已经解析的源块中，全部外群的最佳结果已经算完。应保留多层计算，但只让它处理尚未解析、确实携带 gluing/allowed-domain 改变的部分。

**一个可执行下一步。** 取下一份实际 source comparison 中最先离开上述固定 block 的箭头：保留它的完整 unit region、global prime-strip 标记、目标列 log-shift 和原地方权重，求该箭头前后局部 lattice 的相对矩阵及 source-allowed domain。若仍是第4节线性情形，精确消去；若不是，展开那个具体 nonlinear/标记重建步骤，并检验它是否能提供 (6.1) 所需增量或真正的全局 principal relation。不能用自由 q/Θ 字段、任意 global arrow 或新的“补偿假设”代替它。

最终缺口仍是：没有证明实际全球输出 family 在原 normalization 下达到或逼近 fixed native Q；也未找到完整合格初始 Θ-data 的反例。局部上界和可计算性结论已证明，不等于 P6 已证明。

## 7. 证据与验收

源版本固定为本地 corpus 的 II December2020、III May2020、IV April2020、Topics in Absolute Anabelian Geometry III；SHA256 在本包 EVIDENCE 中。作者网页 II/III/IV PDF 本轮再次只读核验。来源范围与定位见上文，不声称逐页重读全部文章。

脚本：c9_evaluation_defect_20261024.py。

证书：C9-EVALUATION-DEFECT-CERTIFICATE-20261024.json。

实际执行结果：216 个精确有理数矩阵案例通过（p=5,7,11，r=1,…,4，m=-5,…,12）；12 个 procession 系数恒等式通过；二十因子的 Smith 重数、维数、两种次序的 9 log p 差额及完整当地 procession 系数核验通过。百万维案例使用已证明的任意 r 公式压缩，不声称实际构造/枚举百万维矩阵。

自然语言证明由 root 自审；新增了适用条件，不改变原目标量词。计算只核验相应代数和局部域模型。Lean statement_compiles、proof_body_checked、kernel_closed、comparator、Project build、独立审查均未运行；target_accepted=false。当前未写任何 Lean。
