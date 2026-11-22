# C9 stage1：B=O_K 与 B=I 分支的源生成元判定

任务 ID：task-154（C9-MODP-BRANCH-PROOF-20261025）；owner：logdescent；日期：2026-10-25。C9 stage1 自然语言/精确计算研究；只写本文件；未写 Lean/Project、未改目标、未改其他 owner 文件。消费者：n8-c9-output-region-source-route，SHEAF stage1。完整 P6 未证明；target_accepted=false。

本文件遵守 task-147 和 task-149 的两轮修正：
- 不复制 C9-TAME-LOG-DOMAIN-20261025.md 第 2 节的旧 donor 构造（rho 不是群同态、没有分裂、不是「rho 的像=Sp」、不是「所有 boundary-word 自由群替换都是实际 Galois 自同构」、不是「2025 trace 基=2026 symplectic 基」）；
- C9-TAME 第 5 节的 (11)-(14) 不是 target proof；F(Hull(...)) subset H_C 不能由环同构推出；全 Ind1 是 procession 自同构群，不是有限 label translation；任何 target-container 结论都要 TC-A..TC-H 加 TC-S。
本文件只做局部有限模 p 分支判定；不声称任何 target hull 包含或全局 h_C >= Q_C。

## 0. 冻结输入与版本

- TAME = tmp/sheaf/n8/closure/C9-TAME-LOG-DOMAIN-20261025.md，SHA256 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06；只把其第 6 节的 B 分类作为待核问题，不把第 2/5 节当成已证。
- SYM = tmp/sheaf/n8/closure/C9-SYMPLECTIC-SOURCE-20261025.md，SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70；采用其修正后的 H=Phi^{-1}(Sp) donor 与全部 caveat。
- IND1 = tmp/sheaf/n8/closure/C9-IND1-GLOBAL-20261025.md，SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8；本文件按它的 TC-A..TC-H、TC-S 与「(11)-(14) 不是 target proof」执行。
- EXT = tmp/sheaf/n8/closure/C9-LOG-DOMAIN-EXTEND-20261025.md，SHA256 CC52A8CF0D5FB56172A7AF2F6FB0C5C57EB726A5A459D3CCDE42FDDD3DAF2DFA；仅用于 e>=p-1 时 J 改变、本分支不可外推。
- C9-GLOBAL-ASSEMBLY-20261025.md（SHA256 6AB115790D8CDFD9E261985F7F209E4817C572AF6AAF4A48EB0EFDC2DE52CCF2）与 C9-UNIFORM-HULL-20261025.md（SHA256 2BF7A8C4D61ED142D9699E2CEC8B8CCAD8407C4C274E2CB1CA16F6EFFCF695FA）只用于说明分支的局部算术后果；其全局结论按 IND1 全部降为 conditional/withdrawn，除非 TC 条件补齐。
- 外部原文：Kondo 2026 arXiv:2605.25428v2（Definition3.2、Lemma3.3、Lemma1.3、Lemma1.6、Theorem2.6 proof）；Kondo 2025 arXiv:2512.09231v1（Theorem D、Theorem1.3、Section2、Remark2.16、Theorem2.17、Remark2.18）。loci 以 SYM 第 1 节核对过的为准；本文件不复述、不加强。

## 1. 局部类型与精确问题

固定 p 奇素数，K/Q_p tame totally ramified cyclic，e=ell 为奇素数，p>e+1，故 f=1、剩余域 F_p、d=[K:Q_p]=e=2g+1，g=(e-1)/2>=2。取 uniformizer pi，pi^e=p u，u in Z_p^×，m=pi O_K，O_K=Z_p[pi]。低分歧（e<p-1）给出

    J := log(O_K^×) = m,      I := p^{-1}J = m^{1-e} = pi^{1-e}O_K.    (1.1)

本节只在这个 tame 类型讨论。EXT 已指出 e>=p-1 时 J=m^{n0}（n0=ceil(e/(p-1))），O_K/J 不再是直线；本文件的二分类不适用于该情形（第 7 节）。

令 Gamma 为某个实际源作用在重建加法空间 K_+ 上的有限/闭像子群；B 定义为

    B := closed_span_Zp ( union_{gamma in Gamma} gamma(O_K) ).    (1.2)

需要在源条件 (H_A) 下判定

    B = O_K   还是   B = I.    (1.3)

(H_A)：Gamma 的每个元素保持 O_K、J、I，并在 I/J 上给出模 p 的 F_p-线性作用；B 满足 J subset B subset I。TAME 第 6 节在同样前提下定义 B；这里的 (H_A) 是 source-conditional hypothesis，不是 Kondo 定理。SYM/IND1 只证明 H 保持 O_K^× 与 J 的一部分/接口，未逐项证明 H 保持加法 O_K 或 p-整基；因此必须显式列出 (H_A)。

## 2. 局部 trace/U-W 分解：先不用 Kondo 基

### 2.1 I/J 的结构

由 I=m^{1-e}、J=m，有 O_K-模同构

    I/J = pi^{1-e}O_K / pi O_K  ≅  O_K / pi^e O_K = O_K / pO_K,    (2.1)

因 pi^e=p u 且 u 是单位。故 I/J 是 e 维 F_p-向量空间。O_K/J=O_K/m 是一条 F_p-直线 l；因 e>=1，O_K=m^0 subset I，故 l subset I/J。

### 2.2 实际 trace 给出 canonical U 与 W

tame totally ramified 时 trace Tr_{K/Q_p} 满足

    Tr(O_K)=Z_p,   Tr(m) subset pZ_p,   Tr(m^{1-e})=Z_p.    (2.2)

（pi^k 对 1<=k<=e-1 的 trace 为 0；Tr(1)=e；Tr(pi^e)=e p u in pZ_p；different 指数 e-1。）因此 Tr 诱导非零 F_p-线性泛函

    tau : I/J -> F_p,   tau(1)=e mod p != 0   (p>e).    (2.3)

定义

    U := l = O_K/J = <1 mod J>,        (2.4)
    W := ker(tau) subset I/J,   dim_Fp W = e-1 = 2g.    (2.5)

则 I/J = U 直和 W，tau 在 U 非零、在 W 为零。这是局部代数已证分解，不依赖 Kondo 2025/2026 的基对齐，也不依赖 rho 的任何性质。U 正是待判定的直线 l。

与 Kondo 2025 Theorem1.3 的关系：该文给 ker Tr_{K/K^{d=1}} = <y_2,...,y_d>（奇数 d；2025 JW 基 y_i）。在本节 K^{d=1}=Q_p（f=1、tame totally ramified）时 Tr 目标与 Tr_{K/Q_p} 相同，所以在同一基下相容。但 2025 trace 基与 2026 symplectic 基是否同一，是 SYM/IND1 标出的 inferred convention；本文件不把它当已证（第 3.2 节）。

### 2.3 B 分类引理

在 (H_A) 下，B/J 是 I/J 的 F_p-子空间、Gamma-稳定，且包含 l=U。

分支结构引理（局部代数，条件性）。设 Gamma 包含子群 H，其模 p 像含 Sp(W)，作用在 W 上，且 W 是 F_p 上不可约的 Sp(W)-模。则：

    B=O_K  <=>  B/J=U  <=>  对所有 gamma in Gamma，gamma(l)=l；
    B=I    <=>  存在 gamma in Gamma，其 gamma(l) 的 W-分量非零.    (2.6)

证明：若所有 gamma(l) subset U=l，则 B/J 由 l 的像生成，等于 l；因 J subset B、B subset I、O_K/J=l，得 B=O_K。若某 gamma(l) 有非零 W-分量 w，H 的 Sp(W) 不可约作用使 H.w 张成 W，于是 W subset B/J；又 U subset B/J，得 B/J=I/J，即 B=I。反向若 B=O_K 则 B/J=l，故每个 gamma(l) subset l；gamma 可逆、l 一维，故 gamma(l)=l。证毕。

不可约性标准事实：Sp_{2g}(F_p) 在标准 2g 维表示上传递作用在非零向量上，故无非零真子模；g>=1，p 奇。此引理只用 (H_A)、H 含 Sp(W)、局部 trace；不使用 Kondo 的 rho 同态或 boundary-word 替换。

## 3. 正确 donor H=Phi^{-1}(Sp) 与基对齐

### 3.1 SYM 的 corrected donor

按 SYM 第 2 节、IND1 第 2 节：
- Phi: Out(G_K) -> GL_d(Q_p) 连续闭同态；Definition3.2 给出 diag(1,Sp_{2g}(Z_p)) 嵌入；Lemma3.3 给 Phi(Out(G_K)) 含 Sp。
- 2025 rho: Mod(S \ {P}) -> Out(G_K) 只是 set-theoretic map，不是已知群同态（Remark2.18），没有分裂；正确 donor 是预像

      H := Phi^{-1}(Sp_{2g}(Z_p)) subset Out(G_K),   Phi(H)=Sp_{2g}(Z_p).    (3H)

- 不是「rho 的像=Sp」，也不是「H 是 Sp 的分裂拷贝」。H 可能比抽象 Sp 更大。
- 实际源箭头是 mapping-class/Dehn-twist 构造；boundary-word 自由群替换不是自动的 Galois 自同构。2025 trace 基与 2026 symplectic 基的同一性是 inferred，不是跨论文定理。

本文件只用 H，不用旧 TAME 第 2 节的 rho/边界词构造。

### 3.2 基对齐的精确矩阵条件

设 B_tr=(y_1,...,y_e) 为 2025 trace-adapted Q_p-基，U=<y_1>，W=<y_2,...,y_e>=ker Tr。设 B_sym 为 2026 Definition3.2 的基，其中 Phi(H) 矩阵为 diag(1,Sp_{2g})。令 T in GL_e(Q_p) 为 B_tr 到 B_sym 的坐标变换：

    [v]_sym = T [v]_tr.    (3.1)

在 I/J 上取模 p，需要两个基均给出 I/J 的 F_p-基且 T mod p in GL_e(F_p)；这是 SYM/IND1 的 caveat，不是论文定理。把 T 的模 p 矩阵仍记为 T。

- B_sym 中 H 固定直线 L_sym=<e_1^sym>，在 W_sym 上由 Sp 不可约作用。
- trace 线 l=U=<e_1^tr> 在 B_sym 中的坐标向量是 u=T e_1（T 的第一列）。
- H 固定 l 当且仅当 u 的 W_sym-分量全为零，即 T 的第一列=(a,0,...,0)（a!=0）。若如此，H 每个元素在 B_tr 中矩阵第一列为 (a,0,...,0)，H.l=l，由 (2.6) 得 B_H=O_K。
- 若 u 的 W_sym-分量非零，则 H.l 含非零 W_sym 向量；Sp(W_sym) 不可约，H.l 张成 I/J，故 B_H=I。这是 H 单独给出的第二支，但它是基对齐失败/不同 convention 的产物，不是 Kondo 定理直接给出的实际第二支。

因此精确的 donor 条件是：

    B_H=O_K  <=>  P_{W_sym}(T e_1)=0  <=>  T e_1 in <e_1^sym>；
    B_H=I    <=>  P_{W_sym}(T e_1)!=0.    (3.2)

若 T=I（自然推断的同一 JW 基），则 B_H=O_K；若 T 只把线映到线但保持 U/W 分解（例如块对角），仍 B_H=O_K；若 T 混合 U 与 W，则 H 自己就移动 l，得到 B_H=I。T 不是 Kondo 2026/2025 明确给出的；这是 branch 的核心 convention gap。

### 3.3 全 Gamma 与 H 的区别

B 的分支由全部实际 Gamma 决定，不由子群 H 决定。H 只保证 Sp(W) 子群；H subset Gamma 且 (3.2) 给 B_H=O_K 时，仍可能有额外 gamma in Gamma\H 移动 l，使 B_Gamma=I。反过来 B_Gamma=O_K 需要所有 gamma 第一列（trace 基）W-分量为零。

精确矩阵判据（trace-adapted 基 B_tr）：对每个 gamma in Gamma，模 p 矩阵 M_gamma=(m_ij)，第一列为 gamma(y_1) 坐标。则

    B=O_K  <=>  m_{i1}=0 对所有 i=2,...,e 和所有 gamma in Gamma；    (3.4)
    B=I    <=>  存在 gamma in Gamma 和 i>=2 使 m_{i1}!=0.    (3.5)

这是本任务要求的最终 finite matrix condition。它不依赖 H 的 rho 性质，也不枚举 GL_e(F_p)：只需实际源生成元集合的每个矩阵第一列；若 H 已给一组 Sp 生成元，只需再检查额外源生成元是否在抛物稳定子 P(l) 内。

注意：若使用 B_sym 而非 B_tr，则 M_gamma^sym = T M_gamma^tr T^{-1}；条件 (3.4) 变为 M_gamma^sym(T e_1) in <T e_1>。不要误把 B_sym 的 e_1 当 trace 线。

## 4. 源动作是否强制某一支？

结论分三层。

### 4.1 只用 corrected donor H

在 (H_A) 与 (3.2) 的 T 条件下：
- 若 T 保持 trace 线（自然 reading T=I 或块对角），H 每个元素第一列为 (a,0,...,0)（trace 基），故 B_H=O_K。
- H 的 Sp(W) 作用在 W 上不可约，但完全固定 U；因此 H 不能产生 B=I。旧 TAME 第 2/6 节若把「存在 gamma 移动 l」归因于 symplectic donor，是错的；SYM/IND1 已修正为预像 H，rho 不是同态，也没有分裂。
- 若 T 混合 U/W（基对齐失败），H 自己会移动 l，给出 B_H=I；但这不是新的实际源箭头，而是同一 H 在不同 convention 下的矩阵表现。必须由源级 trace/symplectic 基比较决定 T。

### 4.2 全部 Gamma

Kondo 论文只证明 Phi(Out(G_K)) 含 Sp，没有证明 Phi(Out(G_K)) subset P(l) 或存在元素在 P(l) 外。因此：
- 现有 source 动作不强制 B=I；事实上已证 H 子群在 natural alignment 下强制的是 B=O_K（B_H）。
- 现有 source 动作也不证明 B=O_K，因为可能还有额外 gamma in Gamma\H 移动 l；Kondo 没有给出完整 Phi(Out(G_K)) 的模 p 矩阵，也没有排除 U-W mixing 的 unipotent。
- 决定全 Gamma 的唯一精确方式是计算 (3.4)/(3.5) 的第一列；这不是枚举全部 GL_e(F_p)，而是实际源生成元的有限矩阵数据。

### 4.3 明确有限反例/见证（仅矩阵条件，不声称源实现）

在 trace 基中：
- H 的矩阵 diag(1,Sp)（或任意 Sp 生成元）第一列为 (1,0,...,0)，故 H.l=l，B_H=O_K。
- 第一列为 (1,1,0,...,0) 的矩阵（例如 unipotent 1+E_{2,1}）把 l 送到 <e_1+e_2>，其 W 分量非零；若它是实际 Gamma 的元素，则 (2.6) 给 B=I。这个矩阵在 GL_e(F_p) 允许，但没有 Kondo 源定理说它属于实际 Gamma。它只说明两支的 finite matrix 判据非空，而不是自动二选一。
- 对 e=5,g=2，diag(1,Sp_4) 与 1+E_{2,1} 的 5x5 模 p 矩阵可直接验证上述第一列条件；对 e=41,g=20 同理。这里不把这些矩阵说成实际源作用。

## 5. 局部体积公式：只是条件性局部算术，不是 target proof

按 TAME 第 6 节的 (16)/(17) 记局部 normalized log-volume（未进入 target H_C）：

    B=O_K 时：L_A = sum_i p^s pi_i D_r,   nu_A/log p = -s - 1/e;    (5.1)
    B=I   时：L_B = p^{s-r+1} J^{tensor r},   nu_B/log p = -s + (r-1) - r/e.    (5.2)

差为 (r-1)(1-1/e)。但必须保留 SYM/IND1 的 status：
- (5.1)/(5.2) 的格生成/末端全轨道公式是 TAME 的 inferred 后果（standard lattice lemma + orbit generation），不是 Kondo 2026/2025 定理；
- 它们还依赖 (H_A)、J=m（低分歧）、TAME 第 6 节 tensor 分配律/饱和假设；
- corrected donor 下，若 T 保持 trace 线，H 只给 B=O_K，B=I 的 (5.2) 没有源实现；若 T 混合，H 给 B=I，但那是 convention-dependent，必须先由源基比较确认；
- 若 B=I 的额外 gamma 不来自实际 source，则 (5.2) 不能用于全局 C9。

特别声明：C9-TAME 第 5 节的 (11)-(14) 不是 target proof；F(Hull(...)) subset H_C 不能由环同构推出。上面的 nu_A/nu_B 只是局部 additive lattice 的 normalized log-volume 算术，不是 target hull H_C 的 volume；任何把它升级为 h_C >= Q_C 的步骤都必须补 IND1 第 6 节的 TC-A..TC-H 加 TC-S。

## 6. Full Ind1 与局部 Gamma：不能混同

IND1 已明确：对固定 n，Ind1 是 procession Prc(n,circ D^dag_T) 的自同构群，不是有限 label translation。level j 的 capsule-full poly-automorphism 包含：
1. capsule 指标集合的 permutation；
2. 各 D^dag-prime-strip 的任意同构；
3. 每个 level j 独立选择（procession 箭头是全 collection，未指定固定 flag）。

Full Ind1 比局部 symplectic H 大；H 只用于产生非恒定局部 orbit，不等于 Ind1。局部 B 分支由 Gamma（局部 Aut(G_K) 像）决定，不是由 full Ind1 决定；即使局部 B=I，要成为 target H_C 的 possible image 还需要：
- TC-A（source procession/Phi,Psi 实际同构，beta in Ind1_src）；
- TC-B（H_C 是 full target possible images 的 hull，或 F 是 allowed target automorphism）；
- TC-C（F 保持 integral closure/hull 与 normalized log-volume，或正 determinant factor 已算）；
- TC-D（row j/vQ/bad-good profile 保持；permutation 时 H_C 需 full Ind1 union）；
- TC-E（Theta-pilot/Theta-times-mu gluing/q/BPS/target-column class 保持）；
- TC-F（log/Kummer branch 与 Ind3 相容）；
- TC-G（fixed n；n->n' 是另一问题；infinity/+infinity branch 不在此局部公式中）；
- TC-H（Ism/Ind2；整数格不变不代表 target hull/log-volume branch 不变）；
- TC-S（corrected symplectic donor：H=Phi^{-1}(Sp)、mapping-class/Dehn-twist、trace basis alignment、Tr_{K/K^{d=1}} 且 tame totally ramified K^{d=1}=Q_p、J=m low-ramification、standard-lattice lemma）。

因此本文件只能给出局部 B 判据；不能声称 F(Hull(...)) subset H_C，也不能把局部 nu_A/nu_B 当作全局 h_C/Q_C 比较。C9-GLOBAL 的 b=3/B=I「局部转正」若没有 TC-A..H + TC-S，是 conditional/withdrawn，不能作为 target 结论。若 B=O_K 支（natural alignment 下 H 强制），C9-GLOBAL 的局部剩余亏损数字只是局部算术；其全局结论同样受 TC 缺口限制。

## 7. e>=p-1 的边界

EXT 给出：e>=p-1 时 n0=ceil(e/(p-1))>=2，J=m^{n0}，I=m^{n0-e}，O_K/J=O_K/m^{n0} 的 F_p-维数为 n0（不是 1），I/J=O_K/m^e 仍 e 维。于是：
- TAME 第 6 节「O_K/J 是一条直线 l」不成立；
- B/J 含 n0 维的 O_K/J，B 的二分类 B=O_K/B=I 不再由 U/W 直线+Sp 不可约性给出；
- trace/U-W 的 U 维度从 1 变为 n0（或按 trace 核的分解需重做），W 的不可约模也改变；
- 任何 e>=p-1 的源作用与体积结论必须重新推导，不能把本文 (2.6)/(3.4)/(5.1)/(5.2) 外推。

## 8. 已证 / 条件 / 未证

已证（局部代数，不依赖 Kondo）：
- (2.1) I/J 同构 O_K/m^e，dim_Fp=e；l=O_K/J 是直线。
- (2.2)-(2.5) trace 诱导 tau，U=l，W=ker tau，I/J=U 直和 W，dim W=e-1=2g。
- (2.6) 在 (H_A)+H 含 Sp(W)+W 不可约下的 B 分类引理；矩阵判据 (3.4)/(3.5)。
- Sp_{2g}(F_p) 在 W 上不可约（标准事实，g>=1、p 奇）。

已证（SYM/IND1 引用的论文层面，非本文件重证）：
- Kondo 2026：Phi 连续闭；Definition3.2 的 diag(1,Sp_{2g}(Z_p)) 嵌入；Lemma3.3 的含 Sp。
- Kondo 2025：JW presentation/trace kernel（对 k/k^{d=1}）；rho 只是 set map，非已知同态（Remark2.18）；Mod -> Sp_{2g}(Z) 的像（Theorem2.17）；Dehn twist 实际外自同构。
- 2026 Theorem2.6 proof 的 alpha_+ log = log alpha^times（unit/log 兼容）。

条件/inferred：
- (H_A)：Gamma 保持 O_K、J、I 并作用 I/J；SYM 只给 unit/J 的接口，加法 O_K 与 p-整性未逐项证明。
- T 的存在/模 p 可逆与 T e_1 的 W 分量：2025 trace 基=2026 symplectic 基是 inferred convention，不是论文定理；T 的实际值未计算。
- H 在 trace 基中为 diag(1,Sp)（T 保持 trace 线）是 natural reading，未被原文明确陈述。
- (5.1)/(5.2) 的 orbit generation、J=m、volume gain 是 TAME 的 inferred 后果，不是 Kondo 定理。
- 完全 Gamma 的模 p 生成矩阵未知；H 只是子群。

未证/明确 gap：
1. 计算实际源 Gamma（完整 Aut(G_K) 有限像，不只是 H）在 trace-adapted 基 I/J 上的第一列，决定 (3.4)/(3.5)。这是本任务精确剩余问题。
2. 计算 2025 trace 基到 2026 symplectic 基的 T，或证明 T e_1 in <e_1>；SYM/IND1 指出这是 convention gap。
3. 证明 (H_A)（实际源保持加法 O_K/I/J/p-整基），或替换为正确 source-conditional 版本。
4. 若走 B=I，证明额外 gamma 来自真实 Dehn twist/映射类，不是 boundary-word 自由替换；不能用「所有 boundary-word-preserving 自动是 Galois 自同构」。
5. e>=p-1 时重做 B 分类（第 7 节）。
6. 即使 B=I，还要 TC-A..TC-H + TC-S 才能谈 target H_C；本文件不提供 target containment。
7. 全局 h_C/Q_C、archimedean、完整 C/weighted sum、fixed q-volume class 均未证明。

## 9. 精确剩余计算（可执行）

给定实际 C 的 K、Gamma 生成元：
1. 用 trace 基 B_tr=(y_1,...,y_e) 写 I/J 的 F_p-基，e_1=1 mod J，e_2,...,e_e 为 W 基（例如由 JW 生成元/log 单位模 p 给出）。
2. 对每个实际源生成元 gamma in Gamma（Dehn twist/映射类产生的实际外自同构），计算其模 p 矩阵 M_gamma 第一列 (m_{11},...,m_{e1})。
3. 检查 (3.4)：若所有 i>=2 的 m_{i1}=0，则 B=O_K；否则 B=I。
4. 若使用 2026 symplectic 基，先算 T 并换算；或直接证明 T e_1 in <e_1> 以采用 natural reading。
5. 对 e=41,g=20 类型只需实际 Gamma 的有限生成元/矩阵，不得用任意 GL 或 boundary-word 替换。
6. 得到 B 分支后，仍要逐条检查 TC-A..TC-H + TC-S 才能把它接入 target；不要直接从局部 B=I 推出 h_C>=Q_C。

若不能得到实际 M_gamma（源 C 没有足够自动同构/矩阵），精确 gap 就是：缺实际 Gamma 的模 p 生成矩阵（第一列）与 T 的源级比较；不能由「非 Hodge-Tate」「Out 维数大」「H 含 Sp」推出 B=I。

## 10. 结论

局部 trace 把 l=O_K/J 识别为 I/J 的 canonical U，W=ker Tr 为标准 Sp_{2g}-模；corrected donor H=Phi^{-1}(Sp) 在 natural basis alignment 下固定 U，故 H 只能给 B=O_K，不能产生旧 TAME 中的 B=I。全 Gamma 的分支由实际源矩阵第一列是否全部落在 U 决定，精确判据是 (3.4)/(3.5)。实际源矩阵与 2025/2026 基对齐 T 未给出，因此目前既没有证明 B=O_K，也没有证明 B=I；B=I 只是 source-conditional 的有限矩阵可能性，不是 Kondo 定理的后果。

即使得到 B=I，也仍须 TC-A..TC-H + TC-S；本文件不声称 F(Hull(...)) subset H_C，不声称全局 h_C>=Q_C，不把 TAME 第 5 节 (11)-(14) 当 target proof。

## 11. 源引用

- IUT I：Section0 capsule/capsule-full poly-morphism（lines 1688-1710）；Definition4.10 processions（6761-6778）；Proposition4.11（6779-6838）。
- IUT III：Proposition1.2(vi) log-shells（1898-1949）；Proposition3.2 tensor packets（5687-5785）；Theorem3.11(i) Ind1/Ind2/Ind3（9151-9280，9434-9436）；Corollary3.12 target hull/Q-Theta（10326-10358，10359-10410，10843-10898）。
- Kondo 2026 arXiv:2605.25428v2：Definition3.2、Lemma3.3、Lemma1.3、Lemma1.6、Theorem2.6 proof。
- Kondo 2025 arXiv:2512.09231v1：Theorem D、Theorem1.3、Section2、Remark2.16、Theorem2.17、Remark2.18。
- 内部冻结：TAME、SYM、IND1、EXT、C9-GLOBAL-ASSEMBLY、C9-UNIFORM-HULL（哈希见第 0 节）。

## 12. 验收记录

- 本文件只写 C9-MODP-BRANCH-PROOF-20261025.md；未改 Lean/Project/目标/其他 owner 文件。
- 自然语言自审：已完成；引用的 Kondo 论文位置以 SYM/IND1 核对为准；未独立重跑证书/脚本。
- Lean/Project/kernel/comparator/独立审查：未运行，不适用。
- 明确依赖旧 TAME 第2节/第5节的地方均已标注 corrected-by-SYM/IND1；未把旧构造当证明。
- target_accepted=false；完整 C9/P6 未闭合。
