# C9：实际 log 定义域、源辛群作用与输出 hull

任务 ID：C9-TAME-LOG-DOMAIN-20261025；owner：当前 chat root；日期：2026-10-25。用户要求自然语言研究、单线程、不写 Lean。前一 goal turn 分类为 progress。

消费者/阶段：n8-c9-output-region-source-route，SHEAF stage1。目标保持：每份原文合格完整 C，固定 native q/BPS/gluing/目标列/normalization，排除整个最终输出族的统一严格亏损 h_C<Q_C。下面的局部类型只用于攻击子问题，不增加为原目标假设。

前包复用：C9-FIXED-GLUING-SWAP-20261025.md，SHA256 f734bc7bd33d8aa605315ad7e16709908722186ac27eece0e5a5c10cb10b1b19；实际 tensor 加性格、raw Ind1 家族的共同末端运输与非零商群长度均已研究。原全局比较未闭合。C9-EVALUATION-DEFECT-ATTACK-20261024.md（SHA bfdad69825b86a4f1372f822117b03a0451a01af8bb404c0c4ee3f4657098912）的 full-GL 外界不能反用为实际下界。

本包实际问题：展开原 log-link 的方向、定义域、所用有限域/Galois invariants 和 Kummer 识别，判定实际分支是否改变 Gaussian 中的 p 整数标量。特别检查 tame e=ell、p>e+1 类型中的真实 log(O_K^×)、归一化 shell、迭代单位域。若这些仍不能提供规模所需增量，则定位完整源的全局剩余比较；不把「外 shell 较大」当作实际输出存在。

statement dependencies：III Def1.1、Prop1.2、Rmk1.1.1/1.2.2、Prop3.4/3.5、Thm3.11；固定实际 local fields、unit groups、标记 Gaussian action、末端 hull 与源权重。proof dependencies：真实 log/exp 域，连续加性运输的整数标量兼容，源声明的上包含/覆盖，积分格的精确指数。原输入与待证比较分开记录。

精确读：上述 III 文本与其必要 AbsTopIII 引用；I Def3.1/field-of-moduli 定义；IV 与该实际局部容器有关的包含式；已冻结研究证据。精确写：本文件、对应 EVIDENCE、必要精确计算脚本/证书；owned DAG 新字段；AUDIT_LEDGER/STATE/queue 仅追加。其他 owner 文件和 Lean 不动。集成负责人当前 root；构建不适用。

验收：给出实际允许分支的区域像，或对这一具体补偿机制的严格排除及其对原全局反证的影响。只有完整原目标达到并验证才可关闭 P6。本包根自审；Lean/Project/kernel/comparator/独立审查未运行。

状态：本包自然语言局部证明完成，根自审；完整原 P6 仍未证明。下面的 source-relative 结论复用所列原文的真实构造，不表示这些源依赖已在 Lean 中闭合。

## 1. 真实 log 定义域：低分歧情形在第二步终止

设 K/Q_p 有限，p 奇，绝对分歧指数 e<p−1，m 为其极大理想。对 x∈m，v_p(x)≥1/e>1/(p−1)。对 n≥2，v_p(n)≤(n−1)/(p−1)，所以 n v_p(x)−v_p(n)>v_p(x)；log(1+x) 的一次项严格控制其赋值。同理，v_p(n!)≤(n−1)/(p−1) 给出 exp 的收敛和相同的一次项控制。log、exp 在 1+m 与 m 间互逆。Teichmuller 根单位的 log 为零，故

    J_K=log(O_K^×)=m，I_K=p^−1 m。                       (1)

这里 I_K 是原 III Def1.1(i)/Rmk1.2.2(i) 的归一化 shell。乘 p^−1 是构造 shell 的步骤，不是 log-link 自身多了一条可任意反复调用的 p^−1 箭头。

III Def1.1(i) 的 log-link 是普通 log 后接 log(F) 到下一 F 的 Frobenioid 同构；相应非零整数 monoids 的同构保持单位/非单位。源 finite Galois invariants 对应 K，其像仍在下一有限域的 Galois invariants 中。因此第一次 log 的非零像属于 m，后接的实际同构仍把它送成非单位。Rmk1.1.1(i) 要求下一条 log-link 的输入必须为单位。故在这种局部类型中，从源有限域单位开始的连续 h 次 log-link：h=1 的像为 m，h≥2 的定义域为空；log 为零的根单位也不能作为下一步的单位输入。

相应 Kummer 零次路径携带原 O_K 的整数结构，第一次 log 路径的像在 O_K 内。于是，在 Ind1 的 mono-analytic 重新表示之前，允许的这些 log/Kummer 路径生成的积分格恰为 O_K。这个结论只论实际有限域 invariants 和原指定路径；不把整个 ind-topological ambient field 当积分域。若路径中还插入保持 J_K 的 mono-analytic 模块同构，第一次 log 像仍不能离开 J_K=m 成为下一步单位。

一个必须拒绝的伪补偿是先在代数闭包取所有 p^N 次根、再放宽 Galois invariants 的顺序。取 v=exp(p)∈O_K^×，在代数闭包选 v_N^{p^N}=v，则 log(v_N)=p^{1−N}。若这些被无条件当作同一个有限 K 的允许积分输入，其 log 像无界，已超过源紧 shell。Def1.1(i) 的 pre-log-shell 来自取 perfection 以前的真实单位 Galois invariants；ambient perfection 并不授权上述积分域替换。

这里没有将所有 Ind3 现象一般性判为零；e≥p−1 或其他域/关系的情形不由 (1) 覆盖。无穷处也不适用。

## 2. 新的源供体：真实 Aut(G_K) 的辛群像

本轮新读 Kaiji Kondo, *Lubin-Tate representations over nontrivial finite Galois extensions of Q_p are not Aut-intrinsically Hodge-Tate*, arXiv:2605.25428v2，24 September 2026，尤其 Theorem1.2、Lemma1.3、Definition3.2、Lemma3.3。实际使用的是 Lemma3.3 的群作用构造，而不是仅从 non-Hodge-Tate 性质猜测体积扩大。

对 d=[K:Q_p]=2g+1≥3、p 奇，论文的 mono-anabelian 加性作用

    Φ:Out(G_K)→GL(K_+)

的像含有一个在某实际源基中形如 diag(1,Sp_{2g}(Z_p)) 的闭子群。这是实际 Galois 群自同构的像，不是先取一个任意 GL 外群。

其源构造可以展开：Jannsen–Wingberg 型生成元 σ,τ,x_0,x_1,…,x_d 的奇数次数关系中，x_2,…,x_d 只通过 [x_2,x_3]⋯[x_{d−1},x_d] 进入关键关系。对这些生成元取保持该 boundary word 的自由群自同构，固定其他生成元，会保持整个 G_K presentation 及 pro-p normal-subgroup 条件；逆替换给出逆同构。譬如一个 pair 上 x_2↦x_2x_3、x_3↦x_3 保持该 commutator。映射类群的作用在交换化上给出 Sp_{2g}(Z)，而 Φ 的像闭，故包含其闭包 Sp_{2g}(Z_p)。原文的 rho 不被误写成一个已给定的群同态；使用的是生成的闭子群及其像。

与 IUT 接入：III3.11(i)(Ind1) 的 procession 由 D⊢-prime-strips 构成，非阿基米德分量是实际 G_K 的 Galois category；故上述自同构给出允许的分量自同构。在指定高阶 capsule 使用它，在 1-capsule 取 identity 代表，按 I Def4.10 组装成完整 procession 选择，保持指定 core/gluing。使用上包的共同末端运输。作用须施于整份 (A,S) 表示，实际输出为 α_+(A(S))。

这两份加性作用的匹配不是仅凭名称。AbsTopIII Def5.4(iii) 将 k~ 定义为 (O^×) 的 perfection；Prop5.8(i) 用 local reciprocity 在 G^ab 中重建 O^×，(ii) 从该单位/perfection 图重建 k~ 与 shell。对有限 G-invariants，任意 log(u) 的像由重建的单位像唯一确定，且 log(O_K^×) 张成 K_+。Kondo §0 的 O^×(G)⊂G^ab 与 k_+(G) 使用同一 reciprocity 与单位/perfection 构造，2026 文 Theorem2.6 证明中的交换图明确给出 α_+ log(u)=log(α^×u)。故由张成性，两者在有限 K 上相同。AbsTopIII5.8(i) 对 open embeddings 采用 contravariant transfer；在 automorphism 上若采用反方向 convention，则换成 α^−1，整份作用像不变。IUT III1.2(vi) 正是调用 AbsTopIII5.8(ii)，并给出与 holomorphic log module、shell 和体积相容的实际同构。Kummer/cyclotomic 识别的单位标量差不改变下面的 Z_p-lattice 像；全塔 Ism=Z_p^× 的已核结果可复用。不能把该 Ind1 作用误归入固定 Galois 标记的 Ind2：后者仍只有单位标量。

以下证明仅需这份实际辛群子作用，不需要未知的完整 Out(G_K) 像等于 GL。

## 3. trace 消去未知基坐标：实际轨道生成整个极大理想

假设 K/Q_p 为次数 e=ell≥5 的 tame totally ramified cyclic extension，p>e+1、μ_e⊂Q_p，π^e=p u、u∈Z_p^×。这是上一包的 bad 局部类型。令 J=m=πO_K。用第2节的实际辛群子作用 G，写其 Q_p-表示为

    K_+=U⊕W，dim U=1，dim W=e−1，
    G|U=identity，G|W=Sp_{e−1}(Z_p)。                    (2)

这里不把论文未给出的基到 π-power basis 的坐标矩阵设为 identity。

首先，实际 Galois 自同构的单位作用与 log 交换，故保持 J=log(O_K^×)。关于未知源基与 trace 的关系，本轮又读到 Kondo 的另一篇原文 *Anabelian aspects of the outer automorphism groups of the absolute Galois groups of mixed-characteristic local fields*, arXiv:2512.09231v1，10 December 2025，Theorem1.3：奇数次数时 ker Tr 恰为 <y_2,…,y_e>。这直接给出 W=ker Tr；因为 trace 非零，它在 U=<y_1> 上非零。对第2节的辛子群 G，由其在 U 上恒等、在 W 上作用可得

    Tr(γ x)=Tr(x)，γ∈G。                                (3)

这条 trace 公式只需用于该辛子群；不必另外假设整个 Out(G_K) 逐点固定 Q_p 的加性直线。2025 文 Lemma1.2 的全群 trace-kernel 稳定性也是可用的原文结果。若选用另一 Kummer 单位标量代表，可先在 lattice 像层消去该单位标量，而不改变结论。

辛群中的 z=diag(1,−I_W) 保持 J。因为 p 奇，(1+z)/2、(1−z)/2 是保持 J 的投影，故

    J=J_U⊕J_W，J_U=J∩U，J_W=J∩W。                     (4)

标准 Sp_{e−1}(Z_p) 在 W 上的任意满秩稳定 lattice 都是标准 lattice 的 p 整数幂倍：取 lattice 的最小坐标赋值向量，Sp 对 primitive vectors 的传递性给出所有同一最低赋值的基向量，反向包含由最小赋值定义。因此，在适当整体缩放后，J_W 是标准辛整数格。这里没有更改实际 J 或 volume reference。

上述传递性可以直接构造：若 w 是标准辛整数格的 primitive vector，非退化 unimodular alternating form 给出 w' 使 <w,w'>=1；分离这对向量及其正交补，再递归选辛基。两份以指定 primitive vector 开头的辛基之间的变换就在 Sp(Z_p) 中。

取 1≤t≤e−1，A_t=π^tO_K⊆J。直接用 π-power basis 得到

    Tr(A_t)=pZ_p=Tr(J)，
    length_Zp(J/A_t)=t−1<e−1。                          (5)

第一式因为 Tr(π^a)=0（1≤a≤e−1），而 A_t 的基包含 π^e=p u。由 trace 在 U 上非零、在 W 上为零，(5) 说明 A_t 的 U 投影等于 J_U。

若 A_t 的 W 投影包含于 pJ_W，则 A_t⊆J_U⊕pJ_W，从而 length(J/A_t)≥e−1，与 (5) 矛盾。因此其 W 投影含一个 J_W-primitive vector。Sp 轨道生成整个 J_W；用 z 分离 U、W 投影即得

    closed_span_Zp ⋃_{γ∈G} γ(A_t)=J。                   (6)

反向包含也成立，因为 G 保持 J。整个 Aut(G_K) 同样保持 J，且包含 G，故 (6) 对全部实际 Aut(G_K) 的像仍是等式。

写 n=s e+t，1≤t≤e−1。单位 u 的幂不改变 ideal，且所有加性作用与 p^s 交换。得到本包的准确新结论：

    closed_span_Zp ⋃_{α∈Aut(G_K)} α_+(π^nO_K)
      = p^s m_K。                                      (7)

两端都是实际区域，右端已是一个 fractional ideal。于是相应 field holomorphic hull 也恰为右端，其 normalized volume 相对原 π^nO_K 的增量为

    ((t−1)/e) log p。                                  (8)

当 t≥2 时，(8) 是实际源自同构产生的、hull 可见的严格增量；与上一包只在 tensor-order 内部增长的商群长度不同。t=1 时没有增量。整数 s 完整保留，没有取 Gaussian 的 1/j² 次根。

## 4. 有限见证与 tensor 输出区域

(6) 不要求枚举不可数个自同构。取一个 A_t 中具有 J_W-primitive 投影的向量；在 J_W/pJ_W 上用有限个辛矩阵把其非零投影送到一组基，再取各矩阵的源提升。取一个 U 投影生成 J_U 的 A_t 向量，连同 z，用加减及 1/2 提取 U、W 分量。至多 2e 个这样的源输出点即可在模 p 上生成 J；相应闭 Z_p-span 由 Nakayama 等于 J。辛模 p 矩阵可由整数辛矩阵提升，再由上述 boundary-word 自同构实现。有限计算只需处理实际有限 residue action；其源提升来自第2节，不能由任意矩阵直接充当。

若只要求 field holomorphic hull，甚至有两条候选分支的直接反证见证。取上述 a=u+w∈A_t，u∈J_U，w∈J_W primitive。因为 Tr(π)=0 且 π∈J\pJ，所以 π 也是 J_W 的 primitive vector。用实际 Sp 子作用分别选择 γ_1、γ_2，使 γ_1w=π、γ_2w=2π；二者都固定 u。因此实际输出点为

    y_1=γ_1a=u+π，y_2=γ_2a=u+2π，y_2−y_1=π。

若两个点都在 m²，则差 π 也在 m²，矛盾。故至少一个 y_i 属于 m\m²。该分支的整个实际区域 γ_i(A_t)⊂m，并含有一个 valuation 恰为1/e的点，所以

    存在实际 γ：Hull(γ(A_t))=m；
    对 n=se+t，存在实际 γ：Hull(γ(π^nO_K))=p^s m。     (8a)

这给出的不是一个任选的非零不变量，而是实际 output 的可定位点和由它确定的完整 fractional-ideal hull。至多两条候选分支中至少一条成功；这条局部反证的假设是两点同时落入 m²，不冒充已排除原全局 h_C<Q_C。

在本包更特殊的 tame power-basis 情形，甚至可以直接选出一个成功点：Tr(π^t)=0，且 π^t∈J\pJ（1≤t<e），因此 π^t 和 π 都是 J_W 的 primitive vector。上述辛基构造给出一个实际 γ，使

    γ(π^t)=π，γ(π^n)=p^s u^s π（π^e=p u）。           (8b)

所以实际乘法输入1的输出 π^n，经这个真实源作用，直接成为 valuation 为 s+1/e 的输出点。对于小单位 log 域，输入 exp(p) 的 log 为 p，实际输出 pπ^n 经同一 γ 成为 p^(s+1)u^sπ。γ 是加性但一般不是环同构；(8b) 不说 γ(π^t)=γ(π)^t。存在该非环作用正是第2节真实 Galois 自同构供体带来的内容。

有限计算也只需这个构造的模 p 版本：在 J_W/pJ_W 中，将 π^t 的非零类送到 π 的类，提升所需辛矩阵到 Sp(Z) 再提升为源自同构。所得实际点与 π 相差 pJ，而 pJ⊂m²，所以 valuation 仍恰为1/e。因而无需计算任意高 p-adic precision，也无需用数值近似猜测非零量。

这个有限线性步骤最多用两次辛 transvection。记 alternating form 为 < , >。若 <x,y>≠0，取 v=y−x、c=<x,y>^−1，则 T_{v,c}(z)=z+c<z,v>v 为辛变换，且 T_{v,c}(x)=y。若 pairing 为零且 x≠y，选 z 同时不属于 x 与 y 各自的正交超平面（两个真超平面的并不覆盖 p>2 的向量空间），先送 x 到 z，再送 z 到 y。将 v、c 的坐标提升到整数，仍得到整数辛 transvection；其实际 Galois 源提升由第2节给出。脚本已在每个格案例中执行这个有限 transport，验证输出在 m/m² 中非零。这一步不声称测试所选基就是某份完整 C 的未知 Jannsen–Wingberg 基；基无关的一般证明负责这项量词。

在 r=j+1 个 bad 因子的实际 tensor order D_r 中，对 Gaussian 标记因子应用 (7)，其余因子保留原整数区域，再用允许的 factor permutations，得到实际输出生成格

    L^Sp_{r,n}=Σ_i (p^s π_i)D_r。

固定一次共同末端 T 后，有 T(L^Sp_{r,n})⊆H_{C,j,p}。上一包精确指数公式现在取余数1，给出

    ν(L^Sp_{r,n})/log p=−(r−1)(e−1)/(2e)−s−e^(−r)。    (9)

这一步保留 tensor-order/integral-closure 损失。虽然 (7) 在一个 field 中已经是 ideal，不能据此将一个一般非环 T 与整个 tensor holomorphic hull 交换。第5节随后用完整真实 Ind1 轨道和实际 field-copy isomorphisms 得到更强下界；那一步并不交换任意 T 与 hull。

对上一包 bad/good profile 的同一局部类型，设 b j²=s_j e+t_j。由于 e=ell 为素数、ell∤b、1≤j≤(ell−1)/2，所有 t_j 都非零。原加权公式中的 all-bad 项可严格改善为

    ell_j^Sp=−c[(j+1)rho−1+(1−rho)^(j+1)]
             −rho^(j+1)[s_j+e^(−j−1)]，c=(e−1)/(2e)。 (10)

这是实际辛群的内作用下界。每层相对上包的改善量恰为 rho^(j+1)[(t_j/e)^(j+1)−e^(−j−1)]≥0。若仍用保守的 p-per-factor 小单位域，再减 j+1；零次 Kummer 整数路径则不加这个损失。

整数部分仍然无法由 (7) 消掉。给 b 加 e，(10) 仍下降 j²rho^(j+1)；这与上一包相同。新作用补足了余数方向的实际源构造，没有自动完成 native-q 全局比较。

## 5. 将区域送入指定目标：完整 Ind1 轨道消除末端坐标障碍

这里补上比第4节更强的一步。固定原完整 C、原 core/gluing 代表 η、原末端 procession 代表 Φ 和相应 T。III Thm3.11 的开头明确要求所有 theaters 相对于同一份 given initial Θ-data；III Prop3.2 也使用该同一 initial datum。因而，在实际 holomorphic realizations 中，源和目标每个相应地方的有限域都是给定 K_v 的副本。选择这些真实 field-copy isomorphisms f_{j,i,v}，不是由向量空间维数相同选择任意矩阵。

在每个 r=j+1≥2 的 capsule 上，令 Ψ 的分量代表为 f_{j,i,v} 所诱导的实际 D⊢-prime-strip isomorphisms；在 1-capsule 上仍选原 η。I Def4.10 的 morphism 定义逐 capsule 指定 capsule-full poly-morphisms，各相邻箭头是全部这类 poly-morphisms，没有另外固定的 flag 需要这些代表逐点保持。故这些代表组成一份允许的完整 procession isomorphism Ψ，且其 core 代表仍为 η。把所有 S、A、global embedded data 一同作用；不只换 Gaussian 的 label。

令 β=Φ^−1 Ψ。它是源 procession 的实际自同构，core 代表为 identity。通过原 Kummer identifications 进入有限 packet 坐标后，functoriality 给出

    T ◦ β_+ = F，                                      (11)

其中 F 在每个 r≥2 的 holomorphic tensor packet 上由这些 f 的 direct sum/tensor product 组成，因此是实际 Q_p-algebra isomorphism。III1.2(vi)/3.2(i) 的 Kummer 自然性保证 (11)；若采用 Ism-orbit 的另一代表，出现的 Z_p^× 因子不改变本包实际整数格及 ideal。

对任一源允许的 γ，βγ 也在完整 Ind1 族中，且 core 代表仍是 identity。因此在这个固定 T、固定 η 的同一输出容器中，存在真实分支

    R_{βγ}=T(β_+ γ_+(A(S)))=F(γ_+(A(S)))。              (12)

这是实际 output 的等式；A 是原 Gaussian/evaluation 作用，S 是原允许积分输入。我们没有把 q 的整数幂改掉。β 通过已给定源同构的复合产生，不是借用 full GL 来反求需要的体积。F 也没有替换固定的 Θ-gluing；Ψ 在 core 上仍是原 η。这里只在原 full-poly/Ind1 允许的高阶 capsule 代表中做选择。

由 (12)，先在目标内得到真实区域，再取目标 hull，因 F 是环同构而有

    F(Hull(⋃_γ γ_+(A(S)))) ⊆ H_C。                      (13)

这没有声称 Hull(TL)=T(Hull L) 对一般 T 成立。它使用完整 Ind1 族对 βγ 的封闭性，构造出了另一组实际分支。

应用于第4节同一 all-bad tuple：源实际加性格含 L^Sp_{r,n}=Σ_i p^s π_i D_r，而它在 E_r 的 holomorphic hull 为

    Hull(L^Sp_{r,n})=Σ_i p^s π_i O_{E_r}。

对 E_r 的每个 field component，每个 π_i 都有 p-赋值 1/e，因此上式的阈值恰为 s+1/e。于是 (13) 证明目标完整输出 hull 满足

    ν(H_{C,j,p})/log p ≥ −s_j−1/e                       (14)

于此 all-bad tuple。这个下界不再含 tensor-order/integral-closure 损失：该损失是真实的 additive-lattice 体积损失，第4节计算仍正确；完整源分支对齐后，最终授权的 holomorphic hull 确实可以将其消去。不是在进入目标以前把 D_r 擅自换成 O_{E_r}。

利用 (8a) 可进一步看到 (14) 已由一条选出的实际分支实现：在标记因子使用成功的 γ，在其他因子取原 O_K。输出包含 p^s y⊗1⊗⋯⊗1，y∈m\m²；它在 E_r 每个 field component 的 valuation 均为 s+1/e，而整个区域包含于相同阈值的 ideal。经 (12) 进入目标后，该分支的 hull 因而恰有 (14) 的值。这里没有把 y 作为 singleton 直接代入 Haar volume；使用的是包含 y 的实际满秩区域及其原授权 hull。

在同一个 p 的坏/好混合 profile 中，若 tuple 有好因子，选原允许 permutation 将 Gaussian 标记移到好因子，得到实际 D_tuple；在 (12) 的目标坐标内，它的 holomorphic hull 是 O_{E_tuple}。因此相同坏质量 rho、坏 qhat 赋值 b/e 的 profile 满足更强的下界

    ell_j^aligned ≥ −rho^(j+1)(s_j+1/e)，
    h_p^aligned/log p ≥ −(1/m)Σ_{j=1}^m rho^(j+1)(s_j+1/e)，
    m=(e−1)/2，b j²=s_j e+t_j，1≤t_j<e。               (15)

如只使用直接可追踪的 principal-unit 小域，则 S=p^(j+1)D_tuple；(12) 同样适用，每层 (15) 再减 j+1。因为 exp(pz) 是实际单位、log(exp(pz))=pz，这个小域无需把外部 shell 当原始积分像。

这里对完整 C 的使用保持在原 stage1 源构造范围：先前冻结包的 raw Ind1 饱和、实际 Kummer/evaluation 图和共同末端运输被复用。本包重读了 I Def4.10、III1.2(vi)/3.2/Thm3.11 的精确定义；没有调用 Cor3.12(xi-f) 所要证明的 q 比较。若某实现将高阶 capsule 的代表额外限制为 core 的固定 diagonal 延伸，它就无法使用 (12)，并且须先解释该额外限制的源依据；当前源定义没有这个限制。

## 6. 未标记整数环的完整轨道只有两个可能结果

本节给出另一条精确结论，便于后续计算完整局部族。令 Γ 为实际 Aut(G_K) 的加性像，I=p^−1J，B=closed_span_Zp⋃_{α∈Γ}α(O_K)。因为 J⊂O_K⊂I，且 Γ 保持 J、I，有 J⊂B⊂I。于是 B/J 是 I/J 的 F_p-子空间。

I/J 的维数为 e；(4) 给出它作为 G-module 的分解 Ubar⊕Wbar，维数为1、e−1。O_K/J 是一条直线，trace mod p 非零，因为 Tr(O_K)=Z_p、Tr(J)=pZ_p。B/J 是 G-stable，并包含这条直线。用 z 将其 U、W 投影分离，再用 Sp_{e−1}(F_p) 的标准表示不可约性，只剩两种可能：

    B=O_K 或 B=I。                                     (16)

更具体地，令 l=O_K/J，barΓ 为 Γ 在 I/J 上的有限像：若 barΓ 保持 l，则 B=O_K；若某真实 γ 将 l 移走，则其轨道和已实现的辛作用生成全部 I/J，从而 B=I。这里没有证明实际输入必处于第二种；non-Hodge-Tate、Out 群维数较大均不能替代这个模 p 直线问题。

对固定一个 all-bad r-tuple，只允许原 Gaussian 整数区域、全部逐因子 Γ 和 factor permutations，(7)、(16) 给出这个实际子族加性生成格的精确分类：

    B=O_K 时： L_A=Σ_i p^s π_i D_r；
    B=I   时： L_B=p^(s−r+1) J^{⊗r}。

证明是 tensor 对有限和的分配律：标记因子的轨道和恰为 p^sJ，其他因子的轨道和恰为 B；逐因子作用独立，故 tensor 生成格正好是这些格的 tensor。第二种中 J=pI，使各标记位置给出的格相同。全部作用在这一有限域类型内已经饱和，因此重复任意多层同类自同构不会出现第三种格。

由 (11)–(13) 的源对齐，以及完整轨道本身的稳定性，这个子族在目标 holomorphic hull 的归一化值分别为

    ν_A/log p=−s−1/e；
    ν_B/log p=−s+(r−1)−r/e。                            (17)

两值之差为 (r−1)(1−1/e)。这里的精确分类只针对所列实际子族，不是整个 C 的全部 log/Θ/无穷处输出族的上界。原 log 定义域分析也不授权在每层随意插入一个新的 p^−1。

这留下的是一个可定位的有限表示问题：计算实际 barΓ 是否保持 l；不能通过枚举所有 GL_e(F_p) 直接选择第二支。即使第二支成立，其增量只随 r 线性增长，仍不能对任意 b 抹掉 s_j 中的 b j²/e。

## 7. 精确计算、成功范围与原反证的剩余量

本轮执行 c9_source_symplectic_span_20261025.py，exit0；证书为 C9-SOURCE-SYMPLECTIC-SPAN-CERTIFICATE-20261025.json。72 个 finite symplectic span cases 检验实际证明所需的模 p 格生成结论，包含 e=41 的 trace-adapted 基变化；同72例另构造了至多两次 transvection 的直接输出点见证。24 组 residue thresholds 检验第4节格下界；新增24组检验第5节最终 hull 下界。辛群的源提升由文献和第2节给出，不由这些矩阵算例给出。基变化用于检验基无关格命题，不被声称是额外允许的源作用。

在零次 Kummer 整数域版本中，(15) 已经严格改善上一包的大 b 门槛。由于 s_j+1/e≤b j²/e，若 rho≤1/2，则

    h_p^aligned/log p ≥ −(b/e)(1/m)Σ j²rho^(j+1)
                       > −rho b/e = Q_p/log p。

最后一个严格号可直接证明：P_m(rho)=(1/m)Σ j²rho^j 单调；P_2(1/2)=3/4<1，m≥3 时前三项的和为21/8<3，j≥4 的各项 j²/2^j≤1。因此 P_m(1/2)<1。这里仍然只证明规定 profile 的局部比较，没有将 rho≤1/2 添加为原始 C 的假设。

e=41、rho=1/2 时，单位均为 log p：

| 实际积分域 | b | 本包目标 hull 下界 | native q 局部值 |
|---|---:|---:|---:|
| 零次 Kummer 整数域 | 3 | −56311/10485760 ≈ −0.0053702354 | −3/82 ≈ −0.0365853659 |
| 直接单位 log 小域 | 1347 | −172082321/10485760 ≈ −16.4110489845 | −1347/82 ≈ −16.4268292683 |

第二行全程使用实际 exp/log 单位域；相较上一包 b=1620 的首次成功门槛，现在 b=1347 即成功，所有更大且3|b、41∤b 的 b 均成功。该无限尾部由 b↦b+41 的精确 affine-period formula 和有限 residue 检查证明，不由有限采样外推。第一行所有正的 admissible b 均成功。

补充局部 realization 的精确化：上一包使用 p=1231，其 Q_p 不含 i；所以它从未构造完整 initial Θ-data。为同时满足 I Def3.1(a) 的局部 i 条件，本包改用已核素数 p=12301，其 p−1 可被60·41整除。Tate q=p^3240 给出全30-torsion、qhat=π^1620、K=Q_p(π)、π^41=p；若取新的小域阈值 b=1347，则 q=p^2694 给出原文要求的全6-torsion，qhat=π^1347，仍有 K=Q_p(E[41])=Q_p(π)，因为 gcd(2694,41)=1。此处是实际坏局部源 realization；尚未将一个好地方和全局大 Galois image 一同构造成完整 C，不能冒称全局例证。

对 uniform bad profile rho=1，第5节已消除末端坐标和 tensor-order 下界损失，但 b=3 的已证子族仍给出 −411/41，而 Q_p=−3/41。若 (16) 的较大支确实发生，则完整逐因子子族可达到9/41；本包没有任选该支。对 b=273，即使取这个子族的较大支，也只有 −38736/41，仍低于 Q_p=−273/41。这不证明整个源输出族亏损；它精确说明该子族的能力范围。

uniform 情形不是可以忽略的弱输入：若原 F_mod=Q，则 I Def3.1(e) 的 V→V(F_mod) 是一份 section，每个有理 p 只有一个选定地方；其指定 bad 质量只有0或1。不能把 K 的所有 conjugate places 改成新的 rho=1/2 平均来回避它。

## 8. 本包完成什么、下一步证明什么

已完成的 stage1 局部链条为：真实 Galois presentation 的 boundary-word 自同构 → 真实单位/reciprocity/log 作用 → trace 与格指数确定 π^nO_K 的完整轨道生成格 → 整份 (A,S) 的实际输出 → 固定 core/gluing 下的合法 βγ 分支 → 原目标容器中的 holomorphic hull 和精确下界。输出来自实际点和实际区域；不来自 label 的自由 thetaImage，也不来自 singleton 的随意 volume。

原目标仍为排除完整 C 的 h_C<Q_C。第7节只排除了特定局部 profile 的亏损，不足以排除所有 C 的全局亏损。尚缺：uniform bad profile 的源补偿机制；其与原无穷处及其他有限处的实际加权和；全部 row/Θ/log 分支的原固定 q 体积类识别。不能把第6节子族的上界用作完整 H_C 的上界。

下一项可执行任务：以一个原 F_mod=Q 的完整 C 为测试对象，保留原 q、全20层和全部源积分域，用 (14)/(17) 写出明确剩余亏损；计算其实际 archimedean 区域及原 log-Kummer 列间复合是否提供同一量纲的补偿。与此同时，若需要第6节较大支，任务必须是 source generators 在 I/J 上是否移动 O_K/J 的具体有限像问题，而不是更多任意线性层。只追踪会改变上述精确量的真实源箭头。

验收记录：root 自然语言自审已做；上述精确计算已运行通过；本包没有写 Lean，statement_compiles / proof_body_checked / kernel_closed / Project / comparator / 独立审查均未运行；target_accepted=false。没有证明完整原反证矛盾，也没有制造一份完整 IUT 反例。
