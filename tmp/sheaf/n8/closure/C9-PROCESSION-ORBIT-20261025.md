# C9：实际 procession 置换产生的输出区域

任务 ID：C9-PROCESSION-ORBIT-20261025；owner：当前 chat root；2026-10-25。用户要求单线程自然语言研究，不写 Lean，不派 subagent。

消费者/阶段：n8-c9-output-region-source-route，SHEAF stage1；原 P6 固定 native q 的完整源输出覆盖与严格亏损反证。保留任意原合格完整 C、gluing、目标列和 normalization；不得用下面的子族替换完整目标。

前轮分类：progress。C9-JH-OUTPUT-REGION-20261025.md，SHA256 21f18bdf5689c8e93e7ef9ed305cae00a1ab8169de2b76bcfecab39debadd75c，已证实际 J_H 的输出理想保留 j²，全共轭 norm 为常数；因此本轮不再把这些重写当增益。

新任务：直接构造 III Thm3.11(i)(Ind1) 中纯 capsule 置换的实际输出子族。证明它在完整 procession 上合法，保留原积分结构，计算同一 rational p 上不同地方 q-valuation 进入 tensor 各因子后，最终 holomorphic hull 的真实阈值与原 weighted log-volume。先决定该子族是否足以排除原严格亏损，再研究剩余真实 log/Kummer composite；不把外部 GL 容器反用为内见证。

精确读：I Def4.10/Prop6.9、III Prop3.1及Rmk3.1.1权重、Prop3.4/3.5的作用、Thm3.11(i)的Ind1；已有 allowed-regions/evaluation-defect/J_H 记录。仅查明确引用，不重审全仓。

精确写：本文件、同前缀 EVIDENCE/CERTIFICATE 和本包 Python 计算；owned DAG 新字段；AUDIT_LEDGER/STATE/queue 只追加。其他 owner 文件不改。集成root；构建不适用。

statement_dependencies：实际 capsule tensor packet、源 Gaussian generator、原生积分区域、procession poly-morphism 定义、原分量权重、完整输出 hull。

proof_dependencies：纯置换在源过程中的合法性；实际区域的像；tensor 分量上的赋值；componentwise ideal hull；有限概率分布的最小次序统计量。全部连接须证明，不能仅有相似公式。

验收：一个实际源允许输出族及其精确 hull/下界，或明确失败及原因。仅条件公式不能登记为无条件 P6。statement_compiles/proof_body_checked/kernel_closed/comparator/Project/独立审查未运行；target_accepted=false。

状态：阶段 1 局部研究完成；固定容器中的实际区域/加性格计算已证，完整固定 BPS 的源接入和原 P6 未证。下文区分这两种结论。

## 1. 保持原反证对象

固定原文合格的完整 C、native q、原 Θ-gluing、目标列和 normalization。写原完整可能输出 hull 为 H_C，独立计算的 native q 读出为 Q_C。要排除的是

    h_C = ν(H_C) < Q_C，

即整个最终输出族的一致严格亏损。不是排除某个原始 Gaussian seed 的亏损。最终目标仍是每个 ε>0 均有原允许最终输出 E 满足 ν(E)>Q_C−ε。没有要求每支保存体积，也没有把「同一 p 上坏地方质量≤1/2」加入原合格输入条件。

本轮得到两项可用的普通数学定理：置换轨道的精确区域公式，以及实际输出加性生成格在共同运输下的下界。尚未取得一份完整 C 上满足全部原 gluing/目标标记的源证书，因此不登记为 P6 或 source-complete contradiction。

## 2. 完整 procession 的置换：组合部分已核实

I §0 的 capsule-full poly-morphism 固定一份索引注入，但允许全部对应分量同构。I Def4.10 pp.119–120 的 procession 箭头则包括所有这种 capsule-full poly-morphisms；不是额外指定一条须逐点保持的旗标。I Prop6.9 pp.169–170 保留的正是逐 capsule 的标签不确定性。III Thm3.11(i)(Ind1) 使用这份 procession 的自同构。

令 m=(ℓ−1)/2。对 k=0,…,m，在 r-capsule 上取循环置换 i↦i+k mod r。给定注入 f:[r]→[r+1]，运输后的注入是 σ_{r+1} f σ_r^−1；这在全部注入集合上是双射，所以每个 k 确定一份完整的组合 procession 自同构，1-capsule 自动固定。对 r=j+1，k 的这些取值使被标记的 j 因子遍历所有 r 个位置。

只用 m+1 份完整选择，就能覆盖每层 Gaussian 作用因子的全部位置；不必独立选各层后再假装它们来自同一份分支。不同地方 v 本身没有被任意互换：跨 label 的同一 v 副本作识别，整个 tensor tuple 随因素置换一起移动。

这是 procession 组合和指定副本识别的证明。它还不是「这些选择在固定 gluing 下具有我们所需的最终区域表达」的证明；后者见第 8 节。

## 3. 固定 holomorphic 容器中的实际区域

固定 p。设 A=∏_{v|p}K_v，E_j=A^{⊗(j+1)}，O_{E_j} 为其各有限域分量的整数环之积。使用 integral closure，不能把它与 tensor_i O_{K_{v_i}} 混同。

实际 Gaussian profile g_{j,v} 满足 ord_p(g_{j,v})=j²a_v，其中 a_v=ord_p(qhat_v)≥0；good 分量的 profile 为单位，a_v=0。J_H 的有限幂关系沿用上一包，仅用于确认这里的实际 j²，不能改成其 1/j² 次幂。

令 G_j 将这份 profile 放在最后的 j 因子，I_j=G_j O_{E_j}。在固定 E_j 中主动作用的因子置换 τ_σ 满足

    τ_σ(I_j) = τ_σ(G_j) O_{E_j}。

对旧 tuple (v_0,…,v_j)，新 tuple 的第 i 项是 v_{σ^−1(i)}。因此，在一份固定的目标 tuple w 上，τ_σ(I_j) 的每个 field summand 的 p-赋值阈值为 j²a_{w_{σ(j)}}。这里同时运输了区域、作用和地方索引；只交换 g 的 label 而冻结 tuple 会得到错误公式。

有限 DVR 理想之和的阈值是各阈值之最小值，故

    H^{perm}_{j,p} = Hull(⋃_σ τ_σ(I_j)) = Σ_σ τ_σ(I_j)，
    threshold_{w}(H^{perm}_{j,p}) = j² min_{0≤i≤j} a_{w_i}。       (1)

第二个等号只因这里每支本来就是同一 O_{E_j} 的 fractional ideal；不是任意区域都有 Hull(union)=additive span。若某 w_i 比原 w_j 的赋值小，取该 field summand 的 primitive idempotent e，τ_σ(G_j)e 就属于置换理想而不属于原 seed。该点证明的是离开 seed，并未单独反驳完整 H_C 的亏损。

若原积分区域是置换不变的 S，且 B=Hull(S)，则同一固定环结构中

    Hull(τ_σ(G_j S)) = τ_σ(G_j) B。

每个 field 分量可保留 B 的实际阈值 b_w；(1) 改成 b_w+j² min_i a_{w_i}。所以此种固定环计算的增量不依赖把 S 擅自归一成 O_E。但是，运输到不同环结构前，不得用这个 B 替换实际 S；第 6 节给出正确的一侧比较。

## 4. 原权重下的精确体积，以及该机制的范围

按 III Rmk3.1.1(ii)、Prop3.9 和 IV Rmk1.7.1，设

    α_v=[(F_mod)_v:Q_p]/[F_mod:Q]，Σ_{v|p} α_v=1。

tuple w 的总权重是 ∏_i α_{w_i}；K_v/F_mod 的额外次数按原 normalization 消去，不能对未选定的 K-conjugate places 改用另一种平均。把取值 a_v、概率 α_v 的随机变量记为 X，取独立 X_0,…,X_j。由 (1)，

    ν(I_j)=−j² log(p) E[X]，
    ν(H^{perm}_{j,p})=−j² log(p) E[min(X_0,…,X_j)]，             (2)
    增量=j² log(p)(E[X]−E[min])≥0。

当 r=j+1≥2 且正权重支持上的 a_v 不全相同时，增量严格为正；因为至少一个 tuple 同时含有两个不同取值，它的 min 严格小于某一坐标，且其权重为正。相同取值时增量为零。用实际 B 时两式同时增加 ν(B)，增量不变。

设 distinct 正赋值为 0<t_1<…<t_s，t_0=0，s_k=Pr(X≥t_k)。分层积分给出完全精确的有限式

    E[min(X_1,…,X_r)] = Σ_k (t_k−t_{k−1}) s_k^r。             (3)

因此无需遍历 |V_p|^r 个 tuple 即可计算完整轨道 hull。式 (3) 是证明后的压缩计算，不是从小例子外推。

例如 X=a 的质量为 ρ、X=0 的质量为 1−ρ，则 procession 平均为

    h^{perm}_p = −(a log p/m) Σ_{j=1}^m j² ρ^{j+1}，
    Q_p = −ρ a log p。

在这个固定容器、零基准的局部比较中，达到 native-q 数值当且仅当

    P_m(ρ):=(1/m)Σ_{j=1}^m j²ρ^j ≤1。                        (4)

P_m 严格递增，P_m(0)=0，P_m(1)>1，故有唯一阈值 ρ_m。对所有 m≥2，P_m(1/2)<1：m=2、3 直接算；j≥4 时 j²/2^j≤1，随后递减，因此保留前面严格的余量。一般非负 X 若 Pr(X>0)≤1/2，则对每个 tail s≤1/2 应用 (4)，再用 (3)，得到同一局部数值比较。

这只是识别一个能成功的局部数值范围，没有把这个范围添加到原目标。全局还必须保留实际无穷处、各基准校正和固定源运输。

ℓ=41、m=20、ρ=1/2 时，单位取 a log p：

    seed = −287/4 = −71.75；
    permutation hull = −629097/4194304 ≈ −0.1499884；
    native q = −1/2。

21 份完整组合选择覆盖最大层 2^21=2,097,152 个两地方 tuple。实际计算用 (3)，未声称枚举了全部两百万维矩阵。精确有理阈值区间见证书，ρ_20≈0.629084970036。

相反，X≡a>0 时

    h^{perm}_p = −[ℓ(ℓ+1)/12] a log p < −a log p = Q_p。

纯置换在任意深度下都闭合于同一个有限置换群，不会突破这一界限。再复合保 O_E 的实际 field automorphism/单位乘法也不改变该理想轨道。F_mod=Q 时每个 p 只有一个 F_mod-place，是必须保留的测试情形；不能通过改数域、改 q、换权重排除它。这个结论只排除「纯置换及上述理想不变作用已足够」的路线，不是完整源反例。

## 5. 为什么不能同时使用“轨道取并的 min”和“平均赋值上界”

最小精确诊断为 A=Q_p×Q_p、g=(1,p^M)、E=A⊗A=Q_p^4。按 tuple (0,0),(0,1),(1,0),(1,1) 排列，理想阈值分别为

    I        : (0,M,0,M)，
    swap(I)  : (0,0,M,M)，
    Hull(I∪swap(I)) : (0,0,0,M)。

各支归一 log-volume 为 −(M/2)log p，hull 为 −(M/4)log p。M=10 时是 −5 与 −2.5；即使给「平均赋值上界」增加 1 log p，也仅得到 −4，不能控制这个主动轨道 hull。

IV Thm1.10 proof(iv) pp.26–27 明确说要估计全部可能像之并的 hull；(v) pp.27–29 先在固定 tuple 取 λ=j²a_{v_j}，以任意 φ 计入 Ind1/2，再把 λ 对作用因子的位置作平均。对于本轮的主动固定容器解释，若每支上界为 C(w)−j²a_{w_i} 且 C 对置换对称，那么联合上界应至少取

    max_i{C(w)−j²a_{w_i}} = C(w)−j²min_i a_{w_i}，

不能仅以 C(w)−j² average_i a_{w_i} 代替。平均每支的 log-volume 也不等于并集 hull 的 log-volume。这里最早要核的是跨 tuple 的置换是否真被固定 tuple 中的 φ 覆盖；不是一般加权平均公式本身有错。

若是被动换框架，连目标识别也从 T 改为 Tτ^−1，则 Tτ^−1(τI)=TI，根本没有上述区域增益。主动轨道和被动换框架不能混用。

本轮未声称此四维模型是完整合格 IUT 配置，也未据它宣布 IUT 反例。它是对拟用源解释的严格压力测试：若要计入本轮增量，就必须给出主动输出的具体源路径，并同步说明为何 IV 的对应 tuple 估计适用或需要修正。

对旧证据的局部更正：C9-ALLOWED-REGIONS 第六节曾把 IV1.10 的 uniform-majorant 讨论概括为覆盖全部分支。本轮不再把其中保留平均 λ 的 tuple 上界当作已经验证涵盖主动 factor permutations 的证据。原文固定 tuple 的 lattice 包络以及它的有限性用途没有因此全部撤销；对有限置换轨道可取各 majorant 的最大值，得到 min-λ 的粗有限包络。旧记录保留原字节，以本条修正适用范围。

## 6. 新的一侧运输引理：用实际输出的加性格，避免提前取 hull

这是本轮第二个实质结果。它把「非零变化」转化为一个不要求后续乘法结构一致的区域下界。

在有限维 Q_p 空间 V 中，取有限批实际输出 R_1,…,R_s，令

    L=闭的 Z_p-模生成格(R_1∪…∪R_s)。

假设 T:V→W 是同一份连续加性同构，按原 normalization 保体积；目标 H 是一个 holomorphic fractional-ideal hull，包含每个 T(R_i)。那么

    T(L)⊆H，因而 ν(H)≥ν(L)。                                (5)

证明：H 对加法、Z_p 标量和极限封闭；包含所有 T(R_i) 就包含它们的闭 Z_p-模生成格。连续加性 Q_p 空间同构自动 Z_p-线性，故该生成格等于 T(L)。最后用体积单调性和 T 的保体积性。证明没有把 T 与 holomorphic hull 交换，也没有要求 T 保乘法。

要使用有限的数值下界，L 必须是有界满秩格；这可从实际积分输入或输出基矩阵核验。若秩不足，包含结论仍成立，但不能把 Haar 质量零的格当成有限实数 log-volume 证书。

对源的多 tuple 原加权 log-volume，逐 tuple 使用其 Haar 体积，并要求 T 运输相应 tuple 块及原权重，便可加权求和。不能对任意跨不同权重块的 GL 矩阵直接宣称同一结论。全局只对原完整一组输出计算，保留无穷处及有限支撑。

本引理限于非阿基米德 fractional-ideal hull。无穷处的 hull 球不对任意加法封闭，不能由本引理生成它的加性和；无穷处读出须另用原实际区域计算，再与有限处下界相加。

若实际 R_i 本来是同一个 O_E 的 full fractional ideals，则 L=Σ_i R_i=Hull(∪R_i)。因而在确有同一份合法 T 的情形，(2) 的整个增量不会被随后的共同保体积加性运输消掉，即使该运输不保乘法。需要的是这份共同运输，不是「每支分别有某个保体积映射」。后者可用 T_i=Tτ_i^−1 将所有分支送回同一区域；每支体积仍保持，却完全没有轨道增量。

在原严格亏损反证里，(5) 的实际用途是：找到一批仍属于固定 C、固定 gluing 的输出和共同运输，实际算出 ν(L)≥Q_C，即得 h_C≥ν(L)≥Q_C，与 h_C<Q_C 矛盾。只有某个 ν(L)>seed volume 还不够。

## 7. 原积分 tensor order、ramification 损失与精确机器证书

若实际积分输入仅为 D=⊗_i O_{K_i}，必须计算

    L=Σ_i g_i D，

而不能提前换成 H=Σ_i g_i O_E。D 是 order，O_E 是 integral closure。总有 L⊆H；若从实际 order 计算出 p^c O_E⊆D，则

    p^c H⊆L⊆H，
    ν(H)−c log p ≤ν(L)≤ν(H)。                              (6)

左包含由逐项乘 g_i 后求和得到。在一个 tuple 块内用原 degree-normalized Haar 体积即可。精确损失由有限指数 [H:L] 给出；把实际输出的基向量拼成矩阵，计算满秩 minors 的 p-赋值最小值或 Smith normal form，就能得到 ν(L)。这消除了「需要猜一个合适区域」的数值部分；仍须证明这些基向量来自真实的原分支。

已独立于 IUT 来源做了一组 ramified tensor 检验。p 为奇素数，K=Q_p(x)，x²=p；D=O_K⊗_{Z_p}O_K；E=K×K，对应第二个根 y=±x。D 的基 1,x,y,xy 在 E 的整数基中的矩阵为

    B = [[1,0,0,p], [0,1,1,0], [1,0,0,−p], [0,1,−1,0]]。

det B 的 p-赋值为 1，所以 ν(D)=−(1/4)log p，不是零。令 L_M=x^M D+y^M D。若 M=2k，L_M=p^k D；若 M=2k+1，则

    xD+yD = x O_E。

后一个等式可由 x,y 给出 (x,0),(0,x)，由 xy,p 给出 (p,0),(0,p)（2 可逆）直接验证。于是

    ν(L_M)/log p = −M/2 − {1/4，M 偶；0，M 奇}。            (7)

但源 holomorphic hull 恒为 x^M O_E，体积 −(M/2)log p。偶数情形明确显示提前取 hull 会虚增 1/4 log p；奇数情形则显示实际分支的加性和确能补回这项损失。这里没有把例子的 x^M 宣称为完整 IUT 的 Gaussian。

计算程序用整数矩阵和满秩 minors 验证 (7)，并对 52 个 (p,M) 样本、每个 20 层共同 GL_4(Z_p) shear 复合，验证实际 span 体积保持、目标 holomorphic hull 体积不低于 span。这里的外部 GL 只验证一个对所有共同加性运输成立的下界；没有将这些 GL 当作允许源分支。

## 8. 对“能否产生所需输出区域”的准确判断

已证：

1. procession 全套组合置换确实可以有限覆盖；不是只构造一层标签操作。
2. 在指定 holomorphic realization 中，置换整个实际 ideal region 得到式 (1)，原权重下增量为式 (2)。非均匀赋值时严格非零。
3. 给定一批真实输出和共同保体积加性运输，式 (5) 将它们的加性生成格变成最终 hull 的可靠下界。有限基、tensor order 损失可按 (6)–(7) 精确计算。

尚未证：固定原 BPS/gluing 下，能够同时实现上述所有主动区域，并在所选目标列使用同一份 T，而不是随分支改变为 Tτ^−1；此 T 还必须是原实际 log/Kummer/etale-container 构造的末端映射，不得把跨 Θ-link 的整个 APT 擅自当作集合函数。III Rmk3.11.1(iv) pp.162–163 明确区分了这种算法运输与直接 set-function 运输，故 (5) 不能凭类比自动应用。

即使这个共同运输证书完成，纯置换仍不能处理第 4 节的均匀正赋值输入。因此本包不是原 P6 的证明，也不是“剩下一次形式化”的状态。它提供了一个严格可算的中间消费者：真实输出基向量 → 原加权 additive-span covolume → 目标 hull 下界。

可执行下一步：在一份固定原合格 C 的两个 capsule 因子上，逐箭头列出一次实际 factor swap 的 Kummer/evaluation/单位积分域及末端 container identification；同时计算 identity 分支的同一列表。检查两条路径是否具有共同的末端 T，并给出实际输出基矩阵。共同 T 成立则立即用 (5) 计算覆盖/不足；若是逆耦合换框架，则剪除此增量来源，不再靠加深置换复合重试。随后要处理均匀赋值输入，必须选取确实改变实际 additive span 的另一种源操作。

## 9. 版本、来源和验证

本轮定向阅读（没有宣称重读/审查全部论文）：

- IUT I May 2020：§0 pp.33–34；Def4.10 pp.119–120；Prop6.9 pp.169–170。
  https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf
- IUT III May 2020：Prop3.1/3.2、Rmk3.1.1、Prop3.4/3.5、Def3.8、Prop3.9、Rmk3.9.5、Thm3.11(i)、Rmk3.11.1(iv)、Cor3.12 possible-image 定义及 proof(xi)。另核 Def1.1 的 p*=p（奇 p）/p²（p=2）和 Prop1.2(v)。未用错误的统一 (2p)^−1 log-shell 定义。
  https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf
- IUT IV April 2020：Rmk1.7.1 pp.17–18、Thm1.10 proof(iv)–(v) pp.26–29；comments 所述早期 holomorphic/mono-analytic 修正不能单独解释本轮跨 tuple 的 min/mean 问题。
  https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf
- Alien Copies：pp.102–103 的任意 capsule permutations 和作用因子说明。
  https://www.kurims.kyoto-u.ac.jp/~motizuki/Alien%20Copies,%20Gaussians,%20and%20Inter-universal%20Teichmuller%20Theory.pdf
- On the Formalization of IUT，April 2026，§4 pp.9–11：固定 BPS、dsc/HDD/SHE 四个三角形。此处不是共同末端 T 的逐对象构造证书。
  https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf
- Dupuy–Hilado, arXiv:2004.13228v1，28 Apr 2020，§4.6–4.7 pp.19–21：factor permutation 运输 tuple 的显式公式，作为历史独立说明；不作为 Cor3.12 的证明。
  https://arxiv.org/pdf/2004.13228v1
  特别记录：2025 v2 已改为 Initial Theta Data 并明确不讨论复杂 U_Θ 构造，不能把 v1 的 Ind1 内容误归给当前 v2，也不猜测修改原因。
- Dupuy–Hilado, arXiv:2004.13108v2，29 Apr 2020，§6.2 footnote7、§6.3：其 toy automorphism model 明确未纳入 tensor-factor permutations；good profile=1。该模型不能解决本轮冲突。
  https://arxiv.org/pdf/2004.13108

本地精确源文件版本、复用研究版本、新程序/证书哈希列于 EVIDENCE JSON。

已运行：

    python tmp/sheaf/n8/closure/c9_procession_orbit_20261025.py
    python tmp/sheaf/n8/closure/c9_additive_span_20261025.py

均 exit 0。第一份：16 个精确轨道案例、47,296 个注入运输检查、12 个 prime processions、199 个 half-mass 数值检查；一般定理由上述证明，不由样本替代。第二份：52 个 ramified tensor orders、1,040 个 20 层以内共同运输复合。

没有写 Lean；statement_compiles/proof_body_checked/kernel_closed/comparator/Project build/独立审查均未运行；root 自审与上述精确数值检查已运行；target_accepted=false。原固定 BPS 的完整输出比较仍开放。未更改最终目标、自由增加假设或替换实际定义。
