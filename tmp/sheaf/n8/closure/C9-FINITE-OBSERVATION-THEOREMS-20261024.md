# 输出包络的有限模约化：候选命题、证明与计算

任务 ID：n8-c9-finite-observation-theorems-20261024；owner：当前 chat root；日期：2026-10-24。

用户当前要求：主动提出辅助数学命题，证明或否定它们，通过多层逻辑消去将复杂输出比较化成机器能计算的问题。继续单人自然语言研究，不写 Lean，不派 subagent。这是对上一包“未获可行性证据不展开”的推进方式的修订：允许现在构造并证明中间理论，但不把未证条件添进原目标。

消费者：dag/nodes/n8-c9-output-region-source-route.json 的 P1/P6；先处理固定 source-qualified packet 在真实 Ind2 作用下的 holomorphic hull，保留 q-pilot、目标 holomorphic structure 和原 normalization。完整 Kummer/log/Ind3/全局比较仍保持原量词。

既有证据：C9-FIXED-Q-DEEP-COMPARISON-20261024.md，SHA256 fe93128b5526e97236e42a45d741866e44bf420ae1c2680dc275a9acd58a6b51。复用其 source Ism 定义、finite-witness 命题及错误路线分析，不重新全仓审查。

精确读文件：IUT II p.39 Ism(G) 定义、III Th.3.11(i)(Ind2)、Remark3.9.5(i)；上述研究记录及 root 节点；必要外部研究用于复用调查。

精确写文件：本记录；同目录 finite_observation_certificates_20261024.py、C9-FINITE-OBSERVATION-CERTIFICATES-20261024.json、C9-FINITE-OBSERVATION-EVIDENCE-20261024.json；root 所属 DAG 节点；AUDIT_LEDGER、STATE、queue 追加。无其他 owner 文件、Lean 目标、生产接口修改。构建负责人不适用。

待研究候选：

1. 对最终 hull 而言，线性路径可在 Z_p-span 层精确计算，是否无需保留全部逐点分支？
2. 保持 reference lattice 的群轨道包络，是否只依赖一个可计算精度的有限群像？
3. 有限生成作用下，是否有明确饱和步数界，从而消去任意长的线性路径？
4. 多层线性相容条件，是否可用 Smith 因子给出“有限精度解提升”的明确阈值？
5. 只改坐标的图边能否消去，且完整保留非平凡 holonomy 和积分校准？
6. 是否可以凭连续几层观测稳定就判定整个无限源塔？先查反例，不假设成立。

验收：每条候选给精确量词、证明或反例，区分一般定理/实际源局部应用/尚未构造的有效数据。计算是可复核精确证书，不用样本代替全称证明。自然语言自审；所有 Lean/kernel/comparator/project checks 未运行；target_accepted=false。

状态：本包辅助命题已完成自然语言证明、反例和精确计算；原 fixed-q 比较未闭合。下文是一组本项目的新研究结果，不声称这些线性代数事实在数学文献中具有首创性。

## 1. 本包实际改变了什么

研究对象仍是固定原文合格输入的实际输出区域。设最终非阿基米德目标 algebra 为 E=∏K_a，O_E=∏O_{K_a}，其 holomorphic hull 为最小的 λO_E 包络。Q 是独立构造的 native q-pilot 校准体积，不能由输出 hull 反向定义。

本包证明三个可以直接消费的约化，而不是给原定理添加三项假设：

1. 固定线性块的全部逐点输出，可以换成 Z_p-span 计算，最后的 holomorphic hull 完全相同。提前换成 O_E-hull 则可能错误。
2. 对保持 reference lattice 的群，给定 full lattice 的整个线性区域轨道已经是有限的；所需模 p 精度由格子的厚度明确决定。任意长群字的包络可在有界次数的格子扩大后算完。
3. 有限线性相容图可以先消去纯坐标边，再用 Smith 因子把“精确可提升”化成一个指定精度的有限环计算。无限源塔的相容性仍须另有证据，但最终 hull 的内外相等可以绕过完整群分类。

辅助条件的地位：所有定理均明确写出一般适用条件；对真实 Ind2 局部线性块，保持格子的条件来自 source 定义。尚未接通的 Kummer/log/Ind3/全局条件仍留在原 DAG，未冒充已证输入。

这些约化保持最终 hull，并不自动保持未经源授权扩大前的全部原始分支体积谱。将最终 hull 读出用于 Values/P6，继续依赖前包单独核对的原文区域扩大和全局校准步骤。

### 1.1 复用调查与来源

- Caruso–Roe–Vaccon, *Tracking p-adic precision*, arXiv:1402.7142v1 (2014-02-28), §2.1–2.2：[正文](https://arxiv.org/html/1402.7142)。启发是用 lattice 保留坐标间的精度相关性。这里不直接援引其非线性精度主引理；第7节的 log 球命题独立证明。
- Giacobazzi–Ranzato–Scozzari, *Making Abstract Interpretations Complete*, JACM 47(2), 2000, pp.361–416, §1.1–1.2：[作者稿](https://www.sci.unich.it/~scozzari/paper/JACM00.pdf)，DOI 10.1145/333979.333989。启发是要求抽象计算与具体计算严格交换，而非只得到外包络。第2节是在 Z_p 模上的直接实现，不把一般抽象解释定理当作源语义桥。
- 原源定位复用前包已核对版本：IUT II p.39 Ism 定义；III Th.3.11(i)(Ind2), p.154；Remark3.9.5(i), p.127。没有重新解读自由 theta interface 为已实现 source map。
- 一般 Smith/Hermite 计算是标准代数；本包把具体证明、精度阈值和失败条件完整写出。没有进行 Lean/Mathlib API 搜索，因为当前授权是自然语言数学。

## 2. 定理 A：线性段的 Z_p-span 是准确的中间对象

设 V 为有限维 Q_p-vector space，U⊂V 有界。定义 M(U)=span_{Z_p}(U)。由于 U 包含于某个 full lattice，Z_p 的 Noetherian 性说明 M(U) 有限生成；因此它也是闭的，不需额外加入拓扑闭包。

对任意 Q_p-linear map T:V→W，以及任意一族 U_i，成立

    T(M(U)) = M(T(U)),
    M(⋃_i U_i) = Σ_i M(U_i).

证明：每个 span 元素是有限个原输出的 Z_p-linear combination；T 与这些有限线性组合交换。反向包含由生成元直接得到。第二式同理。

若 V=E，且 M(U) 是 full lattice（例如 U 包含 full lattice；更一般，span_{Q_p}(U)=E 即足够），则

    Hull_E(U) = O_E M(U).

右边是包含 U 的最小 O_E-submodule；因有界且每个 field 分量非零，它是 product of nonzero fractional ideals，即 λO_E。这与 source hull 定义相同。

若 U 具有正 Haar 测度，则 span_{Q_p}(U)=E 自动成立：否则 U 位于一个 proper linear subspace，选坐标后该子空间包含于一条坐标为0的超平面，其 Haar 测度为0。因而这里不要求任意正测度区域自身含一个开球；需要的 full lattice 是 M(U)。

所以在一段仅由实际 Q_p-linear maps 和允许分支并构成的过程里，用 M(U) 取代全部逐点 U，每一步按模像和模和计算，最后再取 O_E-span，结果完全准确。这里的虚拟线性组合不必都是实际 primitive outputs；准确性指最后 hull 相同，不是声称新组合本身成为源分支。

### 2.1 为什么不能把中间对象进一步压成 holomorphic hull

令 E=Q_p×Q_p，

    L={(x,y)∈Z_p² : x≡y mod p},
    T(x,y)=(x−y,y).

有 Hull_E(L)=Z_p²，但 TL=pZ_p×Z_p，于是

    Hull_E(TL)=pZ_p×Z_p ≠ Z_p²=Hull_E(T Hull_E(L)).

提前取 O_E-hull 丢掉了 x 与 y 的同余关系，而后续 T 正好能观察这个关系。Z_p-span 不会丢掉它。这是一个直接反例，不是以精度为名的实现偏好。

### 2.2 有限控制图与全部路径

设有有限有向控制图。每个顶点 v 有 reference lattice Λ_v、初始 full lattice L_v⊂Λ_v；每条边 e:u→v 是实际允许的 linear map T_e，且 T_eΛ_u⊂Λ_v。图的状态必须保留决定路径允许性的全部离散标记；此处不任意合并不同 χ。

令

    M_v^0=L_v,
    M_v^{k+1}=M_v^k + Σ_{e:u→v} T_e M_u^k.

归纳可知 M_v^k 等于所有长度≤k 的允许路径图像的 Z_p-span。每次严格更新都会使非负整数

    Σ_v length_{Z_p}(Λ_v/M_v^k)

至少下降1。因此严格更新次数≤Σ_v length(Λ_v/L_v)。一轮没有更新时已是固定点，所有更长路径均已包含。最终 Hull_E 读出准确。

若某顶点的初始集合为零，不能直接套用上述 finite-colength bound。可以在确有实际可逆路径时，用该路径带来的 full lattice 作种子；否则须另行证明可达子空间/格子界。本包未为一般零种子或扩张算子 p^{-1} 提供这个界。

## 3. 定理 B：线性区域轨道只需要指定有限精度

设 Λ⊂V 是 rank d 的 Z_p-lattice，G⊂Aut_{Z_p}(Λ) 为任意子群，L 为 full lattice，且整数 r≤s 满足

    p^sΛ ⊂ L ⊂ p^rΛ.

令 N=s−r。若 N=0，则 L=p^rΛ，轨道只有一个区域。以下取 N≥1。

### 3.1 整个 lattice orbit 的有限性，而不只是 hull 的有限性

若 g,h∈Aut(Λ) 模 p^N 相同，则

    (g−h)L ⊂ p^{N+r}Λ=p^sΛ ⊂ hL.

末个包含成立，因为 h 保持 Λ，故 hL 包含 h(p^sΛ)=p^sΛ。因此 gL⊂hL；交换 g,h 得到反向包含。于是

    g≡h mod p^N  ⇒  gL=hL.

结论：整个 {gL:g∈G} 由实际有限像 Ḡ_N⊂GL(Λ/p^NΛ) 决定。没有使用 compactness，也没有把 G 换成全 GL。对于非 lattice 的原始 U，相同结论只保证 gM(U)，不声称 gU 本身由这个精度决定。

精度在一般情形不能降低：取 d=2，L=Z_pe_1+p^N Z_pe_2，g=I+p^{N−1}E_{21}。g 在模 p^{N−1} 下等于 I，但其输出第二坐标 hull 指数从 N 降至 N−1。

### 3.2 有界格子饱和消去任意长群字

取实际有限像 Ḡ_N 的一组生成元，并任选在 G 中的 lifts g_1,…,g_m。定义

    M_0=L,
    M_{k+1}=M_k+Σ_i g_i M_k.

始终 p^sΛ⊂M_k⊂p^rΛ。每次严格包含使 length(p^rΛ/M_k) 至少下降1，故严格扩大次数至多

    c=length(p^rΛ/L) ≤ dN.

一旦 M_{k+1}=M_k，各 g_iM_k⊂M_k；由于 |det g_i|_p=1 且 M_k 为 full lattice，包含的 index 为1，所以 g_iM_k=M_k，逆作用也保持它。于是生成子群的全部字都保持 M_k。

对任意 g∈G，有限像中有一个生成元字 h 与 g 同余 mod p^N。第3.1节给 gL=hL⊂M_k。因此固定点恰为

    M_G(L)=Σ_{g∈G}gL,
    Hull_E(⋃_{g∈G}gL)=O_E M_G(L).

在至多 c 次严格扩大之后必定停止；可再做一轮相等检验。算法输入需要实际有限像的生成元，不能以“计算了一个有限层中心化子”冒充它。即使有限像尚未构造，定理本身已经证明输出所需信息只在这个明确精度上。

### 3.3 稀疏实际见证与整体缩放

不要求先给群生成元：从 L 出发，若尚未等于 M_G(L)，就选一个 g∈G 使 gL 不包含于当前模并加入。相同长度下降说明存在至多 c 个实际群元素，其 translates 与 L 一起生成全部 M_G(L)。这是有限见证存在论；若没有实际分支生成器，不由此声称有效搜索必定终止。

对任意整数 t，

    M_G(p^tL)=p^tM_G(L),
    (s+t)−(r+t)=N.

所以纯整体缩放不增加观察精度。它并没有消掉 q-volume：在 μ(O_E)=1、d=[E:Q_p]、ν=(1/d)log μ 的局部读出下，ν(p^tH)=ν(H)−t log p，必须保留这一项。真实 Gaussian profile j² 的非均匀缩放可能增加 N；本定理不提供与 q 无关的统一复杂度界。

### 3.4 因子独立时，算子模可以张量组合

若 source 的某一步确实给出独立的 G_i 作用于 Λ_i，则令 A_i=span_{Z_p}(G_i)⊂End(Λ_i)。乘积群在 ⊗Λ_i 上生成的算子模是自然映射 ⊗A_i→End(⊗Λ_i) 的像。证明只是把每个 A_i 的有限线性组合展开为纯张量的线性组合，反向由群元素张量得到。

这允许先算各 factor 的算子模，再作用于实际 integral-closure lattice L；无需枚举所有群元素元组。不得把 O_E 本身换成 ⊗O_i，也不得对共享 Kummer/χ 约束的非独立选择使用此式。

## 4. 定理 C：只观察最终 hull 的内外相等证书

沿用定理 B。设 S 是一组已经证明属于真实 G 的作用；K_N⊂GL(Λ/p^NΛ) 是一个已经证明包含真实 Ḡ_N 的有限群。S 的源允许性必须有全塔构造/源定理，不由有限层测试替代。

由 S 生成的群可用第3.2节算内模 M_in；由 K_N 的任意 invertible Z_p lifts 算外模 M_out。第3.1节保证外模与 lifts 的选择无关。于是

    M_in ⊂ M_G(L) ⊂ M_out.

若机器核验

    O_E M_in = O_E M_out,

则这两个 hull 就等于真实完整轨道的 hull。不必证明 M_in=M_out，更不必证明 K_N=Ḡ_N。这是目标读出层面的完全证书。

证明：对上面两个包含取 O_E-span，再用两端相等。它没有把外矩阵当成真实分支；下界始终只来自 S 的真正作用。

该条件确实比群/模相等弱。第2.1节的 L 已有 Hull(L)=Z_p²。取 S={I}，而外群容许 [[1,1],[0,1]]，外模扩大到 Z_p²；内外模不同，最终 hull 相同。因此可忽略外群中仍未判定的作用。若后面还有任意非 E-linear map，则只能在终点使用这个相等证书；提前使用会重现第2.1节反例。

对 P6 的实际用法有两种：内外相等时得到准确 hull；即使不相等，只要由内包络和其他真实分支按原规则拼成的全球读出已≥Q，就已经有足够的下界证书。两种用法都要保留实际全局 χ 同步、reference correction、原权重和无穷处误差。当前没有计算出后一种原源证书。

## 5. 定理 D：有限线性相容系统的准确提升精度

设 D:Z_p^m→Z_p^b 为一个固定有限 integral matrix。非零 Smith 因子写作 p^{a_1},…,p^{a_t}，令 a=max a_i；D=0 时令 a=0。对任意 n≥1，令 ρ_n 为模 p^n 的投影，则

    ρ_n(ker D)
      = { x̄ mod p^n : 存在 x mod p^{n+a}，ρ_n(x)=x̄ 且 Dx=0 mod p^{n+a} }.

证明：取 UDV=diag(p^{a_i},0)，U,V integral unimodular。右侧条件在 Smith coordinates z=V^{-1}x 中要求 p^{a_i}z_i≡0 mod p^{n+a}，因此每个非零 pivot 坐标 z_i 均被 p^{n+a−a_i} 整除，特别被 p^n 整除。将这些坐标直接置零，其余坐标保持不动，得到精确 kernel 元素，并与原 x 模 p^n 相同。反向包含显然。

若还要求某些矩阵变量可逆，其 determinant 为 unit 是模 p 就决定的性质；修正保留模 p^n，故可逆性保留。同理，任何完全由模 p^n 决定的 guard 都保留。

应用：有限图的 Galois intertwining 条件 X_vA_e=A_eX_u 是线性的；保持另一个 full lattice BZ_p^d 可引入辅助变量 Y，写成 XB=BY，并要求 X,Y 都可逆。清掉固定分母后仍是有限线性系统。固定标记 Xq=q 可用 X=I+Z 化成 Zq=0，只限于 identity 确实给一个共同基点的系统。一般 affine system 若无已知精确基点，本定理不自动提供该基点。

因此对一个真正的有限相容图，存在准确的 p^{n+a} 阈值；不需要不断猜更高精度。构造这个阈值需要精确矩阵，或足以证明 Smith valuations 的有效表示，不能从任意不可计算 p-adic coefficient oracle 中免费读出。

### 5.1 阈值不可省略

取 D=[9,27]，p=3，希望观察模 9 的解。非零 Smith 因子是9，故 a=2，必须看约束模81。精确 kernel 是 {(-3t,t)}；模9只有9个解。

如果只在模9检查方程，81个向量全部通过，包括 (1,0)；它不可能提升到精确 kernel。穷举模81的6561个向量，再投影到模9，恰好只剩那9个真解。

这一提升定理处理有限个未知量和有限个方程。它没有把无限 Ism 塔变成一个既知有限图；这两件事在本记录中严格分开。

## 6. 定理 E：消去纯坐标层，保留 holonomy 与精度损失

给定有限连通图，每条边 e:u→v 带一个 A_e∈GL_d(Z_p)，未知量 X_v∈Mat_d(Z_p)，约束为 X_vA_e=A_eX_u。这里所有边都是同一 linear object 的实际 integral coordinate comparisons。

选定 spanning tree 和 root。沿树定义 P_v∈GL_d(Z_p)，P_root=I。树的方程等价于

    X_v=P_v X_root P_v^{-1}.

对非树边定义 H_e=P_v^{-1}A_eP_u，则余下约束恰为

    X_root H_e=H_e X_root.

这是解集的双射，在 Z_p 和每个 Z/p^n 上都成立；可逆性也等价。若另有 lattice/mark 条件，必须按 P_v 运输回 root 后保留，不能直接丢弃。

还可证明全大矩阵的非单位 Smith 因子与缩小后的 commutator 系统相同：先令 X_v=P_vY_vP_v^{-1}，并将每条矩阵方程左右乘适当的 P^{-1},P，均为 integral unimodular 变量/方程变化。树边变成 Y_v−Y_u=0。再用根变量与树差分作新变量，得到 d²(|V|−1) 个 unit pivots；消掉它们后恰是剩余 holonomy 方程。于是深度本身不造成额外 p-adic 精度损失。

适用边界：不是把真实 Θ-link 强行变成同一 holomorphic object 的坐标变换；非积分比较矩阵的 lattice indices、log 定义域、Ind3 包含和新的 source object 不能按此法消去。只有已经证实为 integral coordinate comparisons 的边才适用。

### 6.1 二十层精确实例

取20个顶点，每个 X_v 是2×2矩阵。用实际记录在证书中的 P_v∈SL_2(Z) 构造19条树边，最后一条边的 holonomy 为

    H = [[1,81],[0,1]].

原系统有80个标量未知数，80×80约束矩阵。消去后只剩4个标量未知数和 XH=HX。对 X=[[a,b],[c,d]]，约束等价于81c=0、81(a−d)=0。

精确整数 Smith 计算得到：原矩阵的非零因子为76个1与2个81，另有2个0；缩小矩阵为81,81,0,0。根解可取 [[1,2],[0,1]]，运输后的20个矩阵逐条满足原方程。

因此希望知道解模3²时，只需在模3^{2+4}=729检查约束。这是第5节的一般证明保证的准确阈值，80变量的蛮力枚举被消掉；不是根据这一个样本猜测对任意图成立。

## 7. 定理 F：实际小单位球上的 log 是可准确计算的有限块

令 K/Q_p 为有限扩域，赋值按 v_p(p)=1 归一化。取 c=1（p为奇数），c=2（p=2）。则

    log : 1+p^c O_K ↔ p^c O_K : exp

是互逆 bijections，且 v_p(log u−log v)=v_p(u−v)。因此 n≥c 时，它诱导有限商上的准确双射

    (1+p^cO_K)/(1+p^nO_K) ≅ p^cO_K/p^nO_K.

证明：对 z∈p^cO_K，log(1+z) 的一次项赋值为 v_p(z)，每个高次项 z^k/k 的赋值严格更大，因为 (k−1)c−v_p(k)>0。exp 的高次项由 v_p(k!)≤(k−1)/(p−1) 同样控制；在所选 c 上，两个级数收敛，形式幂级数的互逆及乘法/加法恒等式由收敛逐项成立。对 u/v 应用一次项严格支配，得 isometry。

一个统一而保守的计算阈值：计算 mod p^n 时，两级数都截断到 degree 2n−1 即足够。对 k≥2n，log 尾项有

    v_p(z^k/k) ≥ ck−v_p(k) ≥ k/2 ≥ n,

其中 v_p(k)≤k/2；exp 尾项在奇 p、c=1 时由 k−v_p(k!)≥k/2 控制，在 p=2、c=2 时更强。没有浮点误差参与。

若一个实际允许区域恰好是完整 coset u_0(1+p^cO_K)，其中 u_0 在既定 log 定义域，则其像恰为 log(u_0)+p^cO_K，仍可按指定精度计算。若只知道实际区域包含于该 coset，不能把整个 coset 的像当成真实内输出；只能用于外界。

同样不能对非单位 q 直接调用此命题，也不能在 log 前先取任意 Z_p-span：非线性操作不与第2节的 abstraction 自动交换。一个多段混合程序必须在各个非线性边界保留实际域与分支信息。

精确模型计算：Q_3 上模3^5，81个小单位 cosets、6561个有序对；Q_2 上模2^6，16个 cosets、256个有序对。逐项核对了有限 log 表的双射、isometry、乘法变加法及 exp 逆映射，均通过。

## 8. 两个不能靠计算层数补救的错误候选

### 8.1 “连续很多层稳定，因此无限源塔稳定”不成立

固定 Λ=Z_p²、L=pZ_p×Z_p，令 C₂ 由交换坐标生成。给定任意 T，构造两组递降 compact subgroups：

- A：每层都是 C₂；
- B：前T层都是 C₂，从T+1层起都是 {I}。

前T层的全部观察相同，而最终交群的 orbit hull 分别是 Z_p² 与 pZ_p×Z_p。因此仅凭 d、N、compactness 和任意长的观察平台，不能给一个适用于所有这类塔的有效截断深度。

更强的计算论边界也可直接证明：给一个任意机器，将第n层群定义为“机器在n步内未停则C₂，否则{I}”。每层都可有效计算。若有一般算法能决定无限交群的上述两种最终 hull，就能决定该机器是否停机。故不存在覆盖所有可计算约束塔的这种算法。

这不是 IUT 的不可计算性定理：其源塔有额外结构，可能提供专门的有效界或全塔作用构造。它只否定“用机器再多检查几层”作为普遍证明方法。

第3节的有限终止与此不矛盾：那里是一组固定作用反复生成的上升链，一步相等即已对所有作用封闭；这里随层数增加会出现新的约束，当前相等不控制未来。

### 8.2 分别存在的边见证，不等于相容路径见证

具体边仅有 start→middle_0 和 middle_1→finish。若将 middle_0,middle_1 合成一个抽象 middle，则抽象图出现 start→middle→finish，但具体图没有这条路径。

因此有限 quotient 不能只记录“某个 source representative 可到某个 target representative”。要准确合成路径，至少要证明：每条抽象边都可从其 source cell 的每个允许具体状态提升到目标 cell；对真正定义于全 cell 且在 quotient 上良定义的函数，这个条件自动成立。也可以保留足够的共享 χ、Kummer branch 与 guard 数据，避免错误合并。

这正是为什么本包允许消去纯坐标，而不允许消去实际 source branch 的相容条件。

## 9. 组合规则：怎样让多层计算准确，而不重新制造假分支

这里补一个一般但有用的有限观察定理。设控制图的具体状态为 X_v，有有限观察 π_v:X_v→A_v。每条允许边是部分函数 f_e:D_e⊂X_u→X_v，并满足：

1. D_e 是 π_u-fibres 的并，即域/guard 由有限观察决定；
2. 在 D_e 上存在一个有限函数 f̄_e，使 π_v∘f_e=f̄_e∘π_u；
3. 初始有限状态恰为实际初始集合的像；选择参数必须留在状态或边标记中，使以上两点真的成立。

则任意长度的抽象可达路径都有具体可达路径提升，且具体可达集的观察恰等于有限图的可达集。

证明：正向由交换关系逐步投影。反向对抽象路径长归纳：选实际初始点；在下一步，由 fibre-constant guard，当前实际点确在 D_e；应用 f_e 即得到下一指定观察。依次进行。若用关系而不是函数，也可将条件2替换成“每个 source representative 对每条抽象边都存在对应具体后继”的统一提升条件。

这给出明确的组合方式：实际小单位 log 块用第7节的有限商；固定 integral linear map 用矩阵模精度的作用；只含线性操作的终端块用第2–3节的格子饱和加速；有限相容条件的可提升性用第5节；纯坐标冗余用第6节消去。任意长度可达性随后是在一个固定有限图上求固定点，不能反过来把未证明存在的有限观察当成原输入条件。

不能把 Z_p-span 模直接喂给后续 log 或 guard。只有已经证明它们对该抽象准确时才允许，通常应在这些边界保留实际 residue-set relation。第2节的准确性只保证后续线性操作及最后 hull；这一限制是组合定理的实质要求。

最后的 hull 观察也有明确有限性：若 U⊂p^rΛ 且 p^sΛ⊂M(U)，则 M(U) 由 U 在 p^rΛ/p^sΛ 中的像准确决定，因为

    M(U)=span_{Z_p}(任取的 residue lifts)+p^sΛ.

因此在实际完整状态确有上述有限 quotient 的地方，最终 hull 真正化成了有限可达性与格子运算。若抽象选择丢了共享 χ 或 Kummer 相容性，第8.2节说明该组合立即可能失效。

## 10. 与真实源的接点及还没有解决的部分

### 10.1 已有源条件足以消费的部分

Ism 的 source 定义要求 G-equivariance 和所有规定 invariant lattices 的保持。在固定 finite-dimensional factor 的真实 rationalized/log realization 上，实际 Ind2 作用因此落在某个 Aut_{Z_p}(Λ_i) 中。III 的独立 direct-summand / tensor-factor 操作必须按原索引保留；在给定 finite tensor block 上可取它们实际保持的 tensor reference lattice Λ。

对于这个块里一个已构造的 integral region S 及实际 multiplication/transport A，取 L=M(A(S))。当它有界并张成全空间时，L 是 full lattice；与 Λ 比较得到 r,s。因此定理 B 的观察精度不是额外的 IUT 输入假设，而是该真实线性块的数据所决定的整数。

这说明：这个局部子问题不再需要无限精度地列举全部 Ism 作用或全部长字；它只需要确定模 p^{s−r} 下那些会改变最终 hull 的作用。第4节更进一步，允许仅证明足够多的真实内作用与一个计算外界，而不用完整分类该有限像。

### 10.2 剩下的是哪些具体数学问题

- 真实输入 A(S)、reference Λ、目标 O_E 和允许的路径/状态必须来自实际 Kummer/evaluation/log 构造，不能由任意标签或自由 theta 字段代替。本包没有为它们新增任意 inhabitant。
- 有限层中心化条件只给 K_N 外界。要用其中某个作用作下界，仍须构造真正的全塔作用，或证明该 residue class 可提升。Smith 定理只解决有限图，不解决无限个未知层。
- 即使局部 Ind2 orbit hull 已准确计算，也不能自行制造 Kummer/log/Ind3 的跨步骤相容性。应用第9节须核验真实 guard 和 finite quotient；实际无界 log 路径尚无该完整核验。
- 非阿基米德单块结果还需 source 规定的全局同步、uniform finite support、archimedean 一侧近似和原 normalization。以上没有被同一个局部 determinant 所代替。
- 原目标 ν(H)≥Q 的数值方向尚未得到原源计算证明。一个正确的有限化定理既不保证不等式成立，也不把它改成定义。

### 10.3 下一项已经缩成一个可执行问题

对一个固定的真实线性 block，先制作 (Λ,L,O_E,N) 的积分基数据，再同时计算一个可证明的真实内作用集 S 与有限层外约束群 K_N 的 hull。

若两端相等，即可关闭该 block 的完整 orbit-hull 计算；若不等，只保留不同的 field 分量和相应 residue conditions，研究哪些 residue classes 能由真正 Ism 实现。具体地，某分量的最小赋值是否能下降到给定阈值，只依赖第3节的有限像；于是缺口可写成有限观察上的“存在可提升源作用”问题，而不再笼统要求分类整个无限 Ism。

这里选择要提升的 residue class 应由内外 hull 差和 native q 的原读出方向决定。若得到的实际内作用仍不提供所需增量，就明确排除此候选；不靠添加坐标层制造增益。

## 11. 精确计算、复核与本包验收

脚本：`finite_observation_certificates_20261024.py`；输出：`C9-FINITE-OBSERVATION-CERTIFICATES-20261024.json`。使用 SymPy 1.14.0 和 Python integer/Fraction；无浮点数学断言。输入均为辅助命题的显式模型，不是已经构造的 IUT source-qualified Θ-data。

| 计算 | 准确结果 | 检查的数学点 |
|---|---|---|
| 同余格子与提前 hull | 原后像指数[1,0]，提前 hull 后像[0,0] | 不能丢坐标相关性 |
| 内外最终 hull 相等 | 内模 index 3，外模 index 1，hull 都[0,0] | 可只关闭最终观察，无须群/模相等 |
| 20维循环群轨道 | N=3，模27的实际群像20个；19次严格扩大，下一轮固定；一般界60，初始 index 界57 | 有界饱和与全部 orbit sum 一致 |
| 观察精度 | 同模27的 lifts 给同一 Z_p-lattice；只看模9则存在 hull 指数下降反例 | 精度上界有效，少一位一般不够 |
| 20层线性图 | 80变量→4变量；Smith 1×76,81×2,0×2→81,81,0,0 | 坐标层消去且精度损失不变 |
| 有限提升 | 枚举6561对；模81约束投影后9解，精确 kernel 也是9解；模9浅检查错误地给81解 | 必须保留 Smith 损失 |
| 小单位 log | 81+16个cosets，6817个有序对；log/exp、群律、isometry全部通过 | 非线性局部块有准确有限表 |
| 假平台与假路径 | 任意指定100层平台不能决定最后 hull；合并两中间态制造不存在的路径 | 有限测试不替代源提升/相容性 |

上述一般定理的依据是第2–9节的证明，不是模型通过次数。脚本提供可复算的精确构造、Smith 小矩阵变换证书、图边/frames、有限 log 表及全部 assert。没有将本轮0.3秒级别的计算包装成人类不可行的实际 IUT 全流程运算；重点是证明原本的巨大枚举可被严格消掉。

statement_dependencies：前包固定 source-qualified input 和实际 hull 定义；finite-dimensional source Ind2 realization/lattice preservation（用于源应用）；真实 global/normalization 条件继续 open。

proof_dependencies：DVR 上有限生成模/Smith normal form、lattice index 与 determinant、收敛 p-adic log/exp 恒等式；相关推导在本包展开。未使用新的 source-compatibility axiom 或修改目标。

消费者接入：P1 的固定线性块族构造与 P6 的最终 hull 计算获得准确有限观察、饱和和内外证书方法；未证明 C4→实际 IQ region map，未证明 fixed-q coverage。

剪枝：本 chat 不再把纯坐标深度、无限群字长度、裸 p-adic 精度猜测作为主要搜索维度；不恢复旧“任意 GL”路线；本次允许主动研究辅助定理，修订前包仅等待整条路线可行性的工作限制。没有删除源码/import，也不改变其他 owner 的任务。

验收状态：`statement_compiles=not_run`；`proof_body_checked=not_run`；`kernel_closed=not_run`；`comparator=not_run`；`project_build=not_run`；`independent_review=not_run (root self-review only)`；`target_accepted=false`。自然语言证明和脚本的精确 assertions 已检查；没有独立 agent 审查，也没有 Lean 修改。
