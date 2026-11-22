# 四步的真实源证明尝试：格子、Ism、hull、剩余类提升

任务 ID：n8-c9-four-steps-source-attempt-20261024；owner：当前 chat root；日期：2026-10-24；SHEAF 阶段1。用户要求直接用自然语言尝试证明上一答复的四步；不写 Lean，不派 subagent。

目标/消费者：n8-c9-output-region-source-route 的 P1/P6。固定原文完整合格输入、真实 log-theta 配置与 native q-pilot；先证明固定非阿基米德 Ind2 块的四步，再判断它对完整 fixed-q 比较的贡献。不得把整体目标改成弱输入上的一般条件定理。

复用：C9-FINITE-OBSERVATION-THEOREMS-20261024.md（SHA256 d1396a666ac97928cc667f4750aa15eaec9eb00252e21cfd62470762ed81a123）、BPS/允许区域两包研究和冻结源版本。只读相关源位置，不做全仓 inventory。其他 chat 已开始 FiniteObservationHull 形式化；本包不改其文件或任务。

读文件：IUT II Example1.8(iv) p.39；III Prop.1.2(vi)、Th.3.11(i)(Ind2)、Prop.3.1/3.4；IV Prop.1.1–1.2；Minamide–Tsujimura 的 Ism 分类论文最新版及其 local class field theory 证明。已有自然语言定义与实际归一化保持原范围。

写文件：本记录、同目录 C9-FOUR-STEPS-SOURCE-EVIDENCE-20261024.json、ism_scalar_certificates_20261024.py、C9-ISM-SCALAR-CERTIFICATES-20261024.json；tmp/pdfs/ism-scalar-20261024 下原文快照/文本；root 所有节点 n8-c9-output-region-source-route.json；AUDIT_LEDGER/STATE/queue 追加。集成与构建不适用。源文件/既有证明记录不覆盖。

待核：新检索到 Minamide–Tsujimura Th.7.4 将 Ism(G_K) 分类为 Z_p^×。若与原文定义完全一致，则真实 Ind2 的有限像与提升直接解决，而且固定 holomorphic block 的 hull 不因它扩大。须检查最新版、定义、张量/直和索引与后续 log/Ind3 限制，不能直接宣布整个输出过程平凡。

验收：给出四步各自的实际构造、自然语言证明、源依赖及剩余边界；精确计算仅作证书，不当原源输入验证。Lean/kernel/comparator/Project/独立审查未运行；root 自审；target_accepted=false。

状态：固定非阿基米德 Ind2 块的格子构造、有限内外作用比较和剩余类提升已给出自然语言证明；Ind2 对最终 holomorphic hull 的体积增量严格为零。完整 P1/P6、跨 Θ-link 的 fixed-q 比较仍未证明。下列结论替代前包关于“仍需搜索未知 Ism 非标量有限像”的下一步，不撤销一般有限观察定理。

## 1. 实质改变路线的外部定理及定义对应

Minamide–Tsujimura, Anabelian Geometry for Henselian Discrete Valuation Fields with Quasi-finite Residues：

- 最新作者版：https://www.kurims.kyoto-u.ac.jp/~stsuji/AnabelianGeometryforHenselianDiscreteValuationFieldswithQuasi-finiteResidues.pdf
- 77页版本；下载于2026-10-24；PDF元数据日期2026-06-06；SHA256 fbdec753e5b9f9f4fa30fa52b5a4d5b297902034bea248f418509bc831bd1ad4。作者网页当日列为 to appear in Amer. J. Math.。此处没有声称期刊最终版本已发表。
- Definition7.3，印刷p66：Ism(G_K) 是 U^μ_{K^sep} 上的 G_K-equivariant automorphisms，保持每一个有限可分 F/K 对应的 U_F^μ lattice。
- Remark7.3.1，p67：有限剩余域时 U_F^μ≅O_F^×/μ(F)，并明确对应 IUT II Example1.8(iv)。
- Theorem7.4，p67：若 G_k 不是 pro-prime-to-p，Z_p^×→Ism(G_K) 为双射。有限 K/Q_p 的剩余域有限，G_k≅hat Z，满足条件。
- Proposition6.4，p59：保持所有开子群的无扭交换 pro-p 群自同构为单位标量。

2023年 RIMS1973 版本已包含同一分类；此次是补上此前未利用的既有成果，不将该分类宣称为新发现的数学定理。

与源匹配的三个位置：II Example1.8(iv) p39 给出上述 Ism 定义；III Prop.1.2(vi) pp32–33 将其用于 Galois 等变的 log-shell 识别轨道；III Th.3.11(i)(Ind2) p154 在每个 tensor factor 的每个 direct summand 上取独立 Ism。不是用 GL、一般 G_K 中心化子或仅保持一个 lattice 的群来代替源群。

这里固定一个实际 holomorphic realization 和 Galois 标记。Ind1 的 Galois 群识别/置换不是这个固定 G_K 的 Ism，不能一起删掉；无穷处也不属于本分类的断言范围。

## 2. 第一点：实际的 (Λ,L,O_E) 与有限观察精度

量词：给定原文合格输入中的实际有限非阿基米德 block，已经固定其 realization、源 Gaussian generator 及原生积分结构。该量词没有加强为“从任意弱 BPS 构造原文完整 realization”。

写 E=⊗_{i=0}^j K_i=∏_a E_a，均在 Q_p 上，O_E=∏_a O_{E_a}。O_E 是 normalization 后的积分结构，不擅自改成 ⊗_i O_{K_i}。

令 c=1（p奇）或2（p=2），J_K=log(O_K^×)，I_K=p^{-c}J_K。采用1/(2p)的原文惯例得到同一 Z_p-lattice：p奇时只相差一个 Z_p 单位。令 Λ=⊗_i I_{K_i}，按源指定的 direct sums 组装。

证明 J_K 是可由有限数据确定的 full lattice：

1. log 与 exp 在 1+p^c O_K 和 p^c O_K 上互逆，故 p^c O_K⊂J_K。
2. 取有限商 O_K^×/(1+p^c O_K) 的代表 η_t。则 J_K=p^c O_K+Σ_t Z_p log(η_t)。log 是连续群同态，J_K 紧，因而是闭 Z_p-submodule。
3. 取 h，使每个 η_t^{(q_K-1)p^h}∈1+p^c O_K，其中 q_K 为剩余域基数。这样的 h 存在，因为模深单位群的主单位部分为有限 p 群。故 J_K⊂p^{c-h}O_K。
4. 因此 J_K/p^cO_K 是有限群 p^{c-h}O_K/p^cO_K 的一个子群。用
   log η_t=((q_K-1)p^h)^{-1}log(η_t^{(q_K-1)p^h})
   计算其有限像即可。右侧深单位 log 必须多计算 h 位精度；除法不免费。
5. 对这些有限像选代数坐标代表 v_t，得到精确等式 J_K=p^cO_K+Σ_t Z_p v_t。误差全在已包含的 p^cO_K 中，因此无需决定某个一般 p-adic transcendental log 是否精确为零。

由此 O_K⊂I_K⊂p^{-h}O_K。有实际局部域表示和整数环基时，用有限商/Hermite–Smith 计算可构造 Λ 的基。

取实际 Gaussian value g_j，作用放在指定 factor：

    A=id⊗…⊗m_{g_j},   L=A(O_E).

这是原生 holomorphic 积分区域；一般 log 分支的 S_χ 必须依照前包程序生成，不能一概替换为 O_E。III Prop.3.1(ii)、3.4 及前包中的实际积分结构解释是本构造的来源。

设 B_Λ、B_O 为两组基，C=B_Λ^{-1} A B_O。A 可逆，故 L 为 full lattice。若 C 的 Smith 指数为 α_1≤…≤α_D，取 r=α_1、s=α_D，即

    p^sΛ ⊂ L ⊂ p^rΛ,   N=s-r.

这直接证明第一点。只要目的是有限观察，C 与 C^{-1} 的认证赋值界也足够，不必先求最小 N。N=0 时 L=p^rΛ 已被所有保持 Λ 的作用固定；下文有限探针取 n≥1，通常令 n=N。

此处已经消除了“lattice 随便假设存在”的问题，但没有声称一个局部模型已验证全部 initial Θ-data、global gluing 和 q-pilot。

## 3. 第二点：全源塔上的真实内作用

对每个有限 F/K，写 M_F=O_F^×/μ(F)，按加法记其 Z_p-module；其秩为 [F:Q_p]。给定 u∈Z_p^×，在每个 M_F 上取 x↦ux。

这些映射保持 M_F，与有限扩张的嵌入、G_K 作用相容；逆映射为 u^{-1}。故它们共同定义整个源塔上的 Ism 元素，而非仅一个有限商上的候选矩阵。在乘法记号中是单位模根单位上的 p-adic power action；在 log 坐标中是乘 u。无需定义非单位 q 的 u 次幂。

因此所有单位标量都给出真实内作用。下一节证明只用有限个真实范数条件即可排除全部额外有限候选。

## 4. 第二、四点的核心：2d−1 个真实范数条件精确确定有限像

这是一份适合当前计算任务的有限化证明，来自标准局部类域论和上面的源 Ism 定义。我们没有声称这一有限表述在文献上首次出现。

固定 F/K，M=M_F，秩 d，取其 Z_p 基。对任意开子群 C⊂M，令 π_μ:O_F^×→M 为商映射，选 uniformizer ϖ_F，并设

    H_C=⟨ϖ_F⟩·π_μ^{-1}(C) ⊂ F^×.

H_C 是开有限指数子群。局部类域论的存在定理给出有限阿贝尔扩张 F_C/F，其范数群恰为 H_C。由

    N(F_C^×)∩O_F^×=N(O_{F_C}^×)

得模根单位后的范数像恰为 C。这一步使用的标准供体是 Milne, Class Field Theory, I Theorem1.4 与其前 Lemma1.3（印刷p22），不是待证 IUT 比较。

若 σ∈Ism(G_K)，它与 Gal(F_C/F) 的作用交换，又保持 M_{F_C}。范数是这些 Galois translates 的和，因此

    σ_F N^μ_{F_C/F}=N^μ_{F_C/F} σ_{F_C}.

于是 σ_F(C)=C。这里 F_C 可以嵌入同一个 K^sep；它只是测试源定义本来就量化的有限扩张，不是给 initial Θ-data 添加额外假设。

现在只取 n≥1 和下列 2d−1 个 C：

    C_i={x : x_i≡0 mod p^n},                    1≤i≤d;
    C_{1i}={x : x_1−x_i≡0 mod p^n},           2≤i≤d.

每个商 M/C≅Z/p^nZ。因此上述 F_C/F 是度数 p^n 的循环扩张；由于 uniformizer 已在范数群中，它是全分歧扩张。借助 Lubin–Tate reciprocity，也可将它具体实现为一个有限 torsion extension 的固定子域。

令 K_n 为 GL_d(Z/p^nZ) 中保持这些子模的共同稳定子。证明 K_n=(Z/p^nZ)^×·Id：

- 对 i≠j，e_j∈C_i。保持 C_i 迫使矩阵第(i,j)项为0，所以矩阵为对角阵。
- e_1+e_i∈C_{1i}。保持 C_{1i} 迫使第1和第i个对角元相等。
- 可逆性迫使共同对角元为单位。反向包含显然。

源实际有限像包含于 K_n；反过来，每个 u_bar∈(Z/p^nZ)^× 取任一 p-adic 单位提升 u，由上一节在整个塔上构造的标量作用实现。故

    真实内作用的有限像 = 源 Ism 的有限像 = K_n.

这同时完成真实外约束和全部剩余类提升。没有使用“有限层可解便自动全塔可解”：提升给出了显式全塔公式。

若希望直接得到无限层分类，让 n 变化即可知每个 σ_F 是一个 Z_p 单位标量；在 F⊂F' 的嵌入上相容，且 M_F 非零无扭，迫使所有标量相同。这给出 Theorem7.4 的有限局部域特例证明，不依赖其更一般无限剩余域部分。

## 5. 第三点：按源的 tensor/direct-sum 结构比较 hull

源允许每个 factor 的每个 direct summand 取独立 Ism。对 coarse tensor tuple τ=(v_0,…,v_j)，其作用为

    u_τ=∏_{i=0}^j u_{i,v_i} ∈ Z_p^×.

因此在 E=∏_τ E_τ 及其 finer field decomposition 上，作用是乘一个 ε∈O_E^×。这里同一 coarse tuple 的 finer field factors 共享相应标量；没有把它扩大成任意独立 O_{E_a}^× 作用。

对任何固定目标 holomorphic frame 中的有界 U，非阿基米德 product hull 为各 field component 上最小含零整数球之积，等价于相应 O_E-submodule hull。因此

    Hull_E(εU)=ε Hull_E(U)=Hull_E(U).

第一式来自 O_E-linearity，第二式来自 ε 为 O_E 单位；也可逐分量直接看所有点的赋值不变。

于是对固定源位置的一次完整 Ind2 orbit：

    Hull_E(⋃_{σ∈Ind2} σU)=Hull_E(U).

因为每个 σU 已在 Hull_E(U) 中，而 identity 作用包含原 U。真实内作用即使只取 identity，所得最终 hull 也已等于准确外作用的 hull。不存在还需靠非标量 residue lift 扩大的 hull 差。

对于原生区域 L=A(O_E)，L 是 O_E 的可逆 fractional ideal，所以 εL=L，连区域本身也固定。对于跨 coarse components 有耦合的任意 Z_p-lattice，不声称区域本身固定；本段一般断言只是最终 product hull 固定。

若同时运输 action 与积分资料，(σAσ^{-1})(σS)=σ(A(S))。固定 block 中 A 为指定 factor 上的乘法作用，与单位标量作用交换；没有暗中改变 Gaussian exponent 或另选 S。

结论：固定非阿基米德 Ind2 块的 hull 增量、相应 normalized log-volume 增量均严格为0。这排除了“通过寻找非标量 Ism 获得正体积增量”的具体路线；不排除 Ind1 或其他源步骤的作用。

## 6. 体积读出：能证明什么，不能从中多拿什么

设 D=[E:Q_p]，d_j=[K_j:Q_p]。对指定 factor 的实际 A，有

    det_Qp(A)=Norm_{K_j/Q_p}(g_j)^{D/d_j}.

故对同一 Haar reference 下的正有限体积区域 S，采用每维归一化 ν=(1/D)log μ，

    ν(A S)−ν(S)=(1/d_j)log|Norm_{K_j/Q_p}(g_j)|_p.

这个公式保留原生区域的 reference term；不能把 ν(S) 随意删掉。乘 ε 的 determinant 绝对值为1，且上述 hull 完全相同，所以它不改变同一源 normalization 下的读出。

由此可证明 fixed q 标记已经关联到某个输入区域后，在此固定线性 Ind2 步骤中的体积读出不变。然而“native q 的指定体积类已属于跨 Θ-link 生成的完整输出族”仍需另外证明。局部单位标量、determinant 等式及同一容器不产生这个关联。

尤其不能在后续非线性箭头前无条件消去 Ind2。必须区分：

    log(x^u)=u log(x)       （单位幂作用与 log）；
    log(ux)=log(u)+log(x)   （同一个域里的乘法后取 log，须在定义域内）。

两种表达对应不同的源位置。分类定理控制的是固定 log 模块识别的 Ism；连续多条 log-link 的允许域、Ind1 识别和 Ind3 控制仍须按实际箭头核对。

这条边界还可以进一步精确计算，而非只留下警告。若在同一实际局部域 K 中，非空集合 U⊂O_K^× 先受字段乘法 x↦ux（u∈Z_p^×），随后进入通常的 p-adic log，则

    ⋃_{u∈Z_p^×} log(uU) = log(U) + log(Z_p^×)
                         = log(U) + p^c Z_p.

单位标量保持 log 的单位定义域；等式由 log 的群同态性质逐元素给出。取最终 O_K-hull，有

    Hull_K(⋃_u log(uU)) = Hull_K(log U) + p^c O_K.

证明最后一式时，右边显然包含左边；由于0∈p^cZ_p，左边包含log U；再固定一个x∈log U，以(x+b)−x恢复每个b∈p^cZ_p，得到反包含。此处非空条件已明确。

例如 K=Q_3、U=1+9Z_3，则 Hull(log U)=9Z_3；若先允许所有单位标量乘法再log，最终 hull为3Z_3，读出增加log3。这是实际局部运算的精确例子，说明本包“Ind2增量0”严格限定于固定最终线性块，不能用于任意带后续log的长路径。它不是对原文某个完整分支顺序的认定；实际源位置仍须核对。下一步可以据此判断某一源箭头需要标量消去，还是需要保留明确的p^cO_K修正。

同理，IV Prop.1.2 对更大的 lattice automorphism group 给出的 uniform outer bounds 仍有效。该群比实际 Ism 大并不构成原文矛盾；不能将这种上界群反过来当可实现内作用。

## 7. 已实际执行的精确证书

脚本 ism_scalar_certificates_20261024.py；输出 C9-ISM-SCALAR-CERTIFICATES-20261024.json；退出码0，所有 assertions 通过。以下是实际局部域/有限算术，不是完整全局 Θ-data 的实例。

例A：F=Q_3(i)，i²=-1，为非分歧二次扩张。O_F/27O_F 中共有648个单位。以

    log(u^8)/24 mod9 = x+y i

识别主单位模相应深单位群，三个 character 为 x、y、x−y。精确计算得到81个像，每个纤维8个元素；三个 kernel 各72个元素；逐一验证648²=419904个乘法对的 character 加法关系。

用 Lubin–Tate polynomial f(T)=3T+T^9，primitive level3 的方程为 3+f(f(T))^8=0，度648。令 y=T^8 后压缩为

    3+y(9+3y+y(3+y)^9)^8.

脚本精确验证该多项式为 Eisenstein，并保存全部82个压缩系数。Lubin–Tate 定理将上述三个 kernel 的固定子域实现为三个实际循环度9扩张；它们的范数条件正是本证明的三个探针。脚本检查的是有限算术，标准 reciprocity 定理由文献供体提供，未宣称脚本重证了类域论。

在 GL_2(Z/9Z) 的3888个矩阵中，这三个稳定条件精确留下

    Id, 2Id, 4Id, 5Id, 7Id, 8Id.

全部由相应整数单位的全塔作用提升。完整 character 表、幸存矩阵及排除见证已写入证书。

例B：K=Q_3(π)，π²=3。取 U_r=1+π^rO_K。log(U_2)=3O_K；U_1/U_2 由1+π生成，而 log(1+π)≡2π modπ²（级数中n=1,3贡献这两个π，其余项赋值至少2）。故 J_K=πO_K，I_K=(1/3)J_K=π^{-1}O_K。

局部 Gaussian profile 取 a=π、a^{10}=3^5、j=2、g=a^4=9；L=9O_K。相对于 Λ=I_K 的基(1,π/3)，L 的基矩阵为 diag(9,27)，所以 r=2、s=3、N=1。

采用 μ(O_K)=1，μ(L)=3^{-4}，每维读出 ν(L)=−2log3。若先把 μ(Λ)归一化为1，读出为−(5/2)log3；加回 reference correction +(1/2)log3 才恢复原值。Ind2 两边都增量0。这个例子也验证不能丢掉 reference correction。

例B只满足写出的局部 Gaussian 代数 profile；没有声称 a、q 和这一个 K 已实现完整原文 global Θ-data。例A的扩张是源 Ism 定义允许的真实辅助测试扩张，无须成为 global initial-data 的新输入。

## 8. 四步状态、剪枝和下一项

| 原步骤 | 本包所得 | 仍未完成的范围 |
|---|---|---|
| 1. 构造 Λ,L,O_E,N | 固定实际 realization 的原生 block 已自然语言构造；两个实际局部域的精确计算完成 | 完整所有 log/Ind3 分支的 source family 尚未构造完 |
| 2. 真实内作用及有限外约束 | 全塔单位作用；2d−1个真实 norm probes；有限内外像相同 | 不替代 Ind1 的群变化/全局同步 |
| 3. 比较 hull | 固定非阿基米德 Ind2 的 hull 精确相等，增量0 | 不得提前穿过后续非线性 log/Ind3 取 hull |
| 4. 差类提升及 native-q 比较 | 所有有限候选都有显式全塔提升；此块无 hull-visible 差类 | native q 经完整源复合后的体积类覆盖仍 open |

撤下的活动子路线：在固定非阿基米德 Ism 中搜索非标量 residue，试图由它们制造正 hull 增量。此前一般 finite-observation、inner/outer sandwich、path lifting 定理仍正确，可供真正存在其他作用的块使用；不覆盖或撤销其他 chat 的相关数学代码。

下一可执行数学任务：沿 III Remark3.10.2/Prop.3.5 的实际分支，固定 Gaussian generator 和原生积分资料，定位 Ind2 的插入位置；在每一个最终线性 Ind2 块使用本包消去它。随后明确写出尚存 Ind1/log–Ind3 箭头对(实际区域，pilot 标记，reference 读出)的运输关系，先证明一个箭头的源相容性。不得把它写成待证结论同义的 eta-compatible 假设。

最终目标、量词和原文 normalization 未改变。本包提供确定的缩减而非完整 fixed-q/Cor3.12 证明。statement_compiles、proof_body_checked、kernel_closed、comparator、Project build、independent_review 均未运行；仅 root 自审和精确 Python 计算；target_accepted=false。

## 9. 供体链接

- 原始 Ism 定义：[IUT II Example1.8(iv)](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf)。
- 实际使用位置：[IUT III Prop.1.2(vi), Th.3.11(i)](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf)。
- 分类及定义对应：[Minamide–Tsujimura, Definition7.3, Remark7.3.1, Theorem7.4](https://www.kurims.kyoto-u.ac.jp/~stsuji/AnabelianGeometryforHenselianDiscreteValuationFieldswithQuasi-finiteResidues.pdf)。
- 范数子群的实现：[Milne, Class Field Theory, I Theorem1.4](https://www.jmilne.org/math/CourseNotes/CFT.pdf)。
- 具体有限扩张构造：[Kedlaya, §4.6, Corollary4.6.13 and Theorem4.6.16](https://kskedlaya.org/cft/sec_lubin-tate.html)。
