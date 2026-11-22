# C9：固定 gluing 的 factor swap 与共同末端运输

任务 ID：C9-FIXED-GLUING-SWAP-20261025；owner：当前 chat root；2026-10-25。用户要求自然语言研究、单线程、不写 Lean。

阶段/消费者：SHEAF stage1；n8-c9-output-region-source-route 的原 P6 严格亏损反证。原目标为每个原文合格完整 C、固定 native q/BPS/gluing/目标列/normalization 的完整最终输出族满足 ∀ε>0 ∃E, ν(E)>Q_C−ε。不以一个方便的局部输入替换它。

前轮分类：progress。上一包 C9-PROCESSION-ORBIT-20261025.md（SHA256 b7a45e8c28bbe42461476ec0b4eb2acf889a0202a9439dde78b3410e34e329a5）证明固定容器的 min 轨道公式与共同运输下实际 additive span 的下界；没有证明共同运输的源接入。该限制保持。

本包具体目标：展开恒等分支与一次两因子 swap，在同一完整源配置中追踪实际 Kummer、evaluation、积分输入和 container identification；判定是主动区域族还是逆耦合被动换框架。区分 ①同列/同容器 Ind1 轨道，②跨 Θ-link 的整体 APT，③由实际同构实现的末端加性运输。不得把三者混为一条自由线性箭头。

精确读：IUT I §0/Def4.10/Prop6.9 的已核内容；III Prop3.2/3.4/3.5/3.9、Rmk3.10.2、Thm3.11(i)-(iii)、Rmk3.11.1(iii)-(iv)、Cor3.12 的输出定义；仅跟随这些对象的 II 中引用。已有 frozen research 复用。只在这份新问题需要时读补充文章，不重新泛读。

精确写：本文件、同前缀 EVIDENCE、必要的精确算例脚本/证书；owned DAG 新字段；AUDIT_LEDGER/STATE/queue 仅追加。其他 owner 和 Lean 文件不动。集成：当前 root；构建不适用。

statement_dependencies：固定源 gluing、实际 procession、Kummer/evaluation 与单位域、目标 packet 和原 log-volume。

proof_dependencies：源索引作用和图自然性；Ind1 saturation 与给定 container poly-isomorphism 的关系；同一 BPS 的关联保持；真实 additive-span 体积计算。源允许的输入不是缺口；未证的自然性/关联不能改为新增假设宣布原目标成立。

验收：一个逐箭头的源构造/严格反驳，及其对原反证的实际影响。自然语言自审和精确算例另报；Lean/Project/comparator/独立审查未运行；target_accepted=false。

状态：本包自然语言研究完成。共同末端 packet 同构对完整原 Ind1 轨道的应用已由源定义推出；没有把整体 APT 当成集合映射。实际 tame tensor 积分格下界已算出。原全局 P6、均匀赋值情形和固定 q 体积类的最终比较仍未证明。

## 1. 对上一包悬而未决问题的判断

上一包担心：对不同 factor permutations τ，末端映射是否被迫改成 Tτ^−1，导致一切增益消失？

本轮结论是：对 III Cor3.12 所定义的全部可能像之并，这种逐支抵消不是必须发生的，也不能用它删掉完整 Ind1 轨道。可以选择一次末端 packet 同构 T，并对整个轨道使用它。此结论是 III Prop3.2/3.9、Thm3.11(i) 的原有 functorial packet 构造和 Ind1 定义的推论；不是新增一个「存在兼容 T」假设，更不是原 q 比较已经成立。

这里必须区分：

- 固定 Θ-link/BPS gluing，及其中被指定的 q-pilot；
- 该 gluing 在 mono-analytic core 上的同构；
- 输出 procession 的各 capsule 内部的 label presentation。

改变最后一项不必改变前两项。尤其，不能在原定义之外要求一个高阶 capsule 中选定的 core 嵌入逐点不动：I Def4.10 的相邻箭头包括全部 capsule-full poly-morphisms，不是另指定的一条旗标。

## 2. 共同末端映射的逐项构造和作用

固定完整源 C、源列 0、目标列 1，以及所研究的实际 row/log-Kummer realization。记实际 mono-analytic processions 为 P_0、P_1，tensor-packet 构造为 Q。它在一个 capsule 上就是按原地方作 direct sum、再按 capsule 因子作 tensor product；相应态射由实际 prime-strip 同构逐因子诱导，见 III Prop3.2。

原固定 Θ-gluing 在 coric unit/prime-strip 上诱导同构 η。II Cor4.10(iv) 和 Cor4.11(i)–(iii) 给出该 core 的 full poly-isomorphisms；III Cor2.3 的径向/核心数据显式允许核心同构，并给出其 fullness。III Thm3.11(i) 末尾将此同构延伸为 compatible poly-isomorphisms

    P_0 ≅ P_1，Q(P_0) ≅ Q(P_1)，

并与 core P_{0,1}≅P_{1,1} 相容。选择其中一份代表 Φ，其 core 代表为原 η。不能改 η 去实现希望得到的体积。

这一步的「延伸指定 η」也可直接展开，避免仅从 Nonempty 推出有指定限制的同构。对列 s=0,1 的每个 capsule 因子 P_{s,j,i}，选源中已有的 mono-analytic 副本识别 a_{s,j,i}:P_{s,1}→P_{s,j,i}；1-capsule 的 a 取恒等。令相应因子箭头为 a_{1,j,i} η a_{0,j,i}^{−1}，取 index bijection 为恒等。I Def4.10 的态射定义逐 capsule 接受这些 full-poly 代表，而无另指定的固定嵌入旗标，故它们组装成 core 代表恰为 η 的 Φ。这里的副本识别来自实际源 prime-strips 的 isomorphisms，不是从裸向量空间维数相同推出来的任意线性映射。

固定源和目标的实际 Kummer packet identifications κ_0、κ_1，则在 holomorphic realization 坐标中得到

    T = κ_1^−1 ◦ Q(Φ) ◦ κ_0。                              (8)

这是明确指定实际箭头后的复合。它连续、加性，按 III Prop3.9(ii) 及 Thm3.11(ii)(a) 与原 packet log-volume 相容；各 tuple 块和地方权重也按原构造运输。它不被声称为环同构，不被声称直接运输整个跨 Θ-link APT，更没有由此推出 native q 被送成哪个区域。

现在选取一份完整 procession 的 capsule permutation γ：在 1-capsule 的代表选择为恒等，在高阶 capsule 按上一包的循环置换选择；分量同构取同一地方的实际副本识别。严格地说，capsule-full poly-morphism 在 1-capsule 仍是一整份 full poly-automorphism；这里选择其恒等代表，而不是把 full poly 改成单元素对象。

I §0 的 poly-morphism 复合按全部可复合代表的 Cartesian product 定义，I Def4.10 在不同 capsule 上未加入逐点固定旗标的约束。因此这些代表可以选择；它们不需要把 Φ 同步改成 Φγ^−1。III Rmk3.11.4(iii) 又明确说明：Ind1/2 在 evaluation 以前不改变所用 geometric containers，而作用于 evaluation 后的 packet 表示。这不是将源 theta 函数或 q 参数另换一份。

对完整表示数据中的作用 A、积分资料 S，γ 的作用为

    A ↦ Q(γ) A Q(γ)^−1，S ↦ Q(γ)S，

所以实际输出变为 Q(γ)(A(S))，而不是只换标签不换点。若在源 holomorphic coordinates 中将 Q(γ) 写成 τ，则恒等分支和交换分支在目标中的输出分别是

    T(R)，T(τR)，                                         (9)

这里使用同一个 (8)。对多个 γ 同样成立。

集合层面的准确理由：Ind1 让全部可能输出族 U_0 在相应自同构下饱和；functoriality 给出

    Q(Φ)(Aut(P_0)·R)
      = (Φ Aut(P_0) Φ^−1)·Q(Φ)(R) ⊆ U_1。                 (10)

其中只需取保持指定 core 代表的子族即可。III Cor3.12 proof(xi-b) 写出的 U_0≅U_1 正是这份 packet 同构在完整可能像族上的限制；此处仅使用该构造/包含，不使用 (xi-f) 的 q 不等式。

选择 Tτ^−1 并同时选择 τR，确实可得到原来的 T(R)。但这只说明存在一类抵消的代表选择；不说明其他合法复合 T∘τ 被删除。把所有允许代表的复合限制为这条逆耦合子关系，会改变原 full-poly/Ind1 输出族的量词。

源使用边界：这里的 source-relative 证明复用 III3.11 的实际 packet functor、原 Ind1 饱和和所述 functoriality；没有在本包重新证明它们引用的全部 anabelian 定理，也没有宣称 Lean 中的自由 theta-interface 已因此接入。若项目实现只有逐支 Nonempty 同构而没有这些实际原构造，它仍不能调用本结果。

## 3. BPS 关联图与 packet 图不能混为一张图

本轮按 PDF 阅读流程目视核对了 III 原 PDF 第152、154页。Rmk3.10.2 的图两行分别是

    env → gau → LGP → lgp，

垂直箭头都是向上的 Kummer identifications；它说明 lower evaluation/tautological maps 是 upper étale evaluation/natural maps 经相应 Kummer 箭头共轭得到。Rmk3.11.1(iii) 的 IPL 复合先逆走前两个 lower arrows，再上行，再走三个 upper arrows。

这个图保留原 pilot 与原 BPS 的来源。它不说把输出 capsule 的每次位置置换都逆作用到固定目标 packet 坐标。packet 末端图则是第 2 节的 κ_0、Q(Φ)、κ_1。两图由原 functoriality/核心兼容相接，但不能把 BPS 对象的一个抽象同构，直接当作保数值的向量丛 determinant 同构。

因此本轮消除的是「共同末端 packet 映射不存在，可能只能逐支抵消」这一个疑点；未消除「最终 hull/determinant 仍与输入 q 的指定体积类有多强关联」的原核心问题。

## 4. 保留真正的积分输入和输出基

在一个源 holomorphic realization 中，Gaussian/LGP 作用由 III Prop3.4/3.5 构造。III Example3.6(ii) 的 fractional ideals 是实际 local integer modules，Prop3.7(v) 与 Def3.8(i) 用实际 splitting generator 生成 pilot 的这些理想。

固定 p 和 tuple (v_0,…,v_j)，取

    D_v = O_{K_{v_0}}⊗_{Z_p}…⊗_{Z_p}O_{K_{v_j}}
      ⊆ O_{E_v}，E_v=⊗_{Q_p}K_{v_i}。

本包只取这些实际积分 tensor 的像作为下界证书，不把 D_v 替换为 O_{E_v}。被标记的 Gaussian generator 作用在第 j 因子，输出为 G_j D_v；对 τ 后成为 τ(G_j)D_{τv}。其基向量是实际乘法 G_j(e_0⊗…⊗e_j)，不是由所需体积反解的一组数值标签。

单位域也有保守的直接实现：在 p 为奇数时，任意 z∈O_K 的 pz 都可写成 log(exp(pz))；exp(pz) 在原实际 principal-unit 域内。逐因子 tensor 后得到 p^{j+1}D_v。乘 Gaussian 发生在该单位/log packet 表示已经形成以后；没有把非单位 q 放进 p-adic log。p=2 应换 p²，本包 tame 数值例限于奇 p。

后一个小域提供更小的可追踪积分子区域。我们只利用它的点被完整输出 hull 包含，不声称每次缩小都保留同一个 primitive pilot 的体积，也不把原 log-shell 的外包络整体冒充一个实际原始像。

对 (9) 的一批真实输出取加性生成格 L。上一包已证，目标 holomorphic hull 对加法和 Z_p 标量封闭，因此

    T(L)⊆H_{C,j,p}，ν(H_{C,j,p})≥ν(L)。                   (11)

本包把 (11) 所需的共同 packet 运输接回第 2 节；满秩、有界性由上述实际积分格与 Gaussian 非零性给出。此结论仅是有限处下界；无穷处读出另留，不把球当加性子群。

## 5. 源相关的 tame 分歧：精确算出实际加性格

上一包四维模型不能忽略 IUT I Def3.1(c) 的条件 ℓ 与坏地方 q-order 互素。事实上，这通常迫使 K/F 在所选坏地方有 ℓ-tame ramification。本包使用与这一条件相容的局部类型，而不再假设坏地方 K=Q_p。

设 p≠ℓ 为奇素数、μ_ℓ⊂Q_p，且所研究 bad local field 为 tame totally ramified cyclic extension K/Q_p，次数 e=ℓ。取 uniformizer π 满足

    π^e=p u，u∈Z_p^×，O_K=Z_p[π]。

实际 qhat 有 ord_p(qhat)=b/e，b>0、e∤b；Gaussian g_j 的因子理想等于 π^{b j²}O_K，因为其差别只是该实际 field 因子的单位。每个因子上的单位乘法保持实际 tensor order，所以没有丢掉积分域条件。

对 r 个这样的 bad 因子，写

    D_r=O_K^{⊗r}，E_r=K^{⊗r}≅K^{e^{r−1}}。

在 D_r 的实际 Z_p 基 π_1^{a_1}…π_r^{a_r}（0≤a_i<e）中，设 n=q e+t，0≤t<e。乘 π_i^n 将基向量重新排列，并在输出坐标 a 上引入系数

    p^{q+1_{a_i<t}} × 一个 Z_p 单位。

于是各因子实际输出的和

    L_{r,n}=Σ_{i=1}^r π_i^n D_r

在坐标 a 上恰有指数 q+1_{所有 a_i<t}。满足后一条件的基坐标有 t^r 个，故

    length_{Z_p}(D_r/L_{r,n})=q e^r+t^r。                 (12)

这是真实乘法矩阵的计算，不是先取 hull 后反推矩阵。

还须保留 D_r 与 integral closure 的差。以第一个 K 为系数域，将其余 π_i 送到 ζ^{s_i}π；相应 evaluation matrix 是 r−1 份 Vandermonde matrix 的 Kronecker product。ζ 的互异差为单位，每一份的 π-adic determinant valuation 为 e(e−1)/2。由 tensor determinant 公式得到

    length_{Z_p}(O_{E_r}/D_r)
      = (r−1)(e−1)e^{r−1}/2。

原 degree-normalized log-volume 因而是

    ν(D_r)/log p = −δ_r，δ_r=(r−1)(e−1)/(2e)，
    ν(L_{r,n})/log p = −δ_r−q−(t/e)^r。                  (13)

unit u 不改变 p-adic index。公式也可带上 unramified extensions；它们不增加 different，原 degree normalization 消去共同次数。

还可从 (12) 提取一份不会被共同 T 抵消的正整数证书。令 R_1=π_1^nD_r，则 R_1⊆L_{r,n}，且

    length_{Z_p}(L_{r,n}/R_1)
      = n e^{r−1}−(q e^r+t^r)
      = t e^{r−1}−t^r。                                  (13a)

当 r≥2 且 0<t<e 时，(13a) 严格为正。连续加性同构 T 自动是 Z_p-线性的，因而诱导商群同构 L_{r,n}/R_1≅T(L_{r,n})/T(R_1)，该长度无法被同一 T 消掉。对应的 normalized volume 增量恰为 [t/e−(t/e)^r]log p。在本包 e=ℓ 素数、ℓ∤b、1≤j≤(ℓ−1)/2 的范围，t_j≠0，所以每层 all-bad block 都有这份严格正增量。

必须保留比较基准：(13a) 比较实际 tensor 子格，不比较已经取过 holomorphic hull 的两个区域。对 uniform bad profile，原 R_1 的 O_E-ideal hull 已经等于各因子轨道的 ideal hull；这份增量没有越过该 hull。因此「非零且不被共同运输抵消」已证，「足以排除原完整输出族亏损」仍须另算，不能混称。

## 6. 多层 bad/good profile：有穷计算的精确压缩

考虑一个源允许局部类型的计算：在该 p 上，bad profile 的原 F_mod 权重为 ρ，good profile 的权重为 1−ρ；只有一个 bad 地方，或各 bad 地方都使用上述同一个 K 的同构副本；good local fields 为 unramified，bad Gaussian 赋值为 b j²/e，good profile 为单位。ρ=1/2 的例子可以按一个 bad、一个 good、相同 F_mod local degree 的类型理解。一般不同 tame field 的 tensor decomposition 未被悄悄归入该公式。本段不是声称每份原合格 C 都满足此局部类型，也不由这些局部条件宣称已构造完整全局 initial Θ-data。

r=j+1 个位置的 tuple 若含 k<r 个 bad 因子，则某个允许位置为 good，取该位置的实际 Gaussian 单位作用即可得到整个 D_v；其他 Gaussian 都是整数，所以该 tuple 上的加性和恰为 D_v。其 tensor-order 损失是 δ_k=((k−1)_+)(e−1)/(2e)。若 k=r，使用 (13)。令 b j²=q_j e+t_j，则加权所得实际格读出为

    ℓ_j(e,b,ρ)
      = −c[rρ−1+(1−ρ)^r]
        −ρ^r[q_j+(t_j/e)^r]，c=(e−1)/(2e)。             (14)

这里 ν(L_j)=ℓ_j log p。原 tuple 权重保持不变；没有对 K 的未选定 conjugate places 另取平均。

procession 读出为 h_p(b)=(1/m)Σ_{j=1}^m ℓ_j(e,b,ρ)，m=(e−1)/2；native q 的对应当地数值为 Q_p(b)=−ρ b/e，均以 log p 为单位。对于小单位/log 子区域，再减去准确的

    (1/m)Σ_{j=1}^m(j+1)=(m+3)/2。

因此连更保守的真实单位域损失也可以保留。

现在定义 S_m(ρ)=(1/m)Σ_j j²ρ^{j+1}。由 n_j=bj² 的除法余数，得到精确的 affine-period 关系

    h_p(b+e)=h_p(b)−S_m(ρ)，
    (h_p−Q_p)(b+e)=(h_p−Q_p)(b)+ρ−S_m(ρ)。              (15)

上一包已证明 ρ=1/2 时 ρ−S_m(ρ)>0。因此只需计算 b mod e 的 e−1 个非零余数类，即可给出所有较大 b 的门槛；不是只检查有限个高度后猜测普遍成立。若还要求 3|b 以兼容 q-order 的 6-divisibility，则每个余数类选择相应 k mod 3 即可，不改变证明。全局源可实现性仍须另证，不能由这个整除条件单独推出。

e=41、m=20、ρ=1/2：

- 使用实际 tensor 整数格，第一组 3|b、41∤b 的成功参数为 b=273；h_p≈−3.320721767，Q_p=−273/82≈−3.329268293，故 h_p>Q_p。
- 保留小单位域经 log 的额外损失，第一组成功参数为 b=1620；h_p≈−19.749723960，Q_p=−810/41≈−19.756097561，仍严格跨过当地门槛。
- 对所有同样满足整除条件的 b，整数格版本 b≥393 足够；小单位域版本 b≥1740 足够。完整精确有理数和每个余数类的门槛见证书。

这个成功参数的 bad local field 也有明确 Tate realization，而不只是形式的 Eisenstein 环。取 p=1231、e=41、b=1620；1231 是素数，p−1=30e。取 Tate 参数 q=p^{3240}，则 μ_{30e}⊂Q_p、q^{1/30}=p^{108}，所以 Tate uniformization Q_p^×/q^Z 给出的 30-torsion 全部定义在 Q_p 上。又 gcd(3240,41)=1，故该 Tate 曲线的 41-torsion field 为

    Q_p(E[41])=Q_p(q^{1/41})=Q_p(π)，π^{41}=p，
    qhat=q^{1/82}=π^{1620}。

后一个根选择给出原 2ℓ-root 的实际代表；其他允许根只差根单位。于是 Gaussian 因子理想确实为 π^{1620j²}O_K，并且原 bad q-order 与 ℓ 互素。Q_p 内的 30-torsion 也满足局部 2、3、5-torsion 要求。此处证明的是这个 bad 局部输入的存在；权重 1/2 的第二个 good 地方、所有全局初始数据、Galois image 和原固定完整 C 仍未由此构造，不应以局部 Tate realization 代替它们。

最大 all-bad block 的 Q_p 维数为

    41^21=7386879101213258109624223688656841。

没有构造这张巨矩阵；(12)–(15) 是压缩它的严格代数证明。对小 block，程序另从实际乘法基矩阵作整数 Hermite normal form，而不是复用大尺寸公式作自我验证。

## 7. 为什么仍未完成原反证

共同 T 的疑点在原 raw possible-image family 层已按第 2 节解决；所以不再把它留作无限循环的待办。但 (14) 的成功只是特定局部类型的真实下界。

原目标仍要求任意原合格完整 C 的全局比较。我们没有证明：

- 每个相关 p 的原地方分布都有足够的非均匀性；
- 局部不足能由其他地方和实际无穷处贡献补足；
- 授权 hull/determinant/approximation 后，与固定 q 的输入关联足以给出完整目标。

尤其 ρ=1（均匀 positive profile）时，(13) 给出的实际格至多达到原 Gaussian ideal hull，其 procession 体积仍满足

    h_p ≤ −[e(e+1)/12] b/e < −b/e = Q_p。

tensor-order 内部可能有有限的加性增量，但它只填补原 integral-closure 缺口，不能越过这个原 ideal hull。这里没有构造一份全局完整 IUT 反例。

这里 h_p 是本包算出的子格读出，不是整个目标 H_C 的上界。一般 mono-analytic T 与目标 holomorphic hull 不交换；其他源分支或目标取 hull 仍可能给出更大区域。因此本节排除的是「当前下界证书已足够」的说法，不是断言真实完整输出族在 uniform 情形失败。

IV1.10(v) 的 min/mean 问题也不能通过被动换框架消解：对原主动 Ind1 轨道，跨 tuple 的联合上界仍必须处理最小赋值。本包不从这一点直接宣布 IV 全定理有反例；尚需把其完整假设、所用区域和 tuple bound 逐项对齐。但该平均 λ 的上界不能作为已经验证的供体，反过来否定本包的实际区域计算。

对下一步的具体收窄：从原完整坏 C 的 h_C<Q_C 出发，在各 p 的实际 source output 基上计算可获得的全部 additive spans；对 (14) 已覆盖的局部类型直接复用，不再重做。剩余必须检查第一个改变实际 integral-domain span、而非仅换框架/置换/乘单位的 log-Kummer 分支，并保留 Gaussian 的整数标量部分。对于均匀输入，若新分支仍只给同一个 Gaussian 乘子乘一个固定有界单位格，则不能声称已取得所缺补偿。全局与无穷处必须保留，不能新增「其余贡献非负」假设。

## 8. 源版本与验证范围

定向复用/新核：

- IUT I May 2020，§0 pp.33–34 的 poly-composition；Def3.1(b)(c) pp.61–62；Def4.10、Prop6.9。
- IUT II December 2020（按本地文本首页核验；更正本包草稿的 May 2020 记载），Cor4.10(iii)–(iv) pp.159–160、Cor4.11 pp.163–164；Rmk4.7.3/4.7.4 pp.143–147 作为 zero/nonzero arithmetic-label symmetry 的反查。该 arithmetic symmetry 不等于固定 cardinality capsule 中的 naked-index permutation，本包不混用。
- IUT III May 2020，Cor2.3 的实际 radial/coric morphisms；Prop3.1/3.2、Prop3.4/3.5、Example3.6(ii)、Prop3.7(v)、Def3.8、Prop3.9；Rmk3.10.2；Thm3.11(i)–(iii)、Rmk3.11.1(iii)–(iv)、Rmk3.11.2(ii)、Rmk3.11.4(iii)；Cor3.12 的 U 定义及 (xi-b)，没有把 (xi-f) 当作待证比较的证明供体。
- IUT IV April 2020，Thm1.10 的额外假设与 proof(iv)–(v)；上一包的 min/mean 诊断保持。

官方 URLs：

https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf
https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf
https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf
https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf

使用 PDF skill 做只读图像核对；第152、154页本地 Poppler 渲染并目视检查，没有创建/编辑论文 PDF。来源哈希见 EVIDENCE。

已运行：python tmp/sheaf/n8/closure/c9_tame_source_span_20261025.py，exit0。32 个实际整数格案例，每例分别计算单分支与加性和的 HNF、核验 (13a) 的商群长度；288 个逐 tuple 与压缩公式比对；12 个 e 的两种积分域、共24组余数类门槛证书。一般结果由 (8)–(15) 的自然语言证明支持，有限检查不代替证明。

本包只作 root 自审；没有独立审查、Lean 编译、kernel、comparator 或 Project 构建。已给出上述明确 bad-local Tate realization；没有构造完整全局 initial Θ-data 作为数值实例，没有完成全局/无穷处 q 比较。target_accepted=false；原 P6 open。
