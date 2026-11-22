# 两份黎曼猜想工作的哪些步骤能用于 IUT

2026-11-22，单线程研究。对应 SHEAF 节点 §19.3 的原 III.3.12 固定输入，以及 §18.5 的整数 ABC 测试。前者可采用一个保留输出来源的模 3 判据，后者可以精确说明 Dirichlet GRH 所给估计与固定底数 2 还差哪个量词。[原任务与量词](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#本轮暂停交接)

## 两种方法各自提供了什么

**Levent Alpöge 与 Claude。** 11 月 20 日发布的 Lean 声明覆盖任意模数 \(N\ne0\) 的 Dirichlet 特征。其 \(L\) 函数在 \(0<\Re s<1\) 内的零点都在 \(\Re s=1/2\)。Lean/Mathlib 社区已独立核对 RH，Andrew Sutherland 的记录也给出了五个公开定理的公理和类型比较结果。本次使用的是这项 Dirichlet 结果。一般数域上任意 Hecke \(L\) 函数的零点需要另有来源。[公开定理原码](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Statements.lean) · [社区核验](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [五个定理的独立核验](https://math.mit.edu/~drew/grh/)

作者说明第 1、3、4 页给出的想法是用迭代自守 theta 提升实现 Stepanov 式重数。对长度 \(X\) 的 von Mangoldt 和取约 \(\sqrt X\) 层，同时核算提升范数、整除量和各层代价。第 4 页第 13–18 项尤其相关，跨 Hecke 特征粘合同一个整结构，才有可比较的公因子和余体积。源码中的 `ch_top` 先用 `IdentU` 识别同一数据上的主项和被估量，再应用独立的大小与误差界。这里可借的是在**同一对象**上识别两个读数的做法。仓库的迹商行列式已有候选，若给 Θ 与 q 两端同时换参考格，辅助行列式会精确约去。用它支付高度差以前，仍需原 Θ 侧产生带原度量的商映射。[作者说明](https://alpo.ge/remark.pdf#page=4) · [ch_top 的证明](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L37) · [仓库已有的行列式核算](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#strength-and-determinant)

**Alessandro Maria Masullo。** 11 月 20 日公开的《The Music of the Primes》讨论数域上的 Hecke \(L\) 函数。第 27 页先用指标函数 \(\alpha_{k+1}-\alpha_k\) 按除子分层切开提升后的卷积核，再逐块算迹与对角质量。这个操作顺序适合本仓，因为一旦只保留 `sourceStepXILogVolume_eq` 的常值实数，就无法再区分好槽和坏槽。原稿第 514 页的 §12.3 是从全局核过渡到 \(S\)-局部核的环节，该版只留脚注 “Include section.”。Vakil 在发布页的更新中记录了收到的问题报告。下面只借有限层上的指标函数，其算术性质逐项证明。[Masullo §1.3](https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=27) · [§12.3](https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=514) · [Vakil 发布及更新](https://math216.wordpress.com/2026/11/20/hurried-announcement-alessandro-masullo-grh/) · [本仓常值读数](../tmp/sheaf/xif/paper/S3138SourceProcessionProfileActual.lean#L59)

## III.3.12 固定输入上的判据

取 \(p=3,\ \ell=5,\ d=3\)。目标有序元组为 \((G,B,B)\)，即好、坏、坏，默认标记为槽 2。置 \(\tau=(2,0)\)。其拉回是 \((B,B,G)\)，同时运输元组与标记时，源的好槽 2 落在目标好槽 0。具体模型 `image_thetaFiniteOn_ind1Reindex` 明确把标签集 \(S\) 送到 \(\tau S\)。因此在目标上仍要求读取标记 2 时，必须指出原求值如何接收这个标记 0 的输出。原 III.3.12 先取各行各位允许像的并，再取其 holomorphic hull。固定源点 \(1\) 时，已有目标是从同一原输入取得 \(E_\tau(1)\in U_{2,3}\)。[模型的整族换位](../Iut/Concrete/Ind1Invariance.lean#L592) · [原 III.3.12 第 174–175 页](IUT-TEXT/III.txt#L10376) · [固定例的源与目标](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#本轮暂停交接)

**从同一次求值检出几个指定投影同时为单位。** 选一组要在同一次求值中比较的域因子 \(K_i/\mathbf Q_3\)，用原参考格归一化。令 \(W\) 是一个有限候选集，每个 \(w=(D,x)\) 带着同一固定输入下的原允许输出 \(D\) 和其中一个有来源的点 \(x\)。记该点的标记投影为 \(z_i(w)\)。先设这些投影都在 \(\mathcal O_{K_i}\)。取
\[
 t(w)=\prod_i N_{K_i/\mathbf Q_3}(z_i(w)),\qquad
 J_W=\sum_{w\in W}\mathbf Z_3\,t(w).
\]
则 \(J_W=\mathbf Z_3\) 当且仅当存在**同一个** \(w\)，其所有指定投影都是单位。证明是对非零投影用 \(v_3(Nz)=f_i v_{K_i}(z)\)，其中 \(v_{K_i}\) 给一致化元赋值 1，\(f_i\) 为剩余次数。各项非负，和为零恰在每一项为零时成立。零投影使乘积为零。最后，一批 \(\mathbf Z_3\) 元素生成单位理想恰好要求至少一个生成元模 3 非零。也可对每个 \(w\) 直接相乘各槽的单位指标函数。对只要求 \(|z_i|\ge1\) 且未证整性的包，用各槽 \(\mathbf1_{\{|z_i|\ge1\}}\) 的乘积，免除正负赋值相消的问题。这是本次推导，适用范围只包括需要同一见证的投影。

**在固定例上实际可读出两种结果。** 模型默认参考点在各指定投影的绝对值为 \(3^{-6/5}\)，所以 \(t\bmod3=0\)。运输好槽的参考元 \(1\) 后投影都是 \(1\)，所以 \(t\bmod3=1\)。保留同一见证这一条件确实影响答案，例如两次输出分别为 \((1,3),(3,1)\)，两列分别生成 \(\mathbf Z_3\)，两次输出各自的乘积却都等于 3。把它们合成 \((1,1)\) 会造出原集合中没有的点。同理，若原 hull 允许在不同元组分别取极值，判据按各自容许的范围使用，不额外强求所有元组共用一个见证。[固定模型数值与各元组的原量词](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#finite-slot-certificate)

**下一次检查只需一条原箭头。** 沿 III.3.10.2 的同一 IPL（即这次跨列识别所用的整套数据），跟踪 \((B,B,G;2)\) 的 \(1\) 到目标列，写出承载它的原允许输出 \(D_\tau\)、落点和标记 0 的投影。若得到该点的成员证据并且 \(t\bmod3\ne0\)，就完成这一元组上这组投影的单位见证。只拿到标量或裸换位时，记录最后仍有标记的箭头。换另一批样本得到的阴性结果只排除那批样本。原读数的归一化、其余元组的覆盖、所有实际输出的上界与全体输入仍各有其证明义务。`S1447` 的覆盖引理在读数和上界得到识别后才接入。[原求值任务 §19.3](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#本轮暂停交接) · [原输出的条件式构造](../tmp/sheaf/n8/closure/SourceAllowedOutputActualAttempt.lean#L74) · [读数消费者](../tmp/sheaf/xif/paper/S1447ReportFMarkedTraceActual.lean#L354)

## 整数 ABC 中固定底数 2 的检验

§18.5 要在无穷多个奇素数指数 \(\ell\) 上找到 \(p\parallel 2^\ell-1\)。对 \(p\mid 2^\ell-1\)，有 \(\operatorname{ord}_p(2)=\ell\)。写 \(k=(p-1)/\ell\)，则 \((2^{p-1}-1)/(2^\ell-1)\equiv k\not\equiv0\pmod p\)。所以所需的一次整除恰等价于费马商
\[
 q_p(2)\ne0,\qquad q_p(b)=(b^{p-1}-1)/p\bmod p\quad(p\nmid b).
\]
这个写法直接给出可问 Dirichlet GRH 的对象。\(q_p\) 把乘法变成加法，\(q_p(1+p)=-1\bmod p\)，故 \(H_p=\ker q_p\) 是 \((\mathbf Z/p^2)^\times\) 的真子群，\(b\mapsto\exp(2\pi i q_p(b)/p)\) 是模 \(p^2\) 的本原特征。测试指定了特征在 **2** 处的值，而且 \(p\) 须整除这个 \(2^\ell-1\)。[项目 §18.5](R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#abc-route-decision)

Dirichlet GRH 配合 Lamzouri–Li–Soundararajan 定理 1.1(2) 给出一个显式结论。对每个素数 \(p\ge101\)，存在素数 \(b\le4(\log p)^2\) 且 \(q_p(b)\ne0\)。代入模数 \(p^2\ge3000\) 和子群 \(H_p\) 即得，因为其唯一素因子 \(p>4(\log p)^2\)（\(x/\log^2x\) 在此区间递增）。但变底数问题已有更强的无条件界，Bourgain–Ford–Konyagin–Shparlinski 给出最小底数至多 \((\log p)^{463/252+o(1)}\)。最小底数可取素数，因为费马商对乘法可加。具体在 \(p=1093\) 上，\(q_p(2)=0,\ q_p(3)=312\)，足以看清同一 \(p\) 上变换底数的影响。这个数例只比较底数，不充当素数指数族的反例。[显式素数界，定理 1.1](https://arxiv.org/abs/1309.3595) · [变底数的无条件界](https://doi.org/10.1307/mmj/1281531459)

有一项 GRH 推论直接作用于本原 \(a+b=c\)。Lagarias–Soundararajan 证明，对每个 \(\kappa>8\)，有无穷多组本原解的全部素因子都至多为 \((\log c)^\kappa\)。它适合检验想用“总有大素因子”来支付高度的路线。其估计数的是一族光滑解，项目需要的是每个三元组的 \(\operatorname{rad}(abc)\) 下界。两者之间仍需把各个不同素因子的贡献和重复幂损失联系起来。[原论文与定理](https://arxiv.org/abs/1102.4911)

## 证据版本

研究 owner 为本 chat，沿用现有手稿节点。`statement_dependencies` 是 §19.3 的原允许像、标记投影和 §18.5 的指定素幂族。`proof_dependencies` 中，固定模型的换位复用现有源码，模 3 判据有上述局部域证明，原允许输出与读数身份为 gap。两份 RH 工作只登记为研究来源。

仓库 HEAD 为 `a997af4b1cb2339d1e7403ef0781a16f809f4476`，工作树含既有修改。核对时 `ThetaRegion.lean`、§Ind1Invariance.lean§、11 月 18 日交接的 SHA-256 前 16 位依次为 `f7a9f18f07c0c694`、`9d3b75939495957f`、`d90a54d81ed152c6`。Alpöge 说明与 Masullo 原稿的 SHA-256 前 16 位依次为 `3fc97784b71ddd44`、`e039d3f6cf0a4b14`。Lean 镜像固定为 `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`。

独立于符号推导，用整数运算枚举了 \((\mathbf F_3^2)^2\) 的 81 组候选对，并对 \(3\le\ell\le19\) 的所有奇素数指数及 \(2^\ell-1\) 的全部素因子核对了一次整除判据。此次未改 Lean。`statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 均未运行。外部构建和公理检查引用上列独立记录。
