# C9：由实际 J_H 到源允许输出区域

任务 ID：C9-JH-OUTPUT-REGION-20261025；owner：当前 chat root；2026-10-25。单线程自然语言研究，不写 Lean，不派 subagent。

消费者/阶段：n8-c9-output-region-source-route；SHEAF stage1；原 P6 固定 native q 原体积类的完整源输出覆盖。固定任意原完整 C、gluing、目标列、原 normalization；反设所有最终源允许输出有统一严格亏损，数值核心 h_C<Q_C。

新任务：用户要求证明上一包的实际全局数 J_H 能产生所需输出区域。把 g_(v,j)^N=u_v^(-j^2)J_H^(j^2) 接到实际积分区域、相对 determinant 与原输出族；不能把可构造的 fractional ideal 自动算作允许输出，也不能按所需答案选择 root/rescaling。

冻结复用：C9-STRICT-DEFICIT-LOOP-20261024.md，SHA256 610aad551d02e5480b1c79460b75dc8ed040dd3fec93b8a64e0281e57d865a90；其 EVIDENCE-20261025。已证 J_H 非零、坐标无关、选定坏地方 J_H=u*q^(m(m-1))，N=2ell*m(m-1)；marked moment 非零。该包没有源输出覆盖结论。

精确读：III Prop3.5 的 monoid action/积分结构，Prop3.7(v) 的 fractional ideal，Rmk3.9.5(Ob3/4) 的相对 determinant；有需要时仅查其明确引用；旧局部群/有限观察结果按既有记录复用。新外部来源仅围绕本任务的单位稳定性、Kummer roots、norm/region 构造，不重复泛读旧解释。

精确写：本记录、同名前缀 EVIDENCE/计算文件、root-owned DAG 新字段；AUDIT_LEDGER/STATE/queue 只追加。其他 owner 的 Lean 与定义不改；集成 root；Lean 构建不适用。

statement_dependencies：实际源 eval 数 g、积分区域 U/其 log image、source-allowed actions 与最终 hull、原 weighted normalization。
proof_dependencies：冻结 J_H 等式；需要证明单位对具体域的作用、取幂/取根的源许可与区域效应、实际 reference 与完整共轭地方/目标列的比较。

验收：实际区域等式/包含及其源 provenance，或明确不可行的子路线及证明；最终 Q_C<=h_C 没有完成就不登记为已证。statement_compiles/proof_body_checked/kernel_closed/comparator/Project/独立审查未运行；target_accepted=false。

状态：本包实际区域计算及自然语言证明完成；J_H 重建原 Gaussian 理想但没有提供额外输出增量。新证 eta 乘积公式、全共轭乘积常数公式和精确单位/hull 结论。原 P6 的完整输出覆盖、统一严格亏损反证仍未证明；不能据本包否定原目标。

## 1. 本包回答的准确问题

沿用上一包 m=(ell-1)/2、s=m(m-1)、N=2ell*s。固定原完整 C 的一个源允许 holomorphic realization；v 是原选定坏地方，q=q_Tate,v，qhat^(2ell)=q，g_j=zeta_j*qhat^(j²)，zeta_j 属于 mu_(2ell)。

上一包已从同一个实际循环覆盖构造 J_H=disc(f_H)^6/Delta(E^sharp)^s，得到 J_H=u*q^s 及 g_j^N=u^(-j²)*J_H^(j²)。本包不把单纯的 J_H 非零当作输出充分性，而分别检验：

1. 它是否生成实际 fractional ideal；
2. 生成的理想是否来自原被标记的 pilot；
3. 其原 normalized log-volume 是否达到固定 native q；
4. 把所有共轭乘起来能否给出额外的全局关系。

结论是第1项可以精确完成；保留第2项时，第3项仍是原 Gaussian 收缩；第4项的普通 norm 精确丢掉 q。原非零 marked pairing 仍成立，但本包没有从它产生新的源分支。

## 2. 先把未知单位算清：J_H 的精确 eta 公式

在通用 prime-level pair (E,H) 的 X_0(ell) 上，H 为原曲线的循环 ell 子群，E^sharp=E/H，D 为对偶 isogeny 的核。沿用实际选定 cusp 的参数 E=E(q)、E^sharp=E(q^ell)。令 k=6(ell-3)。则

    J_H(q) = q^s * product_(n>=1) ((1-q^(ell*n))/(1-q^n))^k
           = (eta(ell*tau)/eta(tau))^k.                     (2.1)

这是对上一包 kernel-discriminant 数的识别，不是把 J_H 重新定义成另一个数。

证明分四步。

(a) J_H 是 X_0(ell) 上的有理函数。Weierstrass 坐标变化 x->a²*x+b 时，disc(f_H)^6 与 Delta^s 都乘 a^(12s)，所以比值下降；f_H 的根是 D 非零点的 ± 对的 x 坐标，集合随同 (E,H) 代数地变化。

(b) 在特征0的开模曲线 Y_0(ell) 上，D 是 étale，互异 ± 对有不同 x 坐标，故 disc(f_H) 和 Delta 均非零。在任何光滑模型局部平凡化中它们也没有极点。因此 J_H 的零极点只在两个 cusps。上一包 Tate 展开已给选定 cusp 阶数 s；另一个 cusp 的参数 t 满足 q=t^ell，E^sharp=E(t)，D=mu_ell，故阶数 -s。于是 div(J_H)=s([infinity]-[0])，其中选定 cusp 记为 infinity。

(c) eta 候选的指数为 r_1=-k、r_ell=k。权重和为0；ell^k 是有理平方；两个 cusp 阶数为 ±k(ell-1)/24=±s，整数。Darmon–Daub–Lichtenstein–Rotger《Algorithms for Chow-Heegner Points via Iterated Integrals》§4.3、Def4.3.1 给出适用的 eta modular-unit 判据与 cusp 公式：
https://www.math.mcgill.ca/darmon/pub/Articles/Research/56.DDLRS-AWS/paper.pdf
作者站另一份为 https://web.mat.upc.edu/victor.rotger/docs/DDLR-S.pdf 。本包仅用上述明确判据，不引用该文的 Chow-Heegner 主结论。

(d) 两个函数的除子相同，所以比值在紧致光滑 X_0(ell) 上是常数。Tate 坐标下每个 x(q^i;q^ell)-x(q^j;q^ell)、i<j，首项为 q^i，Delta(q^ell) 的首项为 q^ell。故 J_H 首项系数1；eta 候选也是1，常数为1。这个函数域恒等式在源数域的光滑 pair 上成立，并给每个选定坏地方的收敛 q 展开。

因此

    u(q)=product ((1-q^(ell*n))/(1-q^n))^k
        =1+k*q+O(q²) ∈ 1+q*O_(K_v).                       (2.2)

特别地它是明确的单位。不能从 u≡1 推出它在所有实际点都是1或 torsion。若 p 不整除 k，且 ord_p(q)>1/(p-1)，首项支配给 ord_p(u-1)=ord_p(q)，p-adic log 在此小域单射，所以 log(u)≠0；这是许多局部 specialization 上的确定非 torsion 结论。没有把这个附加条件施加给原全部 C。

## 3. 实际积分区域：单位何时确实可以消去

设 E 是指定 tensor packet 的有限 étale Q_p 代数，O_E 为各 field summand 的整数环之积。指定 factor 的单位 u 映入 O_E^×。

对任意子集 S⊂E，记 Hull_E(S) 为最小的分量 fractional-ideal hull（若无有限上界则用相应扩展值）。则

    Hull_E(u*S)=u*Hull_E(S)=Hull_E(S).                     (3.1)

证明：u 是 O_E 单位，乘 u 给出 O_E-submodule lattice 的自同构；每个分量的 valuation 不变，且 u*I=I 对每个 fractional ideal I 成立。两边的最小性给 (3.1)。特别地 u*O_E=O_E。

这消除了上一包“单位可能改变最终 holomorphic 理想”这一未决点，但没有给出 u*S=S。若 S 是 log(O_K^×) 或原张量格子，它可能只是 Z_p-lattice，并非 O_E-module。后面还有非 O_E-linear 映射或 log 时，不可提前取 hull；(3.1) 只能用于最后这个 holomorphic hull 步骤。

另外 log(u*U)=log(u)+log(U) 是单位域上的公式；当 u∈U 且 U 是群时左边就是 log(U)。这与 IQ 上的乘法 u*log(U) 是不同操作。非单位 q、J_H 不得直接投入普通 p-adic log。

## 4. 精确产生哪些理想：j² 没有消失

在源规定的同一个 realization 中，定义原生理想 I_j=g_j*O_E，并以 I^[a] 表示理想乘积的 a 次幂。代入实际等式和 (3.1)：

    I_j^[N] = J_H^(j²)*O_E.                              (4.1)

每个 field summand 的 fractional ideal 由 valuation 唯一决定，因此在存在的范围内取 N 次理想根是唯一的。故

    I_j = root_N(J_H^(j²)*O_E).                          (4.2)

这是一个确实与原输出相接的区域等式：左边的 g_j 是源 cyclotomic/Kummer evaluation，不是自由 thetaImage；右边是实际 J_H 的理想运算。对一般 transported S 必须保持原 g_j；若从 (4.1) 重新选元素的 N 次根，还会出现 mu_N 的歧义，不能把 mu_N 自动扩成原 pilot 允许的 torsion。对 O_E 理想而言这些单位歧义不改变 (4.2)。

另一方面，数值为 native q 的实际局部理想是

    I_q=qhat*O_E=root_N(J_H*O_E),
    I_j=I_q^[j²].                                       (4.3)

这里理想根不要求在原域额外选取一个元素 beta 满足 beta^N=J_H：已知 qhat^N=q^s，且 J_H/q^s 为单位，所以 qhat*O_E 本身就是所需理想根。若某个表达框架先在有限扩域中写出元素根，扩域度数的 normalization 也必须一起保留，不能据此添加原配置没有的输出分支。

由于 ord(qhat)>0，j>1 时 I_j 严格包含于 I_q。于是 J_H 提供了实际 q 理想的代数描述，但将 (4.2) 换为 (4.3) 正是在各个 j 分量删去了 j²；这一步没有由原 pilot 的身份推出。

尤其不能把 pointwise N 次幂像 {x^N:x∈S}、理想乘积 S^[N]、有限覆盖的推前、以及相对 determinant 混为一谈。本文 (4.1)–(4.3) 仅对 fractional ideals 作乘法。

## 5. 源许可的核查结果

精确原文如下：

- III Prop3.4、Prop3.5：指定 monoid 在指定 tensor factor 上作用；同时分别保留 unit/log domains 与 nonunit splitting action。Prop3.5(ii)(c) 的 splitting monoid 的 units 是原 2ell-torsion；其 infinity 版本是 torsion。
- III Prop3.7(v)，pp111–112：monoid 元素的局部 fractional ideals 可构造相应 global Frobenioid 对象。这是对象构造的范围。
- III Def3.8(i)，pp112–113，以及 II p158 的 pilot 定义：pilot 由 splitting monoid 的指定生成元（模 torsion）确定。它没有说环境中的每个 rational power 都是同一个 pilot 的另一个输出。
- II p88–89、Theta^Q>=0 的定义：完美化的环境容许正有理次幂。这个事实提供 root 对象，不自动保留指定 pilot 标记。
- III Rmk3.9.5(vii)(Ob3/4)，pp132–133：先作与 det(O_E) 的相对修正，再对比较两边共同取足够可除的 M 次 tensor power。它没有逐 j 将一个被标记对象改成 1/j² 次幂。

故本包能交付的 source-qualified 构造是“用 J_H 重写原 g_j 的作用及其原生理想”，而不能交付“每个 j 都输出 I_q”。j=1 的原分量确实有 I_1=I_q；原完整 procession 带有其余 j 的位置和权重，不能把一个 j=1 分量复制到全部位置来替代它。

更强的同一性结论：若把每条原分支中的 g_j 仅按其真实等式用 J_H 和 u 重写，保留原 root、原 S、原后续映射与标记，则每条分支逐点完全未变。任意多层这种重写都不会添加输出，更不会因书写层数增加而产生增益。这个结论只否定“重写本身带来扩大”，不否定真实 log/Ind1 等分支能够在原族内产生扩大。

## 6. 体积与相对 determinant 的最终计算

在一个 packet 中 D=[E:Q_p]，g 来自 degree d 的指定 factor。相对 O_E 的 normalized log-volume 为

    nu(g*O_E) = (1/D) log|det_Qp(m_g)|_p
              = (1/d) log|Norm_(K_v/Q_p)(g)|_p
              = log|g|_v.                               (6.1)

这里 |p|_v=p^-1，局部次数未重复吸入 |.|；地方/packet 权重按原文放在外面。det(m_g)=Norm(g)^(D/d)，所以维数在 (6.1) 中精确约掉；单位的 relative determinant 绝对值为1。共同 M 次 tensor power 后再除 M 同样不变。

令 L_v=-log|q_v|>0。由 (4.2)–(4.3)，

    nu(I_j)=(j²/N)*log|J_H|=-j²*L_v/(2ell),
    nu(I_q)=(1/N)*log|J_H|=-L_v/(2ell).                  (6.2)

对 j=1,...,m 用原 procession 平均：

    (1/m)*sum j² = ell(ell+1)/12 = A_ell,
    theta_seed,v=-(ell+1)*L_v/24,
    Q_v-theta_seed,v=((ell+4)(ell-3)/(24ell))*L_v>0.       (6.3)

沿用已核的原地方权重，Gaussian seed 的全局 numerical readout 为 A_ell*Q_C。这里没有构造跨 Theta-link 的 calibrated arrow，也没有声称 theta_seed 等于完整 h_C。完整输出 hull 可大于 seed；正是其额外增长尚需证明。

ell=41 的例子：m=20、s=380、N=31160，theta_seed,v=-7L_v/4，而 Q_v=-L_v/82；仍缺 285L_v/164。J_H 非零与 marked log moment 正值，都与这个严格 seed 亏损同时成立。因此仅把非零量存在接到反设 h_C<Q_C，尚无逻辑矛盾。

## 7. 新的完整共轭计算：普通 norm 精确成为常数

有一个比“可能抵消”更强的精确公式。对固定原 E 的所有 ell+1 条 H⊂E[ell]，使用同一定义的 J_H，有

    product_(H in P^1(F_ell)) J_H = ell^(-3ell(ell-3)).   (7.1)

证明先求另一个 cusp 的首项。令 zeta 为原始 ell 次根，t_i=zeta^i+zeta^(-i)，x_i=1/(t_i-2)，i=1,...,m。实 cyclotomic polynomial P(T)=product(T-t_i) 满足 P(2)=ell、disc(P)=ell^(m-1)。后一公式也可直接由

    Phi_ell(z)=z^m*P(z+z^-1),
    Phi_ell'(zeta)=ell*zeta^-1/(zeta-1),
    product_(i=1)^m (t_i^2-4)=(-1)^m*ell

求导并乘遍根得到。分式线性变换的判别式公式于是给

    disc(product(X-x_i))=disc(P)/product(t_i-2)^(2(m-1))
                         =ell^(-(m-1)).                  (7.2)

所以另一个 cusp 上 J_H 的首项常数为 ell^(-6(m-1))=ell^(-k/2)。Fricke 对偶交换两个 cusps，故同样的除子/首项论证给 J_H 的对偶值为 ell^(-k/2)/J_H。

写 F(q)=q^s*product((1-q^(ell*n))/(1-q^n))^k。若 q=t^ell，则全部核类型的值为 F(q) 以及 ell 个 ell^(-k/2)/F(zeta^i*t)。而

    product_(i=0)^(ell-1) F(zeta^i*t)=F(t^ell).          (7.3)

证明 (7.3)：product_i(1-zeta^(i*n)*t^n) 在 ell 不整除 n 时等于 1-t^(ell*n)，在 ell 整除 n 时等于 (1-t^n)^ell；逐项约去无限乘积即可。前面的 zeta 次幂乘积是1。代入即得 (7.1)。这是函数域恒等式，随后可在实际 smooth E 上取值。

若 K/F 的实际 torsion Galois 群 G 对这些 lines 传递（原 SL2 条件保证），则

    Norm_(K/F)(J_H)=ell^(-3ell(ell-3)*|G|/(ell+1)).       (7.4)

各 H 的重数为 |G|/(ell+1)，所以无需假定每个局部 orbit 大小相同。没有把 F 擅自认成 Fmod，也没有从此推出选定地方的 source normalization 是完整 K-place normalization。

在原坏地方 p!=ell，(7.4) 是单位，所有 q 依赖精确消失。原 marked pairing 的正值没有被推翻：带地方相关 marker 的和并非普通 norm 的 log；把它变成全局 norm 时恰好删除了这个 marker。它不能据 (7.4) 同时被说成正数又等于0。

## 8. 可以明确剪掉的路线与下一项实际构造

可以剪掉：

1. “J_H 非零，因此生成 q 体积输出”的直接推论；(4.2)、(6.2) 给出真实输出而保留 j²。
2. “多取共同 tensor power / determinant / extension norm 会自动除掉 j²”；(6.1) 明确否定。
3. “取完整共轭 norm 后用 product formula 得到 marked 正值矛盾”；(7.1)–(7.4) 给出精确常数。
4. “在固定 X_0(ell) 上继续制造更多仅在 cusps 有零极点的 modular units 就获得独立 q 方向”。两个 cusps 意味着任何这样的 V 都有 div(V)=a([infinity]-[0])，故 V^s/J_H^a 是常数。它可提供不同表达或已知常数项，不能在保持原 evaluation 校准的同时凭空添加新的 cusp 斜率。此剪枝不涉及高 level、多边界的新源对象或具有内部除子的函数。

实际下一步须研究原源允许 branch 如何改变最终目标坐标中的理想阈值。对每个真实输出 R_chi，保留其实际输入域和映射，计算目标 holomorphic 分量 a 上

    b_(chi,a)=inf { ord_a(x_a) : x in R_chi }.

最终 hull 的对应阈值是 inf_chi b_(chi,a)。固定候选坏容器的各分量 threshold 之后，只有一条真实 branch 产生更小 valuation，或一个真实 archimedean region 产生更大半径，才能在该分量增加 hull。单个分量逃出还不必达到完整 global native Q；必须按原权重合计净增量。这是计算实际输出点/区域，而非计算 label 的 thetaImage。

本包把 J_H 降为精确校准工具：用 (6.2) 对每条候选实际分支的前后 readout 记账。要排除统一严格亏损，必须从源允许的动作和完整积分域取得达到 Q_C 所需的加权增长，不能把该增长作为新假设输入。下一个候选应是第一个不能被上述同一性/单位/hull/共同幂消去的实际 log-domain 或 Ind1 composite，且必须写出其域、像、目标分量；没有这些数据就不启动无目的二十层枚举。

这没有证明整个输出族严格亏损，也没有将“每个分量都含 I_q”加强为原 P6 的必要条件。原目标仍只要求同一 C 下完整输出族的原 global normalized volume 达到或单侧逼近 Q_C。

## 9. 验证与交付边界

精确脚本 c9_jh_output_region_20261025.py 调用上一包的 Tate x 展开函数，但不重跑其 SL2 枚举。新检查：

- ell=5,7,11,13,17,19,23,29,31,37,41,43，共12个素数；独立从 kernel differences 和 eta product 算单位展开至 q^40，492个整数系数全同；
- 24个有限域检查确认 (7.2) 的精确 ell 次幂首项；
- 按 cyclotomic 乘积规则逐因子检查 (7.3) 至 degree 3ell²；
- 48个有理 q-valuation 案例核验原区域、目标区域、共同幂及正亏损。
- 独立于 eta/cusp 展开，枚举实际有限域椭圆曲线的全部 rational ell-torsion，逐条 H 构造 Vélu quotient，取对偶核的实际 x 根和判别式，再乘全部 J_H：ell5、p101、E:y²=x³+x 得6个 J，乘积84；ell7、p197、同式得8个 J，乘积191；ell11、p353、E:y²=x³+7x+72 得12个 J，乘积1。分别恰等于 ell^(-3ell(ell-3)) mod p。这些是独立的代数运算核验，不是原 characteristic0 完整 IUT 输入，也不替代 (7.1) 的证明。

执行 `python tmp/sheaf/n8/closure/c9_jh_output_region_20261025.py`，exit0，所有断言通过；产物 C9-JH-OUTPUT-REGION-CERTIFICATE-20261025.json。一般命题依赖上述证明，有限计算不是替代。没有计算完整 IUT 输出族。

复用调查：已有 C9-ALLOWED-REGIONS-NATURAL-RESEARCH、C9-EVALUATION-DEFECT-ATTACK、C9-STRICT-DEFICIT-LOOP 的精确对象/normalization；外部新供体限 DDLR §4.3 的 modular-unit 判据。当前自然语言阶段不做 Mathlib 搜索或 Lean 实现。

statement_compiles：未运行；proof_body_checked：未运行；kernel_closed：未运行；comparator/Project：未运行；独立审查：未运行，只有 root 自审。target_accepted=false。没有证明原完整输出覆盖，没有真实源严格亏损反例；未改原目标、定义或他人文件。

实际消费者接入：原 owned DAG 节点追加本包证据，关闭“J_H 到原生理想的未知单位效应”在最终 holomorphic ideal 层的子问题；原目标列 log-shift、全局 native-q 回接及实际扩大下界仍开放。研究历史保留，不把单条失败路线宣称为 P6 的反证。
