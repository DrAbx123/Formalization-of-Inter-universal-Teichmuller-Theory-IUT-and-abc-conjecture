# C9：严格亏损与实际源闭环

任务 ID：C9-STRICT-DEFICIT-LOOP-20261024；owner：当前 chat root；日期2026-10-24。单线程自然语言研究，不写 Lean，不派 subagent。

节点/阶段/消费者：n8-c9-output-region-source-route；SHEAF stage1；P6 固定 native q 原体积类的完整源输出覆盖。原完整 C、q、gluing、目标列与 normalization 固定；反设 h_C=ν(H_C)<Q_C，Delta=Q_C−h_C>0。目标为实际源越界输出/见证族或同一源数据中的矛盾，不以更强的逐路径保体积代替。

冻结复用：C9-MARKED-IMAGE-DESCENT-20261024.md，SHA256 5485c9195c32d75f1fc4560b63f7befa5d37e48223b6102de1678b0f4701b521；已有 local-global、Gaussian deficit 及反证有限化记录按该文引用复用。

精确读：III Rmk3.9.4、Rmk3.9.5(Ob9)/(cQ3)/(cQ4)、Rmk3.11.1(iii)、Cor3.12(xi)；ELS §3.10 Stp7–8/FxGl/Englf；LANA July2026 原始报告及直接相关回应，仅核其数学比较。精确写：本记录、同名 EVIDENCE JSON、必要的本任务前缀计算/来源摘取文件；root-owned DAG 节点新研究字段，AUDIT_LEDGER/STATE/queue 只追加。

statement_dependencies：原完整输出族、固定 native-q 读出、目标列实际 arithmetic determinant 对象和局部化。
proof_dependencies：实际源闭环的读出下降（本包未证责任）；已核的源允许 hull 扩大；Rss log-Kummer 体积校准；标准算术 Frobenioid 模型。

验收：逐步证明及明确源适用范围；能实际使用 Delta>0 的新证据；失败时指出具体未构造箭头，不把引用或目标改写当作证明。Lean/Project/比较器/独立审查未运行；target_accepted=false。集成 root；构建不适用；不修改其他 owner 的 Lean 或定义。

状态更新（2026-10-25）：完成源循环覆盖的 torsion-height 比较、严格非零的带标记读出，以及一个由实际源覆盖构造的非零全局代数数 J。已证明它与真实 Gaussian evaluation 在指定坏地方的有限次幂关系。没有证明原严格亏损与完整源输出闭环矛盾；P6 保持 open。

## 1. 用户纠偏与新的具体任务

本包初段重复核读 III/ELS/LANA，未得到新比较。用户指出：同样的任务反复读同样的文章，不能算新研究。依此停止原泛读任务；LANA 的 tex 快照只留作历史证据，不计证明进度。

新任务为：从同一完整 C 的源椭圆曲线、实际 degree-ell 循环覆盖和指定地方出发，计算 torsion 的全局高度平衡；判定平衡是否确实进入选定输出。用户随后要求构造一种不能抵消、确定非零的方法。本包对这个新任务给出了显式构造和证明。

精确新增读：I Def3.1(c),(d),(e),(f)；EtTh Def2.1 前的覆盖构造及 Def2.5(i)，仅用于识别这次计算中的覆盖、核和地方；Baker–Ih–Rumely《A finiteness property of torsion points》arXiv:math/0509485v1，§3.1 式(21)–(23)、Prop3.1；Dokchitser–Dokchitser《Local invariants of isogenous elliptic curves》arXiv:1208.5519v4，Appendix A ThmA.1。不是再次综述原 P6 缺口。

新增精确写：`c9_strict_deficit_marked_height_20261025.py`、`C9-STRICT-DEFICIT-MARKED-HEIGHT-CERTIFICATE-20261025.json`、本记录的 EVIDENCE。均位于本目录；研究记录开始于2026-10-24，结果和计算完成于2026-10-25。

原反证对象不变：固定任意合格完整 C、native q、gluing、目标列与 normalization；反设完整输出 hull 满足 h_C<Q_C。以下非零量是新的辅助对象，不把目标改成“某个辅助量非零”。

## 2. 必须用覆盖曲线上的实际核点

记原源椭圆曲线为 E/F，K=F(E[ell])，ell>=5。初始数据中的 type (1,ell-tors) 曲线紧化后给一条 degree-ell isogeny

    psi: E^sharp -> E,

其核 D 为循环群。选择一个核点作原点后，这个叙述与原覆盖相容；所需 kernel polynomial 不依赖非零生成元的选择或符号。令 phi:E->E^sharp 为对偶 isogeny，H=ker(phi) 为 E[ell] 中一条直线。

在原选定坏地方，EtTh Def2.5(i) 要求覆盖商来自 skeleton 的 Z -> Z/ell；因此局部模型是

    E^sharp = E(q^ell) -> E(q)=E,
    u mod q^(ell Z) |-> u mod q^Z,
    D={q^j mod q^(ell Z):0<=j<ell}.                     (2.1)

对偶映射 u |-> u^ell 的核是 canonical mu_ell 线，所以原选定坏地方恰处于 H=canonical line 的类型。I Def3.1(f) 固定相应 generator up to sign。这里不能把 D 未经说明替换为原 E(q) 上由 q^(1/ell) 生成的 subgroup；那会把 local height 系数错一个 ell。

在另一个地方，如果 H 不是 canonical line，则 H=<zeta^a q^(1/ell)>；由 Tate uniformization，

    E^sharp=E(q'), (q')^ell=q,
    phi induced by u |-> u,
    psi induced by u |-> u^ell,
    D=mu_ell.                                         (2.2)

这是实际源曲线及其全局固定 isogeny 在不同地方的两类局部实现，不是自由创建 thetaInterface 数据。若原 E 在较小局部域非分裂，工作在已有 K 的分裂 Tate 实现；ell-torsion 全部有理使此乘性情形分裂。下面使用的 |q|=|j(E)|^(-1) 在共轭地方一致。

## 3. 线性平均为什么恰好抵消

绝对值约定：有限地方 |p|=p^(-1)，local height 不吸收地方次数。全局高度为 sum_w d_w lambda_w，其中 d_w=[K_w:Q_v]/[K:Q]，复地方次数为2。Baker–Ih–Rumely 的式(21)采用把次数放入绝对值/height 的约定；本包已把次数移到外侧，不能再乘一次。

固定一个坏地方 v of F，设 L=-log|q_v|>0。记

    a_w = (ell-1)^(-1) sum_(P in D\{0}) lambda_w(P).

对 Tate 参数 q_*、|q_*|<|u|<=1，标准局部高度公式为

    lambda(u) = -log|1-u| + (1/2) B2(log|u|/log|q_*|) (-log|q_*|),
    B2(t)=t^2-t+1/6.

**选定类型。** 在(2.1)，u=q^j，q_*=q^ell；第一项为0。故

    a_w = (ell L)/(2(ell-1)) sum_(j=1)^(ell-1) B2(j/ell)
        = -L/12.                                      (3.1)

用到 sum_(j=0)^(ell-1) B2(j/ell)=1/(6ell)，所以非零 j 的和为 -(ell-1)/(6ell)。B2(t)=B2(1-t)，半列 j=1,...,(ell-1)/2 的平均也为 -L/12。

**其他类型。** 在(2.2)，所有非零核点为 zeta^j；q_* 的长度为 L/ell。因原坏地方 residue characteristic !=ell，|1-zeta^j|=1。因此

    a_w=L/(12ell).                                    (3.2)

若去掉 p!=ell 条件还须减去 log|ell|/(ell-1)；本包没有把该修正忘在 ell-adic 地方，那里不使用(3.2)。

**实际比例。** G=Gal(K/F) 包含 SL2(F_ell)，因而传递作用于 E[ell] 的 ell+1 条直线。固定一个 w_0|v，其 decomposition group 保持 canonical line T_0。地方 w=sigma w_0 的 canonical line 是 sigma T_0；H=canonical 当且仅当 sigma^(-1)H=T_0。每条直线有相同数量的 sigma 原像；条件在 decomposition-group coset 上不变。K/F Galois，地方次数相同。因此在正确的地方权重

    alpha_w=[K_w:F_v]/[K:F],       sum_(w|v)alpha_w=1

下，两类地方的质量是 1/(ell+1) 与 ell/(ell+1)。于是

    sum_(w|v)alpha_w a_w
      = (-L/12)/(ell+1) + ell/(ell+1) * L/(12ell)
      = 0.                                            (3.3)

补偿在同一个底层坏地方之上的其他共轭地方已经发生；并不必等到 archimedean 地方。I Def3.1(e) 的代表地方选取不是这个全地方平均：它保留(3.1)的类型，且采用原指定 normalization。不能把(3.3)的0当成选定地方的局部高度，也不能将其他类型不经源允许 map 直接加入原输出族。

对原 E(q)[ell] 全部非零点的普通平均也有同样诊断：q 的 Bernoulli 系数精确为0；完整和为 -log|ell|。这个旁证不是取代上面实际覆盖的证明。

## 4. 新构造：不抵消而且仍对 L 一次齐次

定义由上述类型决定的整数标记

    r_w=-ell,  若 H 是 w 的 canonical line；
    r_w=1,     否则。

则每个 w|v 都满足

    a_w = (L/(12ell)) r_w,
    r_w a_w = (L/(12ell)) r_w^2 > 0.                  (4.1)

**命题 M（带标记读出）。**

    M_v := sum_(w|v) alpha_w r_w a_w = L/12 > 0.      (4.2)

证明：r 的二次平均为 [ell^2+ell]/(ell+1)=ell，代入(4.1)。每一项已经为正，没有用“正负项也许不抵消”的推测。r 只来自覆盖核与 canonical line 的关系，不含未知输出 hull 或待证 Q_C<=h_C，故不是把答案写入定义。

另有两个确定非零的读出：

    E_v := sum alpha_w a_w^2 = L^2/(144ell) > 0,
    A_v := sum alpha_w |a_w| = L/(6(ell+1)) > 0.       (4.3)

M_v 与 A_v 对 L 一次齐次；E_v 是二次齐次。不能把 E_v 直接当原 normalized log-volume。用原坏地方权重 rho_v，sum rho_v M_v>0，因初始坏地方集合非空且每个 L_v>0。native q 的数值可从此辅助读出恢复为

    Q_C = -(6/ell) sum_(selected bad v) rho_v M_v,     (4.4)

其中 Q_C 使用已冻结记录中的 qhat=q^(1/(2ell)) 约定。式(4.4)是 native-q observable 的精确恢复，不是输出覆盖定理。

### 4.1 多层运输和遗漏标记的区别

把直线集写成 S=P^1(F_ell)，|S|=ell+1。对 T in S 定义向量 r_T=1-(ell+1)e_T。归一化内积给

    <r_T,r_U> = ell,  T=U；
                  -1, T!=U.                         (4.5)

Gram matrix 为 (ell+1)I-J，零和子空间上的特征值为 ell+1；其秩为 ell。这里 J 是全1矩阵，勿与下一节的代数数 J_H 混淆。

每一次真实 Galois 换标记同时置换 r 与 a，故 <r,a>、<a,a> 都不变；任意有限复合仍不变，层数没有上限。这个结论仅对已说明的共同置换有效，不声称 theta-link、log、hull 是这样的置换或等距映射。

若把 r 冻结在原 frame 而只换 a，则配对分别变成 L/12 和 -L/(12ell)；再次全轨道平均恰为0。这个计算明确指出要保留的资料是两个标记的实际对应关系。泛称“有 provenance”不足以证明共同运输。

## 5. 更具体的非零对象：由实际源核构造全局代数数

仅有新的数值读出还不能进入 Kummer 构造。下面给同一 E^sharp/K 和 D 的一个实际非零代数数。

令 m=(ell-1)/2；选 E^sharp 的任意 K-Weierstrass equation。定义核多项式

    f_H(X) = product_(P in (D\{0})/{+/-1}) (X-x(P)),
    J_H = disc(f_H)^6 / Delta(E^sharp)^(m(m-1)).       (5.1)

**命题 J。** J_H in K^times，且不依赖 Weierstrass equation。

证明：核的非零点两两按 +/- 配对；不同配对有不同 x 坐标，所以 f_H 可分、disc(f_H)!=0。椭圆曲线光滑给 Delta!=0。核集合由原 isogeny 定义，故 f_H 的系数在 K 中。变换 x=u^2 x'+r 时，disc(f_H) 乘以 u^(2m(m-1))，Delta 乘以 u^12，两者在(5.1)中权重相同而抵消。生成元和符号的改变只重排根。证毕。

**指定坏地方的精确赋值。** 在(2.1)的 Tate equation 上，x(q^j;q^ell)=q^j+更高赋值项，1<=j<=m。因此若 i<j，

    ord(x(q^i)-x(q^j)) = i ord(q).

这没有发生 leading-term cancellation：两个最低阶数不同，最低项系数为1。于是

    ord disc(f_H) = 2 sum_(i=1)^m i(m-i) ord(q)
                 = m(m^2-1)/3 * ord(q).

又 ord Delta(E(q^ell))=ell ord(q)。故

    ord J_H = [2m(m^2-1)-ell m(m-1)]ord(q)
            = m(m-1) ord(q),                          (5.2)

用到 ell=2m+1。

在另一类型(2.2)，D=mu_ell。Tate x 坐标的常数项为 z/(1-z)^2，并且

    z/(1-z)^2 - t/(1-t)^2
      = (z-t)(1-zt)/((1-z)^2(1-t)^2).

z,t 为不同 +/- 配对的非平凡 ell 次单位根，p!=ell；分子和分母都是单位，故 disc(f_H) 是单位。由 q'^ell=q 得

    ord J_H = -m(m-1)/ell * ord(q).                   (5.3)

因此在这些坏地方

    log|J_H|_w = 12m(m-1) a_w,
    sum_(w|v) alpha_w r_w log|J_H|_w
      = m(m-1)L > 0.                                (5.4)

这不是任意非零函数：J_H 由同一实际源曲线及其 isogeny 核构造，属于实际 K^times，确有 Kummer class；非零性和指定坏地方的 q 系数已证明。普通全地方 product formula 仍成立，并不因为(5.4)而失效。

## 6. 接到实际 evaluation 的一个有限次幂等式

复用已冻结的实际 evaluation 公式

    g_(w,j)=zeta_(w,j) qhat_w^(j^2),
    qhat_w^(2ell)=q_w,   zeta_(w,j) in mu_(2ell).

这里只在同一允许 realization 的原选定坏地方使用它。由(5.2)，存在实际单位

    u_w := J_H / q_w^(m(m-1)) in O_(K_w)^times.

设 N=2ell m(m-1)。则

    g_(w,j)^N = u_w^(-j^2) J_H^(j^2).                (6.1)

证明：N 是2ell的倍数，先消去 zeta；再代入 qhat^(2ell)=q 与 J_H=u_w q^(m(m-1))。没有猜测单位、没有把任意 label 当实际 output。

对局部 fractional ideals，(6.1)立即给

    g_(w,j)^N O = J_H^(j^2) O,
    (1/N) log|J_H|_w = -L/(2ell).                    (6.2)

因此原 native-q 数值在指定坏地方有一个明确的全局代数数有限次幂模型。实际 g_j 的 j^2 仍然存在，不能从(6.2)删除；源允许积分区域若不是整个 O，也不能擅自断言单位 u_w 保持它。更没有证明 J_H 或其根、逆元自身是原 C4 的允许输出。

把 local height 直接代入原 evaluation 可再校核：

    log|g_j| = -lambda_(E^sharp)(q^j) - (j/2)L + (ell/12)L.

半列平均为

    theta_seed = -(ell+1)L/24,
    Q_native   = -L/(2ell),
    Q_native-theta_seed = ((ell+4)(ell-3)/(24ell))L>0. (6.3)

与旧 evaluation-defect 包完全一致。高度的 normalization 常数和线性 j 项不能省略。这个 seed 的严格数值亏损与(4.2)、(5.4)的非零守恒同时存在；它说明辅助非零性本身尚不足以排除体积亏损。seed 不是完整输出 hull，不能据此给原 P6 反例。

## 7. 反证推进到哪里，以及不能填入的零等式

已构造的量在坏反设 Delta=Q_C-h_C>0 下满足

    Delta * sum rho_v M_v > 0.

但原全局高度0或 product formula 只控制未加 r_w 的和。r_w 随地方变化；没有理由把带 r_w 的和也写成0。事实上(4.2)、(5.4)已经计算出它严格非零。因此不能用同一个旧零恒等式拼出虚假的 0>0。

从本包得到的具体改变是：有了实际 J_H、明确的单位 u_w、有限指数 N、共同运输下不消失的标记配对，可以逐项测试实际源操作；不再只有一个待寻找的“全局补偿”。尚未得到的是：原源允许动作和积分区域如何把这些数据送进完整输出 hull，并使 h_C<Q_C 与某个对同一量有效的闭环恒等式或不等式矛盾。

另须保留全局边界项：J_H 在其他共轭坏地方的赋值由(5.3)给出，并不为0；在 ell-adic 和 archimedean 地方还需各自计算。因此不能把 div(J_H)/N 无条件等同于原 normalized native q 对象。在同一 K-realization 中，先定义原始局部除子集 d_q^sel：指定坏地方的系数为 qhat 的赋值，其余系数为0。此时可定义系数层面的真实差项

    D_boundary^raw := div(J_H)/N - d_q^sel,

本包证明其在原指定坏地方的系数为0。d_q^sel 本身尚不是已接入的全局 native-q arithmetic object：K 的全地方次数权重与 Fmod 的选定地方 normalization 必须显式转换；不能把式(3.3)的平均权重用到原 Q_C。archimedean metric、原 Ob3 reference 及原度数权重也需独立核对。本包未证明这些边界项在实际 relative determinant 中被抵消。

**一个可执行下一步：** 在原 Gaussian integral region 上代入(6.1)，逐项计算它的 weighted relative determinant：保留实际 u_w 的作用域、J_H^(j^2)、原 Ob3 reference、目标列 log shift 及 D_boundary。优先判定哪些操作共同运输 r 与 evaluation 标记；不可把它们按两个独立平均处理。需要交付实际 region 的等式/包含和剩余除子，而不是再次泛读 eta 的抽象解释。若某个候选步骤只是乘 J_H 的逆元而原动作不允许，则明确剪掉该步骤，不扩大输入或输出族。

## 8. 验证与验收

命令：`python tmp/sheaf/n8/closure/c9_strict_deficit_marked_height_20261025.py`；2026-10-25 最终版本运行 exit0。

精确核验：12个素数 ell=5,...,43；280920个 SL2 矩阵的 determinant 和直线像计数；8808个 marked Gram 项；每个 ell 一个20步共同运输例子。还有实际 Tate x 的整数系数截断展开、24个有限域中的非选定类型核多项式判别式，以及 J_H / Gaussian 的赋值指数等式。一般结论来自上面的证明，不靠有限测试外推。

ell=41 的例子：m=20；disc(f_H) 的 q 指数2660；J_H 在指定坏地方的 q 指数380，在其他类型为-380/41；N=31160。M_v=L/12，E_v=L^2/5904，seed=-7L/4，而 native q=-L/82。这些量严格区分。

自然语言证明：root 自审；无独立 agent 审查。statement_compiles、proof_body_checked（Lean）、kernel_closed、Project build、comparator 均未运行；target_accepted=false。没有修改 Lean 定义或原目标。P1/P6 和原严格亏损反证均保持 open。本包证明“能构造不抵消且源生成的非零量”及其局部实际 evaluation 接合，未证明完整输出体积保留。
