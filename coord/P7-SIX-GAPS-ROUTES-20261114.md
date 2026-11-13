<!-- BEGIN P7-SIX-GAPS-ROUTES-20261114 -->

## 六个剩余缺口：以实际构造和弱比较绕开过强接口（2026-11-14，单线程）

本节接续用户最新查重表，重点回答“下一步怎样消掉缺口”。A1 的交付重点是可替代同构的构造主线，不是再给一个 no-go。以下保留原文合格初始数据的范围；新增的比较、同构、归一化等式不能作为最终定理的外部输入。

这是阶段 1 的研究交接。已针对六个缺口追读实际定义、供体证明及本地论文；没有全仓逐一定理审计，也没有新运行 Lean 构建、公理检查或目标 comparator。下文“证明草案”与“已有源码定理”分开标明，不能据此把 P7 整体改成 DONE。单线程，无任务派发，无原 owner 源码覆盖。

独立交接文件与攻击计划中的本节为同一份内容快照。详细源码版本见 `dag/nodes/p7-six-gaps-route-assessment-20261114.json`。

### 0. 本轮建议如何改变工作顺序

| 缺口 | 主攻方向 | 具体应消除什么 | 本轮判断 |
|---|---|---|---|
| A1 | 保留实际 tensor，构造根格的逆像/收缩格；以包含、行列式比较替代载体同构 | `blockEquiv`、无修正的逐块读数相等 | 有明确可算的中间格和局部比较证明；接入原文允许 hull 是必须完成的构造步骤 |
| A4 | 保留实际剩余次数与局部次数，把它们放回 B5 和归一化 | 一般输入上的 `residue-one`、`weight=1` | 通用主线不应依赖这两个简化；真正全分裂的原输入可复用现有条件定理 |
| A5 | 复用 S3139 商及 mutation，补真实局部 log-shell、局部作用和来源兼容 | 模型对象到原文对象的实现与 Ind1/Ind3 识别 | 不是从零重造 production，也不是只填三个 `Nonempty` |
| A6 | 三个不交平移给出根侧 hull 相对质量 `≤1/3` | 通过 `1≤paperBox` 吸收常数的过强中间要求 | 对当前 S1915 对象有完整自然语言证明草案，优先形式化 |
| A7 | 直接用已有逐坏位依赖乘积；需要张量时才按 p 分组 | 全部 Bad 共用同一 p | 构造路线明确，不需要判定所有原输入是否碰巧同素数 |
| A8 | 使用“位置 × 标签”及 capsule 的多指标对象；最后证明重标记不变性 | 从位置硬选唯一 theta-label | 不追求任意函数的 inhabitant，构造原文实际索引与评价族 |

建议先做 A6 的短证明，同时在原 owner 的工作线上完成 A7 与 A1 的真实局部块；A4 接入同一套权重；A8 与 A5 一起供应真实多指标作用。这里是三条互补的推进链：**实际载体上的格比较；真实带标签的 multiradial 实现；当前上界的直接加强**。不是声称任一条单独已经证明整个 3.12。

本轮明确不重复安排：

- A2：复用 `Mzk1P2QNativeSourceArrowActual.p2QHat_norm_eq_qVFamily_norm`，以及同文件已经证明的 `p2RootQhatMagnitude_eq_native`、`p2QNativeReadingGap_holds`。该文件开头仍有旧 GAP 注释，不能用旧注释否定后面的证明。
- A3：复用 `productNormalizedLogPerDim_weighted`、`nativeWeightedMassDifference_eq_p2R13_of_blockwise`、已有 `processionAverage_eq_sum_div`、`processionAverage_scaledClosedForm`。剩下是给这些定理供应**正确的实际逐块比较和权重**，不是再证明有限和代数。
- #7：实际 tensor 的域乘积分解、finrank 和已有 diagonal 质量结论继续复用。
- 当前 `thetaR13Defect` 的零值/符号到 `nativeLComparison` 的条件消费链也已存在。保留这些证明，不另造同义接口；新工作应计算实际比较，而不是再要求一个 defect 符号输入。
- 已有 root norm、qhat/λ 整系数、单位质量归一化、局部主生成元/count 供体继续复用；不重新开旧 C3 inhabitant 任务。

### 1. A1 主线：构造原 tensor 上的比较格，不要求它等于根扩张乘积

#### 1.1 真正需要交付的弱关系

只为证明体积不等式，通常不需要

\[
A\simeq_{\mathbf Q_p}\prod_b L_b
\]

这样的指定代数同构。更合适的目标是在**原来的实际 tensor 载体** A 上构造一个格 J，并逐步证明

\[
Q_A\subseteq J\subseteq H_A^{\rm paper},
\tag{A1.1}
\]

其中 `Q_A` 是同一原输入的实际 q 格，`H_A^{paper}` 是该输入通过论文允许的 Ind1–3 和 holomorphic hull 得到的区域。两次包含配合同一测度的单调性，就给出所需方向的 log-volume 比较。

如果完整集合包含太强，只需比较实际格的 determinant；见 1.6。这里有意降低的是**中间运输要求**，原 q、原 theta hull、量词和最终不等式都不降低。

不得把 `H_A^{paper}` 改定义为“包含 J 的某个集合”，也不能把 (A1.1) 作为新 contract 的自由字段。J 要由已存在的根、赋值、实际域嵌入构造；第二次包含要给出原文允许操作的具体见证。

#### 1.2 第一步直接复用已有域分解，但保留它自己的因子索引

先固定同一份原文输入 S，再从 S 取得本地 T、theater family 和实际 q/θ。`OriginalInput` 原本就以初始 Θ-data 和 Hodge-theater family 为参数；若原定理允许这些输入，就从它们向下取局部数据，不额外要求从任意较弱的 native T 重造全部 family。反之，尚未证明来自 S 的 source identification 必须实际完成，不能同时传入独立的 T、I 再自由假设它们的 q 相同。

固定一个实际 p 块和一个实际 tuple，令

\[
A=\bigotimes_i E_i,\qquad
\eta:A\xrightarrow{\sim}\prod_{s\in S}F_s.
\]

`Mzk1P3TensorCoreActual.tensorCore_fieldProduct` 和
`FinitePlaceArithmeticTensorBlockFields.exists_arithmeticTensorTuple_fieldProduct`
已经供应这种分解。使用其实际 `S` 和 `F_s`，不再额外要求 `S ≃ Bad`。

这一点直接消掉一个错误的任务方向：分解因子是该 tensor 的域因子，不是全局坏位的重新命名。多项式的嵌入、tuple 及分裂行为都会影响因子数；它们不必逐个对应 Bad。

`Mzk1P3NativeDReanchorActual.BlockProductAlignmentData.factorEquiv` 当前只是集合 `Equiv`；另一份同名结构才要求代数等价。集合双射即使能选择出来，也不供应 Haar 或格运输。新主线不花时间填这个过弱又无实际消费者保障的双射字段。

#### 1.3 在每个实际域因子上放入所需根，再收缩回原域

先由源 q 元和实际 tensor 结构映射得到 `q_s ∈ F_s`。在 `F_s` 的代数闭包中加入**本块有限多个实际使用的根值**，得有限扩张 `L_s/F_s`。这里不要求全部根位于原 completion；复用正确域上的 N8/root 构造。

在最先应做的秩一块，写

\[
q_s=\alpha_s^N,\quad N=2l,\quad
H_s=\alpha_s O_{L_s},\quad
J_s=\{x\in F_s:\iota_s(x)\in H_s\}.
\tag{A1.2}
\]

`ι_s` 是实际代数嵌入，不是待证的跨载体同构。`J_s` 是现成对象的逆像，因此构造本身不需要比较假设。对已经有 `λ_s` 的最大根值块，也可取 `H_s=λ_s O_{L_s}`；以下公式用其实际赋值。

已有 `Mzk1P2LabelBlockCoefficientActual` / `Mzk1RouteC0RootQLatticeV2Actual` 给出实际

\[
\widehat q_s=\lambda_s c_s,\qquad c_s\in O_{L_s}.
\]

不要重证这条整性。需做的是把这个具体块实例接到 `F_s→L_s` 的同源 q 和 theta 值上。等式方向、根的选择及范数识别用 A2 供体。

#### 1.4 收缩格的公式及“损失如何支付”：这里有明确证明

令离散赋值 `v_F(π_F)=v_L(π_L)=1`，`e=e(L/F)`，`m=v_L(λ)>0`。对 `x∈F`，

\[
v_L(\iota x)=e\,v_F(x).
\]

于是逆像格不是未知对象，而是

\[
J=\pi_F^{\lceil m/e\rceil}O_F.
\tag{A1.3}
\]

证明逐步如下：

1. `x∈J` 等价于 `v_L(ιx)≥m`。
2. 代入 `v_L(ιx)=e v_F(x)`。
3. `v_F(x)` 为整数，故等价于 `v_F(x)≥ceil(m/e)`。
4. 用实际 DVR 的主理想赋值描述得到 (A1.3)。这只用单点离散赋值，不用两边载体等价。

若 `q=α^N∈F`、`λ=α`，设 `a=v_F(q)`，则 `ea=Nm`。因 `N≥1`，有 `a≥m/e`；又因 a 是整数，得到

\[
a\ge\lceil m/e\rceil,\qquad qO_F\subseteq J.
\tag{A1.4}
\]

更一般地，已知 `ι(q)=λc` 且 `c∈O_L` 时，直接有 `e v_F(q)≥m`，同样得到 (A1.4)。因此不是“假设取整误差足够小”，而是**实际整性自动支付取整误差**。

设 `|κ_F|=p^{f_F}`。相对单位格的真实 Haar 读数为

\[
\log\frac{\mu_F(J)}{\mu_F(O_F)}
=-f_F\lceil m/e\rceil\log p,
\]

所以

\[
\log\frac{\mu_F(J)}{\mu_F(qO_F)}
=f_F\bigl(a-\lceil m/e\rceil\bigr)\log p\ge0.
\tag{A1.5}
\]

这是一条可在原域直接使用的比较，既不需要 `f_F=1`，也不需要 `[L:Q_p]=[F:Q_p]`。

与按绝对维数归一化的根读数比较时，记 `e_F=e(F/Q_p)`、`d_F=e_F f_F`，则

\[
\frac1{d_F}\log\frac{\mu_F(J)}{\mu_F(O_F)}
=\log\|\lambda\|_L-\delta,
\quad
\delta=\frac{\log p}{e_F}
\left(\lceil m/e\rceil-m/e\right),
\quad 0\le\delta<\frac{\log p}{e_F}.
\tag{A1.6}
\]

这给出精确 degree/rounding 修正。不要把 δ 丢掉再要求一个假等式；(A1.4) 已提供实际增益覆盖 δ 的整数证明。

例：`F=Q_p`，`α^N=p`，`L=F(α)`，`e=N,m=1`。根侧相对质量是 `p^{-1}`，原域收缩格是 `p Z_p`，原域质量也是 `p^{-1}`；但二者**按各自维数归一化**后分别是 `-log p/N` 与 `-log p`。原域 q 格与 J 相等，比较完全成立；没有任何理由要求两个归一化数相等。这正是弱比较能够绕过强识别的例子。

#### 1.5 回到 tensor，并把缺口变成具体的生成元任务

定义

\[
J_A=\eta^{-1}\left(\prod_s J_s\right).
\]

先证明实际 q 格的每个生成元，经 `η` 后的各分量均属于 `J_s`。如果该 q 格是主格，这就是上面的赋值计算；多生成元时逐个做有限检查。**不要先假定 `η(Q_A)` 是各投影格的全乘积**：一般 tensor 整格在域分解后可能是非极大 order 的格，必须使用它的真实像。

随后攻第二个包含 `J_A⊆H_A^{paper}`。这里建议按以下具体顺序推进：

1. 从已有整基/trace-dual/SNF 供体取 `J_A` 的有限 `Z_p` 生成元 `g_t`；保留实际 tensor order 的指数。
2. 对每个 `g_t`，在源 procession 的真实标签和位置上给出一个允许的 representative/操作字，算出其落点，或给出这些落点的实际整线性组合。
3. 核对这些操作属于原文的 Ind1、Ind2、Ind3，不把任意线性变换宣布成允许操作。
4. 用原 hull 的定义所允许的闭包操作，把有限个生成元的证书提升为整个格的包含。
5. 用 `Mzk1Thm311MultiradialBundleActual.region_subset_possibleImages` 接入已有 possible-image 商框架；该定理只负责将**真实 representative 的区域**放入 possible images，不负责制造 representative。

如果 `J_A` 太大，继续缩到由这些实际可实现落点生成的格 `J'_A`。只要能给出实际 q 生成元在 `J'_A` 中的整系数表达，就有
`Q_A⊆J'_A⊆H_A^{paper}`。这是有意义的弱化：减少需要实现的 theta 区域，不削弱原结论。

特别注意：一个 q 点落入 hull 不足以比较正体积格。还必须证明整个 q 格落入，或证明原 hull 对相应整数环乘法/有限和封闭后由生成元推出。不能把零测度的单点包含当作体积比较。

**这一步是 A1 与 A5 的真实交点。** 本轮已经给出了 J 的构造、局部公式、误差计算和 q→J 的证明；尚未从现有源码验证所有 `g_t` 的原文允许落点证书。它应当成为实际下一包，而不是再写 `Nonempty BlockProductAlignmentData`。

#### 1.6 更弱的备选：只证 determinant 比较，连集合包含也可不要求

如果原 q 区域和 theta 区域都已证明是同一有限维空间中的满秩格，选一个**共同参照格** Λ 和实际坐标矩阵 `G_Q,G_H`。令

\[
C=G_H^{-1}G_Q.
\]

相同 Haar 测度下，

\[
\log\mu(H)-\log\mu(Q)
=-\log|\det C|_p.
\tag{A1.7}
\]

只要 `v_p(det C)≥0` 就够了；这比所有矩阵元素整、从而 `Q⊆H` 更弱。因矩阵是源生成元在共同基下的坐标，这不是任意选择一个有利 determinant。

执行方法：先复用 P2 的实际 `q=λc` 对角块；再加入 procession 置换、tensor 作用及实际基变换矩阵。用
`det(A⊗B)=det(A)^{dim B} det(B)^{dim A}` 和 determinant 的乘法性计算总因子。若需要从 `L` 回到 `F`，用
`det_F(Res M)=Norm_{L/F}(det_L M)`。

不同格的饱和指数必须算入：若 `Λ⊆Λsat`，则
`log μ(Λ)=log μ(Λsat)−log[Λsat:Λ]`。两个区域各算自己的指数，不能只给 theta 一侧免费饱和。已有 B5/count、整基和 trace-dual 的结果正是用于算这项，而不是重造一般理论。

这个备选的验收出口是**计算出来的 determinant 界**。如果最后仍只写“假设 `|det C|≤1`”，则任务未完成。

#### 1.7 读数怎样接，才能不再碰到原来的矛盾点

使用有符号实数读数

\[
\ell_\Lambda(S)=\log(\mu(S)/\mu(\Lambda)),
\]

并明确正、有限质量和原文所用维数/位置/标签权重。当前 `nativeTensorLogVolume` 经 `haarLogVolume(...).toReal` 得到非负截断值，不能把它当成可能为负的 `log‖λ‖` 来做精确识别。保留这个已有 API；另给原文比较建立有符号读数及与原目标的语义对应，避免悄悄改变旧定义。

`nativeLSideThetaReadout` 目前仍是该读数的别名；换成 `nativeLComparison` 的名称不自动解决原文对应。最终的 `−|log(q)|`、`−|log(Θ)|` 必须按原定义对齐：q 侧可用实际 norm<1 消去绝对值；theta 侧若要同样消去，须证明对应有符号 log 非正，或使用原文已确定的符号约定及其证明。尺度、参照项、常数 offset 和取绝对值都不能省略。由原始质量单调性得到的数值比较，只有经过这一步才能交给最终 3.12 消费者。

Haar 整体常数在同一空间、同一参照格的相对读数中会抵消。因此先在 A 上做 (A1.1) 或 (A1.7)，通常不需要再求跨两个独立 `addHaar` 选择的比例。

现有 `logMass_eq_add_log_factor` 和 `logMass_eq_add_log_addHaarScalarFactor` 仍可复用，但它们比较同一载体上的测度；它们不负责构造跨维度运输。普通嵌入的像也不能直接当作高维满 Haar 区域。

完成逐块不等式后，用实际非负权重求和，再复用 A3 的有限和/归一化供体。**不再要求 margin=1，不再要求逐块精确相等，不把 procession 平均替换成最大单标签值。** P2 的 λ 最大球只供应目前已证明的局部工具；它是否足够代表论文平均，必须由真实 production 的包含或 determinant 计算回答。

A1 推荐第一包：在一个实际 `qVFamTensorBlock T b` 上实现根格逆像 `J_b`、(A1.3) 和 `qO⊆J_b`，接入有符号相对读数。第二包才扩展到实际 tuple 和 permitted-image 生成元证书。所有陈述最终只参数化于合格输入及其索引，不带 `hcomparison`、`hblockEquiv`、`hδsmall`。

### 2. A4：把 residue-one 从一般主线删去，用实际 f 和 e 完成比较

#### 2.1 先分清三个不同的“次数为一”

本轮已核对 `Mzk1C17ResidueWeightChainActual`：

- `localResidueDegree_eq_one_of_residueFieldEquiv` 确实已证明，不重做。
- `nativeBadLocalWeight_eq_one_of_residueFieldEquiv` 还使用 finite、agree、**相对 ramification index=1**；仅剩余域同构并不单独推出 weight=1。
- `Mzk1P1ResidueOneActual` 中 `log N(v)=log p` 是绝对剩余次数为一；`K_w/Fmod_v` 的剩余次数为一是相对命题。相对次数为一不把底层数域的绝对次数也变成一。

因此需要保留两层

\[
N(v)=p^{f_v},\quad N(w)=N(v)^{f_{w/v}},\quad
[K_w:Fmod_v]=e_{w/v}f_{w/v}.
\tag{A4.1}
\]

Tame 本身不推出 `f=1`，也不推出 `e=1`。例如非平凡非分歧局部扩张就有 `e=1,f>1`；这是检验推理形式的例子，不冒称已经构造了整个项目 T 的反例。曲线的 split multiplicative reduction 也不等于任意选定数域扩张在该处完全分裂。

#### 2.2 通用构造：用已经存在的 norm/count 证明，不改写成 residue-one

对实际有限位 v，直接定义 `f_v` 为相应剩余域在 `F_p` 上的维数，或与项目 `residueInertiaDegree` 对应的实际 `inertiaDeg'`。然后应用本地 Mathlib 已有

`Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver`

（`.lake/packages/mathlib/Mathlib/NumberTheory/RamificationInertia/Inertia.lean`）到 `Z→O_K` 和实际 lying-over 位，得到 `N(v)=p^{f_v}`。这补的是项目实际 `residueNormBase`、`residueCharacteristic` 与现成 norm 定理的定义对齐，不是去引用外部新结果。

相对塔中已存在 `ArithmeticQPilotBaseChange.residueNormBase_eq_lower_pow`，直接复用。完成两者对齐后，`Mzk1B5FvResidueDegreeActual.ResidueDegreeStatement` 应有实际 `f_v` 的无条件实例，而不再只是 rows。

把已证明的局部主生成元/count 和 norm 桥代入，有

\[
-\log|g_v|_v=a_v\log N(v)=a_v f_v\log p.
\tag{A4.2}
\]

这里 `a_v` 必须是已有 count/valuation 对应给出的整数；绝对值若采用谱范数而非剩余域规范绝对值，则应改为 `a_v/e_v·log p`。两种规范通过实际局部次数相连，不能混用。

按绝对维数归一化时尤其简单：

\[
\frac{a_v f_v\log p}{[K_v:Q_p]}
=\frac{a_v}{e_v}\log p.
\tag{A4.3}
\]

所以 f 会在**正确归一化**中自然消去；不需要先证明 f=1。若使用项目的相对权重 `1/[K_w:Fmod_v]`，则保留相对塔的 e、f 和底层绝对次数，逐项约分，不把这项权重设成 1。

#### 2.3 如何接原比较而不只是把假设改名

有两种实际消费者，必须分开：

1. **等式型 B5/乘积公式消费者**：保留 `f_v log p=log N(v)` 的完整等式，接已有有限支撑、分式理想 norm、全局 determinant 汇总。禁止把丢掉 f 的旧等式继续当目标。
2. **只需下界的 prime-conductor 消费者**：若实际 `a_v≥1,f_v≥1`，则 `a_v f_v log p≥log p`。从同一 p 的实际非空纤维选一个位就够了；其余未加权非负项可以保留或舍去。不必要求该纤维的所有 N(v) 都等于 p。

若外面带有小于 1 的局部权重，第二条不能直接得出同样的 `log p` 下界；应保留权重并使用原文实际的全纤维次数求和式。只选一个 section place 与对全部上方位求和，不是同一公式。

已有 `sum_relativeCompletionDegree_eq_fieldDegree` 以及 `FinitePlaceDegreeSumBound` 的次数和供体可复用。新任务是把消费者的实际索引接进去，不是重证次数和。

#### 2.4 如果原文某处确实只允许 degree-one 输入

这时才走 residue-field 同构路线：从**实际已给定的全分裂/局部同构**构造整数环映射，再降模得到 `κ(v)→κ(w)`，证明它满射；域同态的单射性给出代数等价，最后调用现成条件链。

可执行证据必须是原数据中的具体局部同构，或具体定义多项式在该处的完全分裂及所选因子计算。仅有“finite/tame/split”字样，或者把剩余域同构再包装成 `Nonempty`，不算构造。

本轮读到的 IUT I Definition 3.1(b)、(c)、(e) 分别给出坏位、l 的互素条件和选位 section，并未在这些条款中给出一般 `K_w/Fmod_v` 的 `e=f=1`。这不足以否定其他特定原文情形，但足以要求本主线不无依据依赖它。

A4 推荐下一包：固定实际 v，完成 `N(v)=p^{f_v}` 的项目定义对齐，直接接现有 B5/count，输出保留 e、f 的原文规范读数。只有精确来源支持的 degree-one 特例才另接已有条件定理。

### 3. A5：复用已有 S3139 production；补的是原文局部实现和作用识别

#### 3.1 对查重表再做一层精确修订，防止重复安排

以下源码均已读到，不能再写“production 完全不存在”：

- `S3139SourceMultiradialQuotientActual` 已有 carrier、商映射、logVolume、possibleImage、level、Ind1/2 不变性、Ind3 上半兼容和 nonempty。
- `S3139FirstTriangleResidualActual.sourceMultiradialMutationDemandInhabitant` 已实现指定 0-column etHT 级 mutation=id。
- `S3139FirstTriangleFieldBActual.sourceLGPDataMissing_Real_holds` 和 `sourceLogShellContractMissing_Real_holds` 已供应**标准实数模型层**的前两个 `Nonempty`；其中 valuation/place 是 `Unit`，log-shell 是标准 Real 模块，不能等同于论文局部对象。
- `S3139FirstTriangleFieldACResidualActual` 已将 `Fmod→+*Real` 重分类为建模约定；`S3139C1InfinitePlaceActual` 已构造 actual infinite place choice 和 realification 的 nonempty。
- `S3139FieldCPublicInterfaceActual` 已有无需全局实嵌入的乘法实数 character。这个替代也不应再新建一遍。

因此“还剩三个 `Nonempty`”是偏早的接口快照。当前正确任务是：**将已存在的标准模型和部分商实现，接到真实局部 log-shell、真实 LGP 作用及原文 Ind1–3。**

还要理解已有商的具体含义：`S3138SourceProcessionCoreActual` 的 choice 是 family index × Nat；Ind1/2 实现为格点平移，Ind3 为 level 增加。`S3138SourceProcessionProfileActual.possibleImage` 是对应 theta log-volume 的单点集，其读数恒定性用于证明兼容。这个部分实现值得保留，但尚不能直接代替所有原文可能像及其 hull。

#### 3.2 字段 A：真正的 capsule/log-shell 数据怎样构造

按原文 Theorem 3.11(i)(a)，对每个非阿基米德 p、procession level j、capsule 位置 `i∈{0,…,j}`，建立

\[
E_{p,j,i}=\bigoplus_{v\mid p}K_{v,i},\qquad
A_{p,j}=\bigotimes_{i=0}^{j}E_{p,j,i}.
\tag{A5.1}
\]

每个 `K_{v,i}` 来自同一源 prime-strip/capsule 的实际 completion；每个局部区域来自实际 `sourceLocalLogShellDatum`。有限直和与有限乘积的等价、tensor 对有限直和的分配，复用 `SourceProcessionCapsuleData.tensorPacketEquiv` 和已有 arithmetic tensor 层。

有一个必须处理的类型细节：积分 log-shell 是格，不应未经证明当成 `Q_p` 向量空间。用其实际 ambient/Q-span 做 `LogShellFamily` 的模块载体，同时单独保存积分区域及其包含、紧性、生成性。不要把格强行赋予除以 p 的封闭性。

也不把所有 p 的模块强行放到一个 `Real` 系数域下。按 p 实例化局部合同；阿基米德部分单独用实际实/复 completion。最终的实数只是 log-volume 读数。

`n,m∈Z` 是论文两类 lattice 坐标；j、i 是有限 procession/capsule 索引。它们不能混成一个任意 `n:Nat` 字段。现有 `Procession.ofOriginalInput`、`CapsuleTheaterAssignment` 可作组装供体，但选到的是实际原文 prime-strip family 这一点仍要证明。

#### 3.3 字段 B：把源 theta 乘法单子放回实际局部空间

先在实际局部域/其所需有限根扩张中取现成的 theta 值，再取这些值的乘法子幺半群。`Submonoid.closure` 及 `ThetaPilotObject.ofGenerator` 的轨道构造已有，不重证。

新工作是将生成元固定为**实际 source theta 值**，并对每个 `(i,v)` 写出真实乘法作用。然后用直和映射和 tensor 的多线性泛性质延拓，证明作用律和在 pure tensor 上的计算公式。

若作用在不同位置使用不同标量，旧 `LGPMonoidAction.scalar : G→*R` 的单一标量不足以表达它。此时使用已有局部/tensor action API，或把作用改为 `G→*Module.End R A`，并给出具体对角/分量作用；不把真实独立复制作用压缩成一个未经证明等价的实数缩放。

`Mzk1P2LabelBlockCompleteActual` 已供应秩一 `(b,label)` 的 q、theta、landing、degree 原型。复用它，新增的是原文多指标 tuple 的落点和实际允许换根/单位操作，不能把 identity landing 的原型当作全部多指标证明。

#### 3.4 字段 C：采用现有局部/实化 character，不追全局实嵌入

对有限位，真实副本作用应由原文的局部单位/共轭/log-shell 数据产生。对无限位，复用
`sourceFmodArchimedeanLog`、`sourceFmodArchimedeanScalarCharacter`、`sourceInfinitePlaceChoiceActual`。

`Fmod→Real` 的环嵌入对一般数域并不自动存在；而从实际无限位取绝对值并取 log 的实化通道已经有构造。接下来需证明消费者所需的作用确实经这个 character 因子化；若还需要相位/共轭信息，则继续保留实际复 completion，不能以绝对值替代整个作用。

如果原文同时使用所有无限位，保留整个无限位族及其权重；任取一个无限位的已有构造只能解决存在性，不能代替全局读数。

#### 3.5 Ind1/Ind3 应如何从实际构造证明

Ind1 的下一步是一个可以计算的等变方块：对实际 procession automorphism g、实际源数据 x，逐个证明

\[
\operatorname{eval}(g\cdot x)=g_*\operatorname{eval}(x).
\tag{A5.2}
\]

先对局部生成元证明；再经有限直和和 tensor 延拓；最后用已有商的不变性/下降定理。Ind1 并非随意对 `Z×Z` 指标平移，所以下降框架可以复用，原文作用的识别必须另外落地。

Ind2 同样先做实际副本在局部因子上的作用，再用现有 `ind1_ind2_tprod_commute` 等 pure-tensor 公式完成非干扰。只有该作用适用域和实际系数正确时，既有公式才是原文供体。

Ind3 要按原文 III 3.11(ii) 最后部分处理：非阿基米德处是相应 log-link 区域的包含，无限位处是相应自然满射及其读数兼容。不能只把 `level↦level+n` 的数值单调性宣布成该兼容。

最小执行单元：**一个 p、一个 j、相邻两个 m 列**。构造实际 transport，算清局部生成元的像，证明所需包含/商像关系，再推广为任意 m 的函子律。这比一次性提交一个带十个待证字段的大结构更可检查。

#### 3.6 从 production 到 3.12，必须留下的最后一段实质证明

定义可能像时使用实际 representative 的区域并集；复用已有 quotient/possibleRegion API。接着完成两个方向各自需要的证据：

1. q 对应的允许 representative 或足够逼近的实际像，使 A1 的 q 格/比较格进入原文 hull；
2. 对全部允许 representative 的统一体积控制，使这个 hull 的 log-volume 有限，并符合论文归一化。

第 1 项提供下界，第 2 项提供有限性/上界。一个 nonempty 或一条恒定 profile 不能代替二者。也不能先把 possible log-values 定义为 `Iic(thetaReadout)` 再从定义得到目标。

本地原文 III 3.12 Step (xi-d)–(xi-f)，尤其 pp.183–184，正是这部分源像/可能像比较的定位。本轮没有找到能无条件替代所有这些兼容的现成总定理；这里是仍需实质证明的核心，但上面已将它降到实际局部映射、生成元和作用方块，而不是抽象重述。

### 4. A6：直接压低当前 S1915 读数，不必先排除 disc=cond=1

#### 4.1 为什么要改攻这个方向

已有 `paperBox_disc_one_cond_one_zero` 和 `not_one_le_paperBox_disc_one_cond_one_zero` 只说明“通过 `1≤paperBox` 吸收 1”的旧证明在此失败。它们没有说明实际 `V≤paperBox` 失败。实际 V 可以更小。

现成 S1915 读数是

\[
V_T=1+\log\frac{\mu(H_T)}{\mu(O_T)}
=1+\sum_{b\in Bad}d_b\log r_b.
\tag{A6.1}
\]

由 `S709RootImageRadiusFormulaActual.rootImageRadius_eq_rootNorm` 和
`rootNormedElementNorm_lt_one`，每个 `0<r_b<1`。原输入的坏位集非空，剩余特征为奇素数；选位的 comap 保持该素数。

#### 4.2 完整自然语言证明草案：三个平移

固定一个实际坏位 b，令 `L=L_b`，`O={x:‖x‖≤1}`，`H={x:‖x‖≤r_b}`。

1. **三个中心的距离都是 1。** 在奇剩余特征的 `Q_p` 扩张中，`‖1‖=‖2‖=‖1−2‖=1`。`‖2‖=1` 可由实际 `norm_algebraMap'` 和 `p≠2` 的 p-adic norm 得到。
2. **`H,1+H,2+H` 两两不交。** 若两个平移相交，两个中心之差就是两个 H 元素之差。超度量不等式给出其范数 `≤r_b<1`，与第 1 步矛盾。
3. **三个平移都在 O 中。** 中心的范数≤1，H 元素的范数<1，再用超度量不等式。
4. **各平移质量相同。** 使用实际加法 Haar 的平移不变性。H 为可测闭球，已有正、有限质量供体。
5. **有限可加性和单调性给出**
   \[
   3\mu(H)\le\mu(O),\qquad
   0<\mu(H)/\mu(O)\le1/3.
   \tag{A6.2}
   \]

这条证明不需要先构造剩余域同构，不需要 `f=1`，也不需要重新证明完整局部域 degree 公式。

对每个坏位可做同一计算。只使用一个非空坏位和其余因子的质量比≤1，已有乘积质量公式就给出

\[
0<\mu(H_T)/\mu(O_T)\le1/3,
\quad
V_T\le1-\log3<0.
\tag{A6.3}
\]

也可以得到更强的 `V_T≤1−|Bad|log3`，但下一包只需证明 (A6.3)，不必扩大范围。

于是当 `disc=cond=1,C0=0` 时，`paperBox=0`，直接有 `V_T≤paperBox`。完全不需要从抽象 `CurveData` 排除 `(1,1)`。若消费者使用截断的 `s1915A0`，已有 `s1915_a0_eq_zero_of_closedForm_nonpos` 进一步给出 `s1915A0=0`。

#### 4.3 实现时复用什么、只新增什么

复用：

- S709 的实际 radius=root norm 和严格小于 1；
- `SourcePlacePartitionReduction.badResidueLabel_odd`、实际选位的 residue-characteristic/comap 识别；
- S1915 的 `s1915_local_measure`、`s1915_hull_toReal`；
- `Mzk1HullUBPaperVRawBindingActual.closedForm_eq_one_add_normalizedLog` 所在既有读数链及现有 normalized-log 公式；
- 已有 Haar 平移不变性、可测有限并的可加性，及 `paperBox=0`。

只新增三个实质步骤：局部三平移估计；乘积比≤1/3；当前 `s1915ClosedForm≤0` 并接特殊 `paperBox=0`。建议新包声明只带 T 和当前既有类型类，不加入 `hVnonpos`、`hdiscImpossible` 或 `hresidueOne`。

**验收范围必须明确。** (A6.3) 是对当前 S1902/S1915 根最大球及其 `1+raw relative log` 的证明草案，尚未 Lean 验证。若改成 `1+(log ratio)/D`，同一估计只给 `1−log3/D`；若原文 Ind1–3 允许区域更大，也不能自动保留 `≤1/3`。因此它可消除当前 #9 的这个数值阻点，不能替代 A1/A5 对原文区域和归一化的接入。

#### 4.4 语义侧的备选路线

若最终 #9 必须使用实际曲线的 conductor/discriminant，另一条合法路线是从原输入非空的坏约化位直接证明实际 conductor 或最小曲线判别式理想有非零支撑，从而其绝对 norm≥2，再复用已有 `box_ge_one_of_cond_ge_two` 或 disc≥2 版本。

这只需证明同一源曲线在指定坏位的局部指数>0，不需要承担“所有数域上不存在处处好约化椭圆曲线”的过强命题。要区分曲线最小判别式和数域判别式，且必须把 `CurveData` 绑定到这条实际曲线。把 `cond≥2` 重新作为自由输入仍未完成。

本轮优先推荐三平移路线；它对当前消费者更短，并且可以实际处理 `(1,1)` 而非排除它。

### 5. A7：取消全局固定 p；先复用已有逐位置模型

#### 5.1 最少改动的主线其实已经有基础

`QVFamTensorCoefficientActual` 开头明确说明当前家族按 Bad 依赖索引，每个 b 使用自己的 `qVFamTensorP T b`；`qVFamTensorPlaces T b` 已给该素数下的实际单块。`PaperRootExtensionProductHaarActual` 的根域乘积也允许每个因子有自己的 p。

因此 #10 的根侧单位质量/有限乘积消费者，优先直接使用这个依赖乘积。有限个局部紧群的 Haar 乘积不要求它们都是同一个 `Q_p` 的向量空间。不要为了套一个统一标量域 API，新增“所有 Bad 同 p”的算术假设。

若真实消费者只是 `∏_b μ_b(U_b)`、`Σ_b log μ_b(U_b)`，根本不需要先做 prime partition；已有乘积公式接上即可。

#### 5.2 需要共同 `Q_p` 的 tensor 时，才做真实分块

令

\[
P=\{p_b:b\in Bad\},\qquad B_p=\{b\in Bad:p_b=p\}.
\]

有限性由当前有限 Bad 得到；映射

\[
b\longmapsto(p_b,b),\qquad
Bad\simeq\coprod_{p\in P}B_p
\tag{A7.1}
\]

及逆映射都直接由投影构造。`Mzk1NativeBadPrimeSourceActual.nativeBadToKPlace_completionRationalPrime` 已证明上方位与下方坏位的 p 一致，直接用于每个纤维的 `FinitePlaceAtPrime`。

对每个 p 独立构造 tensor、域分解、实际 Haar 和 A1 比较。然后使用坐标重排的连续/可测等价及有限乘积公式，把结果拼回全 Bad。

要证明的是

\[
\prod_b\frac{\mu_b(H_b)}{\mu_b(U_b)}
=\prod_{p\in P}\prod_{b\in B_p}\frac{\mu_b(H_b)}{\mu_b(U_b)},
\]

以及对应的 log/加权求和重排。已有每个 `μ_b^{norm}(U_b)=1` 的归一化可照用；不把未归一化原始 `μ_b(U_b)` 宣称为 1。

#### 5.3 必须防止的两个拼接错误

第一，不同 p 块的笛卡尔积并不是一个自然的共同 `Q_p` 向量空间。`Σ_b d_b` 可以作为已定义数值权重的分母，但不能伪装成某个不存在的统一标量域下的 finrank。

第二，Bad 的有限乘积与所有有限位的 restricted product 不同。若 #2/#10 最终使用全部有限位，保留现有 restricted-product 载体及几乎处处单位格；这里只对有限坏位部分重排，不能把无限乘积质量公式照抄上去。

A7 下一包：先对具体 #10 消费者检查是否能直接删除 `NativeBadPrimeData` 参数、改接依赖乘积；只有确需 tensor 的消费者才供应 (A7.1)。这条路线对不同素数并存也有效，不靠先证明固定 p 为真。

### 6. A8：由“位置选一个标签”改为真实带标签的评价族

#### 6.1 本 gap 不是普通函数存在性

`BadThetaLabelMap` 只有字段 `labelOf : Bad→ProcessionLabel l`，而 `ProcessionLabel l=(ZMod l)ˣ` 有单位元 1。其裸类型用 `fun _=>1` 就能填。因此“无 inhabitant”应精确理解为**没有已证明原文忠实的标签映射**，而不是这个函数类型本身不可构造。

`candidateLabelOfPlace` 把有理剩余特征模 l 变成单位，只是一个候选函数；它没有把 prime label 变成 theta label 的源证书。下一包不应以 `Nonempty BadThetaLabelMap` 为验收指标。

#### 6.2 主线构造：标签和位置都保留

在最简单的秩一情形，使用

\[
\operatorname{Eval}(b,j)=\theta_{b,j},\qquad (b,j)\in Bad\times\operatorname{ThetaLabel}.
\tag{A8.1}
\]

`Mzk1P2LabelBlockCompleteActual.P2ActualLabelBlock` 已采用 `(b,label)`，实际 q、theta、landing、degree 字段及根关系证明都在。复用它，逐步把其中 SignedLabel 索引接到论文确切的标签对象。

对 procession，真实索引更细：level j、位置 `i∈{0,…,j}`、每个 i 选一个上方位的 tuple。其 tensor 分配后为

\[
\bigotimes_{i=0}^j\left(\bigoplus_{v\mid p}E_{i,v}\right)
\simeq\bigoplus_{\mathbf v}\bigotimes_{i=0}^jE_{i,v_i}.
\tag{A8.2}
\]

这里一个位在不同标签/不同 tuple 中可以反复出现；没有必要、通常也没有理由先从该位选出唯一 j。

若不同标签的实际位置族不同，使用依赖和 `Σ j, Place j`，不是强行笛卡尔积。原文已有的 prime-strip/procession 输入决定这些纤维；A5 的 capsule 实现与这里应是同一套对象。

#### 6.3 如何处理 canonical：证明自然性与选择无关，而非寻找无依据的唯一标签

原文若提供 level/标记数据，则对这些**原有数据**作评价；原文若只决定一个 torsor/轨道，则选择一个已证明存在的标记，并证明换标记由真实 procession automorphism 作用。

对置换 σ，要逐项证明

\[
\theta'_{b,j}=\operatorname{transport}_\sigma(\theta_{b,\sigma(j)}),
\quad w'_j=w_{\sigma(j)},
\]

再由有限和重排得到加权读数相等，或由区域运输得到 hull/体积不变。这个不变性才让最终结论无需额外选择输入。

若使用 `(Z/lZ)×` 与除以 `±1` 的标签模型互换，必须先证明被平均函数的 `j↔−j` 对称性，再计算每个轨道的重数。`SignedLabel` 含 0、`ThetaLabel` 的正代表和 `(ZMod l)ˣ` 的基数不同，不能只凭名称换分母。已有 cardinal 和平均公式继续复用，新增的是实际评价及重数对应。

#### 6.4 #2 的 divisor 消费者怎样接

`Mzk1IQFiniteAdeleStructuresActual.principalSupport_labelImage_finite` 对任意标签函数都成立，它不能给 theta 标签赋予原文意义。若消费者只需有限支撑，直接用已有 `principalDivisorFull` 和其 support 结论。

若消费者需要带标签的支撑，构造 `support(div a)×Label` 或实际依赖索引的对应有限并；有限性由已有 support 和标签有限性得到。无需新设从全部 HeightOneSpectrum 到唯一 theta-label 的函数。

A8 下一包：选一个已有实际 `(b,label)` 块，接入源 capsule 的真实评价及换标记作用；证明一条可供 A3 消费的加权读数不变性。不要重复 principal divisor 的有限支撑证明。

### 7. 建议交接为以下具体小包，沿用现有 owner

以下为建议，未派发、未调整已有 owner。新名称只是任务目标描述，不表示这些 Lean 声明已经存在。

| 包 | 首个实际动作 | 复用供体 | 完成后删除的困难输入/实际消费者 |
|---|---|---|---|
| R6 | 对实际根球证明三个平移估计，再证 `s1915ClosedForm≤0` | S709、S1915、实际 Bad 奇性、Haar 平移 | 当前 #9 的 `1≤paperBox` 吸收入口；处理 `(1,1)` |
| R7 | #10 先改接现有 per-b Haar product；必要时构造 prime fibers | QVFamTensorCoefficient、NativeBadPrimeSource、ProductHaar | `NativeBadModuliFixedPrime` |
| R1a | 构造实际单块 `J=ι⁻¹(λO)`，证 ceil 公式和 q 格包含 | P2 实际整系数、正确根域、现有 DVR/count | 指定 root/base 同构要求 |
| R1b | 用实际 tensor 分解把 J 放回原载体；逐生成元供应允许像证书，或算真实 determinant | tensorCore、trace-dual/SNF、P2、possibleRegion | #6/#10 的 `blockEquiv` 与 #1 强 scalar dictionary |
| R4 | 实例化实际 `N(v)=p^f`，沿原绝对值规范接 B5/degree weights | Mathlib norm、B5/count、relative degree sum | 一般 `residue-one`、一般 `weight=1` |
| R8 | 实现真实 label-place/capsule 评价族和重标记不变性 | P2ActualLabelBlock、capsule、procession average | 没有语义证书的 place→单标签接口 |
| R5 | 在一个 p、j 和相邻 m 列实现局部作用方块，接回 S3139 商 | actual local log-shell、S3139 mutation/quotient/copy channel | 模型到真实 production 的缺口；供应 R1b |

每包都应记录实际原输入、源/目标区域、参照格、局部/标签权重及最终消费者。对 R1b、R5，实际允许像的构造和兼容是尚未完成的数学步骤；不能用一个新 `Data` 结构收纳这些结论就宣称关闭。

### 8. 完成标准与当前交付边界

本轮产生了两类实质内容：

1. **可以直接转成证明包的推导**：A1 的收缩格/ceil/局部 q 比较、实际 determinant 比较路线；A6 的三平移上界；A7 的依赖乘积及 prime 分块；A4 的真实剩余次数规范化。
2. **必须按真实生成元完成的构造路径**：A1 的比较格进入原文允许 hull；A5 的局部作用、跨列兼容及可能像；A8 的原文标签评价及不变性。这里给出了对象、具体映射、局部计算和已有消费者，但尚无完成全部步骤的证据。

最终必须是从原文合格初始数据得到原结论。可以使用论文原有输入及从这些输入实际构造的选择；不能新增 `hcomparison`、`hresidueEquiv`、`hfixedPrime`、`hpaperLabel`、`htransport` 等未证前提买到绿色状态。

本轮四项验收：`statement_compiles=NOT_RUN`，`proof_body_checked=NOT_RUN`，`kernel_closed=NOT_RUN`，`target_accepted=NOT_RUN`。没有修改 Lean 源码，也没有宣称六个缺口或 3.12 已关闭。

本地原文锚点：IUT I Definition 3.1，印刷 pp.61–63；IUT III Theorem 3.11，pp.153–156；Corollary 3.12 及 Step (xi)，尤其 pp.173–174、183–184。本轮未新增外部调研。对于原目标尚未获得的 source identification，仍保留为明确证明责任，不用本地模型的容易比较代替原文命题。

<!-- END P7-SIX-GAPS-ROUTES-20261114 -->
