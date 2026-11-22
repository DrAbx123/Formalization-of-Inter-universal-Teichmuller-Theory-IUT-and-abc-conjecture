# G1／P6／P8 剩余构造路线图

更新日期：2026-11-17；证据截点：23:49:06（UTC+08:00）。核对对象为本次实际读取的工作树、关键声明及 watchdog 记录；版本清单见 [本次证据](D:/lean/coord/P7-G1-P6-P8-ROUTE-EVIDENCE-20261117.json)。Git HEAD 为 a997af4b1cb2339d1e7403ef0781a16f809f4476，工作树含未提交成果。旧正文已移至 [历史快照](D:/lean/coord/archive-20261117/P7-G1-P6-P8-CLOSURE-ROUTE-before-refresh.md)。本文只安排剩余任务，已经实现的构造不再保留教学式步骤。

最终目标仍是：对每个 ε>0，先构造独立于 ABC 三元组的 Cε，再推出原有 ABCConjecture。实际 producer 不接收 hCor312、D1、FreyHeightBound、自由的高度不等式或来源同一化作为新增数学假设。下文“出口”是要证明的命题，不是已经有 inhabitant 的声明。本次只修改研究文档；没有编译、修改 Lean 或重验最终闭包。

## 1. 现在真正剩下的八包

| 包 | 尚未完成的实际内容 | 直接消费者 |
|---|---|---|
| R0 | 将实际赋值、体积、q 高度、普通高度放在同一归一化下；消除单坐标高度与除子高度的混淆 | R1–R3、R6、R7 |
| R1 | 从实际 q/source 构造同一个 θ 对象的 −M 下界；证明全纤维、root、carrier 与原 reading 的识别 | P5→actual hCor312 |
| R2 | 实际 procession/packet 的上界与 R1 的同一个 θ 读数相接；生成 hVh、hlogdK、hsQ 的实际数据 | 独立 C3→C4、IUT IV |
| R3 | 每个 λ 的合格 Θ-data、选素数与被删 q 位的统一误差；产生归一化的局部高度估计 | D1、R6 |
| R4 | 一般有限受保护点的实际 noncritical Belyi map；补一般截面实例与受保护值的有理函数递归 | 有限不交边界族、R5、R6 |
| R5 | 有界次数局部域的 SeparationInput；实际射影点、映射、边界距离与统一紧集的接线 | 固定 K_V 与统一常数 |
| R6 | 实际带度量的 log-canonical 高度、边界 conductor、有效除子高度上界 | hω ≤ (1+δ)D(L)+C |
| R7 | 实际 Fermat lift 的全局不同估计，及在同一实际点上填入 P8 数据 | P8 producer→既有 ABC consumer |

证明方向固定为：

\[
\begin{gathered}
R0+(R1,R2)\longrightarrow\text{实际体积夹逼／hCor312／C4},\\
R3+\text{C4}\longrightarrow\text{归一化 D1},\\
R4+R5\longrightarrow\text{固定有限映射族、固定 }K_V,\\
\text{D1}+R4+R5+R6\longrightarrow h_\omega\le(1+\delta)D(L)+C,\\
R7+\text{上述高度界}\longrightarrow\text{P8 actual producer}\longrightarrow ABC.
\end{gathered}
\]

P6 的最终 display、CTheta 下界的消费者及 P8 consumer 都处于下游；不能拿这些消费者的结论反过来生成它们要求的输入。

## 2. R0：先固定剩余构造真正使用的量

### 2.1 q 的两种赋值和两层域次数

记 b 为 Fmod 的坏位，P 为 F 中位于 b 上方的位，w 为 K 中位于 P 上方的位。统一使用：

\[
v_P(\pi_P)=1,\qquad e_P^{abs}=v_P(p),\qquad
|x|_P=p^{-v_P(x)/e_P^{abs}}.
\]

qVFamNormalizedCoefficient 的实际定义是 −log_p‖q‖，不是按名字就等于整数阶。应当证明的具体字典是

\[
c_P=\frac{v_P(q_P)}{e_P^{abs}}.
\tag{R0.1}
\]

S826CNormOrderRamificationActual 已有给定范数比较后的归约；QVFamNormalizedGeneratorSupplyActual 已有实际 generator 和范数公式。剩余工作是把实际源的赋值、实际 spectral norm 代入，不能再把“c=order”当默认规则。

若 q_P 来自同一 b 的 Tate 参数，或者其阶通过共同 j 值识别，则应得到

\[
\frac{v_P(q_P)}{e(P/b)}=v_b(q_b),\quad
c_P=\frac{v_b(q_b)}{e_b^{abs}},
\]

以及全纤维公式

\[
\frac1{[F:\mathbb Q]}\sum_{P\mid b}f_P^{abs}v_P(q_P)
=\frac{f_b^{abs}v_b(q_b)}{[Fmod:\mathbb Q]}
=\frac{[Fmod_b:\mathbb Q_p]}{[Fmod:\mathbb Q]}c_P.
\tag{R0.2}
\]

实际可复用的是 Mzk1ULOrdTowerActual 的阶运输与 Mzk1ULFiberSumActual 的 Σef；它们不替代“这些 q_P 确实对应同一个算术参数”的证明。该证明用源的 Tate/j 关系逐位导出，而不是要求所有 completion 彼此同构。

Mzk1ULThetaMWeightActual 已证明一个新权重的代数消去式；Mzk1URThetaKLambdaMScaledActual 也已写出新读数定义。但这不证明新读数等于论文对象。尤其按 (R0.1) 使用 spectral norm 时，绝对 ramification 已经进入 c_P；再除 e(P/b) 可能重复除法。先完成 (R0.1)–(R0.2)，再确定上下界共同使用的权重。不要以补齐某个等式为目的重新选权重。

### 2.2 高度归一化的实际修正

本地 Mathlib 的 NumberField.logHeight₁_eq 给出各位贡献的总和；totalWeight_eq_finrank 给出总权重 [L:Q]。现有 Mzk1G1QHeightActual.lambdaHeight/jHeight 直接使用这套高度。另一方面，Mzk1G1LocalHeightCriterionActual.discOver 与 truncConductor 已除以 [L:Q]。

因此后续主线显式使用

\[
\bar h_L(x)=\frac{\operatorname{Height.logHeight}_1(x)}{[L:\mathbb Q]},\qquad
D(L)=\frac{\log|\operatorname{disc}L|}{[L:\mathbb Q]}.
\tag{R0.3}
\]

这是一项需要接入实际消费者的中间量修正，不是把旧 D1 定义悄悄解释成另一种高度。处理方式二选一：全程使用 (R0.3)，或将 D、N 和误差全部乘回域次数。前者更适合论文的 normalized degree；最终在 Q 上两者相同。

已有 jHeight_relation_deg / height_dictionary_deg 的证明直接除以正次数即可复用，不能重派 D3 的多项式估计。剩余证明是高度对域扩张的次数公式及实际 q 高度的对应：

\[
\bar h_L(j(\lambda))
=Q_{\mathrm{all,finite}}(\lambda)+\text{archimedean contribution}.
\]

在固定 K_V 上控制后一个量，以及被排除有限位的贡献，才能进入 R3；不能将 Q 的名字改成 jHeight 就宣布接线。

### 2.3 F4 的高度对象不能沿用当前代理定义

Mzk1HTF4ActualInstanceActual 中

\[
hDivP=\operatorname{Height.logHeight}
       (\text{fun } \_:\mathrm{Unit}\mapsto P(x))
\]

是单坐标的射影高度。Mathlib Height.logHeight_eq_zero_of_subsingleton 直接说明它恒为零。其上界引理对这个定义成立，但不是有效除子在移动点 y 上的高度估计。

同样，Mzk1HTF4DivisorHeightActual 的“有限点集上按系数加权求和”是形式代数；只有将权重构造成依赖 y 和算术位 v 的实际局部 Weil 函数，才会成为此处要用的 h_E(y)。R6 给出直接构造；不安排证明这个零代理量等于真实除子高度。

**本包出口：** 对后续每个真实量给出“对象—度量/赋值—域次数—位权重”字典，并证明 (R0.1)–(R0.3) 的实际实例。公式转换保持原最终 ABC 目标；旧的条件消费者保留作代数供体。

## 3. R1：实际 −M 下界及原 reading 的识别

### 3.1 当前剩余的准确命题

现有 Mzk1URThetaKLambdaSqueezeActual 的无条件下界是

\[
-S_{\rm ceil}\le\theta_\lambda,\qquad
S_{\rm ceil}=\sum_b w_b\,
 \frac{\lceil e_w c_b/(2l)\rceil}{e_w}\log p_b.
\]

已有 c_b/(2l)≤ceil 值，不能反向推出 Sceil≤M。Mzk1URThetaKHP5J1SameQActual 中 hfc 正是额外要求的 Sceil≤M 的逐纤维版本，尚无实际供给。这一条不能只靠 Σef 消掉。

真正应生产的是：实际源的 q-root 格 J_b、实际 θ 源像/作用及实际论文 hull Θ，满足

\[
J_b\longrightarrow\Theta,\qquad
\sum_b w_b\,\nu(J_b)=-M,\qquad
-M\le\nu(\Theta).
\tag{R1.1}
\]

同时输出 ν(Θ) 与锁定的 theta reading、全局 q 和与锁定 q reading 的比较。原来单局部 C3 的 log‖q‖ 不会因全局求和存在而自动变成 −M；若目标采用该原 reading，就必须提供它与真实全局数据的来源关系。面向 ABC 的新全局对象可以独立建设，但不能据此把旧 reading 目标标为关闭。

### 3.2 首选：实际根参数主格，不经过向上取整

1. 对每个 b，从实际 Tate/Kummer 数据取 r_P，证明 r_P^(2l)=q_P。先查该根是否已在实际 K_w 中：E[2]、E[l] 的 Tate 描述能给出根的存在时，证明选定 torsion point 对应的根关系即可。
2. 若原 K_w 不含所需根，可在共同有限扩张 L_w 中取根，**同时**基变 q、θ、参考格和作用。扩张不能只用于计算 q 的体积；要证明基变前后归一化读数兼容。
3. 对实际根主格 r_PO_{L_w}，以 O_{L_w} 为参考计算
   \[
   \nu_{L_w}(r_PO_{L_w})
   =\frac1{[L_w:\mathbb Q_p]}
      \log\frac{\mu(r_PO_{L_w})}{\mu(O_{L_w})}
   =\log|r_P|_p=-\frac{c_P}{2l}\log p.
   \]
   使用已有 fractional-lattice/mass 供体；不要求不同维 carrier 等价。若锁定 reading 用的是 raw Haar log-volume，这个相对参考格的 ν 还须加回 log μ(O)/维数。证明该参考项在两侧抵消，或将它明确带入上界；不能以重新归一化代替 unitMass 识别。保留原 signed log，不用绝对值翻转 θ 的符号。
4. 证明根主格是**源端真实的 label-one 区域**：用 theta/Kummer 值的实际方程辨认 generator，再证明源作用、log、线性化的交换方块。单独的 identity∈p6Phi 只能证明该保格族非空，不能代表所有实际源箭头。
5. 将 r_PO_{L_w} 的像放入实际 Θ，证明正有限测度及单调性；使用 R0 的全纤维公式相加。到此才得到 (R1.1)。
6. 对每个引用到的消费者输出同一对象的 identifications，不分别选“容易下界的 θ”和“容易上界的 packet”。

**最先应交付的窄结果：** 一个真实坏位、真实 root、真实源箭头的方块，连同 root 格的准确质量与 hull 包含。它决定这条主线是否能直接消除 ceiling，而不是先批量包装全局接口。

源作用的 provenance 也在这一包内补：对一般 DPrimeStrip 箭头，先在其实际 arithmetic realization 中辨认整数单位及挠子群，利用同一局部 reciprocity/Kummer 数据诱导 U/μ 上的 β；证明不同 realization 的选择在该商上相容。再证明 β 保持 p^k 次幂过滤，接单位商→log 像→有理化的已有供体。若已实际识别 U/μ 为有限自由 Z_p 模，p^k(U/μ) 就是邻域基，群同态保持该过滤立即给连续性；无需先增加一个“连续 β”假设。真正要构造的是这个实际识别和 β 的来源，不能从 DPrimeStrip 的抽象群字段直接宣称单位作用已经存在。

### 3.3 替代一：行列式格与范数，绕开 root 所在 carrier 的同构

使用 restriction of scalars 的 determinant line，而非 tensor≃root-product 的代数等价。

- 对真实源格 Λ 和其像 Λ′，构造共同有限维 Q_p 空间中的满格；记录参考格。若用不同空间，则先作共同基变，并证明归一化 determinant 的塔式相容。
- 计算乘法 m_a 的 determinant：det_Qp(m_a)=N_{L/Qp}(a)，从而 normalized covolume 的变化等于 log|a|_p。
- 对真实运输映射计算 Smith 指数或有限余核长度。q-root 对应的分数指数可先乘 2l 成为整数，再用 determinant line 的有理次数，而不是在未含根的域里伪造元素。
- 将实际源对应的余核长度与参考格比较，证明所需方向的指数界；通过 Haar 唯一性或有限指数体积公式回到原 ν。
- 基变的次数因子必须在 q、θ、different 三侧共同消去。这条路产出的是真实 covolume 比较，不能只有一个虚拟 determinant 数值而无回到实际 hull 的定理。

它与首选路线的区别是：首选先找实际根元素与区域包含；本路线先找满格间的线性映射、范数及指数，根只出现在有理化的 determinant 数据里。

### 3.4 替代二：保留取整误差，走严格量化的最终吸收

设 a_b=c_b/(2l)，ε_b=ceil(e_wa_b)/e_w−a_b，则 0≤ε_b<1/e_w。证明真实下界

\[
-M-E_{\rm round}\le\theta,\qquad
E_{\rm round}=\sum_b w_b\epsilon_b\log p_b.
\]

将这个量完整保留到夹逼：

\[
-M-E_{\rm round}\le\theta\le H
\le\kappa_l(A-c_lQ)-M
\quad\Rightarrow\quad
c_lQ\le A+E_{\rm round}/\kappa_l.
\tag{R1.2}
\]

证明 Σ_b w_b log(p_b)/e_w 的实际 support 上界；若它≤C_d(D+N)+C，则除以 κ_l≈l/4 后成为 O((D+N)/l)，可以交给 R3 的 l 随高度增长的选择。若只有 O(Q) 界，就必须检查其系数除以 κ_l 后是否仍可吸收，不能把它称为常数。

这是针对最终 ABC 的备用路径。它只有在误差实际满足预算时才走通；要关闭**精确**原 reading 的 −M≤θ，仍须另证明误差消失或在原定义内抵消。两项验收必须分开。

## 4. R2：独立上界的实际对象与算术输入

### 4.1 现在要接的是 procession 对象，不是再次证明平均恒等式

Mzk1URThetaKC3UpperTerminalActual 的 C3_upper_route_lambdaWeights 仍接收 hVh、hlogdK、hsQraw；hHpkt 两边只是同一个 weighted average 的两种展开。它并未给出实际 ksThetaHullLog 与那个平均量的比较。

另一个实际细节：Mzk1URPacketActualInstanceActual 的局部上界当前结论使用 urActualB T；其形参 b 并没有让结论遍历 b。先让构造实质依赖给定 b，再汇总。文件中已写出的局部证明可复用；该文件及 C3 terminal 本次看到的最新 watchdog 记录仍有 FAIL，不能标为当前版本 kernel-closed。

还要区分两个运算：

\[
\nu\bigl(\overline{\bigcup_j R_j}\bigr)
\quad\hbox{与}\quad
\frac1n\sum_j\nu(R_j).
\]

后者不是前者的一般上界。现有 ksThetaHull 是 nonzero-label 区域之并的闭包；如果这些区域是嵌套格，其并主要由最大区域决定。不能用 sum-of-squares 平均直接压低并的体积。

### 4.2 首选：从真实 procession 做有限乘积／张量块，再读平均

1. 从 paper 的 procession 数据建立真实索引 (b,j,slot)，保留 distinguished slot、其余单位 slot、per-label generator、different 和 exceptional 集。每个有理素数单独构造局部块，再做有限乘积；不对不同 p 的局部域作同一 Q_p 张量。
2. 对每个 j 构造真实行区域 H_bj，调用已实现的局部 hull/Step-V 估计，生产 V_bj=ν(H_bj) 及 hVh。不同 j 的不同维数先用各自 normalized volume 归一化，再依论文行权重求和。
3. 通过真实 procession 的比较映射，把 P5 源对象送到同一乘积/张量对象。要证明的是该映射对 q-root 参考格的质量公式，以及对 θ 可能像的覆盖。若作用只定义在单块上，逐块构造后证明与 procession 转换相容。
4. 定义 H 为这个真实对象的读数，证明 H=Σ_b w_b·avg_j V_bj，随后复用 StepVProcessionAverage、StepVDistinguishedSlotAverage、Mzk1ULStepVIIILambdaActual。
5. 回到 R1 的 Θ，证明 ν(Θ)≤H。若只有 union-hull，不能凭名称认作 procession 乘积；必须给出实际运输及体积方向。

此路的研究难点集中在第 3、5 步：它们连接源几何与平均对象。交付应是带 source map 的格/区域图与可计算的局部指数，而不是再加一个 htheta 字段。

### 4.3 两条不同的替代机制

**机制二：过滤与 associated graded。** 若源对象不是直积，按 procession 构造实际格的有限过滤。证明每个相邻商恰由相应 slot 数据控制；用短正合列的 determinant 乘法性将总 log-covolume 分解为商的和。扩张类保留在格中，不要求分裂成 product。关键局部证明是过滤稳定、商识别、有限指数及真实 θ 像对过滤的相容；然后把 Step-V 上界施加在各商。不能把多个 label 的同一个子格重复计为独立商。

**机制三：有限精度纤维计数。** 在共同参考格 modulo p^N 上，直接数真实可能像。沿 procession 的投影计算每个纤维的基数上界；乘法计数得到总基数界，除以总维数并转 Haar。单局部 log/单位计数及已经实现的 truncated-unit 供体优先复用。证明模 p^N 截面确实表示原闭区域；若只有近似，给出 N→∞ 的误差消失。这个机制绕开连续分裂和 associated-graded 同构，但不能把并集的基数写成各分支基数的乘积。

三路共用同一个实际 q、同一个源作用和同一个目标读数，分歧只在如何证明体积可控。

### 4.4 hlogdK、hsQ 的具体剩余任务

**域先固定。** per-λ 的 FtpdLam=Q(λ) 已有实际定理；Fmod=Q(j(λ)) 不等于它。S_ar 的 different、conductor 必须在正确层级定义。当前 SAr_tripodal_Ftpd 已改为接收 logF 的定义，而一些 hbad 包装仍按旧参数表使用它；这是当前接口迁移未完成，不能继续抄旧签名。

**hlogdK：** 现有 HlogKAssembly / HlogKLambdaNumeric 仍以相对 different 总上界为输入。用实际 K/Ftpd 塔逐位实现以下步骤：

- 以源构造中的 torsion/ramification 数据区分 good、tame、wild 位；
- good 位证明局部不同为单位理想；tame 位用实际 e−1；wild 位用已实现的 Prop 1.3(ii)/Serre 上界，并固定 p=2、3、5、l 的贡献；
- 将局部 different 运输到全局不同理想的因子指数，再以 f_P log p 求和；
- 用真实塔的 discriminant 恒等式压到 S_ar+2log l+21；
- 将标量总界与实际各块 D_b 的加权和识别。Unit 索引的包装不能替代这一步。

**hsQ：** 优先使用实际有限坏素数 support 的 log-product；不要先取最大坏素数 X，再将所有 ≤X 的素数都装进 urSQ X。这种 primorial 放大可远超原 s^Q，已有 paper s^Q 上界不能自动给它提供 hsQraw。

将 q-support、different-support、特殊素数 support 明确分开。q 部分沿已有 qNo 供体；different 部分先在同一 p 的**完整纤维**上比较 δ、e、f，不能用任意单个分歧位代表全纤维。局部 deg_E 分母使用实际纤维总次数；全局 [Fmod:Q] 因子在求和时才产生。当前 LocalSupportData 的 hlocal/hsumD/hsumF 都是待实例化字段；可证明覆盖 support 的求和 ≤ 全局量即可，不必强求仅在截断 support 上的等号。

另一个可直接缩短的接法是先按 p 分组：对 w_b=[Fmod_b:Q_p]/[Fmod:Q]，由完整 Fmod 纤维的 Σef=[Fmod:Q] 得 Σ_{b|p, bad}w_b≤1。因此
\[
\sum_b w_b\log p_b
=\sum_p\Bigl(\sum_{b\mid p,\ bad}w_b\Bigr)\log p
\le\sum_{p\in support}\log p.
\]
这样可以把真实 weighted prime sum 直接送入 retained Step-VIII。当前 hsQraw 的 (Σ_b w_b)·log(urSQ X) 是额外放大，应改造该中间消费者的估计步骤，不能继续将它作为必须满足的算术输入。对论文对象保持不变，改的是中间粗估计。

保留精确的允许常数，最终产出与本包权重一致的 hlogdK、hsQ。替代界若改变系数，重新经过 C3→R3 的误差预算，不再声称是原常数已闭合。

### 4.5 在这里产生 CTheta 下界，避免强行填过强的 certificate

S2953CThetaUpperCertificate 额外要求 CThetaPaper=thetaLogVolume/M；一般上界并不保证取等，因此不应把填这个等式作为必经任务。已有 S2715CThetaPaperScaleActual 的下界消费者只需要实际包含下界与实际 upper。

在 R0 保证 M=paperQAbsLog、R1 保证 −M≤θ、R2 保证 θ≤κ_l(A−c_lQ)−M 后，对 M>0 直接除以 M，得到 −1≤CThetaPaper。Q、M、θ 和 A 必须是上述同一数据的量。M=0 时单独使用 Q=2lM 及 A≥0 的实际退化分支，不伪造正 q 或空 carrier。随后再调用 CThetaPaper_ge_neg_one_iff 与 P6 的最终 display。

这个方向没有使用 final display 证明自己的上界。原始 qPilotLogVolumeReading≤thetaPilotHullLogVolumeReal 则在 R1 的来源/读数比较验收，不能仅凭 CTheta 的标量结论登记为已完成。

## 5. R3：每个 λ 的实际数据与局部高度 producer

### 5.1 要产生的量词，及当前包装尚未完成的内容

出口应是归一化版本：

\[
\forall d,K_V,\eta>0\;\exists C_{d,K_V,\eta}\;
\forall L,\lambda,\quad
[L:\mathbb Q]\le d,\;\lambda\in K_V
\Rightarrow
\bar h_L(\lambda)\le(1+\eta)\bigl(D(L)+N_L(\lambda)\bigr)+C.
\tag{R3.1}
\]

K_V 条件须约束规定局部位上的全部相关共轭，且排除 0、1、∞。现有 D1AnalyticInput、D1LetterSource、D4Inputs、D2SecondForm 都是消费者或数据契约。D3 和纯实数吸收已实现，保留作供体；当前剩余是实际输入，尤其不是将 Q 直接替换成 jHeight。

Mzk1G1F2ThetaFieldsActual/ThetaKConstructionActual 的 torsionCoords 仍是参数；现定义还使用 FLam 的正规闭包，文件注释中的“就是 Ftpd 加 torsion”不足以识别实际域。要先对照源的 F、K 构造确定塔，逐个证明域的包含和生成关系。

本包内部再区分三个节点：R3a 构造逐 λ 的源，R3b 用独立的局部/素数估计构造 l 与遗漏量，R3c 才消费 R1+R2 得到高度界。R3a、R3b 的证明不得依赖 R3c 或最终 IV display；R1、R2 先作为对任意合格实际源 T 的定理建立。这样不会出现“先用高度界选出产生高度界的数据”的隐含循环。

### 5.2 逐 λ 构造合格源，而非固定 T 通用于所有点

给定 λ≠0,1：

1. 取 Ftpd=Q(λ)、Fmod=Q(j(λ))，从实际 Legendre Weierstrass 方程构造曲线。复用已存在的 tripodal field 身份与 2-torsion 数据。
2. 填入实际 E[3]、E[5]、E[l] 坐标。优先用实际乘法映射的核；若对应一般接口尚不够，按 division-polynomial 递推构造 ψ₃、ψ₅、ψ_l，加入 x 根及满足曲线方程的 y，再用加法公式证明枚举恰为所需 torsion。仅取一个 splitting field、却不证明 roots 与 torsion 的对应，不能关闭 torsionCoords。
3. 在同一代数闭包中构造必要 compositum/normal closure，证明有限、正确的 Galois 作用与 degree 上界。需要 |GL₂(F_l)| 时，把作用定义在实际 torsion 基上并证明 faithful，而非只引用已有群阶数公式。
4. 坏位上的 Tate 参数、Kummer 根及 source arrows 从这条塔产生，接 R1 的局部方块。这里的 common tower 是构造所得；不得另接一个无关的 SourceNativeInitialThetaData inhabitant。
5. 将源中所有仍实际使用的合格条件逐一从上述数据推出，包括需要的 tame/split、选定位、procession/label 条件。只验证了结构的一部分就保持“部分构造”，不让全局 Nonempty 隐藏其余字段。

这些构造依赖 λ、l，但后续常数只能依赖已固定的 d、K_V 和允许的显式 l 因子。不要选择依赖 λ 的额外扩张后，把其 discriminant 作为“固定常数”。

### 5.3 选 l 与 q 的遗漏量：合并两种不同的缺失

现在已有 QSelected、hMinusQ 和它们的精确加法恒等式，但这是**既定 Bad 纤维中**的 selected/full split。它不自动等于论文 Cor 2.2 中“全部 q 位减去合格 Θ-data 所选择的位”。

构造两张明确的索引表：

- 全部 finite q 位 → 进入当前 Bad 的位／被局部条件排除的位；
- 每个 Bad 纤维 → 实际用于源运输的 lift／其余 lift。

分别计算差，再加 archimedean 与固定特殊位差，得到

\[
0\le Q_{\rm all}-Q_{\rm used}
\le C_d\sqrt h\log(2C_dh)+C_{K_V},
\qquad h=\bar h(j(\lambda)),
\tag{R3.2}
\]

或同强、足以吸收的绝对值界。来源不同的差项不应共用一个 hMinusQ 名字而省略识别。

选 l 的操作是：从实际 torsion/局部条件写出有限排除集合；给该集合的 Σlog p 一个与 h 有关的上界；将已有素数计数、Chebyshev 与避素数供体用于区间，取未排除的 l，证明

\[
\sqrt h\le l\le C_d\sqrt h\log(2C_dh).
\]

固定阈值以下的 h 单独吸收。每一步记录 l≥5 和合格 source 条件，不重新证明已实现的素数估计。

### 5.4 C4 到高度的正确方向

R1、R2 先产生同一套实际量的

\[
c_lQ_{\rm used}\le A+\mathrm{Err},
\quad c_l=\tfrac16-\tfrac2{l^2}.
\]

用 (R3.2) 写 Qused=h−Δ，于是

\[
c_lh\le A+\mathrm{Err}+c_l\Delta.
\]

这里 h 与实际 q 高度的有限/无限位字典来自 R0；Err 包括真正保留的 root rounding、运输指数与 exceptional 项。只有证出它们满足统一预算，才调用现有 sqrt·log 次线性和 D4 吸收。

当前 D1LetterSource 要求逐 λ 的 d4C 精确等于两个预先固定常数，这比所需的统一上界更强。实际构造时用 dmod≤d、e*≤E(d,K_V) 及各系数非负，将逐点系数上界化成统一 C_d、C_K，再接吸收引理。不要花力气让变化的域数据恰好给同一个 d4C。

若源估计先在 Ftpd=Q(λ) 成立，向包含 λ 的 L 运输时证明

\[
D(Ftpd)+N_{Ftpd}(\lambda)\le D(L)+N_L(\lambda).
\tag{R3.3}
\]

证明方法是逐个 base bad prime 使用
Σ_{w|v}e_wf_w=[L:Ftpd] 和 δ_w≥e_w−1：truncated conductor 在扩域后损失的部分由 relative different 支付，最后用 discriminant tower 求和。现有 LocalConductorInhabitant、DiscrAssembly、阶与不同供体用于这一个具体算术实例即可，不需为此重建一般 scheme 的 Riemann–Hurwitz。

完成后，(R3.1) 才成为实际 producer。固定范围内的高度字典、D4 代数以及 final display 不再是待办。

## 6. R4：一般受保护点的 noncritical map

### 6.1 目前接口的真实范围

PsiGeneralRRData 的索引仍是 T:Finset Q，u0 是整个固定 chart0 上的正则函数，u1 位于固定的 infinity localization。其实际实例是 ∏(x−t)。这不是任意 Galois-stable 几何点集的截面构造。

特别是 B1FinalHAvoid 的 hbranch 要求任意有限 scheme 点集 T 包含于 DTFixed n Tr。若 T 含 generic point，这个要求不可能由有限闭零点集满足；对非有理 chart 坐标也没有给定构造。该强中间接口应退出主线，直接产生原本需要的 map，而不是继续填 hbranch。

B1FiniteProducer 本身只记录有限 boundary preimage 和 avoidance，未记录 Branch(φ)⊆{0,1,∞}。它足够供部分组合引理使用，但 R6 的 log-canonical 恒等式还要真正的 Belyi 分歧结论。应在同一实际 φ 上保留这两个证明，不能用弱 producer 冒充完整 noncritical map。

### 6.2 三种一般截面构造，共同出口为 reduced 零纤维

输入是实际曲线 Y_n 上不交的有限闭几何点集 S,T，均作 Galois-stable 下降。目标是构造 reduced 有效除子 D，T⊆supp D、supp D∩S=∅，以及 O(D) 的两个无共同零点截面 s0,s1，使 div(s0)=D、s1 在 D 上不消失。然后

\[
\psi=[s_0:s_1],\quad \psi^{-1}(0)=D,\quad
0\notin\psi(S)\cup Branch(\psi).
\tag{R4.1}
\]

**路线 A：实际 divisor 的 RR／Serre 实例。** 将已存在的两图、function field、Ω frame 接入一般 D 的 principal-parts/Čech 空间；不能只用 D=0 的 serrePairing。

- 扩充 T 为避开 S 的有限 Galois 轨道并集，使 deg D≥2g+1。只需存在性，不必优化 genus 常数。
- 对每个几何 x，以 deg(K−D+x)<0 证明没有非零截面；这一步利用实际 divisor 的 degree 与非零有理函数 principal divisor degree=0。
- 在实际 D−x 上构造 residue pairing，证明其 annihilator/维数关系，得到 H¹(O(D−x))=0，再由短正合列推出 evaluation 非零/满射。
- 复用 exists_forall_apply_ne_zero，在有限个非零 evaluation 的核之外选择 s1。对闭点在有理系数空间上作选择：一个 section 在 residue field 非零即足够，基变到各共轭后仍非零。
- GeometricallyConnected 的一般基变实例若仍为 RR 接口所需，从既有两图在任意代数闭扩域下的 Jacobian/不可约证明运输得到；当前 F2AGWiring 的 hgc 仍是参数，不重新构造 smooth/proper。

真正新证明是一般 D 的 pairing、evaluation 与实例，不是已经完成的 chart function field 或 Ω 计算。

**路线 B：高次平面截面的 jet 插值。** 绕开一般 RR/Serre API。选择有理线性形式 ℓ，使 ℓ 不在 S∪T 上消失，将有限条件放到同一实际 affine chart。

- 在点的互异极大理想平方上作 CRT：给 T 的每个点规定非零一阶 jet，给 S 规定非零值。
- 将所得函数齐次化成 O(m) 的 section。扩大 m 后，仍满足这些条件的 section 构成非空有理仿射参数空间。
- 对 T 外的点 x，利用 O(m) 的一阶 jet 满射，证明“section 在 x 至少二重消失”在参数空间中余维至少 2；让 x 沿一维曲线变化，坏参数的像仍落在真闭子集。T 已由预设 jet 保证单根。
- 取真闭子集外的有理参数，得到 reduced 零除子 D。再从 O(m) 的 section 选 s1，在有限 D 上都不为零；没有共同零点，得到 (R4.1)。

这里要实现的是有限 subscheme 的 jet evaluation 与一次参数空间维数论证。必须证明整个零除子 reduced；只保证原 T 处导数非零还不足以排除零纤维中别处的分歧。

**路线 C：函数域的显式近似／模计算。** 在已有有限投影下，将函数域按 1,y,…,y^(n−1) 的基写成 Q(x) 向量；用各闭点的 DVR 条件描述“至多这些极点、规定这些 principal parts”。

- 将有限局部条件清分母，成为 Q[x] 有限模的线性同余；使用 CRT/Smith 形直接求解，而不是先建立一般 cohomology。
- 选避开 S 的有限极点除子，随次数扩大，可用 Riemann–Roch 的显式维数计数或有限投影模的秩计算证明解空间有足够自由度。
- 在所得有理函数族中排除使零纤维出现重根的 resultant 条件，证明该条件不恒等为零；规定 T 的一阶 jet 和 S 的非零值继续保持。
- 用所得函数 f 的零/极点 divisor 构造 morphism；验证 poles 处使用 1/f，零点处用 f，重叠上互逆。

本路线的难点是具体线性系统秩和非零 resultant，输出是实际函数域元素及其所有零/极点阶，不是抽象 Nonempty 近似接口。三路只择一路实施到 (R4.1)，复用同一后半段。

### 6.3 用截面决定覆盖，解除固定 chart 的错误限制

在 D(s1) 上用 s0/s1，在 D(s0) 上用 s1/s0，两个开集覆盖 Y。将它们各自与既有两图相交，得到至多四类实际仿射局部图；用 localization 的通用性质定义环映射，在交集验证乘积为 1。

不要要求 s0/s1 在整个原 chart0 上正则。s1 可能在 chart0 内有零点，这是正常的有限映射；在那些点用另一个目标图即可。

若下游仍要求所有 scheme 点 T：把闭点部分交给上述构造；generic point 在非恒定 dominant map 下映到 generic point，自动不落入三个闭边界点。这样保留消费者的量词，而不要求 generic point 属于有限零除子。

### 6.4 受保护值的 Belyi 递归：使用有理函数，不强求最终为多项式

本地原文 Noncritical Belyi Maps 的 Lemma 2.4 使用有理 Möbius 变换。当前 M2AnalyticTarget 要求一个最终 q∈Q[X]；这个限制不能由原文递归直接得出。推荐将中间对象升级为实际 P¹→P¹ 的 rational map；原定的 noncritical scheme morphism 目标并未要求多项式。

令 S1=ψ(S)∪Branch(ψ)，β=0，(R4.1) 保证 β∉S1。每轮：

1. 对 S1 作 Galois closure，取最大 minpoly 次数 d0>1 的点 α0。
2. 选有理 Möbius 变换 m，使所有非无穷远 S1 点落在 |z|≤1，而 |m(β)| 超过由 d0 给出的显式阈值。这个步骤复用已有 Cauchy/分离供体，选参数时避开有限极点。
3. 对 m(α0) 的 monic minpoly f0 作系数界；据此同时控制 f0(m(S1)) 和 f0 的临界值。阈值保证 f0(m(β)) 不在二者并集中。
4. 设置新坏值集合为上述并集；max reduced degree 或其最大次数层总量严格下降。临界点由 f0′ 的次数≤d0−1 控制；原最大次数轨道被送到 0。复用现有良基下降和 critical-values composition 引理。
5. 到全有理情形，调用已实现的 finite-beta Belyi 供体。按实际 scheme morphism 复合各个 m、f0 和最终映射；分歧集按 Branch(g∘f)⊆g(Branch f)∪Branch g 运输。

多项式局部的 graphIso_holds、导数非零处 smooth 的证明已经可复用，不再安排构造。Möbius 部分用 P¹ 自同构及其无分歧性；一般有理函数局部可写成互素齐次 (P,Q)，在 Q≠0、P≠0 两图分别处理 Wronskian P′Q−PQ′。

**本包出口：** 对任意原文合格 S,T，产生同一个实际 φ，证明有限非恒定、Branch⊆{0,1,∞}、φ(S) 入边界、φ(T) 避边界。有限不交边界族在这一完整 producer 上构造，不再依赖 rational-chart 特例。

## 7. R5：实际局部点到固定 K_V

### 7.1 通用局部域现在只补 SeparationInput 的实际实例

本次已核到 UniversalIFNormedActual 与 UniversalMonogenicIntegersActual 的成功记录：有限 intermediate field 的 normed 结构、整数环单生成不再安排重证。UniversalSeparationToUFLEActual 仍接收 SeparationInput；后者才是当前出口。

对每个 M⊂PadicAlgCl、[M:Q_p]=m≤d：

1. 从 nonempty_monogenicIntegers 取 x，使 O_M=Z_p[x]。将 x 经 M→PadicAlgCl 送入共同闭包，证明 minpoly 的次数=m、整系数、monic、|x|≤1 及 M=Q_p(x)。
2. 使用已存在的 monogenic different=导数生成理想，把实际 different 阶转为 |f′(x)| 的下界。
3. 接入已有 local different upper bound。当前直接包装仍显式需要 base Q_p 的 different=0；用 self-extension 的 differentIdeal_self_eq_top 和实际整数环识别填掉它，不可从“base different 非负”删去上界中的 base 项。
4. 选**对所有 m≤d** 有效的 B(p,d)。不能直接以 d(v_p(d)+1) 替代 m(v_p(m)+1)，因为 v_p 不单调。可取有限最大值，或先用保守的 d(d+2)。
5. 所有共轭根都积分，所以 |x−x′|≤1；从 f′(x)=∏_{x′≠x}(x−x′) 与导数下界推出每个因子的统一下界 p^(−B)。
6. 填入 SeparationInput，调用已有显式 N、系数有限化、Krasner 与 universal field assembly。

剩余核验是 minpoly/different 的实际范数识别和 uniform B 的装配。DeltaBoundFinal/Direct 本次仍有构建失败记录，不能把源码中出现该 theorem 当作当前可导入的完整供体。

### 7.2 映射值必须在射影直线上，距离才是全局连续的

当前 GKDeltaAssembly 的 lam:ProjY→L 要求一个全域 affine-valued map；实际非恒定 φ 有极点，不能把其值都放入 L 并维持连续性。

构造真正的 φ_L:Y_n(L)→P¹(L)，先用既有图式公式在 normalized-coordinate quotient 上下降，再与实际 scheme morphism 的点值证明相等。使用射影距离

\[
\rho([a:b])=
\frac{\min(|a|,|b|,|a-b|)}{\max(|a|,|b|)}
\]

或等价 chordal 版本。分母在非零齐次坐标上为正，缩放不变；ρ 在 0、1、∞ 恰为零，别处严格正，且在全 P¹(L) 连续。复用已有距离与紧性引理时，要把这一个全局函数的定义域接正确，而非给极点任意填入 λ=0。

当前 projective compactness/product 供体是非阿基米德版本。还要将 archimedean 因子加入：在 C³ 的单位球面上取 Fermat 闭子集，连续投到射影商；实点作闭子集，有限乘积仍紧。无须重做已完成的 p-adic compactness。

### 7.3 将有限不交边界族接到全部局部共轭

固定 n、次数界 d 及有限相关位集 V，先用 R4 构造 r+1 个映射，r=d·|V|，其 reduced boundary E_i 两两不交。

- 对局部元组 x=(x_{v,k}) 定义
  δ_i(x)=min_{v,k}ρ(φ_i(x_{v,k}))。
- 每个 x_{v,k} 至多位于一个 E_i，所以至多 r 个 i 被排除。直接在局部点/基变后的边界上用鸽巢原理；不必把超越于 Q 的局部点硬改为 Q 上的闭几何点。边界的 scheme 不交性经基变保持。
- 实际 scheme 点值与局部坐标字典保证“δ_i=0”恰对应落入该 E_i。由此给出 GKBoundaryAvoidBridge 的真实内容。
- 复用已有 uniform_positive_away，得到 δ0>0。再在每个 P¹(L_v) 中取 ρ≥δ0 的闭集，其位于去掉边界的 affine 开集内；此时才转换为 K_V 的 affine 坐标。
- 对任意次数≤d 的点域，把所有局部嵌入放入已固定 universal fields；同一个 i 必须避开元组中的**所有**共轭。不足 d 个时重复已有坐标，不能为每个共轭分别选 i。

**本包出口：** 真正由 R4 的映射形成的 K_V、δ0 和“每个点存在一个共同适用 i”的证书；常数在点 y 出现前已固定。

## 8. R6：实际高度运输——用同一数域与多截面消去冗余

### 8.1 只保留主线需要的几何高度结论

本包在 R5 选出的同一个实际映射 φ_i 与点 y 上工作。设 E_i=(φ_i^*{0,1,∞})red，点域为 L，λ=φ_i(y)∈L。所需三个实际结论是

\[
\begin{aligned}
\bar h_L(\lambda)&=h_\omega(y)+h_{E_i}(y)+O_i(1), \tag{R6.1}\\
N_L(\lambda)&\le N_{E_i,L}(y)+O_i(1)
              \le h_{E_i}(y)+O_i(1), \tag{R6.2}\\
h_{E_i}(y)&\le\kappa_i h_\omega(y)+C_i. \tag{R6.3}
\end{aligned}
\]

这些 O_i(1) 要由有限模型、截面和度量产生，并对次数≤d 的所有点统一。不能以“每个点的误差有限”代替统一常数。

这里直接把 R3.1 用在 L 上，避免先将 λ 降到 Q(λ)、再为每个 φ 单独建立一般 scheme different 的高度运输。R3.3 已处理从 Θ-data 的点域到 L 的算术扩域。**原路线中为这一处另建完整一般 Riemann–Hurwitz／不同运输 API 的任务退出主线。** 若其他消费者仍需该 API，其任务可独立保留，不能算本路线剩余前置。

### 8.2 从实际微分得到 (R6.1)，不用空的 line-bundle 结构

因 R4 证明 φ_i 真正为 Belyi map，局部参数 t=u z^e 给出 char 0 下 ord(d t)=e−1，故

\[
\omega_Y(E_i)\simeq\phi_i^*\omega_{\mathbb P^1}(0+1+\infty)
\simeq\phi_i^*\mathcal O(1).
\]

在非边界处 φ 无分歧，边界处 R=(φ^*D−E_i)，两处吻合。复用已有 Ω 的两图 frame 与 transition，逐图写实际导数诱导的映射；确认在重叠上的乘法单位相容。现有 F1HeightTransportData 的 trivialCover/1-frames 只显示接口非空，不能用于这里。

给这些实际 line bundles 选定 adelic metrics。将上式的等价作用在截面上得到局部 log-norm 等式。其度量比在 archimedean 紧的 Y(C) 上上下有界；在有限多个模型坏素数之外是 integral unit、贡献为零。将有限坏位的界以正确的局部次数相加并归一化，得到统一 O_i(1)。

已有 ω 与 O(n−3) 的 frame 关系继续复用。选择 hω=(n−3)·bar h_O(1)，并证明该选择与上述实际 ω metric 的差有界；这使 hω≥0，也与已有 F8 消费者匹配。

### 8.3 边界 conductor 不再用自由 local_bound 字段

先为固定 Y、φ_i、E_i 选共同模型于 Z[1/N_i]：

- 将两图方程、映射分子分母、互逆数据、导数与边界的系数清分母；
- 因固定的 generic-fiber 等式/étaleness 已证，取有限个表达式的共同分母及相应非零判别量，保证好素数上边界 pullback 与 reduced support 相容；
- 对 p∤N_i，λ 的 reduction 落在 {0,1,∞} 当且仅当 y 与 E_i 相交。truncated exponent 只计一次，≤该交点的非负整数长度；
- 对 p|N_i，直接以每个 p 的全部局部 degree 权重估计，归一化后总贡献≤固定倍数 log p；不乘一个随点增长的坏位数量；
- 将局部长度转为实际 E_i 的局部 Weil 函数。archimedean 部分只有固定的下界修正，得到 N_E≤h_E+C。

Mzk1HTF3ConductorHeightActual 的有限和引理只是最后一步；实际 conductorExponent、localHeight 与统一误差按上述模型产生。不要把 pointwise local_bound 留在最终 producer 的参数里。

### 8.4 首选 F4：用一组齐次截面，直接构造真实边界高度

这一条比“把一个多项式值的高度认成除子高度”短，也避免 §2.3 中发现的单坐标高度为零问题。

1. 对实际 reduced E_i，取其在 Fermat 平面模型上的齐次理想。可从有限个闭点的 residue evaluation 核取交，再由 Galois-stable 性下降到 Q；或在两图中取理想并齐次化。证明在 Y 的每个边界点，该理想在 DVR 中为一次 maximal ideal。
2. 取有限齐次生成元，乘齐次坐标单项式补到同一足够大次数 m_i。保留所有必要单项式，使补齐不会制造新的共同零点。得到
   \[
   P_{i,0},\ldots,P_{i,s}\in\mathbb Q[X,Y,Z]_{m_i}
   \]
   在 Y 上的 base divisor **恰为 E_i**，在 Y\\E_i 上不同时为零。
3. 用这些截面定义 actual local Weil function：
   \[
   \lambda_{E_i,v}(y)
   =m_i\log\max(|x_0|_v,|x_1|_v,|x_2|_v)
    -\log\max_j|P_{i,j}(x)|_v
   \]
   并加入为模型所选的固定 metric normalization。它对齐次代表缩放不变；局部 min_j ord(P_ij)=1 给出正确的边界重数。
4. 对 v 求和，由 product formula 得到
   \[
   h_{E_i}(y)
   =m_i\,\bar h_{\mathcal O(1)}(y)
     -\bar h([P_{i,0}(x):\cdots:P_{i,s}(x)])+O_i(1).
   \]
   后面的**多坐标**射影高度非负，于是
   \[
   h_{E_i}(y)\le
   \frac{m_i}{n-3}h_\omega(y)+C_i.
   \]
5. 将这一个 h_E 同时用于 (R6.1)、(R6.2)。两套 metric 的比较在固定模型上证明有界即可，不必强求逐位严格相等。

这条路线的新证明是实际有限齐次生成元、base divisor 与局部 metric 的识别；不需要重新证明通用多项式高度上界。m_i 只需有限，不需最优：有限映射族先固定，之后再按 κ=max_i m_i/(n−3) 选择 η。

### 8.5 两种备用构造：避免在一个几何 API 上反复碰壁

**备用 A：现有 orbit product 加有效补除子。** 复用已完成的 orbit product/齐次性/函数域映射。在有限 Galois splitting field 中选过每个边界点的线性形式，取其 Galois norm，证明系数落回 Q，且不在整条 Y 上恒零。对所得 degree-r section P，使用
\[
\operatorname{div}_{section}(P)=\operatorname{div}(P/Z^r)+r\,\operatorname{div}(Z).
\]
这一步不能省略 Z=0 处，否则 principal divisor 的 degree=0 与 section 的 degree=rn 混淆。用实际 DVR 重数证明 div_section(P)=E_i+F_i、F_i≥0。为处理 P(y)=0 但 y∉E_i 的情况，取有限多个 P，使补除子的共同交点在 E_i 外为空。有效补除子的局部高度统一有下界，推出 (R6.3)。

**备用 B：曲线上的有效 divisor 比较。** 直接在函数域/Čech 层证明某个 mω−E_i 有非零截面，给出实际有效 divisor F∼mω−E_i。建立该截面的局部度量并证明 h_F 有统一下界，即得 h_E≤m hω+C。这条路线依赖 R4 路线 A 的实际 RR 输入，但绕开平面理想、Galois polynomial norm 与 section 的齐次化。

三路的共同出口必须是同一个实际 h_E 的 (R6.3)，不能以更换 h_E 定义使不等式成为 rfl。

### 8.6 如何真正产生 hω 的统一界

把 R3.1、(R6.1)–(R6.3) 连起来：

\[
h_\omega+h_E\le(1+\eta)(D(L)+h_E)+C,
\]
\[
(1-\eta\kappa)h_\omega\le(1+\eta)D(L)+C.
\]

先固定 n、d、有限映射族及 κ，再选择 η>0，使
(1+η)/(1−ηκ)≤1+δ。已有 F6 eta/吸收代数可直接用。得到同一实际点 y 上的

\[
h_\omega(y)\le(1+\delta)D(L)+C_{n,d,\delta}.
\tag{R6.4}
\]

i 随 y 变化只从固定有限族取值，故对各 i 的常数取最大值。所有常数在 ABC 三元组前固定。

## 9. R7：实际 Fermat lift 的不同估计与最后装配

### 9.1 现在保留的 F7 任务是实际域的 ramification 实例

已有 fermatRoot、单根的 minpoly 次数界，以及 global discriminant sum、tame count 上界、wild 的归一化代数。它们不能直接给实际 fermatLiftL 的 F7。

对互素 a+b=c，令
\[
x^n=a/c,\qquad y^n=b/c,\qquad L=\mathbb Q(x,y).
\]
复用根对象，在第二次 adjoin 上再次用 X^n−b/c 的关系，证明 [L:Q]≤n² 及实际 NumberField 实例；把 (x,y,1) 送入已存在的 Y_n。无需接口中无关的额外 Fermat 数值等式；x^n+y^n=1 直接来自 a+b=c 与 root_pow。

随后按实际素数分三类：

1. **p∤nabc。** a/c、b/c 是 p-adic units。两个 monic Kummer 方程的导数 nX^(n−1) 在根处都是单位；归一化对应有限 étale algebra，逐 completion 得到 unramified，different contribution 为零。
2. **p∤n、p|abc。** 在最大非分歧扩张中，unit 有 n 次根，所有相关根都落在加入 π^(1/n) 的 tame 扩张中。由此证明实际局部子扩张 tame；不能只由 p∤n 和总域次数≤n² 猜 e 与 p 互素。之后调用已实现的 tame different/count 供体与 Σef，得每个 p 的归一化贡献≤log p。
3. **p|n。** 使用实际局部次数≤n² 的 different upper bound。取一个对全部 e、局部次数≤n² 一致的上界 B_n(p)，并以完整纤维的 e·f 权重求和；归一化后≤B_n(p)log p。不要遗漏 residue degree f。这些 p 的集合由 n 固定，全部放入 C_n。

于是实际得到
\[
D(L)\le\sum_{p\mid abc}\log p+C_n
=\log\operatorname{rad}(abc)+C_n.
\tag{R7.1}
\]

路线不需要 sharp 的 wild 常数。用有限最大值或很粗的次数函数即可，关键是它独立于 a,b,c。

### 9.2 在同一组实际数据上填 P8，而非另造标量 witness

给定 ε>0，先选 δ，再选 n≥4 使 n/(n−3)≤1+δ；固定 d=n²。随后执行 R4、R5，固定有限映射族、K_V、κ；再选择 R6 的 η 并取 R3、R6 的统一常数。这个次序避免让常数依赖待估计的三元组。

对每个三元组，使用 9.1 的同一个 L 和同一个 y：

- hOmega 取 R6 的实际规范化 canonical height；
- DL 取 D(L)，使用 (R7.1)；
- hPi 取实际 π(y) 的规范化高度，复用已经实现的 F8/height dictionary，补齐 R0 的除次数转换；
- hOmega≤(1+δ)DL+C6 用 (R6.4)；
- F8 与 π(y)=a/c 给 log c≤hPi+C9，以及 hPi≤n/(n−3)hOmega+C8。

然后调用既有 routeF9_of_F6_to_F8、P8ProducerAssembly 与 ABC equivalence。无需重写 F9 或 abc 对数/乘法等价。这里的“最后装配”只有在上述量都来自同一个实际点、同一个数域、同一套高度 convention 后才关闭。

## 10. 接下来应做的顺序与交付判据

第一批先处理三个会让后续任务走错对象的问题：

1. **R0/R1：** 交付一个实际坏位的 c=ord/e、root 格质量和 full-fiber 权重图。明确 Θ 使用哪一个实际读数，并解释新 thetaMWeight 是否真的对应该对象。不要先扩大全局接口。
2. **R2：** 写出实际 procession 与 R1 的同一 Θ 之间的源映射；把 hHpkt 的自反包装替换为真正要证明的比较。检查 weighted s^Q 使用实际 support，避免 primorial 放大。
3. **R6：** 把 F4 的单坐标高度代理从本路线消费链中移出，优先构造有限齐次截面族及 base divisor=E 的局部字典。已存在的函数域、形式 divisor 和 polynomial API 继续复用。

第二批补 R4 的一般受保护点 producer 与 R5 的 SeparationInput/射影距离接口；R3 同时沿现有 arithmetic owner 的 per-λ Θ-data、different/conductor 输入推进。这里是任务之间的逻辑独立性，不是要求本 chat 启动其他线程。

第三批才将 R1+R2 的实际夹逼、R3 的数据与误差预算、R6 的实际高度运输、R7 的不同估计装到既有消费者。

每包交付必须能回答以下四项：

| 项 | 本路线要求的证据 |
|---|---|
| 实际对象 | 从已锁定算术/几何输入构造，不是任意标量、trivial cover 或自由 Nonempty |
| 剩余前提 | 明列消费者中被消掉的字段；标准结构条件与目标等强假设分开 |
| 证明方向 | 所用上游定理的传递依赖不含本包要生产的 hCor312、D1、P8 或 ABC |
| 目标对应 | 新中间对象与原 reading/height 的比较有证明；不能用命名一致代替语义一致 |

本次研究文档的 statement_compiles、proof_body_checked、kernel_closed、target_accepted 均为 NOT_RUN；复用的历史 watchdog 成功记录与当前失败记录单独保存在证据文件中。已移出正文的完成项只在历史快照和证据索引留痕，不再列为实施任务。当前八包全部是尚未完成的生产或语义接线工作；闭合一包时删掉该包的实施指导，只留下其作为后续供体的引用。

