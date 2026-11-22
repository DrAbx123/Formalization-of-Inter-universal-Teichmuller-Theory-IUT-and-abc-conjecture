# R0–R7 交接：怎样让 Θ 的两侧接上

2026-11-18（上海）｜性质：研究交接、构造设计，不是证明完成报告。保留[权威路线](P7-G1-P6-P8-CLOSURE-ROUTE-20261116.md)、[活动进度](GOAL-PROGRESS-R0-R7-20261117.md)及现有 owner；本文件只细化其 R1/R2 难点及失败后的出口。依据工作树而非仅凭模块名；[证据版本与 DAG](../dag/nodes/r0-r7-theta-comparison-handoff-20261118.json)。

**只求标准整数 ABC，从 [§18 重复素幂的连分数路线、立项判断和验收](#abc-route-decision) 读起，更新于 2026-11-19（上海）。** 一次欧几里得算法列全每组指定重复素幂的候选，并有跨多组输入的显式界。§17 留存平方归约的证明，原 III.3.12 的固定输入问题见 [§16](#finite-slot-certificate)。

## 1. 先锁端点：不同的 Θ 到底能证明什么？

固定 III.3.11 **原范围内**的一组数据。记 `qₛ=−|log(q)|`，`Θₚ=−|log(Θ)|` 是带符号的读数，不是正的体积，也不是某个 `j` 的 theta 值。[III.3.12 原文](IUT-TEXT/III.txt#L10326)的 q 是同一表示中**不再施加** Ind1–3 的 q 像；Θ 是对相关 Kummer 表示中**所有允许的像**取并、取 holomorphic hull 后的 procession-normalized 读数。初始值域为 `ℝ ∪ {+∞}`；结论是 **`Θₚ` 有限且 `qₛ ≤ Θₚ`**。原假设含非空坏位，故 `|log(q)|>0`；于是任意满足 `Θₚ ≤ CΘ·|log(q)|` 的 `CΘ` 都有 `−1 ≤ CΘ`。不需要证明 `Θₚ=qₛ`，也不需要证明 Θ 的集合等于 q 的集合。

| 已经能从同一输入证明的东西 | 可以交付 | 仍然不能交付 |
|---|---|---|
| A. 构造同一源读数，`qₛ ≤ Θₚ ≤ H`，且 `H` 有限；另把 q、H 与算术量接通 | 原 III.3.12；若 `qₛ=−M`（或有足够方向的算术比较）且 H 有独立 C3 上界，再得 C4 | 只做实数代数，不自动产生原文两端 |
| B. 两个模型 `L,U` 的类型、载体甚至局部行都不同，但 `qₛ ≤ L ≤ Θₚ`，另证 `Θₚ` 有限 | **仍是原 III.3.12**。若同时 `Θₚ ≤ U ≤ H`，也是同一论文 Θ 的 IV 上界 | 不必强证 `L=U`。若只知 `Θₚ ≤ U` 而 `qₛ ≤ U`，两个上界不能比较 |
| C. 只证 `−M ≤ L ≤ U ≤ H`，且 `H ≤ κ(A−c_l Q)−M`，没有连向 `Θₚ` | **精确算术 C4**：`c_l Q ≤ A`；可接 R3。可直接以 `L` 填标量消费者的中项 | 原 III.3.12、IV 对**原** Θ 的解释及其 `CΘ`，均未交付 |
| D. 中间比较仅带误差 | 固定输入可任意逼近，或全局缺陷同号抵消，有机会恢复精确结论；否则只试 §5 的 ABC 预算 | 有界误差、相对误差趋小或另取一组源，均不能自动恢复原 III.3.12 |

这里 `L,U,H` 全是**按指定方式计算出的读数**，不能倒用 C4／ABC 定义它们。一个最小判别例：`qₛ=−3, L=−3, U=−1` 与 `Θₚ=−4` 相容；即使还知道 `Θₚ≤U`，也推不出 `qₛ≤Θₚ`。正确的补箭头是 **`L≤Θₚ`**，不是再找一个共同上界。若算术 q 与源 q 不相等，给原 III 的方向是 `qₛ≤−M` 后接下界；用原 III 给 C4 的方向反过来，是 `−M≤qₛ`。不能把一个方向双用。

仓库已有适于 B 的入口：[原 reading 的单向运输](../tmp/sheaf/xif/paper/Mzk1ActualReadingTargetActual.lean#L159)。它的实质是 `Q_src ≤ Q_norm ≤ H_root ≤ H_tgt`；中段已有证明体，两条外箭头是该定理的**参数**。`Q_src` 是 `qPilotLogVolumeReading P`，`H_tgt` 是 `thetaPilotHullLogVolumeReal C3`。应从同一源生成 `T,I,P,C3` 和两条外箭头；不能任取独立的 `P,C3,T`。Lean 的标量行通过后还须证这两个锁定端点确实实现原文的全局、逐行、按权读数。反过来，若源语义已构造但旧 API 不是它的同一读数，保留源定理和旧目标之间的缺口，不动目标定义。

## 2. R0：把 q 的单位、全纤维与根做对一次

**先检查旧目标的真身。** [锁定的两端](../tmp/sheaf/xif/paper/S3137QThetaPilotLogVolumeReadingsActual.lean#L77)分别计算一个 `P.line.C3` 的 q，以及 `actualHolomorphicHull C3 (actualUnitRegion C3)` 的原始 Haar 对数（同文件第 97、128 行）。后者的定义并不枚举 `(p,j,t,Ind)`。因此「源码里也叫 holomorphic hull」不能充当对论文读数的语义证明。能证旧区域是允许外盒，只给一个上界；要让旧读数承接论文下界，还得在正确方向连回源并验权。若不能双向识别，分别登记“旧 Lean 目标”“原文目标”“算术 C4”。

**交付 R0-a：一张有标签的算式。** 固定实际塔 `w|P|b|p`（依次属 `K,F,Fmod,ℚ`）。记 `v_P(π_P)=1`，`e_P=v_P(p)`，`f_P=[κ(P):𝔽_p]`，`d_P=e_P f_P`。对同一个非零 `q_P`，在**延拓 ℚ_p 绝对值的那个范数**上证明

\[
 -\log\|q_P\|/\log p = v_P(q_P)\log N(P)/(d_P\log p)=v_P(q_P)/e_P=:c_P.
\]

从[谱范数公式](../tmp/sheaf/xif/paper/S829PaperNormValuationSpectralActual.lean#L40)出发，落实 `ν(q)=v_P(q)`、`N(P)=p^{f_P}`、completion degree=`e_P f_P`，以及 generator 的来源。旧系数 `v_P(q)·log N(P)/log p=f_P v_P(q)=d_P c_P`；[现有字典](../tmp/sheaf/xif/paper/Mzk1ULR0RealDictionaryActual.lean#L55)中 `hpaper` 是参数，不是一般定理。诊断取 `e_P=2,f_P=3,v_P(q)=4`：新系数 2，旧系数 12；`normRatio=1` 或再次除相对 `e(P/b)` 都不是修复。若只知道默认范数到谱范数的单向比较，保留方向并把 q 身份及权重单独证明。

**交付 R0-b：用共同模数不变量，不要求 q 相等。** 从[源中模数的 j 与 Tate 实现](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L416)取 `j_b` 的实际下降；经同一曲线的实际 Tate 比较，证明 `q_P·j(E_P)` 是单位（Tate 展开主项为 `q_P⁻¹`，其余项乘 q 后在极大理想；曲线坐标变换保持 j）。置 `m_b=−v_b(j_b)>0`，于是 `v_P(q_P)=e(P/b)m_b`，不必构造 `F_P≃F_{P′}` 或证明所选 q 元素相同。把 `f_P=f_b f(P/b)` 及 `Σ_{P|b} e(P/b)f(P/b)=[F:Fmod]` 代入：

\[
 \frac{\sum_{P|b} f_P v_P(q_P)}{[F:\mathbb Q]}
 =\frac{f_b m_b}{[F_{mod}:\mathbb Q]}
 =w_b c_b,\qquad w_b=\frac{[F_{mod,b}:\mathbb Q_p]}{[F_{mod}:\mathbb Q]},\quad c_b=m_b/e_b.
\]

`hprime` 只允许把同一个 `log p` 提出求和；它不产生上式。**验收**：左边枚举所有 `P|b`（而非每纤维挑一位），右边固定同一 `j_b`；`cPFullFiber=w_b c_b` 用实际实例推出，不作输入。区分这里 *模数不变量 j* 与后文 *标签 j=1,2,…*。

可以比从头做谱唯一性更短：直接串[同一实际 q 上的范数幂公式](../tmp/sheaf/xif/paper/Mzk1P0QVFamNormBridgeDonorActual.lean#L63)、[默认范数与 raw 阶](../LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotBaseChange.lean#L71)和[局部次数及剩余域大小](../LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean#L66)，最后用[实数消元](../tmp/sheaf/xif/paper/Mzk1ULR0COldActual.lean#L18)。`ramificationIdx` 在 `𝓞 ℚ` 与在 `ℤ` 的两个表达须运输，不是 `rfl`。共同 j 的计算也有短路：在[每个 P 的实际 `qVFamAt`](../tmp/sheaf/xif/paper/Mzk1ULQPilotMagnitudeV2Actual.lean#L36) 上用[无 1728 单位假设的 `H(q)=q+R(q)`](../LeanFormal/IUT/Foundations/PAdicAnalytic/TateDeltaIntegral.lean#L274)、[余项范数界](../LeanFormal/IUT/Foundations/PAdicAnalytic/TateEstimatesGeneral.lean#L57)和 `H(q)=j(q)⁻¹`，得 `‖R(q)‖≤‖q‖²<‖q‖`。将 `realizesCurve` 与 j 的坐标变换/基变公式相接，然后[沿收缩位运输 j₀⁻¹ 的离散阶](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionNormTransport.lean#L352)，而非运输所选 q。[`MpaperB` 的权重提取](../tmp/sheaf/xif/paper/Mzk1ULR1MpaperBWeightActual.lean#L49)本身不用再证，尚欠的是 Tate 比较和整纤维身份。

**交付 R0-c：固定 q 的端点。** 写明 `Q` 是未除 `2l` 的论文 q 总量，`M=Q/(2l)` 是本链使用的正量，若当前模块的 `actualQ` 采用另一读法，另证它等于 Q 或给所需方向；不要从变量名认同。[实际 q 的逐位桥](../tmp/sheaf/xif/paper/Mzk1ULBridgeActualQPaperMActual.lean#L45)正好显示剩余逐位前提。核对在 `Fmod,F,K` 及另加根的扩张上的次数：局部范数已除绝对 e，全局高度用总和除 `[L:ℚ]`，不可重复除。最后输出 **两个**结论：论文 `qₛ` 的来源关系，以及供 C4 用的 `−M` 算术等式。任一暂缺也不妨碍继续做另一端。

**两个不同 lift 怎么办？** [旧接口](../tmp/sheaf/xif/paper/Mzk1BaseChangeQCorrespondenceActual.lean#L104)要求 `comap_F(w)=chosenLift(b)`；“都在 b 上”不蕴含相等。有两条真路：① 对真实几何传输，固定 `w`，先取 `P₀=comap_F(w)` 再在 `P₀` 取源 Tate 见证；[canonical lift](../tmp/sheaf/xif/paper/Mzk1URCanonicalLiftActual.lean#L26)使这**一组新选择**的对齐成立，completion map 可接，但旧目标不会因此变成 `rfl`。② 若只比较算术数值，在两 lift 各证共同 j 的 R0-b，于是 `c_{P₀}=c_{P₁}`；不需交换两个 completion。若还要运送作用，须给出真实共轭/基变图并证明 choices 不变，或构造另一条通向同一源观测的桥；不能由系数相等推出映射相等。[实际 Tate 的坐标变换](../LeanFormal/IUT/Foundations/Geometry/TatePointQuotientBoundary.lean#L124)，与[所有实际坏位的 q 见证](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L952)配套使用。

## 3. R1：从原文输出得到下界，而不是给 q 格改名

**先定共同的观测对象。** 给定 `T` 及由它得到的原文 0/1 两列、Kummer 实现和全局 degree 标定。固定 `(p,j)`，在 1 列的 `IQ(S±_{j+1};D_p)` 内，令 `Sₚⱼ` 为依 III.3.11 得到的所有允许 Θ 像的并，`Uₚⱼ=HolHull(Sₚⱼ)`。允许箭头、输入、作用、列及投影都由这一个源给出；定义中不得含所求不等式。定义一次 `read(T)`，上下界均以它或到它的单向定理为端点。[III 的逐行定义](IUT-TEXT/III.txt#L10378)；[hull 定义](IUT-TEXT/III.txt#L7656)是包含原区域的最小允许形状 `α·O`（分解后各分量非零）；不是“对并集取拓扑闭包”。不相对紧时原文另有全空间分支，不能略去。对来源不明的 `closure` 对象先只建立包含，不断言等于 `Uₚⱼ`。

**路线 R1-I：在同一载体中给出区域。**

直接复用选根，不要重试错误的域：当 `v_P(q_P)` 与 l 互素，若 `x^(2l)=q_P` 在原 `F_P` 成立，会迫使 `l∣v_P(q_P)`；[原 completion 不可能性](../tmp/sheaf/xif/paper/S342QVFamilyRootImpossibleActual.lean#L60)已把这个障碍写出来。[扩张中的实际根](../tmp/sheaf/xif/paper/Mzk1URRootExtensionActual.lean#L76)和[同一参考格下的精确质量](../tmp/sheaf/xif/paper/Mzk1URRootExtInstancesActual.lean#L120)已有证明体。实施的起点是把此扩张与**论文指定**的 K 位／源实现接上（真正 lying-over 的情形有[归一化 completion 代数映射](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceRelativeNormalizedCompletion.lean#L63)），不是二次开发开根或 Haar 积分。解析侧若用平方根，其兼容选法是 `r^l`（此处 `r^(2l)=q`）。

1. 从 `clauseB.q_comparison` 在所选 `P` 取 q，再从 **该点的** Tate/Kummer 表示取 `r` 及 `r^(2l)=q`。若实际 `K_w` 不含根，可同基变到 `L_w`，但须同时运输参考格、Θ 像、源作用及 Haar；证结果可下降或读数基变不变。两个根相差 `μ_{2l}`，主格不依赖选择；这只解决局部格，不能代替 Kummer 箭头的相容性。
2. 对 `J=r·O_L`、`d=[L:ℚ_p]` 计算 `ν(J)=log(μ(J)/μ(O_L))/d=log|r|_p=−c_b·log(p)/(2l)`；用 `det(m_r)=N_{L/ℚ_p}(r)`。另一可行构造是先用未开根的 `q·O` 算 `−c_b log p`，再用**原文规定**的 `1/(2l)` 读 q 的有理次数。二者是不同的实现，只可计一次。现有[坏位 q 区域](../tmp/sheaf/xif/paper/Mzk1URBadPlaceActualMapActual.lean#L65)的 `badPlaceQRegion_nu` 明写 `−c·log p`；[容器的标量](../tmp/sheaf/xif/paper/Mzk1URThetaContainerP5Actual.lean#L67)则带 `1/(2l)`。两个公式正确也不直接给实际 Θ 像。
3. 写出源的 theta/Kummer 箭头、completion 中的实际生成元及单位商上诱导的线性作用，检验它们交换。有限位的原文乘积 hull 只需逐个坐标有源见证达到目标半径；见证可以不同，单个全坐标达到阈值的点也足够。§9.4 给出该判据的充要性和固定行的计算。要从 prime-strip 箭头取线性作用，仍须由实际实现识别单位商、核对过滤与线性延拓。
4. 若直接比较两个 Haar 测度，先辨明比较的是线性像本身还是它的乘积 hull。直线的像在高维空间中的原始 Haar 质量为零，其乘积 hull 的体积可由各坐标半径给出。若采用满格运输这一实现，则证明像的秩、参考格及 Jacobian，并按 `log μ(J)=d·ν(J)+log μ(O)` 恢复参考项。§9.4 的坐标方法直接作用于已辨明的乘积 hull。
5. 证明源下端的**全局**读数是 `qₛ`：不能用 label-one 的量替代所有标签的平均。两种足够的出口：(i) 对每个实际行给下界 `aₚⱼₜ`，按 §4 同一组权平均并证总和 `≥qₛ`；各行无需都 `≥qₛ`。(ii) 不逐行比较，证明 Step XI 的全局 degree 射线包含 `qₛ`（R1-II）。逐位下界只要能随实际权重求和即可；若仅 `j=1` 有源箭头，在该行停下，不能升级成 (i)。

**路线 R1-II：载体不同，改在行列式线／有序次数上比较。** [III Step XI-d 至 f](IUT-TEXT/III.txt#L10826)正是先取秩大于一的块的行列式及适当正张量幂，再比较 `qₛ ∈ (−∞,Θₚ]`；[Fig. 3.8](IUT-TEXT/III.txt#L10949)说的是 **q 的两种计算**，不是 `Θ=q`。构造方法：

- 从 0 列 Θ 对象沿原 `Θ^{×μ}_{LGP}` 链取像，和 1 列 q 的 Kummer 表示分别送到**同一全局算术次数线**；在 1 列取 log-Kummer 来校正单位部分和 log-shell 的层差。用同一输入 prime-strip 的实际对应识别这两个路径的 q 次数；不要求局部完成域同构。局部 `O` 与 `p^kO` 如只看抽象对象易混淆，degree 差 `−k log p` 必须由全局标定固定（见 [III Step XII](IUT-TEXT/III.txt#L10965)）。
- 对每个实际满格保持参考格，算 `log|det|`，在共同正整数张量度上清分母；基变次数与参考质量同步除回。[加权行列式](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/WeightedNormalization.lean#L97)只做已给次数的代数。[hull 的伴随/最小性](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean#L358)只给一般接口。仍需实际源对象、对应态射与到 `Uₚⱼ` 的比较。这里是**为比较读数**取原文所需的正幂，不是把 Θ-pilot 换成它的任意张量幂再套同一不等式（[III xi-h](IUT-TEXT/III.txt#L10954)）。
- 精确的小目标：构造一个来自源的允许输出 `z`，证 `qₛ≤deg(z)` 且 `deg(z)≤Θₚ`；更强但非必要是第一式等号。若只得到一族逼近，按 §5 固定端点取极限。把 `qₛ∈(−∞,Θₚ]` 放在记录字段中再取出来等同假设结论，不能交付。若已有目标载体中的 q 区域，亦可直接用[包含到原 reading 的条件引理](../tmp/sheaf/xif/paper/Mzk1Cor312ActualReadingBridgeActual.lean#L66)，逐项产生它要求的包含、q 读数、正测度和有限测度。

可将两条路径的行列式对象具体放在[原文的共同 Frobenioid 容器](IUT-TEXT/III.txt#L5250)的 `Pic`，读取同一算术 degree，对照[仓库的 P5 容器笔记](R1-P5-COMMON-CONTAINER-DOC.md)。要验证的是该处**不同**的负 pilot 元素如何比较、有界射线如何从实际发生的输出读出，不是把两个域任意嵌入更大域再宣布所有对象相等。XI-d 至 f 叙述了要重建的对应，并没有免费给根格的满秩嵌入。

**有限性独立验收。** 下界需要一个实际正测度的内格，上界可由允许的紧外格得到有限测度；无穷处按其自身规则。全局还须证支集可求和／除有限多位外为规定的标准项。[III 证明中的紧性步骤](IUT-TEXT/III.txt#L10409)也可给独立的有限性证明，故原 III 不必等 IV 全部常数。不要用 `ENNReal.toReal ⊤=0`、`Real.log 0=0` 获得假有限读数；若模块容许 `M=0`，须单独证明它的弱分支，不能除以 M，亦不能拿它替代原文 `M>0`。

## 4. R2：为同一读数构造上界。先固定 p，再选 j 和位置元组

[IV Step (iv)](IUT-TEXT/IV.txt#L1585)明确重述 III 的 Θ 定义。有限有理位 `p` 下令 `E_p={v|p in Fmod}`（**全部**位），`λ_v=[Fmod_v:ℚ_p]>0`，`n=(l−1)/2`。对 `1≤j≤n`，遍历所有有序 `t:Fin(j+1)→E_p`，允许重复。源空间是「各位 log-shell 张成空间的直和」的 `j+1` 重张量；先把张量对直和分配，再投到实际 `t` 分量。记 `V(p,j,t)` 是按原参考格、维度归一的源 hull 分量读数。必须证明它确为 `read(T)` 的分量（或上界方向的比较）；不能把 `V` 定义为想要的上界。目标表达式为

\[
 R_p=\frac1n\sum_{j=1}^n\frac{\sum_t W(t)V(p,j,t)}{\sum_t W(t)},\qquad
 W(t)=\prod_{i=0}^j\lambda_{t_i},\qquad \sum_tW(t)=(\sum_{v\mid p}\lambda_v)^{j+1}.
\]

若 hull 和投影次序不同，不先声称可交换。对**积形允许盒**逐分量证 `pr_t(Sₚⱼ)⊆Box_t`，从而 `Sₚⱼ⊆∏Box_t`；验证该积在原分解中也是允许的 holomorphic 区域，则由最小性得 `Uₚⱼ⊆∏Box_t`。这是上界所需的方向；源像跨分量有相关性也能用。若要号称等号，需另证原读数的分解及全部参考格归一；不能以独立性替代。各 `R_p` 最后按[IV Step (viii)](IUT-TEXT/IV.txt#L1862)对**有理位**求和，不再乘一次 `λ_v`；若改写成按坏位 `b` 求和的代码，先证重排等式且补 good、ordinary 和无穷位。

### 4.1 一条实际的局部上界应交什么？

1. 在 [Step (v) 指定的槽](IUT-TEXT/IV.txt#L1626) `i†=j`，由同一源给出 `varpi`：good 位贡献 `ord=0`，bad 位 `ord_p(varpi)=j² o_{t_j}/(2l)`，`o_v` 为未开根 q 的规范阶。其余槽保留各自的 `K_{w_i}` 及 log-shell。`r^{j²}` 是**这个槽**的因子，不是再把它作用 `j+1` 次。不同元组的域与位置必须能追溯到源指定的 lift。
2. 给出实际张量块的有限域积分解 `e`、参考格、`Phi` 和每个允许箭头的表示。Ind1/2：证明源诱导的 `φ` 保持 unit-log lattice，图像写作 `φ(tprod(1,…,varpi)·x)`。用于上界的 `Phi` 可以是已证覆盖源箭头的较大家族；取 `id` 只能证非空。Ind3：依 [IV 的包含方向](IUT-TEXT/IV.txt#L1654)，源的所有上半连续允许像仍在相应放大的外格内；不要求每一个都是 Ind1/2 的原像，更不能从一个例子推出覆盖。最后证明这个外格是 `g·O_hol` 型，再取 hull。
3. 复用[实际张量的可能像、最小 hull 和单行上界](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L668)及[其 hull 版定理](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L814)。该定理已处理指定 `places,tuple,e,varpi,Phi` 的几何外格；**仍须实例化**这些量并证原 Θ 像的包含，尤其 Ind3，而不能将构造的可能像集合直接命名为论文集合。设 `d_v` 为归一化 different 阶，实际例外槽 `e_{w_i}>p−2`，用原 R4 估计将例外和上界为 `4(j+1)ι_p l*`（这里 R4 是 IV 中的局部条件，不是本项目 R4 包）。得到

   `V(p,j,t) ≤ B_j(t,j)`，其中 `B_j(t,s)=[−j² o_{t_s}/(2l)+Σ_i d_{t_i}+1]log p +4(j+1)ι_p l*`，`l*=log(e*_mod l)`；`ι_p=1[p≤e*_mod l]`。务必用该块原有的 p-adic 阶口径和各 e 的来源。无不同／非 distinguished 的有限有理位及无穷位使用 IV (vi)、(vii) 的相应盒，不能把此式套遍全部位。
4. **现有捷径：只要最后一槽的界。** 对每个 `j,t` 得上式，直接用 [`processionNormalized_le_of_distinguishedBounds`](../LeanFormal/IUT/IUTIV/Estimates/StepVDistinguishedSlotAverage.lean#L109)，取 `slot j=Fin.last j`。理由是 `Σ_t W(t)B_j(t,s)` 与固定的 s 无关（交换元组槽位；权积不变），**不要求**每个 `V(t)` 在交换下相同。另一接口 [`processionNormalized_le_of_collectionBounds`](../LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean#L217)要求逐元组 `V(t)≤avg_s B_j(t,s)`；只有确实有这个更强事实才用。两条都不需要证明“并集的体积不超过均值”。

### 4.2 两行算例：先在这里暴露不可能的比较

- **`l=5, n=2, j=1`**：`t=(a,b)`，槽 1 的 q 项是 `−o_b log p/(2l)`；different 项是 `(d_a+d_b)log p`。交换 `(a,b)↔(b,a)` 后右端通常不同，但两项的权都是 `λ_a λ_b`。这是为什么可在求和后对称，而不能固定元组把 `o_b` 擅换成 `(o_a+o_b)/2`。
- **同一 p，`j=2`**：`t=(a,b,a)`，最后槽用 `r_a⁴`，q 项 `−4o_a log p/(2l)`；different 项 `(2d_a+d_b)log p`；权 `λ_a²λ_b`。还需 `(a,a,b)` 等元组，各按自己的最后槽取 q。在 `E_p={a,b}` 时两行分别有 4、8 个元组，分母分别为 `(λ_a+λ_b)²`、`(λ_a+λ_b)³`，最后两行各占 `1/2`。若指定数据只有一个 b，不捏造第二个位；先验证单纤维，再用一般两位元组恒等式或另一个**实际具有两位**的源检验混合项。
- **下界的反向测试**：设 `0<|r|<1`、同一参考格，`ν(rO)=log|r|`，`ν(r⁴O)=4 log|r|`。于是 `j=1` 内格虽有预期 q 质量，`rO⊄r⁴O`，第二行并不给同样下界。只能回 §3 的全行加权下界或 XI 的全局 degree 对应。**上界的反例**：在 `ℚ_p` 取 `A=ℤ_p,B=pℤ_p`，`μ(ℤ_p)=1`，则 `log μ(A∪B)=0 > (log μ(A)+log μ(B))/2=−(log p)/2`。[当前 K 侧 hull](../tmp/sheaf/xif/paper/Mzk1URThetaKSideActual.lean#L88)恰为同一块中跨标签并后取 closure；[名为 Step V 的 Prop](../tmp/sheaf/xif/paper/Mzk1URThetaProcessionActual.lean#L85)不是把它变为平均值的证明。这两个反例淘汰的是捷径，不是论文命题。

### 4.3 分量不直接分裂怎么办？两种可执行后备

**能在实际 K 侧先下一个更强的诊断。** 对任一原模块允许的坏位 b，记 `R₁=ksThetaRegion(oneLabel)`，`C=ceilRegion`。仓库已有 [`R₁⊆ksThetaHull`](../tmp/sheaf/xif/paper/Mzk1URThetaKSideActual.lean#L252)、[`ksThetaHull⊆C`](../tmp/sheaf/xif/paper/Mzk1URThetaKLowerBoundActual.lean#L121)、[`R₁=C` 及其 log-volume](../tmp/sheaf/xif/paper/Mzk1URThetaKLowerCoreActual.lean#L214)。三式合起来，**这一个现有的 `ksThetaHull` 本来就等于第一行的取整格**，其读数是 `−u log p`，`u=urCeilC(T,b)`；不是只“暂时没找到”它含有第二行信息。这里是由现成声明推出的纸面结论，本次没有新增或编译 Lean 定理。代入[平均的精确式](../LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean#L54)，在 `n=2,l=5` 时，旧的自由参数命题等价于 `Q/4≤u log p+(5/2)D+S+10T′`。固定 b，取 `D=S=T′=0, Q>4u log p` 就失败；**不**反驳参数来自同一个真实源时的比较。这个 K 壳仍可作第一行的内格／局部供体；要对它做 C4 比较须另证上述类型的真实算术界，要做 IV 则回到原逐行 `Uₚⱼ`，别在旧壳中寻找遗失的槽。

**“忘掉一槽”也要选对映射。** 固定 j 时有[源的槽间同构](../tmp/sheaf/xif/paper/MultiradialProcessionActual.lean#L42)，不等于从 `j+1` 重张量降到 `j` 重张量。若拟议线性忘槽 map 要与被忘因子中的 `−1` 等变、目标又令该作用平凡，则 `π(x)=π(−x)=−π(x)`，特征零迫使 `π=0`；先排除这种不可能的满射。可改取**同源联合行像的坐标投影**：在精度 N 定义前两行联合像 `X₁₂,N` 和其第一行投影，证明每个前缀的延拓数上界，再逐层求和。联合直积若一次除以总维数，会给 `d_j/Σd_i` 权，而非论文 `1/n`；仍须逐行除以其张量维数（因子局部度的乘积），然后按 §4 求平均，或严格证明正张量幂清分母的标定。计数控制联合像不自动给各行 holomorphic hull 的读数，需要外格及最小性这一步。

- **格过滤。** 在实际 `ℚ_p` 块选共同满参考格 `Λ`，从源作用证明它有过滤 `Λ_i`，求诱导像与余核，对严格短正合的格序列用指数相乘。若 `p^kΛ⊆Γ⊆Λ`，`log(μΓ/μΛ)=−length_{ℤ_p}(Λ/Γ)log p`；用其它离散赋值环须乘 residue degree。对张量映射，因子 A 的 determinant 在 `A⊗B` 中带 `dim B` 的幂，除总维数后才可比较。上界要的是源 hull 在外格内（等价相应指数下界），下界要内格在源 hull 内（指数方向反之）。不分裂并非障碍；若过滤不是源不变的，此分解不能用。还要核对整体 degree 确实是 §3 的 `read(T)`。
- **有限商计数。** 在同一个有界满格 `Λ≃ℤ_p^d` 工作（必要时先缩放），对**实际** `U=Uₚⱼ` 及候选内外格取 `mod p^NΛ`。外界可对所有源像的坐标给兼容剩余类覆盖；下界必须来自实际内格或可提升的可能像，不能仅数点。递归按槽遗忘，证明每个非空基底纤维的统一上界，再用 `#S=Σ_x #S_x`；仅有各投影的基数不足以推出独立/下界。若 `U` 闭且紧，约化逆像之交就是 U，归一化 Haar 比为 `lim_N #red_N(U)/p^{Nd}`；只给超集时只得对应方向。对格的 Smith 因子可在足够精度直接精确计算；对一般区域须证相容、有限测度与极限。一次 `N` 或模拟数字只排错。越过取 log 的步骤要有正下界。

**R2 的另两张收据：** [hlogdK](../tmp/sheaf/xif/paper/Mzk1ULR2HlogdKTowerActual.lean#L32)仍接受 `hbound`：在同一 `K/F` 上把 good（不同为 0）、tame（`δ=e−1`）、wild（有效上界）逐位按 `f_w log p` 求和，并用 tower、导子及特殊位常数闭合，接到 `SAr_F+2 log l+21`。[hsQ](../tmp/sheaf/xif/paper/Mzk1ULR2HsQSupportActual.lean#L47)中有限支集恒等式已写，数值界仍接受 `hbad′`：各 p 只入 support 一次，分 q/different/特殊位，完整纤维的权重和 `≤1` 后求和。不要拿所有 `p≤max bad` 的 primorial 代替它。若出现更弱常数，去 §5 登记缺陷，不伪称原 IV 常数。

## 5. 不同 Θ 或比较差一点时，怎样继续？

**先问差的是什么。** 若只差基、Haar 常数、扩域次数或根的单位，计算 Jacobian、参考项和域次数，把两端送到同一有序实数线；无需逐位对象相等。若有实际可测的内外格 `J⊆Uₚⱼ⊆B`，则用单调性即可。若连逐位包含也没有，先按规定权求和看**带符号**的缺陷：例如同一全局元素引起的行列式缩放，可以尝试用全体位的乘积公式消去；须证它真是同一元素、权正好是该公式的权、所有有限及无穷项都在，不能用局部任取标量凑成 0。仅上界端点度量变大无助于论文下界。

**固定输入可去误差的判据。** 要证原文 `qₛ≤Θₚ∈ℝ`，若有限性已证，只须对 **同一个** `T,l,qₛ,Θₚ` 给出 `∀η>0, ∃` 可由源实现的输出 `zη`，`qₛ−η ≤ deg(zη) ≤ Θₚ`；反设 `qₛ>Θₚ` 取半差矛盾。也可直接得到 `qₛ−η≤Θₚ`。可变的是逼近精度／辅助层，前提是这些层的读数映回不变的端点。**随高度选更大的 l、换 Θ-data、固定 l 只得一个正误差**都不是这个量词。如果只固定 `A,Q,l` 的端点而源 Θ 随精度变化，至多在这些固定算术端点上取极限得精确 C4，不能恢复原 Θ。

**只能保留损失时，用一张误差账。** 设 `κ=(l+1)/4>0`、`c_l=1/6−2/l²>0` (`l≥5`)；`A` 为与该源同一套域、支集和权重的 C3 算术项。把实际估计整理为

\[
 -M-E_-\le L,\quad L\le U+E_t,\quad U\le H+E_+,\quad H\le\kappa(A-c_lQ)-M.
\]

逐项相加而非倒用最终 display，得到 `c_l Q ≤ A+(E_-+E_t+E_+)/κ`。若 C3 本身另有松弛，也计入分子；若已掌握带符号的总修正 `≤0`，则可给精确 C4。算术上只需 `−M≤H` 和 H 的独立上界，甚至可直接以 H 作[既有 `c3_to_c4`](../tmp/sheaf/xif/paper/Mzk1P6C3C4Actual.lean#L9)的中项；难处是从源给出前者。对 `M>0`，把同一 `A,Q` 代入 [IV 指定系数的算术等价](../tmp/sheaf/xif/paper/S2715CThetaPaperScaleActual.lean#L44)，`CΘ_paper=κ(A−c_lQ)/M−1`；有损时只保证 `CΘ_paper≥−1−E/M`。这个标量式不是 `Θₚ≤CΘ_paper M` 的几何证书，更不是 `CΘ=Θₚ/M`。若 `M=0`，在推广接口中用 `Q=0,A≥0` 单走 C4。

| 缺陷 | 实际怎么算 | 可接受的去向 |
|---|---|---|
| 值群取整 `E_round` | `a_b=c_b/(2l)`，用内格时 `0≤ceil(e_w a_b)/e_w−a_b<1/e_w`，乘 `w_b log p_b` 求和；负号给 `−M−E_round≤L`，不是 `−M≤L` | 证明真实支集控制 `Σ_b w_b log p_b/e_w ≤ C_d(D+N)+C`，除 κ 后为 `O_d((D+N)/l)`；或证该内格无需取整 |
| 运输或外盒误差 | 每个原行列出 `log(abs(det))`、余核长度、参考格偏移、所乘次数，标出正负，按 §4 的权求和 | 可精确消掉才回 A/B/C；否则证明其 `/κ` 为一致可吸收量。一个无控制的维数幂/每一位一个自由常数不可用 |
| 选位和高度差 | 写 `Q_used=h−Δ`（`h` 与全部 q 质量的字典另证），则 `c_l h≤A+E/κ+c_lΔ`，不是减掉 Δ | `Δ=O_d(√h log(2C_d h))+O_K(1)` 或同强估计。小高度、有限例外事先取统一常数 |

**预算的数值验收，不只写「可吸收」。** 记 `B=D(L)+N_L(λ)≥0`，目标系数为 `1+η`。若整理主项后有 `h′≤(1+α)B+βh′+C`（`h′` 是目标归一化高度），就明确选择使 `0≤β<1` 且 `α+(1+η)β≤η`，这样除以 `1−β` 才得 D1。恒定倍数的 `B` 不能藏进 `O(1)`。`O(Q)/κ` 若 `Q=O(h+1)` 且 `l≳√h` 才变成次线性；`O(lQ)/κ` 则一般仍是主项。交付一张依赖表：`C=C(d,K_V,η)` 在三元组之前固定；对阈值以上统一证明该预算，对阈值以下及原文例外按统一高度界处理。超预算时先查 IV 规定的权、重复计算的 e 或 `2l`、能否全局抵消，再决定是否只有更弱结论，不直接砍掉 R1/R2。

## 6. R3–R7 怎样消费，哪里可以现在就做？

| 包／实际消费者 | 交给接手人的构造顺序 | 验收：必须交什么，不是只交结构体 |
|---|---|---|
| **R3 → D1** | 对实际 `λ≠0,1` 取 Legendre 曲线，分别识别 `Fmod=ℚ(j(λ))` 与 tripodal 层 `ℚ(λ)`（不要假设两域必不同，也不能默认相等）。在同一闭包中取 `[3],[5],[l]` 的实际核；用 division polynomial 则需证 `ψ_m(x)=0 ⇔ [m]P=O` 的适用条件、两种 y、无穷远及所有点完备。两向包含证明坐标生成域就是源要求的域、作用在实际基上。另从排除素数的 `Σlog p` 界在原区间选 `l`；不能用 D1 选产生 D1 的 l。 | [IV Cor. 2.2](IUT-TEXT/IV.txt#L2382)对 `K_V` 含 2、2 处 j 有界，以及有限 `Exc_d` 外给合格 Θ-data；**不是**要求例外点也造该源。用统一高度界覆盖例外／低高度。大高度 `√h≲l≲C_d√h log(2C_d h)`。做两张不重叠表：全部有限 q 位 vs 入选坏位；入选坏位完整纤维 vs 实际 lift。另记 2、arch 等字典差，先验 §5 预算。扩域时用 `Σef=[L:Ftpd]`、`δ≥e−1` 及 different tower 支付截断导子损失，得到 `D(Ftpd)+N_Ftpd≤D(L)+N_L`。最后才接 C4 得全量词 D1；[已有核入口](../tmp/sheaf/xif/paper/Mzk1G1R3TorsionKernelActual.lean#L27)。 |
| **R4 → R5/R6 的同一张 φ** | 输入不交、Galois-stable 的有限闭几何点 `S,T`。扩 T 得避 S 的 reduced D、`deg D≥2g+1`。`deg(K−D+x)<0` 与对偶给 `H¹(O(D−x))=0`，evaluation 满射；在有限多个真核外选有理 `s₁`，使在 supp D 处均非零，`div(s₀)=D`。在 `D(s₀),D(s₁)` 两图定义 `ψ=[s₀:s₁]`。对受保护值做 Möbius＋有理 Belyi 递归，逐次跟踪分歧值、受保护值和下降。 | 得同一个非恒定有限 `φ`，`Branch(φ)⊆{0,1,∞}`、`φ(S)` 入边界、`φ(T)` 避边界。不要填[所有 D 均非特殊](../tmp/sheaf/xif/paper/Mzk1G1F2H1VanishingDataActual.lean#L52)：正亏格 `D=0` 反例。[原文的消失条件](../papers/motizuki_corpus/text/Noncritical%20Belyi%20Maps.txt#L240)只需所选的大 D。若一般对偶接口代价高，可用高次截面的有限点一阶 jet 插值，但须证明整个零纤维 reduced，不仅仅在 T 单根。 |
| **R5 → 固定 K_V** | 对 `M/ℚ_p, m≤d` 取 `O_M=ℤ_p[x]`；其 minpoly 导数生成 different。填实 `different(ℚ_p/ℚ_p)=0`、`e≤m≤d`，用保守统一 `B=d(d+2)`。从 `f′(x)=∏(x−x′)` 及每个因子范数 `≤1` 推每个因子的分离下界；系数有限化＋Krasner 得固定局部域容纳所需嵌入。取 `r+1` 张边界不交的映射，`r=d·card(V)`，对所有 `v` 及所有共轭同时作 `max_i min_{v,σ}ρ(φ_i(y^σ))`，其中 ρ 是到 `{0,1,∞}` 的射影距离。 | 由不交、鸽巢和紧性得到统一 `ρ₀>0`，一个 y 的所有局部共轭用**同一个** i（不是每个 v 选一个）。包含 arch 因子、2 处以及 j 的有界性；`φ_i` 是 R4 的实际映射。[Separation 接口](../tmp/sheaf/xif/paper/Mzk1G1SeparationInputActual.lean#L45)中的实际输入仍要产生。 |
| **R6 → F6** | 在同一 `L,y,φ_i` 上取 `E_i=(φ_i^*{0,1,∞})red`。由实际 Belyi 分歧和微分得 `ω_Y(E_i)≃φ_i^*O(1)`；模型好位的导子至多交点长度，有限坏位＋无穷位给统一常数。用真实 E_i 的齐次生成元 `P_j X_k^{m−d_j}`（所有 k），在 `X_k≠0` 图上生成同一理想，检查 DVR 重数。[完整坐标族](../tmp/sheaf/xif/paper/Mzk1HTF4R6CrosswalkActual.lean#L23)及[共同零点](../tmp/sheaf/xif/paper/Mzk1HTF4R6CrosswalkActual.lean#L63)已有源码；下一步是理想茎、模型度量和实际曲线比较，**不要重写这个族**。 | 按 [IV:3172 勘误](IUT-TEXT/IV.txt#L3172)，求 `h_E≤2(deg E/deg ω)h_ω+O(1)`，不是等式。仅为 F6，也可证明较粗固定 `κ_i`：选整数 `m` 使 `mω−E` 正度且一正幂全局生成，该高度有统一下界。再将 `h_λ=h_ω+h_E+O(1)`、`N≤h_E+O(1)` 与 D1 相接，`κ=max_i κ_i`，选 `η` 使 `(1+η)/(1−ηκ)≤1+δ`。较粗路线不冒充已恢复勘误指定系数。[GenEll 1.4](../papers/motizuki_corpus/text/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.txt#L294)、[1.6](../papers/motizuki_corpus/text/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.txt#L505)。 |
| **R7 → P8 → ABC** | 先定 `δ=min(1,ε/3)`，选 `n≥4` 使 `n/(n−3)≤1+δ`，固定 `d=n²`、映射族、`K_V` 和所有常数。对每个本原 `a+b=c`，取 `uⁿ=a/c,vⁿ=b/c,L=ℚ(u,v),y=[u:v:1]`。[次数界](../tmp/sheaf/xif/paper/Mzk1G1F7LiftDegreeBasicActual.lean#L56)可复用。`p∤nabc` 用单位导数/étale 得 δ_w=0；`p∤n,p∣abc` 在最大非分歧扩张上单位可开 n 次根，实际局部域嵌入 tame 扩张，故 δ_w=e_w−1；`p∣n` 用 `e_w≤n²` 的一致 different 界。 | 对每个 p 以 `Σ_{w∣p} f_w δ_w log p/[L:ℚ]` 求和，得 `D(L)≤log rad(abc)+C_n`。同一 y 有 `n h̄_L([u:v:1])=h̄_ℚ([a:b:c])=log c`；把实际投影 `π(y)` 的高度及 `ω_Y≃O(n−3)` 的度量接入。现有 [F9 消费者](../tmp/sheaf/xif/paper/Mzk1HT87F7F8F9InterfaceActual.lean#L122)要 `abs(hΠ−n/(n−3) hΩ)≤C₈` 及 `log c≤hΠ+C₉`，不是只有一侧。最终 `∀ε>0 ∃Cε ∀(a,b,c)`，不能先见三元组后选常数。 |

**三个能省下整包工作的选择。**

- R3 用[现有吸收代数](../tmp/sheaf/xif/paper/Mzk1G1D4BridgeActual.lean#L40)即可，最终要交 `∀ d,K_V,η>0 ∃ C ∀ L,λ, … ⇒ h̄_L(λ)≤(1+η)(D(L)+N_L(λ))+C`（d 为正次数界，K_V 满足原条件）。[旧 `LocalHeightCriterion`](../tmp/sheaf/xif/paper/Mzk1G1LocalHeightCriterionActual.lean#L68)用 `Height.logHeight₁` 的总高度，而 D、N 已除次数；转换/比较必须在真实量上证明，不能照抄旧签名。
- R6 如要**正好**得到勘误的系数，也无需先证两套高度成比例。设 `e=deg E_i>0, k=deg ω>0`，则 `ω^{⊗2e}⊗O(−k E_i)` 的度为 `ek>0`。由一正幂全局生成及 [GenEll 1.4(ii)](../papers/motizuki_corpus/text/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.txt#L311) 的一致下界，`2e h_ω−k h_E≥−C_i`，除 k 即可；若有效除子度为 0，则它为空、单列处理。此法不省略实际 line bundle 和度量的识别。
- R7 若固定标准射影度量、实际投影就是 `[a:c]`，可用 `[a:b:c]` 与 `[a:c]` 的本原坐标最大值均为 c 得精确 `C₉=0`；其它等价度量按已证的统一差计入常数。若只能获得 `hΠ≤n hΩ/(n−3)+C₈` 而不能证反向，**可以**由这一个方向直接证 `RouteF9Statement` 再用 [`routeFrey_of_F9`](../tmp/sheaf/xif/paper/Mzk1HT87F7F8F9InterfaceActual.lean#L142)。这是同一个 ABC 目标的替代证明，不是已填满双边 F8/P8 的声明。

## 7. 实施顺序与交接判据

| 顺序 | 先交的可核对产物 | 过不了时下一步 |
|---|---|---|
| ① 一个坏位 | 输出 `T → w → P₀ → b → p`、旧选位 `P₁`、实际 q 和模数 j 的关系、使用的两种范数／参考格；在同一页算出 `c_b` 和 `−c_b log p/(2l)`。 | 位不对齐：几何计算选收缩位，旧算术读数用共同 j；还缺的源等变性独立登记。不要先向下游填 `hcross`。 |
| ② 两条论文行 | 同一输入上依 §3、§4 给 `j=1` 的实际箭头与正测度、`j=2` 元组最后槽的真实根／单位、所有 Ind 像的外盒、different 与测度参考项。给出源对象、映射的定义域/值域、两条合成，不只列定理名。 | 若直线变成高维零测，停止做 Haar 等距，转 XI 的行列式或有满参考因子的张量。若是投影不独立，优先用 §4 的外盒包含而非证明分量独立。 |
| ③ 全标签与全位 | 上界对每个实际 `t,j,p` 给固定槽的估计，送到乘积权平均；下界另证明同一 `qₛ` 属于同一 `Θₚ` 的次数射线，或完成真实逐行加权下界；给有限性。补 ordinary/arch、`hbound/hbad′`，再接 C3。 | 局部全称太强时试**有权的全局**比较。端点只到 `−M≤H` 则提交精确 C4，原 III 保持未闭；写明缺哪一条外箭头，不重开已证的平均恒等式。 |
| ④ 有损／下游 | 依 §5 把每种 defect 填零或给上界，先做预算，再让 R3c 消费。R3a/b 与 R4、R5 不等这一步；R6 用同一点、R7 用同一 L 的估计，最后选择 ε 的常数。 | 固定源可任意小则回精确端点；只有 uniform 吸收则提交带损 C4→D1/ABC 路线；都没有则保留局部新事实及最小反例，不换目标。 |

**正式验收**：先锁定原结论的类型与引用定义（包括 signs、全局输入范围、Ind1–3、位及 procession 权）。按 [SHEAF](../SHEAF.md) 分别登记 `statement_compiles`（陈述编译）、`proof_body_checked`（证明体核查）、`kernel_closed`（传递依赖闭合）、`target_accepted`（目标比较器＋有效原文语义复核）。一个带比较前提的定理可前三者成立，仍不代表它实际构造了前提。Lean 验证只按现有 owner 流程加入 watchdog，查对应版本 DONE/FAIL；闭包只允许 `propext`、`Classical.choice`、`Quot.sound`。文档反例和数值测试不替代它们。

上表记录了最初按两个标签做的来源核对。§8 给出整条坏位纤维的进一步计算，同时说明哪些结果能用于原来的消费者。

<a id="torsion-fiber"></a>
## 8. 从实际扭点域推到整格和 different

这次把两条路线都推到了可以决定取舍的位置。逐标签的逆插值会付出一个可精确计算的整格指数。保留完整的循环子群，在一块占原 q 权重 \(\ell/(\ell+1)\) 的区域上，则能构造满秩基，精确得到 q 下界。下述结果都是对每个合格初始数据 \(T\) 的自然语言推导。实际 III.3.12、同对象的 IV 上界和对任意 ABC 三元组构造合格 \(T\) 仍是不同的命题。

### 8.1 源数据已经给出指定完备化里的根

记 \(F\) 为曲线的定义域，\(K\) 为给定的核域。固定一个位于 Bad 上方的 \(F\)-位 \(v\)，其有理素数为 \(p\)。令 \(q=q_v\) 为该处实际 Tate 比较的参数，\(k=v(q)>0\)，取 \(v(\pi_v)=1\)。源给出 \(p\ne\ell\)、\(\ell\nmid k\)、全部六扭点在 \(F\) 上有理，以及 \(K\) 与实际 \(\ell\)-扭点表示的核域在 \(F\) 上同构。核固定所有扭点的仿射坐标，故 \(E[\ell]\) 在 \(K\) 上有理。Tate 比较在局部代数闭包上与 Galois 作用相容。[初始数据条款 (b)、(c)](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L952) · [点比较的等变性](../LeanFormal/IUT/Foundations/Geometry/TatePointQuotientBoundary.lean#L25)

设 \(m=2\ell\)。\(E[2]\) 与 \(E[\ell]\) 之和给出 \(m^2\) 个 \(K\)-有理点。Tate 商的 \(m\)-扭点恰有 \(m^2\) 个，因为其代表满足 \(z^m=q^a\)，\(a\) 模 \(m\) 有 \(m\) 个选择，每个选择有 \(m\) 个不同的根。固定任一 \(w\mid v\)，这些点因此全部被 \(G_{K_w}\) 固定。若 \(r^m=q\)，则对每个 \(\sigma\in G_{K_w}\)，有 \(\sigma r/r\in q^{\mathbb Z}\cap\mu_m=\{1\}\)。于是每一个这样的根都在 \(K_w\)。同一个证明只用 \(E[2](F_v)\) 就给出 \(\sqrt q\in F_v\)，特别地 \(k\) 为偶数。此处也证明了单位部分的开根。[原来的完备化根接口](../tmp/sheaf/xif/paper/S1281KSideRootCompletionActual.lean#L117)

令 \(S\) 为 Bad 上方的全部 \(F\)-位，所有理想范数均取绝对范数，除非标出了相对域。设
\[
 \mathfrak q=\prod_{v\in S}\mathfrak p_v^{k_v},\quad
 Q=\frac{\log N\mathfrak q}{[F:\mathbb Q]},\quad M=\frac Q{2\ell},\qquad
 \mathfrak J_K=\prod_{v\in S,\,w\mid v}
       \mathfrak p_w^{e(w/v)k_v/(2\ell)} .
\]
上述根证明了指数为整数。\(\mathfrak J_K^{2\ell}=\mathfrak q\mathcal O_K\)，其归一化对数次数为 \(M\)，相对单位格的带符号对数体积为 \(-M\)。这个全局理想容许不同坏位有不同的 \(q_v\)，也容许理想类非平凡。[仓库的全纤维 \(Q,M\) 定义](../tmp/sheaf/xif/paper/Mzk1ULQPilotMagnitudeV2Actual.lean#L94)

这个结果还可用于核对两条容易混淆的源码读数。在选定的 \(F_v\)，写 \(e_v=v(p)\)。谱范数系数是 \(k/e_v\)。非零标签区域按 \(j^2\) 嵌套，含标签 1，因而它们并集的闭包就是闭的标签 1 坏位格。其对数体积为 \(-\lceil k/(2\ell)\rceil\log p/e_v\)。因 \(k\) 为正整数，\(\lceil k/(2\ell)\rceil\le k\)。乘回定义两边共用的非负权，就直接得到提问所贴的 F 侧不等式 \(-\mathrm{actualQPilotMagnitudeClassical}\le\mathrm{paperThetaHullLogRoot}\)。这里根本用不到两套全局权相等。[F 侧读数的定义](../tmp/sheaf/xif/paper/PaperLevelXiFTargetActual.lean#L57) · [非零标签并集](../tmp/sheaf/xif/paper/Mzk1URThetaHullNonzeroActual.lean#L208) · [标签 1 的体积](../tmp/sheaf/xif/paper/Mzk1URThetaHullLowerActual.lean#L195)

在选定的 \(K_w\) 上根已落在值群，连取整损失也消失。要比较不同的 \(F\)-lift，取域模上的共同 \(J=j(E)\)。Tate 展开给出 \(1/J=q+R(q)\)、\(|R(q)|\le|q|^2\)，故 \(-v(J)=k_v\)。若 \(b\) 是 \(v\) 下方的域模位，则 \(k_v/e_v=-v_b(J)/e_b\) 对所有 \(v\mid b\) 相同。将 \(f_v k_v\) 在整条纤维求和，用 \(\sum_{v\mid b} e(v/b)f(v/b)=[F:F_{\rm mod}]\)，恰好得到仓库的 \(\mathrm{thetaLamWeight}_b\) 乘这个共同系数。于是对单张量因子、非零标签取并的 K 侧对象，\(\mathrm{ksThetaHullLogRoot\_lam}=-M_{\rm paper,v2}\)。这个等式里取并与 IV 按 \(j\) 分别取体积再平均是两种运算。[共同 \(J\)](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L407) · [Tate 展开](../LeanFormal/IUT/Foundations/PAdicAnalytic/TateDeltaIntegral.lean#L274) · [余项估计](../LeanFormal/IUT/Foundations/PAdicAnalytic/TateEstimatesGeneral.lean#L57) · [K 侧参考体积](../tmp/sheaf/xif/paper/Mzk1URThetaKLowerCoreActual.lean#L222) · [K 侧权重](../tmp/sheaf/xif/paper/Mzk1URThetaKSideActual.lean#L202)

### 8.2 固定一条全局循环子群，实际保留哪些坏位

在 \(E[\ell](K)\) 固定任意一条直线 \(C\)，取生成元 \(P\)。令 \(B\) 为 \(C\) 的定义域，\(L\) 为无符号点 \(\{P,-P\}\) 的定义域。源的 Galois 像含 \(\mathrm{SL}_2(\mathbb F_\ell)\)。它在 \(\ell+1\) 条直线上传递，直线稳定子借助对角矩阵在其非零生成元模正负号上也传递。因此 \([B:F]=\ell+1\)，\(L/B\) 是 Galois 扩张，群为 \(H=\mathbb F_\ell^\times/\{\pm1\}\)，次数为 \(n=(\ell-1)/2\)。同一条 \(C\) 用于所有坏位。[实际表示与核域](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1011)

在 \(v\in S\)，Tate 商把 \(E[\ell]\) 映到 \(\mathbb Z/\ell\)，方法是令代表满足 \(z^\ell=q^a\)，取 \(a\bmod\ell\)。核是 \(\mu_\ell\)，局部 Galois 在商上作用平凡。除核外，每条直线都含**唯一**一个映到 1 的点，且这个点有唯一的代表 \(s\) 满足 \(s^\ell=q\)。唯一性来自同一类的代表之比是 \(q^\mathbb Z\)。于是这 \(\ell\) 条直线作为 Galois 集，与 \(X^\ell-q\) 的根集等变同构。\(\ell\nmid k\) 迫使 \(F_v(s)/F_v\) 的分歧指数被 \(\ell\) 整除，次数又至多为 \(\ell\)，故它全分歧且次数正好是 \(\ell\)。记它为 \(D_v\)。由 Galois 集的两个轨道得到实际局部分解
\[
 B\otimes_F F_v=F_v\times D_v,\qquad
 L\otimes_B D_v\simeq D_v^n .
\]
第二个等式来自那唯一的生成元被 \(G_{D_v}\) 固定，从而全部倍点都被固定。在另一条分支，标签来自 \(\mu_\ell/\{\pm1\}\)，只需非分歧扩张。以上分解还给出 \(K_w=F_v(\mu_\ell,s)\) 的同构描述，因为固定全部局部扭点等价于固定 \(\mu_\ell\) 和 \(s\)。故 \(K_w/F_v\) 的分歧指数为 \(\ell\)，是驯分歧。

取 \(D_v\) 这条分支，它在 \(B\) 的完整纤维中占局部次数权 \(\ell/(\ell+1)\)，对每一个坏位都是如此。因为 \(s^\ell=q\)、\(\sqrt q\in F_v\) 且 \(\gcd(2,\ell)=1\)，用 Bézout 恒等式将二者相乘取幂，可以在 \(D_v\) 中构造 \(r^{2\ell}=q\)。于是保留的 q 高度严格等于 \(Q_{\rm ram}=\ell Q/(\ell+1)\)，去掉的高度严格等于 \(Q/(\ell+1)\)。这项结论对任意大的 \(k_v\) 同样成立。

**同一高度还能由全局扭点坐标交叉核对。** 取三个有理 2-扭点，将横坐标归一化为 \(e_i\in\{0,1,\lambda\}\)。曲线容许是 Legendre 模型的二次扭曲，归一化的横坐标和以下比值在扭曲下相同。令 \(f(X)=\prod_i(X-e_i)\)，\(d_i=f'(e_i)\)。任选非零 \(\ell\)-扭点 \(P_*\)，设 \(x_j=x([j]P_*)\)。在每个坏位 \(v\) 取 \(|d_i|_v\) 最小的下标 \(i\) 和最大的下标 \(k\)。这只用三个全局已知数，平局时固定次序。则对每个 \(1\le j\le n\) 都有
\[
 \sum_{w\mid v}\frac{[K_w:F_v]}{[K:F]}
 \log\left|\frac{x_j-e_i}{4(x_j-e_k)}\right|_w
       =\tfrac14\log|q_v|_v .
\]
这给了每个真实标签一个全局坐标表达式，所用的图只有六张。以下是验证，不用预先指定每个 \(w\) 上的扭点生成元。

设 \(N=(\ell^2-1)/2\)，\(D_i=\prod_{U\in(E[\ell]\setminus0)/\pm}(x(U)-e_i)\)。令 \(R_\ell(X)\) 为乘 \(\ell\) 映射在横坐标直线上的有理函数。其在无穷远的首项为 \(X/\ell^2\)，因为形式参数被送到 \(\ell t+O(t^2)\)。在 \(T_i=(e_i,0)\) 附近，横坐标差具有二阶零点，故 \(R_\ell'(e_i)=\ell^2\)。\(R_\ell(X)-e_i\) 有一个在 \(e_i\) 的单零点和 \(N\) 个在 \(x(T_i+U)\) 的双零点；有限极点是 \(x(U)\) 的双极点。这些重数来自相同的局部参数计算，乘 \(\ell\) 在特征零不分歧。由零极点及无穷远首项将该有理函数写成因子乘积。在 \(e_i\) 取导数并代入弦切公式 \(x(T_i+U)-e_i=d_i/(x(U)-e_i)\)，得到 \(\ell^4D_i^4=d_i^{2N}\)。Galois 像在这 \(N\) 个横坐标上传递，于是所取比值若先不除以 4，其完整局部纤维平均为 \(\tfrac12\log|d_i/d_k|_v\)。

令 \(W=\log|d_k/d_i|_v\)。在坏位 \(|j(E)|>1\)，三种情形为 \(|\lambda|<1\)、\(|1-\lambda|<1\) 或 \(|\lambda|>1\)。逐一代入 \(j=2^8(1-\lambda+\lambda^2)^3/(\lambda^2(1-\lambda)^2)\) 得 \(\log|j|=8\log|2|_v+2W\)。故除以 4 后的平均正好是 \(-\frac14\log|j|\)。这一修正也覆盖 2 上方的坏位。[Legendre 的 \(j\) 函数](../tmp/sheaf/xif/paper/Mzk1G1QHeightActual.lean#L10)

### 8.3 用真实标签的 Galois 作用构造满秩格

在分裂的 \(D_v^n\) 上用 \(H\) 编号，令 \(a(h)\in\{1,\ldots,n\}\) 是无符号剩余类 \(h\) 的代表。定义 \(z=(r^{a(h)^2})_{h\in H}\)，取它在上节实际标签群作用下的全部 \(n\) 个平移为列。所得矩阵可写成
\[
 M_{t,h}=r^{a(th^{-1})^2}.
\]
每列只有对角元来自标签 1。除以 \(r\) 后对角元为 1，其余元属于 \(r^3\mathcal O_{D_v}\)，故 \(r^{-1}M\) 模极大理想为单位矩阵。其行列式为单位，逆矩阵也在整数环上。因此
\[
 M\mathcal O_{D_v}^{\,n}=r\,\mathcal O_{D_v}^{\,n}.
\]
这里有同一个矩阵的 \(n\) 个独立见证。只允许每个 \(v\) 自己的真实根，换根给各个原始坐标乘单位，同一论证的约化仍为可逆的对角阵。按每标签维数、局部次数和整个 \(B\) 的次数归一化，保留分支上这个实际格的带符号读数**正好是** \(-Q_{\rm ram}/(2\ell)\)。它直接给出一个在完整坏位和正比例区域上计算出来的弱中介。

还可精确说明其定义域。群 \(H\) 的置换保持直积 Haar 测度，也保持直积的实际整数单位对数格。上述满秩结论针对整数环格。一般局部域的单位对数格只先有 \(\mathbb Z_p\)-模结构，不能从矩阵元素整就声称矩阵保持该格。一个能直接检查的充分条件如下。取 \(\pi^a O\subset U=\log(O^\times)\subset\pi^{-b} O\)，若 \(3v_{D_v}(r)\ge a+b\)，则 \(r^{-1}M-I\) 把 \(U^n\) 送入 \(U^n\)。逆矩阵的几何级数也有这个性质，故在这个范围得到双向保格。这里采用对角元为 1 的上述定义。直积标签格与原 procession 的 \(j+1\) 槽张量各有自己的参考格。[仓库的单位对数格包围估计](../LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellSharpBounds.lean)

**把这个满秩见证送进原 R2 的实际结果。** 原 Step V 第 \(j\) 行先固定 \(j\)、槽元组及末槽的 \(\varpi_j\)，才对保对数格的像取 hull。上述列中的置换把槽中的标签从 \(j\) 改为 \(a(jh^{-1})\)。固定行的域自同构作用在 \(r^{j^2}\) 上只改变根或移到共轭位，并保留 \(j^2\) 这个指数。因此不能把这 \(n\) 列登记成该行的 \(n\) 个 Ind 像。若改在联合标签空间上允许全部置换，每个坐标确实都有指数 1 的元；此时逐行取所有像的外盒，也必须容纳这个元。若坚持每行保留原 \(j^2\) 上界，则必须用一个独立的**全局**比较控制整组列的带符号读数。重复应用逐行 Step V 定理不能产生该比较。[逐行定理的量词](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L814) · [标签求和的准确公式](../LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean#L35)

### 8.4 越过插值系数，直接算 different 与整格指数

在保留分支写 \(q=\pi_v^k u\)，\(u\) 为单位。取整数 \(a,b\) 使 \(ak+b\ell=1\)，设 \(\rho=s^a\pi_v^b\)。则 \(\rho^\ell=\pi_v u^a\) 是 Eisenstein 方程，\(\rho\) 是 \(D_v\) 的素元。\(1,\rho,\ldots,\rho^{\ell-1}\) 各项的赋值模 \(\ell\) 两两不同，故其线性组合整当且仅当每个系数整。于是 \(\mathcal O_{D_v}=\mathcal O_{F_v}[\rho]\)，different 由 \(\ell\rho^{\ell-1}\) 生成，阶为 \(\ell-1\)，独立于 \(k\)。相较之下，\(\mathcal O_{F_v}[s]\) 的幂基判别式为 \(\pm\ell^\ell q^{\ell-1}\)。利用两个整格的判别式相差其指数的平方，得到
\[
 \operatorname{length}_{\mathcal O_{F_v}}
 \bigl(\mathcal O_{D_v}/\mathcal O_{F_v}[s]\bigr)
       =\frac{(\ell-1)(k_v-1)}2 .
\]
这区分了大重数 \(k_v\) 所在的具体整格与真正的域 different。对标签的代数 \(L/B\)，两条分支都是非分歧的，relative different 在这些位的阶为**零**。更具体地，非分歧局部扩张的单位范数满射。剩余域的单位范数满射，随后逐层用
\(N(1+\pi^m x)\equiv1+\pi^m\operatorname{Tr}(\bar x)\pmod{\pi^{m+1}}\) 提升，因为剩余域迹满射。取极限再用 \(\log N=\operatorname{Tr}\log\)，便得到真实单位对数格的迹满射，连剩余特征整除剩余次数的情形也适用。

这也给出逆插值路线的实际判定。设 \(x_1,\ldots,x_n\) 为同一循环子群的无符号扭点横坐标。在坏位取整的 Legendre 尖点坐标，即在 \(\lambda,1-\lambda,1/\lambda\) 中取绝对值小于 1 的一个并相应变换 \(x\)。\(\ell\) 在这里是单位，奇数除法多项式的首项系数为 \(\ell\)，所以这些横坐标整。令 \(g(X)=\prod_i(X-x_i)\)。插值序 \(A=\mathcal O[X]/g\) 在分裂分支嵌入 \(\widetilde A=\mathcal O^n\)。评价矩阵的行列式为 \(V=\prod_{i<j}(x_j-x_i)\)。标准基的指数直接给出 \(\operatorname{length}(\widetilde A/A)=v(V)\)。迹配对下 \(\widetilde A^\vee=\widetilde A\)，\(A^\vee=g'(X)^{-1}A\)。后一公式可由 Lagrange 插值核验，\(\sum_i f(x_i)/g'(x_i)\) 等于 \(f\bmod g\) 的最高次系数。故 \(\operatorname{length}(A^\vee/\widetilde A)=v(V)\) 也完全相同。**在真实整数参考格里做逆插值，所需的分母恰是这笔指数。** 同时更换格与参考格会在相对体积中消去这笔数；只更换一侧就必须证明该侧确实使用了迹对偶序。这是撤下“直接除以 Vandermonde 就能接 IV”的理由，与某个标签或某个素数的数值无关。[奇数除法多项式的横坐标求值](../LeanFormal/IUT/ABCBridge/Galois/EllipticDivisionPolynomialEvaluation.lean#L119)

最后把局部式在全部坏位求和。令
\(\operatorname{Rad}_S=[F:\mathbb Q]^{-1}\sum_{v\in S}\log N\mathfrak p_v\)，\(\mathfrak d\) 表示基域中的相对判别式。实际得到
\[
 \frac{\log N(\mathfrak d_{B/F}|_S)}{[B:\mathbb Q]}
  =\frac{\ell-1}{\ell+1}\operatorname{Rad}_S,\qquad
 \frac{\log N(\mathfrak d_{K/F}|_S)}{[K:\mathbb Q]}
  =\left(1-\frac1\ell\right)\operatorname{Rad}_S .
\]
第二式用 \(K_w/F_v\) 的驯分歧指数 \(\ell\) 及全纤维的 \(\sum ef=[K:F]\)。特别地，现有 hlogdK 消费者所需的真实相对 different 已经有一个可独立交付的坏位部分。对没有纳入 \(S\) 的位仍须分别核算。[现有相对 different 消费者](../tmp/sheaf/xif/paper/Mzk1ULR2HlogdKTowerActual.lean#L31)

还有一个可以按全局对象交付的指数。将 \(B\) 的整数环在每个 \(v\in S\) 的完成替换成 \(\mathcal O_v\times\mathcal O_v[s_v]\)，其余完成保持原整数环。局部替换仅有有限处，将它们取逆像再相交就得到一个满秩全局序 \(\mathcal A\)。在完全分歧的 \(D_v/F_v\) 里，任何两个存在于 \(D_v\) 的根相差一个已在 \(F_v\) 中的 \(\ell\) 次单位根，因为这些单位根生成非分歧扩张，故选择不改变该序。逐位指数给出
\[
 \frac{\log[\mathcal O_B:\mathcal A]}{[B:\mathbb Q]}
   =\frac{\ell-1}{2(\ell+1)}
       \bigl(Q-\operatorname{Rad}_S\bigr).
\]
于是同一次构造里有两个可分别检验的量。域的判别式读出坏位的支撑，非极大序的指数读出超过一次的重数。将这个指数当常数将直接漏掉右端。

### 8.5 之后选哪一条路

若目的限于 ABC，我会保留 \(D_v\) 分支、满秩基和上述 different 计算。源条件之外没有新输入。形如
\[
 H_{\rm ram}\le \kappa(A-c_\ell Q_{\rm ram})-M_{\rm ram}+E
\]
的独立上界，代入已算出的 \(H_{\rm ram}=-M_{\rm ram}\) 后，给出
\(c_\ell Q\le A+c_\ell Q/(\ell+1)+E/\kappa\)，其中 \(\kappa=(\ell+1)/4\)，\(c_\ell=(1-12/\ell^2)/6\)。被删分支只花 \(c_\ell Q/(\ell+1)\)。但把左端数值代入也说明，**直接把这个上界当待填字段，已把高度问题原样放进字段**。[准确的 C3→C4 系数](../tmp/sheaf/xif/paper/Mzk1P6C3C4Actual.lean#L8)

一个不同的全局试验从实际商同源 \(E\to E/C\) 开始。它定义在同一个 \(B\) 上。其商横坐标可由
\(X_C(R)=x(R)+\sum_{P\in C\setminus\{0\}}(x(R+P)-x(P))\)
构造。连同纵坐标的同类求和，两函数都对 \(C\) 平移不变，并在零点给出归一化的 Vélu 商。固定 \(\omega\)，以 \(\phi^*\omega'=\omega\) 规定商的微分，取全局函数 \(u_C=\Delta(E/C,\omega')/\Delta(E,\omega)\)，它与 \(\omega\) 的共同缩放无关。第一笔该算的量是两条尖点分支各自的阶和正部。在标准 Tate 商上，核为 \(\mu_\ell\) 的同源由 \(z\mapsto z^\ell\) 给出，目标参数为 \(q^\ell\)；其余分支由细化周期格 \(q^\mathbb Z\subset s^\mathbb Z\) 给出，目标参数为 \(s\)。在 \(p\ne\ell\) 处，同源微分中的 \(\ell\) 是单位，故预期两处分别贡献 \((\ell-1)\log|q|\) 和 \((1/\ell-1)\log|q|\)。按两分支次数权相加为零，而正部保留 \((\ell-1)Q/(\ell+1)\)。验证实际 Vélu 方程的 \(j,\Delta\) 与这些 Tate 商匹配，要用坐标或实际代数同源，单有抽象点群等变不能替代这一步。然后必须对**同一全局函数**估计其坏位正部，显式带上好位、\(\ell\) 位和无穷位。仅有乘积公式会把正负两支抵消，给不出所需的高度上界。我会以能否从这条额外的全局关系压住重数作为继续这条弱路线的判据。

这个全局试验还有两个能先独立验证的环节。

* 对给定 \(\ell\)，\(\prod_C u_C\) 是一个仅依赖 \(\ell\) 的非零有理常数。证明可在通用 Legendre 参数 \(t\) 上进行。积对所有循环子群对称，故在 \(\mathbb Q(t)\) 中。于特征零每个 \(t\ne0,1,\infty\)，光滑曲线的 \(\ell\)-扭点局部无分歧，归一化的商同源有可逆微分，源与商的判别式皆可逆。因此该函数只可能在三个尖点有零极点。置换 2-扭点给出 \(t\mapsto1-t,\,1/t\)，两者都保留该函数，因为同源、微分缩放比和子群全集都自然。三个尖点的阶数于是相等，而主除子的总次数为零，故它是常数。这也解释了为什么仅用完整域范数无法压住坏位正部。
* Tate 横坐标的核 \(f(z)=z/(1-z)^2\) 可直接检查两支的 Vélu 求和。对 \(s^\ell=q\)，\(\sum_{a=0}^{\ell-1}\sum_{m\in\mathbb Z}f(q^m s^a z)=\sum_{b\in\mathbb Z}f(s^b z)\)。对根为单位根的分支，\(\sum_{\zeta^\ell=1}f(\zeta z)=\ell^2 f(z^\ell)\)，由几何级数求导可得。因而在避开极点的实际 Tate 级数上，Vélu 的横坐标和与目标 Tate 横坐标分别相差一个平移，或一个平移加 \(\ell^2\) 缩放。将它用于源的实际全局商，还要核对坐标点映射与所用子群、微分一致。这一核对和控制无穷位正部是两个独立步骤。[横坐标级数](../LeanFormal/IUT/Foundations/Geometry/TateCoordinateSeries.lean) · [周期性](../LeanFormal/IUT/Foundations/Geometry/TateCoordinatePeriodicity.lean#L54)

§8 建立了实际根、保留比例、标签置换给出的满秩格、单位对数的非分歧迹运输及坏位 different。商同源比的两类局部读数、无穷位费用与固定标签的替代映射已在[§9](#global-isogeny-trace)推导。

<a id="global-isogeny-trace"></a>
## 9. 从商同源构造同一个全局比较空间，并证明含 2 的循环子群估计

设 \(E/F\) 是数域上的椭圆曲线，\(J=j(E)\)，\(\ell\ge5\) 为素数。对所有有限位取离散赋值 \(v(\pi_v)=1\)，取绝对值延拓 \(|p|_v=p^{-1}\)。记 \(k_v=\max(0,-v(J))\)，若 \(J=0\) 则令所有 \(k_v=0\)。写 \(n_v=[F_v:\mathbb Q_p]/[F:\mathbb Q]\)，无穷位用通常的实、复次数权。以下两项算术构造在引入大像假设以前进行。

### 9.1 同一个代数数在所有有限位的完整读数

令 \(A\) 是所有 \(\ell+1\) 个循环子群的有限 étale \(F\)-代数，即对 Galois 轨道各取一个子群定义域并作直积。对每条线 \(C\)，用实际商同源 \(\phi_C:E\to E/C\) 定义
\[
 u_C=\frac{\Delta(E/C,\omega_C)}{\Delta(E,\omega)},\qquad
 \phi_C^*\omega_C=\omega .
\]
可取 §8.5 的 Vélu 坐标构造这个商。微分的共同缩放消去，所以这些数构成 \(u\in A^\times\)。下文允许 \(A\) 本身是域。

**先在通用曲线上消去对子群编号的依赖。** 令 \(P_\ell(J,Y)=\prod_C(Y-u_C)\)。在 Legendre 参数上各系数是有理函数。它们不随三个非零 2-扭点的排列或二次扭曲改变，故下降至 \(\mathbb Q(J)\)。这里六个重标记给出的不变域正是 \(\mathbb Q(J)\)，因为 Legendre 的 \(j\) 映射次数为六。特征零光滑纤维附近，\(\ell\)-扭点是有限 étale，商仍光滑，归一化微分处处非零。于是这些系数在每个有限 \(J\) 处正则，包括 \(0,1728\)，是 \(\mathbb Q[J]\) 中的多项式。

在复环面 \(\mathbb C/(\mathbb Z+\tau\mathbb Z)\) 上，商是把格换为指数为 \(\ell\) 的超格，商映射在 \(\mathbb C\) 上为恒等，归一化微分都是 \(dz\)。超格可列为 \(\ell^{-1}(\mathbb Z+\ell\tau\mathbb Z)\) 和 \(\mathbb Z+\mathbb Z\frac{\tau+a}{\ell}\)，\(0\le a<\ell\)。置 \(q=e^{2\pi i\tau}\)、\(s^\ell=q\)、\(\zeta=e^{2\pi i/\ell}\)，选 \(s=e^{2\pi i\tau/\ell}\)。由格判别式的权 12 得到同一多项式的根
\[
 u_*=\ell^{12}\Delta(q^\ell)/\Delta(q),\qquad
 u_a=\Delta(\zeta^a s)/\Delta(q),\qquad
 \Delta(z)=z\prod_{n\ge1}(1-z^n)^{24}.
\]
这个识别只需对上述具体复格族成立。用 \(\wp,\wp'\) 给出格的 Weierstrass 方程，格判别式正比于 \(E_4^3-E_6^2\)。其与 \(\Delta\) 的比是权零的模函数，在上半平面无极点，在尖点由两者的一次首项有有限非零极限，故是常数。常数在比值中消失。同样给出 \(J(q)=E_4(q)^3/\Delta(q)=q^{-1}+744+\cdots\)，其系数为整数，可用 \(E_4(q)=1+240\sum_{n\ge1}\sigma_3(n)q^n\) 直接看出。这样使用真实代数商的对称多项式，跳过了将某个抽象点群同构逐点识别为 Tate 坐标映射的困难。[仓库中的判别式无穷乘积与模变换](../.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L115)

每个对称系数的 Laurent 展开在 \(\mathbb Z[\zeta]((s))\) 中，在 \(s\mapsto\zeta s\) 与 \(\zeta\) 的共轭下不变，故在 \(\mathbb Z((q))\) 中。逐次减去最高极点项所对应的整数倍 \(J^i\)，即证 \(P_\ell\in\mathbb Z[J,Y]\)。将上述乘积逐因子相乘，\(\ell\nmid n\) 时有 \(\prod_a(1-\zeta^{an}s^n)=1-q^n\)，\(\ell\mid n\) 时为 \((1-q^{n/\ell})^\ell\)。约去全部因子，得到精确的 \(N_{A/F}u=\ell^{12}\)。

因此若有限位上 \(|J|\le1\)，每个 \(u_C\) 都整。若 \(|J|>1\)，对整数幂级数 \(1/J(q)=q+O(q^2)\) 作形式反演，系数仍整，在 \(1/J\) 处收敛。得到 \(q_v\in F_v\) 且 \(|q_v|=|J|^{-1}\)。上述**多项式恒等式**可以在局部代数闭包中代入它。恰有一个根满足
\[
 |u_*|_v=|\ell|_v^{12}|q_v|_v^{\ell-1},
 \qquad |u_a|_v=|q_v|_v^{-(1-1/\ell)}\quad(a\ne *).
 \tag{9.1}
\]
这里及下文 \(a\ne *\) 枚举其余 \(\ell\) 条线。唯一的小根对应唯一的线，局部 Galois 固定它，故 \(A_v=F_v\times A'_v\)。对于 §8 的合格坏位，唯一的惯性不动线是 \(\mu_\ell\)，于是这确实是原来分解中的那一支。公式 (9.1) 本身对 \(2\)、\(\ell\) 上方的极点也成立。特别地，所有线的局部正部平均严格等于 \((\ell-1)\log^+|J|_v/(\ell+1)\)。

### 9.2 用全局迹方程取出非规范分支

取 \(b=\ell^{12}u^{-1}\in A\)，任取正整数 \(m\)，定义
\[
 T_m(x)=\operatorname{Tr}_{A/F}(b^m x),\quad
 W_m=\ker T_m,\quad
 \mathscr W_m=W_m\cap\mathcal O_A,\quad
 I_m=T_m(\mathcal O_A).
\]
\(I_0=\operatorname{Tr}(\mathcal O_A)\)。这是实际的满射到一个分式理想，核是秩 \(\ell\) 的饱和格。在 \(|J|_v>1\) 的分解下，\(W_{m,v}\) 是 \(A'_v\) 上的图
\[
 y\longmapsto\bigl(-\operatorname{Tr}_{A'_v/F_v}((b'/b_*)^m y),y\bigr).
 \tag{9.2}
\]
对每个非规范坐标，\(|b_a/b_*|=|\ell|^{12}|q_v|^{\ell-1/\ell}\)。因此第一坐标的范数至多为这个数的 \(m\) 次方乘 \(\max_a|y_a|\)；非阿基米德迹求和不引入次数因子。取整后，投影 \(\mathscr W_{m,v}\to\mathcal O_{A'_v}\) 是同构。由此，一个在 \(F\) 上给定的线性空间同时实现了所有坏位的分支选择，即使 \(A\) 是域也适用。

这个全局选择的有限位代价可精确核算。令 \(\mathfrak q=\prod_{k_v>0}\mathfrak p_v^{k_v}\)。极点处 \(I_{0,v}=\mathcal O_v\)，\(I_{m,v}=b_*^m\mathcal O_v\)，阶为 \(-m(\ell-1)k_v\)。整 \(J\) 处 \(u,b\) 均整，后者也等于其余共轭根之积。若 \(p\ne\ell\)，二者均为单位，\(I_{m,v}=I_{0,v}\)，即使迹理想本身稍小也一样。若 \(p=\ell\)，由 \(\operatorname{Tr}(1)=\ell+1\) 为单位及 \(b^m u^m=\ell^{12m}\)，有 \(\ell^{12m}\mathcal O_v\subset I_{m,v}\subset\mathcal O_v\)。综上，
\[
 I_m I_0^{-1}=\mathfrak q^{-m(\ell-1)}\mathfrak c_m,\qquad
 \mathfrak c_m\mid(\ell)^{12m}.
 \tag{9.3}
\]
除以 \(m(\ell-1)[F:\mathbb Q]\) 后，附带的有限位对数次数至多 \(12\log\ell/(\ell-1)\)。这里使用整个迹理想。若只除以单个数 \(\operatorname{Tr}(b^m)\)，会人为引入该数在好位的零点。

若消费者只使用有限极点，可以把误差也完全清掉。由 (9.3) 逐位可见
\[
 (I_m+I_0)I_0^{-1}=\mathfrak q^{-m(\ell-1)}.
\]
左边来自全局映射 \((x,z)\mapsto T_m(x)+\operatorname{Tr}(z)\) 在 \(\mathcal O_A^2\) 上的像。新增的单位参考在整 \(J\) 处吸收余项，在有极点处自动包含于较大的迹理想中。

还有一个定义在 \(F\) 上的**精确线性投影**，无需除以可能在好位消失的 \(\operatorname{Tr}(b^m)\)：
\[
 P_m(x)=x-\frac{u^m}{(\ell+1)\ell^{12m}}\,T_m(x).
\]
因 \(T_m(u^m)=(\ell+1)\ell^{12m}\)，可直接验证 \(P_m^2=P_m\)、像为 \(W_m\)。在极点处，先送入向量 \((0,y)\)，然后把输出投到非规范分量。在分裂坐标上这个复合的矩阵是 \(I-d f^t/(\ell+1)\)，其中 \(d_a=u_a^m,\ f_a=u_a^{-m}\)。\(f^td=\ell\)，故行列式恰为 \(1/(\ell+1)\)，逆矩阵为 \(I+d f^t\)。各个 \(d_a f_h\) 是单位，因为所有非规范根的绝对值相同。于是对于正规化整数格，此复合在 \(p\nmid(\ell+1)\) 是整同构，在 \(p\mid(\ell+1)\) 的行列式代价也只由 \(\ell+1\) 决定，**与 \(k_v,m\) 无关**。这项估计用于纯横向输入；对任意含有大规范列的输入不能作同一估计。

### 9.3 固定原标签 \(j\)，检查真实张量单位对数格

在有实际根的合格坏位 \(v\) 上，把 (9.2) 通过 distinguished slot 换基到仓库的 \(p\)-进张量块 \(V=L_1\otimes_{\mathbb Q_p}\cdots\otimes L_t\)，其中该槽取能分裂 \(A\) 的实际 \(K_w\)，其余槽是同一有理素数上指定的完备化。令 \(R=\bigotimes_{\mathbb Z_p}\mathcal O_{L_i}\)，\(\widetilde R\) 为在域乘积分解中的正规化。仓库的 \(U\) 是各槽 \(\log(\mathcal O_{L_i}^\times)\) 的纯张量的 \(\mathbb Z_p\)-张成。估计中要保留这个定义。[实际单位对数张量格](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceUnscaledLogTensorLattice.lean#L189)

设 \([F:\mathbb Q]\le d\)，\(D=d\ell^4\)。对扭点域 \(K=F(E[\ell])\)，其次数小于 \(D\)，所以每槽的绝对分歧指数至多为 \(D\)。用 \(v_p(p)=1\)。单槽有 \(p^2\mathcal O_L\subset\log\mathcal O_L^\times\)，因为指数级数在这球内与对数互逆。反向用单位先取剩余域乘法群的阶次幂，再展开 \(\log(1+z)\)。第 \(a\) 项的赋值至少为 \(a/e-v_p(a)\ge-\log_2D\)。取纯张量并求和，便得 \(p^{2t}R\subset U\)，而 \(U\) 在正规化的每个坐标上的赋值不低于 \(-t\log_2D\)。

还需付出从正规化返回整张量序的代价。令 \(\delta_i=v_p(\mathfrak D_{L_i/\mathbb Q_p})\)，则 \(p^c\widetilde R\subset R\)，其中 \(c=\lceil\sum_i\delta_i\rceil\)。证明是 \(\widetilde R\subset R^\vee\)，因为整数元素乘积的迹整，而 \(R^\vee=\bigotimes_i\mathfrak D_i^{-1}\)。用各局部 different 生成元的纯张量乘回即可。各坐标上该生成元的赋值刚好是 \(\sum_i\delta_i\)。此外 \(\delta_i\le1+\log_2D\)。在最大非分歧子域上取素元的 Eisenstein 方程，各个非零导数项的离散赋值模 \(e_i\) 不同，故导数的赋值不超过首项给出的 \(v_p(e_i)+(e_i-1)/e_i\)。于是有可直接使用的夹逼
\[
 p^{A_0}\widetilde R\subset U\subset p^{-B_0}\widetilde R,\qquad
 A_0=2t+c,\quad B_0=\lceil t\log_2 D\rceil .
 \tag{9.4}
\]
[仓库的正规化与张量迹对偶包含](../LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualTensorInclusion.lean#L538)

写 \(c_j=j^2k_v/(2\ell e_v)\)、\(e_v=v(p)\)，\(1\le j\le(\ell-1)/2\)、\(t\le(\ell+1)/2\)。在分裂后的 \(\ell+1\) 份相同 \(V\) 上，(9.2) 的第一坐标是 \(-\sum_{a\ne *}(b_a/b_*)^m y_a\)。取
\[
 m\ \ge m_0=\lceil20d(1+\log_2D)\rceil .
\]
则 \(m(\ell-1/\ell)k_v/e_v\ge\lceil c_j\rceil+2(A_0+B_0)\)。只需代入 \(t\le(\ell+1)/2\)、\(k_v/e_v\ge1/d\)、\(c_j\le(\ell/8)k_v/e_v\)。特别地，对任意 \(y_a\in U\)，图的第一坐标都属于 \(\varpi_j U\)，其中 \(|\varpi_j|_v=p^{-c_j}\)。图上的线性变换是三角剪切，逆变换只需改一个符号，行列式为 1。

同一个计算可以在实际行估计的精度上做。设 \(H_a\) 是对 \(\varphi(\varpi_j\widetilde R)\) 取仓库定义的 holomorphic hull，其中 \(\varphi U\subset U\)。由 (9.4)，各 \(H_a\subseteq p^{-(A_0+B_0)}\widetilde R\)。在规范那份，如果允许恒等或至少一个满足 \(\varphi U=U\) 的作用，则 \(p^{\lceil c_j\rceil+A_0+B_0}\widetilde R\subset H_*\)；前一情形直接用恒等，后一情形用 (9.4) 及逆向保格。于是
\[
 (W_m\otimes_F V)\cap(H_*\times\prod_{a\ne *}H_a)
       \ \xrightarrow[\text{去掉第一坐标}]{\ \simeq\ }\ \prod_{a\ne *}H_a .
 \tag{9.5}
\]
左边是集合时这是带逆的投影；对整数参考格它是加法格同构，用相应格归一化的 Haar 体积也相同。若为弱路线取全部保格自同构，恒等自动在族中。(9.5) 没有要求作用与各槽局部域的标量乘法交换。它处理的是**在固定 \(j\) 上额外按循环子群组成的乘积**。原 III 来源里具体有哪些像及各像之间有没有关联，仍须按原对象判断。[Step V 的像族](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L668) · [可复用的上界](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L814)

还有一次换基指数必须单算。在 §8 的 \(p\ne\ell,\ \ell\nmid k_v\) 处，\(A'_v=D_v\) 为 \(\ell\) 次全驯分歧域，判别式阶为 \(\ell-1\)。设归一化后的某一张量域因子为 \(E'\)，含 distinguished slot 的 \(K_w\)。把 \(\mathscr W_{m,v}\) 真正整换基到 \(\mathcal O_{E'}\)，投影给出 \(\mathcal O_{D_v}\otimes_{\mathcal O_v}\mathcal O_{E'}\)。它在 \(\mathcal O_{E'}^\ell\) 中的长度恰为 \(e(E'/F_v)(\ell-1)/2\)，因为基变后判别式阶乘 \(e(E'/F_v)\)，而分裂乘积判别式为单位。每个因子除以 \(\ell[E':\mathbb Q_p]\) 后给出同一个对数修正 \((\ell-1)\log p/(2\ell e_v)\)。若改用全覆盖的次数 \(\ell+1\) 归一并在 \(S\) 上求和，此修正为 \((\ell-1)\operatorname{Rad}_S/(2(\ell+1))\)。这是从整换基放大到正规化时增加的体积；它只计坏位支撑，不含 \(k_v\)。

### 9.4 一个对所有 \(j\) 共用目标的实际映射

令 \(s=2(\ell-1)\)、\(a_j=j^2-1\)、\(n=(\ell-1)/2\)。取同一个 \(N\ge s\,m_0+n^2\)。乘以实际全局元素 \(u^{a_j}\) 给出
\[
 W_{N-a_j}\longrightarrow W_N,\qquad
 T_N(u^{a_j}x)=\ell^{12a_j}T_{N-a_j}(x).
 \tag{9.6}
\]
这是同一 \(F\) 上的线性同构；所有行落在一个目标 \(W_N\)。保留分支上对 \(r^{2\ell}=q_v\) 逐坐标有
\[
 |u_C^{a_j}|\,|r|^{s j^2}=|r|^s.
 \tag{9.7}
\]
于是对 distinguished slot 的主分式格，清分母后真的把第 \(j\) 行的 \(j^2\) 次幂送到一次幂，保留了 \(j\) 的身份。其余槽取正规化单位参考时，乘单位不影响格的等式。若在 (9.5) 中使用 \(s\) 倍的标量阶，\(s m_0\) 也足以覆盖相应精度。这里的 \(s\) 倍是清除标量的分母，不把整套原文的像族随意取幂。

可以精确检验 (9.6) 是否已经推出 R2。在坏位横向空间中，\(u^{a_j}\) 的每个坐标都放大 \(|q|^{-(1-1/\ell)a_j}\)。除回 \(s\)，参考格的对数读数也增加了 \((j^2-1)(-\log|q|)/(2\ell)\)。因此直接搬运旧行上界时，\(-j^2Q/(2\ell)\) 同时变为 \(-Q/(2\ell)\)。这种搬运不能再消费旧上界的二次主项。整 \(J\) 的好位上这个代价没有隐藏的大素数；\(I_N/I_{N-a_j}\) 相对于整格在 \(p\ne\ell\) 为单位，在 \(p=\ell\) 的额外阶至多 \(12a_jv(\ell)\)，由整的乘法 \(b^{a_j},u^{a_j}\) 双向夹住。由此 §8 留下的“能否固定标签构造转移”已有肯定答案；“原上界能否从它自动跟过来”也有精确的费用表。

**直接在未取幂的原 Step V 行上检验。** 固定同一个 \(p,j\)、槽元组、域分解 \(V=\prod_\alpha E_\alpha\) 和允许的非空作用族 \(\Phi_j\)。写 \(O=\prod_\alpha\mathcal O_{E_\alpha}\)，记 \(H_j(k)\) 为所有 \(\varphi(r^kO)\) 的乘积 holomorphic hull。这里 \(H_j(1)\) 仍使用第 \(j\) 行的槽和作用。原始的 \(j^2\) 次输入对应 \(H_j(j^2)\)，末槽若乘单位亦得同一输入格。令 \(d_j=(j^2-1)v_p(r)\)、\(h=\lfloor d_j\rfloor\)。所有域分量上 \(r\) 的绝对值相同，故
\[
 p^{\lceil d_j\rceil}rO\subseteq r^{j^2}O\subseteq p^h rO.
\]
每个作用与有理标量 \(p\) 交换，且坐标盒的最小性给出 \(\operatorname{HolHull}(pS)=p\operatorname{HolHull}(S)\)。所以这组双向包含对两个实际行盒原样成立。用同一个 Haar 和 \(\dim_{\mathbb Q_p}V\) 归一，行读数之差与 \(-d_j\log p\) 的偏差严格小于 \(\log p\)。当 \(d_j\) 为整数时偏差为零。此处没有把任意域单位与 \(\varphi\) 交换。

还可把最后的误差**精确算成有限商**。取 \(B=rO,\ L=p^{-h}r^{j^2}O\)，则 \(pB\subseteq L\subseteq B\)。令 \(J_\alpha\) 为所有 \(\operatorname{pr}_\alpha\varphi(B)\) 在 \(\mathcal O_{E_\alpha}\) 上生成的分式理想。因作用族保格，像有公共界；一个可逆作用就保证每个 \(J_\alpha\ne0\)。在 \(J_\alpha/pJ_\alpha\) 中取全部实际映射 \(B/pB\to J_\alpha/pJ_\alpha\) 对 \(L/pB\) 的像，再取 \(\mathcal O_{E_\alpha}/p\) 张成，记其逆像为 \(J'_\alpha\)。它恰是由 \(\operatorname{pr}_\alpha\varphi(L)\) 生成的理想，因为这些像生成的理想已含 \(pJ_\alpha\)。记 \(\nu\) 为同一参考下除以 \(\dim_{\mathbb Q_p}V\) 的对数体积，则原行满足
\[
 \nu(H_j(j^2))-\nu(H_j(1))
 =-\left(h+
 \frac{\sum_\alpha\dim_{\mathbb F_p}(J_\alpha/J'_\alpha)}
      {\dim_{\mathbb Q_p} V}\right)\log p.
\]
每个商被 \(p\) 消灭，总维数介于零与 \(\dim_{\mathbb Q_p}V\) 之间。即使 \(E_\alpha\) 分歧，也可以在这一级计算，此时需保留 \(\mathcal O_{E_\alpha}/p\) 的幂零元。固定作用族后，高重数的整数部分已精确提出。为取得实际数值，输入是源作用在这个有限商上的像和原参考格；用全部保格变换替代指定源族会改变结果。[原行的作用域](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L668)

**对 R1 下界的直接更正。** 在一个有界的有限局部域乘积中，给定非零坐标主理想盒 \(\prod_\alpha t_\alpha\mathcal O_{E_\alpha}\)，它包含在原像集 \(S\) 的 holomorphic hull 中，当且仅当每个 \(\alpha\) 各有一个 \(x_\alpha\in S\) 满足 \(|(x_\alpha)_\alpha|\ge |t_\alpha|\)。因为最小盒逐坐标取半径，而有界集合的非零离散绝对值有最大元。若某坐标达不到，包含 \(S\) 的那个坐标盒可再缩一个素元，立即违背包含。因而证明 R1 的一条内盒路线只需给每个坐标一条真实源箭头及该坐标的赋值。每个坐标的见证允许来自不同箭头；若一条箭头在所有坐标已达标，更只需一个点。这里纠正 §3 旧稿额外要求源中有满秩格的说法。该判据用于最小乘积盒；附件提到的模块将非零标签 hull 定义为并集的拓扑闭包，给这个闭包读数求下界时，可用其 label-one 区域定理。[已有的坐标极大值定理](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldProductHull.lean#L63) · [原乘积 hull](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldProductHull.lean#L137) · [附件所用闭包读数](../tmp/sheaf/xif/paper/Mzk1URThetaHullNonzeroActual.lean#L208)

### 9.5 对有理循环子群，给出包含素数 2 的独立高度定理

在标准基本域中写 \(y=\Im\tau\ge\sqrt3/2\)。无穷乘积给 \(\log|\Delta(\tau)|=-2\pi y+O(1)\)，而 \(\log^+|J(\tau)|=2\pi y+O(1)\)，二式的常数绝对。后一式由尖点首项和基本域截去尖点后的紧性得到。权 12 给出 \((\Im z)^6|\Delta(z)|\) 的模不变性和全局有界性。因此对 \(z=(\tau+a)/\ell\)，若 \(y/\ell<1\)，有 \(\log|\Delta(z)|\le6\log\ell+O(1)\)；若 \(y/\ell\ge1\)，无穷乘积直接给出 \(-2\pi y/\ell+O(1)\)。合并两种情形后可统一用 \(-2\pi y/\ell+6\log\ell+O(1)\) 作上界。规范根用 \(\Delta(\ell\tau)\) 直接算。故每一个实际子群都满足
\[
 \log^+|u_C|_\sigma\le\log^+|J|_\sigma+12\log\ell+C_0.
\]
用 \(\prod_Cu_C=\ell^{12}\) 从规范根反推其余 \(\ell\) 项的带符号和，还得到完整轨道的正部平均为 \((\ell-1)\log^+|J|_\sigma/(\ell+1)+O(\log(2\ell))\)。结合 (9.1)，此式在所有数域上给出相同的绝对高度标度。

现在只假定 \(C\) 是 \(F\)-有理的循环子群，因而 \(u_C\in F^\times\)。若 \(\ell\nmid k_v>0\)，大根的离散赋值是 \(-(\ell-1)k_v/\ell\)，不可能是整数。故**同一个全局 \(u_C\)** 在每一个这样的地方都必须取小根。令 \(H_0,H_1\) 分别为 \(\ell\nmid k_v\) 与 \(\ell\mid k_v>0\) 的有限极点高度，\(H_i\) 的每一项为 \(k_v\log N\mathfrak p_v/[F:\mathbb Q]\)。对 \(u_C\) 使用乘积公式，得到
\[
 (\ell-1)H_0\le(1-1/\ell)H_1+h_\infty(J)+12\log\ell+C_0 .
 \tag{9.8}
\]
尤其若所有极点的阶与 \(\ell\) 互素，则 \(H_1=0\)。在指定无穷位紧集上 \(h_\infty(J)\le B_K\)。若以 \(|\log|\lambda||,|\log|1-\lambda||\le c\) 描述紧集，可以取 \(B_K=8\log2+3\log3+10c\)。仓库对 Tripod 曲线已有 \(P.h=H_0+H_1\) 的全有限位字典。因此保留其原有 (P2) 量词，取 \(T_K=\max(0,B_K+C_0)/24\)，(9.8) 蕴含
\[
 ((\ell-2)/24)\,P.h\le 2\log\ell+T_K.
\]
这是源文件中 **CyclicBoundHyp** 的完整命题，包含 2 上方的贡献。仓库的 **cyclicBoundOdd** 已证明减去该贡献的版本，既有消费者也已能用它。这里补的是完整算术命题，另得 (9.8) 对部分不互素极点的加权结论。没有使用 III.3.12、P6、ABC 或大像。[完整接口和已有弱版](../Iut/Tripod/CurveFacts.lean#L414) · [已有奇素数版本](../Iut/Tripod/CyclicIsogeny.lean#L1175) · [高度字典](../Iut/Tripod/Height.lean#L603)

对全局比较空间本身也能把无穷位费用算完。用标准 Hermitian 范数使 \(A\otimes_\sigma\mathbb C=\mathbb C^{\ell+1}\) 的坐标正交，则 \(T_m\) 的算子范数为 \(\|(b_C^m)_C\|_2\)。规范坐标给出 \(\log|b_*|=2\pi(\ell-1)y+O(1)\)，这里的规范坐标指基本域中对应 \(\ell\tau\) 的复格商。对 \(z=(\tau+a)/\ell\) 取具有最大虚部的模变换 \(\gamma z\)。有 \(\Im z\le\Im(\gamma z)\le\ell y\)：其高度为 \(\ell y/|c\tau+ca+d'\ell|^2\)，基本域中每个非零格向量长度至少 1。用权 12 的变换律和 \(\Delta\) 在基本域中的估计，得到 \(-\log|\Delta(z)|\le2\pi\ell y+O(1)\)。这给出
\[
 \log\|(b_C^m)_C\|_2=2\pi m(\ell-1)y+O(m\log(2\ell)).
\]
故以诱导的商度量比较 \(I_m\) 与 \(I_0\)，其归一化算术次数再除以 \(m(\ell-1)\)，有限部分是 \(h_{\rm fin}(J)+O(\log(2\ell)/\ell)\)，无穷部分是各嵌入的 \(2\pi y\) 加同阶误差。总和与 \(h(J)\) 相差 \(O(1+\log(2\ell)/\ell)\)，常数独立于曲线、数域和 \(m\)。这里没有藏入自由选择的无穷位缩放。

### 9.6 让同一个 \(\ell\) 同时满足避除和大像

已有选素数定理给出 \(\sqrt H\) 到 \(10d\sqrt H\log(2dH)\) 的窗口。这里对实际数域的素理想进一步计数，可把上端缩成固定倍数，并留下正比例的可选素数。记 \(H=H_0+H_1=h_{\rm fin}(J)\)、\(X=\sqrt H\)、\([F:\mathbb Q]\le d\)，取充分大的 \(H\)，\(C_d=100(d+1)\)。[已有选素数定理](../Iut/Implication/PrimeSelection.lean#L213)

若有 \(m'\) 个位满足 \(k_v\ge X\)，则至少一半的位有 \(N\mathfrak p_v\ge m'/(2d)\)，因为每个有理素数上至多有 \(d\) 个位。由 \(\sum k_v\log N\mathfrak p_v=[F:\mathbb Q]H\) 得 \(m'\le4dX/\log X\)；具体地，在 \(m'\ge 2d\sqrt X\) 时用 \(\log(m'/(2d))\ge\frac12\log X\)，其余情形直接满足。同样 \(k_v\le dX^2/\log2<X^3\)。于是每个这样的位最多排除两个大于 \(X\) 的素因子，还可排除其本身的剩余特征。总共至多排除 \(12dX/\log X\) 个素数。由仓库已证的充分大时 \((2/3)t\le\vartheta(t)\le2t\)，区间 \((X,C_dX]\) 的素数个数至少为 \((C_d/3-1)X/\log X\)（取 \(X\ge C_d\)）。因而超过半数的素数同时满足所有极点 \(\ell\nmid k_v\)，以及 \(p_v=\ell\) 时 \(k_v<X\)。[仓库的双边 Chebyshev 定理](../LeanFormal/IUT/IUTIV/Estimates/Section2.lean#L393)

对这些 \(\ell\)，若无穷位在固定紧集，(9.8) 对充分大的 \(H\) 排除任何 \(F\)-有理循环子群。另取任一极点，(9.1) 中大根赋值的分母为 \(\ell\)，而这些数都属于 \(F(E[\ell])\) 的局部完备化，所以 \(\ell\) 整除某个分歧指数，从而整除实际表示像的阶。Cauchy 定理给出阶为 \(\ell\) 的元素，在二维特征 \(\ell\) 中这是非平凡幺幂剪切。没有不变直线，故某个共轭剪切的固定线与第一个不同。以两条线为基，分别取幂可得所有上、下初等矩阵，因此实际表示像包含 \(\mathrm{SL}_2(\mathbb F_\ell)\)。这里可直接复用仓库的群论后半段；证明不接收已经含大像字段的 SourceClauseC。若随后作次数 \(<\ell\) 的扩张，大像仍在，因为 \(\mathrm{SL}_2\) 作用到这个数目的陪集时，每个阶 \(\ell\) 的剪切都映到恒等。[群论供体](../Iut/Tripod/SL2Generation.lean#L156) · [原消费者](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1023) · [原 Tripod 塔的次数上界](../Iut/Tripod/CurveFacts.lean#L328)

在这些素数处删去 \(p=\ell\) 的全部位损失至多 \(X\log\ell\)，因为 \(\sum_{v\mid\ell} f_v\le[F:\mathbb Q]\)。再按 §8 舍去规范分支，损失至多 \(H/(\ell+1)\le X\)。若源还要求删去 2，上方的 \(H_2\) 需按原 \(K\) 的 2 进紧集计入。因此这三种具体删位的总损失至多 \(X(\log(C_dX)+1)+H_2\)。其他来源条件不由此自动生成。

§9.2–9.4 得到全局固定行转移、参考格指数以及原行缺陷的精确有限商公式。§9.5–9.6 证明含 2 的循环子群高度估计和加强的选素数窗口。原 III.3.12 尚须将允许的源箭头逐坐标代入，并在同一参考下独立保住 IV 的二次负项。以上为自然语言证明，四项 Lean 验收均未运行。

<a id="strength-and-determinant"></a>
## 10. 能交付多强的结论，以及怎样争取原强度

### 10.1 把固定行转移的费用一直算到高度系数

令 \(n=(\ell-1)/2\)、\(a_j=j^2-1\)、\(\kappa=(\ell+1)/4\)、\(c_\ell=1/6-2/\ell^2\)。\(Q=\sum_v q_v>0\) 是指定坏位上的未开根 q 高度，每个 \(q_v\) 已含原来的局部次数权及 \(\log p\)。若每一行和全部 q 支集都用 §9.4 的标量转移来取得一次幂内格，则相对于原二次上界增加的线性主项为
\[
 E_{\rm all}=\frac{Q}{n}\sum_{j=1}^n\frac{a_j}{2\ell}
 =\left(\frac{\ell+1}{24}-\frac1{2\ell}\right)Q,\qquad
 G_\ell=\frac{E_{\rm all}}{\kappa Q}=\frac16-\frac{2}{\ell(\ell+1)}.
\]
在精确 Step V 盒中，原来是 \(-(\ell+1)Q/24\)，搬完恰好是 \(-Q/(2\ell)\)，与所需下界 \(-Q/(2\ell)\) 相消。若使用仓库略放松的 C4 上界，则 \(c_\ell-G_\ell=-2/(\ell^2(\ell+1))\)。即使把取整和其余接线费用全取零，这种搬运也没有给出正的高度系数。[Step V 的精确平均](../LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean#L54) · [C3→C4 所用系数](../tmp/sheaf/xif/paper/Mzk1P6C3C4Actual.lean#L9)

可以量出弱中介允许损失的范围。令 \(f_{jv}\in[0,1]\) 表示在固定行、固定末槽 \(v\) 后，按原元组权重计算、仍须付出完整转移费的比例。假定其余部分另外取得比较，且把除这笔线性运输费以外的总亏损记为 \(E_0\)。设
\[
 \rho=\frac{\sum_v(q_v/Q)\sum_j a_j f_{jv}}{\sum_j a_j}.
\]
则算术出口是 \((c_\ell-\rho G_\ell)Q\le A_{\rm IV}+E_0/\kappa\)。若使用原 \(\ell+1\) 次覆盖的归一化，只有一条分支在每个坏位付费时，\(\rho=1/(\ell+1)\)。若在其余 \(\ell\) 条分支都付费，即使唯一的特殊分支另有免费比较，也已有 \(\rho=\ell/(\ell+1)\)，保留下的有效系数只有 \(1/(6(\ell+1))+O(\ell^{-3})\)。两种计数都假定分支来自 §8 的同一覆盖和原曲线的 q 质量。

若每个位至多有 \(m\) 行付费，则 \(\rho\le 6m(n+1)/(n(2n+5))\le3m/n\)。若只有前 \(m\) 行付费，则上界是 \(m(m-1)(2m+5)/(n(n-1)(2n+5))\)。因为 \(\sum_{j=1}^n(j^2-1)=n(n-1)(2n+5)/6\)。§9.4 每个坏末槽的取整余量另至多 \(\log p\)。原末槽边际权 \(w_v=e_v f_v^{\rm res}/[F:\mathbb Q]\)，而 \(q_v=w_vk_v\log p/e_v\) 且 \(k_v\ge1\)，所以该项平均求和后至多 \(dQ\)，其中 \(e_v\le d\) 是权重所在基域的次数界。除以 \(\kappa\) 后是 \(O_d(Q/\ell)\)。

因此若 \(\ell\to\infty\)，未补回的 \(\rho\) 一致趋零，且其余算术估计给出 \(Q=H-o(H)\)、\(A_{\rm IV}\le(1+o(1))(D+N)+o(H)+O(1)\)、\(E_0/\kappa=o(H)+O(1)\)，则可保住任意 \(1+\eta\) 的 **D1 高度系数**。这里 \(H\) 取全有限 j 高度，在固定紧集 \(H/6\) 与 Legendre 高度相差有界。具体地，移项时 \(H/6\) 前损失的是 \(12/\ell^2+\rho(1-12/(\ell(\ell+1)))\) 加其余相对误差。选阈值使最后的 \(\alpha+(1+\eta)\beta\le\eta\)，即可应用 §5 的除法。若 \(\rho\to r\in(0,1)\) 而其余项可忽略，此计算给出的 D1 乘数趋于 \(1/(1-r)\)。R4–R7 的高度运输另有自己的输入。对原 III.3.12，量词固定 \(T,\ell\)，故跨曲线趋零只适用于这里的高度路线。

### 10.2 在实际对数格上补回遗漏的商方向

沿用 §9 的循环子群代数 \(A\)、判别式比 \(u\)、\(b=\ell^{12}/u\)、\(T_m(x)=\operatorname{Tr}(b^m x)\)、\(I_m=T_m(\mathcal O_A)\) 和 \(\mathscr W_m=\ker T_m\cap\mathcal O_A\)。新的比较来自实际正合列
\[
 0\longrightarrow\mathscr W_m\longrightarrow\mathcal O_A
      \xrightarrow{\,T_m\,} I_m\longrightarrow0,\qquad
 \det\mathscr W_m\otimes I_m\simeq\det\mathcal O_A .
 \tag{10.1}
\]
在每个离散赋值环上把商理想的一个生成元提升成最后一个基向量，即证这个整行列式同构。它在域上与 \(T_m\) 收缩顶次外幂的公式一致，因而可粘合。乘 \(u^a\) 在全代数上的行列式为 \(N(u^a)=\ell^{12a}\)，在两条迹商线之间由 \(T_{m+a}(u^a x)=\ell^{12a}T_m(x)\) 得到相同的标量。因此在 \(T_m,T_{m+a}\) 给出的域上行列式识别中，核之间的映射行列式系数为 1。整数格和无穷位度量的变化仍由 (10.1) 给出。

固定 \(J=j(E)\) 的一个极点。取 §9.1 的唯一特殊线 \(*\)，先看 \(A_v=F_v\times A'_v\)。对整的 \(x\) 和 \(m\ge1\)，
\[
 b_*^{-m}T_m(x)
 =x_*+\operatorname{Tr}_{A'_v/F_v}((b'/b_*)^m x')
 \equiv x_*\pmod{\mathfrak p_v}.
 \tag{10.2}
\]
各共轭的 \(|b_a/b_*|<1\) 给出同余。于是在这个一维商中，整源集合的迹生成 \(I_{m,v}=b_*^m\mathcal O_v\)，当且仅当其中有一个 \(x_*\) 是单位。全局常数 \(1_A\) 同时在每个极点达到该阶，即使单个 \(\operatorname{Tr}(b^m)\) 在其他地方有零点。

还可给出基域上明确的两个生成元。置 \(\tau_m=T_m(1_A)\)。由 §9.1，\(b_C=\prod_{C'\ne C}u_{C'}\)，故 \(\tau_m=\sum_C b_C^m\) 是那些根的整系数对称多项式，进而 \(\tau_m\in\mathbb Z[J]\)。在尖点只有 \(b_*^m\) 给出 \(q^{-m(\ell-1)}\) 的首项，其系数为 1，故 \(\tau_m(J)\) 是次数恰为 \(m(\ell-1)\) 的首一多项式。于是全基域有精确的分式理想等式
\[
       (1,\tau_m(J))=\mathfrak q^{-m(\ell-1)},\qquad
       \mathfrak q=\prod_{v:k_v>0}\mathfrak p_v^{k_v}.
\]
在任何有限极点，\(\tau_m\ne0\) 且 \(x\mapsto T_m(x)/\tau_m\) 是整的线性投影到对角基域，因而 \(\mathcal O_{A_v}=\mathscr W_{m,v}\oplus\mathcal O_v\,1_A\)。这里使用的两个生成元在同一个 \(F\) 中，不需要极点理想是主理想。 基本的 \((1,J)\) 已经记录极点理想。此处增加的内容，是给出由同一个迹映射作用于 \(1_A\) 产生的代表，并证明它在每个极点同时实现整分裂。

在原 Step V 张量块 \(V\) 的指定槽过能分裂 \(A\) 的 \(K_w\) 后，令 \(U\subset V\) 为实际未缩放的单位对数张量格。取基域的对角映射 \(\Delta y=(y,\ldots,y)\)。对所有充分大的 \(m\)，有实际的**等格公式**
\[
    (T_m\otimes1)(\Delta U)=b_*^m U. \tag{10.3}
\]
证明中只用 §9.3 的格夹逼。令 \(\delta_m=\sum_{a\ne *}(b_a/b_*)^m\)，则 \(b_*^{-m}(T_m\otimes1)\Delta=1+\delta_m\)。在每个分解因子上 \(\delta_m\to0\)。由 \(p^{A_0}\widetilde R\subset U\subset p^{-B_0}\widetilde R\)，对充分大的 \(m\) 有 \(\delta_m U\subset pU\)。故 \(1+\delta_m\) 及其几何级数逆都保 \(U\)。这是同一个真实格的等式。若从给定的源集合来生成整个高秩 \(U\)，所需检验是其归一化像张成 \(U/pU\)。一条一维商线只需 (10.2) 的一个单位见证。若只求乘积 hull 的内盒，则仍可用 §9.4 每个域分量分别达标的判据。[实际格的定义](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceUnscaledLogTensorLattice.lean#L189)

取 \(s=2(\ell-1)\)、\(a=j^2-1\)。用横向 \(\ell\) 个坐标的维数及清分母因子 \(s\) 归一，逆商线 \(I_m I_{m+a}^{-1}\) 在极点的带符号读数恰是
\[
   -\frac{a(\ell-1)}{\ell s}(-\log|q_v|)
   =-\frac{j^2-1}{2\ell}(-\log|q_v|).
\]
它逐行精确抵消 §9.4 横向格的那笔放大费。若按全覆盖归一，横向费和商线费都再乘 \(\ell/(\ell+1)\)，仍恰好相消。映射本身在商上的标量还有 \(\ell^{12a}\)，其全局主算术次数为零，分别比较 \(\ell\) 上方和无穷位时应保留这一项。由此明确了为何一条特殊线值得追，它承载的是其余 \(\ell\) 个方向的行列式总量。

也能直接检验一种可能接法。在同一张量块中 \((T_m\otimes1)(\Delta(r^{j^2}U))=b_*^m r^{j^2}U\)，而一次幂输入得到 \(b_*^m rU\)。若 q、Θ 两端只同时增添完全相同的辅助商线，原来的差额完整保留。这决定了应检查 III 的哪一部分。沿 1 列 log-Kummer 的单位部分追踪 \(\Delta U\)，沿 0 列实际允许的 Θ 输出及 1 列运输追踪其行列式。要辨明同一算术线是否在原文规定的一侧以 (10.1) 的逆商方向出现，并且原 q 读数仍是 \(-M\)。在有限坏位先求归一化的特殊坐标模 \(\mathfrak p_v\)，或对全格求模 \(p\) 的秩。单纯取已缩放 Θ 区域的对角像会保留上式的 \(r^{j^2}\)。原文的 xi-d 至 xi-f 正是在两个表示间比较行列式和单位部分。仓库中由上横箭头及左右 Kummer 箭头构造下横箭头的定理可复用，但它不认证独立给出的原 Θ 输出等于该下横箭头。[原文两列的比较](IUT-TEXT/III.txt#L10827) · [仓库的 Kummer 方块](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceKummerEvaluationSquareExtension.lean#L22)

### 10.3 固定曲线与素数，把辅助行列式的全局误差算到底

给 \(A\) 在每个复嵌入上的分裂坐标赋标准 Hermitian 范数，给 \(I_m\) 诱导商度量。这是本构造选定的辅助度量。对每个位 \(v\) 记 \(B_v=\max_C|b_C|_v\)，以及 \(h_b=\sum_v n_v\log B_v\)，其中 \(n_v\) 是通常的绝对次数权。共轭坐标整体置换，所以最大值与所选局部嵌入无关。以 \(\widehat d(I_m)\) 表示用此度量定义的算术次数除以 \([F:\mathbb Q]\)。有限部分对 I 取 \(-\log N(I)/[F:\mathbb Q]\)。取固定 \(N>\max_j a_j\)。对同一条曲线、同一个 \(\ell\)，存在任意大的正整数 \(k\)，使所有行同时满足
\[
 -\frac{\log(\ell+1)}{2k}\ \le\
 \frac{\widehat d(I_{kN})-\widehat d(I_{k(N-a_j)})}{k}
       -a_j h_b\ \le\ 0. \tag{10.4}
\]

有限位可做到严格等式。局部分解 \(A_v=\prod_i L_i\)，写 \(e_i=e(L_i/F_v)\)、\(d_i=v_i(\mathfrak D_{L_i/F_v})\)、\(b_i\) 为对应分量。由迹对偶，
\[
 v(I_t)=\min_i\left\lfloor\frac{t v_i(b_i)+d_i}{e_i}\right\rfloor .
\]
确实，\(\operatorname{Tr}(\mathfrak p_i^z)\subseteq\mathfrak p_v^h\) 等价于 \(\mathfrak p_i^{z-e_i h}\subseteq\mathfrak D_i^{-1}\)，因为 \(\mathfrak p_i^z\) 是整数环的理想。取允许的最大整数 \(h\)，再对各因子的迹理想求和即得。只有有限多个位的 \(b_i\) 非单位或 \(A_v\) 分歧。取 \(k\) 为这些位各 \(e_i\) 的公倍数并充分大。在 \(t=kN\) 和 \(k(N-a_j)\) 处，最小值都取在 \(v_i(b_i)/e_i\) 最小的因子上，次级常数均为这些因子中 \(\lfloor d_i/e_i\rfloor\) 的最小值。相减后常数完全抵消。

在无穷位，商线中 \(1\) 的范数为 \(1/\|(b_C^t)_C\|_2\)。其对数次数贡献可写成 \(t\log B_v+\eta_t\)，其中 \(\eta_t=\frac12\log\sum_C(|b_C|/B_v)^{2t}\) 单调递减，介于零与 \(\frac12\log(\ell+1)\) 之间。这给出 (10.4) 的符号和常数，也解释为什么有限多个行可以共用 \(k\)。取幂与极限的对象是独立构造的辅助算术线，原 Θ 的允许像和原 q 都固定。其读数能否按原文方向进入该固定的 Θ，仍需 §10.2 的来源映射。

在全部有限极点，\(\log B_v=(\ell-1)\log^+|J|_v\)。在整 \(J\) 的有限位，除 \(\ell\) 上方外 \(B_v=1\)。在 \(\ell\) 上方，有 \(|\ell|_v^{12\ell/(\ell+1)}\le B_v\le1\)，因为 \(b\) 整且 \(\prod_C b_C=\ell^{12\ell}\)。结合 §9.5 的无穷位估计，在固定无穷位紧集 \(K\) 上，
\[
 \frac{h_b}{\ell-1}=H+O_K(1+\log(2\ell)/\ell),\qquad H=h_{\rm fin}(J).
\]
于是逆商线给出的补偿，在横向维数、清分母次数、行平均及 \(\kappa\) 都按 §10.1 除回后，其大小是 \(G_\ell H+O_K(1+\log(2\ell)/\ell)\)。若原文只选了部分坏位，必须另计 \(G_\ell(H-Q)\)。这给弱高度路线一个有实际来源的候选补偿和明确的高度预算。对精确 III，(10.4) 的余项可在固定输入上趋零，但 \(h_b/(\ell-1)-Q\) 包含的无穷位度量与支集差仍在。只有用原读数核对其标定或证明有利的单向比较，才能在原端点取这个极限。

**基域上的射影实现。** 若交付对象要求全部坐标属于 \(F\)，还能消掉单个 \(\tau_m\) 在无穷位可能出现的抵消。取 \(t=\ell+1,\ D=\operatorname{lcm}(1,\ldots,t)\)，构造真实点
\[
 Z_m=[1:\tau_m^{D}:\tau_{2m}^{D/2}:\cdots:\tau_{tm}^{D/t}]
       \ \in\mathbb P^{t}(F).
\]
以标准坐标最大值定义绝对对数高度。每个有限位的 \(h(Z_m)/(mD)\) 局部项恰为 \((\ell-1)\log^+|J|_v\)（乘通常局部权）。在一个无穷位，置 \(z_C=b_C^m,\ P=\max_{1\le h\le t}|\sum_C z_C^h|^{1/h}\)。Newton 恒等式递推给 \(|e_i(z)|\le P^i\)，因为递推式右边的 \(i\) 项各至多为 \(P^i\)，再除以 \(i\)。代入以 \(z_C\) 为根的首一多项式，几何级数估计给 \(\max_C|z_C|\le2P\)。反向由三角不等式 \(P\le t\max_C|z_C|\)。由于 \(\prod_C b_C=\ell^{12\ell}\)，无穷位 \(B_v>1\)。所以
\[
 -\frac{\log2}{m}\le \frac{h(Z_m)}{mD}
 -\left((\ell-1)H+\sum_{v\mid\infty}n_v\log B_v\right)
 \le\frac{\log(\ell+1)}{m}.
\]
这里有限位费用完全精确，无穷位误差甚至与曲线和数域无关。括号中的数与 (10.4) 的 \(h_b\) 可差整 \(J\) 的 \(\ell\)-进项，因为 \(Z_m\) 有坐标 1。这个射影点以 \(J\) 为唯一曲线参数，适合交付为独立的全局 q 高度实现。它本身不记录 III 的两条 Kummer 箭头。

### 10.4 一个现在就能单独交付的大像定理

设 \(H=h_{\rm fin}(J)>0\)、\([F:\mathbb Q]\le d\)、\(h_\infty(J)\le B_1 H+B_0\)，其中 \(B_0,B_1\ge0\) 固定。当 \(H\) 对 \(d,B_0,B_1\) 充分大时，**全部素数 \(\ell>\sqrt H\) 中，至多两个满足 \(\bar\rho_{E,\ell}(G_F)\not\supseteq\mathrm{SL}_2(\mathbb F_\ell)\)**。在 \(\ell>\sqrt{dH/\log2}\) 的范围，至多一个。此命题无需先排除所有极点阶的素因子，也不以初始 Θ-data 的大像为输入。

证明。用 \(\mu(v)=k_v\log N\mathfrak p_v/([F:\mathbb Q]H)\) 作为所有极点上的概率权。对某个例外 \(\ell\)，若有不变直线，则由 (9.8) 解出
\[
 \mu\{v:\ell\nmid k_v\}\le
 \delta_\ell:=\frac1{\ell+1}
 +\frac{\ell}{\ell^2-1}\frac{B_1H+B_0+12\log\ell+C_0}{H},
\]
其中可增大 \(C_0\) 使之非负。若无不变直线，只要有一个 \(\ell\nmid k_v\) 的极点，(9.1) 就在实际扭点域给出离散赋值分母 \(\ell\)，所以 \(\ell\) 整除像的阶。二维素域上的阶 \(\ell\) 元素是剪切，无不变直线时可取固定直线不同的两个共轭，从而生成 \(\mathrm{SL}_2\)。因此对例外素数，上述概率上界在两种情形都成立。[仓库的剪切生成定理](../Iut/Tripod/SL2Generation.lean#L156)

对 \(\ell>\sqrt H\)，有 \(\sup\delta_\ell\to0\)，因为 \((\log x)/x\) 在这里递减。若有三个不同例外素数，充分大时三份 \(\delta_\ell\) 的和小于 1，故至少有一个极点的 \(k_v\) 同时被三个素数整除。但每个 \(k_v\le dH/\log2\)，而三者乘积 \(>H^{3/2}\)，矛盾。对两个都超过 \(\sqrt{dH/\log2}\) 的例外同理。更一般地，对任意有限例外素数集 \(\mathcal B\)（素数至少为 5），逐位使用 \(\sum_{\ell\mid k_v}\log\ell\le\log k_v\) 并取平均，得 \(\sum_{\ell\in\mathcal B}(1-\delta_\ell)\log\ell\le\log(dH/\log2)\)。

**直接用于任意本原正整数三元组。** 设 \(a+b=c,\ \gcd(a,b)=1\)，取 Frey 曲线 \(y^2=x(x-a)(x+b)\)。其不变量为 \(J=2^8(a^2+ab+b^2)^3/(a^2b^2c^2)\)。分子中的 \(a^2+ab+b^2\) 与 \(abc\) 互素，且为奇数。[仓库中实际 Frey 模型的 j 公式](../LeanFormal/IUT/ABCBridge/Geometry/ABCModelHeightComparison.lean#L80)

由此得到
\[
 H=2\log(abc)-\min\{2v_2(abc),8\}\log2,\qquad
 4\log c-10\log2\le H\le6\log c.
\]
这里用了 \(ab\ge c-1\ge c/2\)。又有 \(3c^2/4\le a^2+ab+b^2\le c^2\) 及 \(ab\le c^2/4\)，故 \(J\ge1728\)，并且
\[
 h_\infty(J)=\log J\le 8\log2+6\log c-2\log(abc)
              \le \tfrac12 H+15\log2.
\]
所以无需把三元组的无穷位另限在紧集。对所有充分大的 \(c\)，在**全部素数 \(\ell>\sqrt{6\log c}\)** 中，至多两个使这条 Frey 曲线的 mod-\(\ell\) 像未包含 \(\mathrm{SL}_2(\mathbb F_\ell)\)。更一般的数域命题与这个直接推论均由上面的商同源高度估计导出。这个放宽适用于大像定理，§10.3 将无穷位代价估为 \(O_K(1)\) 仍然使用固定紧集。

这个推论可以进入实际辅助数域。三元组给出的曲线有全有理 2-扭点。固定相应的有理 Legendre 模型后，IV 使用的 \(F=\mathbb Q(\sqrt{-1},E[3],E[5])\) 次数至多 \(2\cdot48\cdot480=46080\)。若 \(\ell>[F:\mathbb Q]\)，则从 \(\mathbb Q\) 限制到 \(F\) 仍有大像。确实，设 \(G\) 为原像，\(G'\) 为限制像，\([G:G']\le[F:\mathbb Q]<\ell\)。\(\mathrm{SL}_2\) 在 \(G/G'\) 上的置换作用杀掉每个阶 \(\ell\) 的剪切，因此整个 \(\mathrm{SL}_2\) 固定单位陪集。又有 \(k_w=e(w/p)k_p\)，在该范围 \(\ell\mid k_w\) 当且仅当 \(\ell\mid k_p\)。将 §9.6 的全极点避除计数用于 \(\mathbb Q\)，并删去至多两个大像例外，即得一个固定倍数 \(\sqrt{\log c}\) 的窗口内同时满足全极点避除和实际 \(F\) 上大像的素数。这完成了这批 Frey 输入的选素数与大像两项。一般三元组的 2 进 q 贡献可随 \(c\) 增长，其他原文条件仍按各自的条件使用。[IV 指定的辅助数域](IUT-TEXT/IV.txt#L1284) · [原来的大像消费字段](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean#L1023)

若目标只要求保留 \(1-o(1)\) 的 q 高度，可把大像和选择范围同时加强。设 \(L=(\log(2+dH))^2\)。记 \(D_\ell=\mu\{\ell\mid k_v\}\)、\(P_\ell=\mu\{v\mid\ell\}\)。对 \(L<\ell\le6L\)，有 \(\sum D_\ell\log\ell\le\log(dH/\log2)\)，且 \(\sum P_\ell\log\ell\le\log(6L)\)。仓库的双边 Chebyshev 界给同一区间 \(\sum\log\ell\ge2L\)。所以至少一半的素数对数权所对应的 \(\ell\) 满足 \(D_\ell+P_\ell=O_d(1/\log H)\)。上述大像例外判据又表明这些 \(\ell\) 对充分大的 \(H\) 全有大像。被省去的 q 高度至多 \(O_d(H/\log H)\) 加 2 上方的实际贡献。并且省去的 \(\ell\mid k_v\) 极点之约化支集次数至多 \(HD_\ell/\ell\)，因为每个这样的 \(k_v\ge\ell\)。这是弱路线的“几乎全部 q 质量”结论。[内部 Chebyshev 界](../LeanFormal/IUT/IUTIV/Estimates/Section2.lean#L393)

严格的 IV 使用范围要区分。I 的定义允许在标作 good 的位置有乘法退化，IV 1.10 增加了 \(2\ell\) 以外这些位置确有好约化的条件，证明内用它推出 (D0) 的非分歧性。故这个较小素数窗口不能直接套原 IV 1.10。要保留这一选位要求，§9.6 的 \(\sqrt H\) 窗口允许把全部 \(2\ell\) 以外的乘法位列入，域塔和其余要求另行核对。若走弱路线，在被省去的乘法位 \(p\ne\ell\) 处，经非分歧二次扩张得到分裂 Tate 曲线时，\(\ell\mid v(q)\) 使 \(q^{1/\ell}\) 落在最大非分歧扩张内，因为单位部分可由 Hensel 开 \(\ell\) 次根。这样控制的是 \(K/F\) 这一层，\(F/F_{\rm tpd}\) 的分歧和重新标作 good 的原源像仍应单算。[I 的选位范围](IUT-TEXT/I.txt#L3146) · [IV 的额外假设](IUT-TEXT/IV.txt#L1260) · [IV 用到的 D0](IUT-TEXT/IV.txt#L1442)

本节交付的是自然语言定理与适用条件。§10.1 给出现有标量路线的确切强度。§10.2–10.3 给出可在同一输入上检验的算术商线和误差。§10.4 的大像结论可独立使用。原 III.3.12 的双列识别、IV 对同一 Θ 的上界及无条件 ABC 均未由本节推出。

<a id="original-iii312"></a>

## 11. 在原 III.3.12 的两列上直接推导

固定 III.3.11 的一份合格初始数据、其中的素数 \(\ell\)，以及该数据上的一份 LGP-Gaussian log-theta-lattice。写 \(n=(\ell-1)/2\)。在第 1 列，令 \(P_{j,p}\) 是从第 0 列 Θ-pilot 经原算法所得的**全部允许像之并**，\(H_{j,p}\) 是此并在第 1 列算术全纯结构中的 hull，\(p\) 包括无穷位。记 \(h_\Theta=-|\log(\Theta)|\)，\(h_q=-|\log(q)|\)。前者先在每个原张量包内取 hull 并作原文加权 log-volume，最后对 \(1\le j\le n\) 等权平均。后者是第 1 列 q-pilot 在原 Kummer 对应下的固定读数。目标是 \(h_\Theta\in\mathbb R\) 且 \(h_q\le h_\Theta\)。这里固定了原对象及先后次序，因此任何正的、有统一上界的系数损失也要在同一输入上消掉。[III.3.11 的量词和原包](IUT-TEXT/III.txt#L9153) · [III.3.12 的定义和目标](IUT-TEXT/III.txt#L10326)

本次能严格推到两个位置。坏位的原 Θ 赋值给出 q 的相容根塔，第 1 列每个原包中都有精确读成 q 次数的比较盒。要推出原不等式，还缺一个真实 Θ 输出在原度量下达到这个次数的证明。§11.4 检验固定覆盖的分支，§11.5 在一个好素数标定全部坏位的总量，§11.6 检验允许逐位损失的全局整态射。

### 11.1 原文的逆线究竟是哪一条

取原包的一个有限位直和项，暂略其权。设 \(V\) 是该项的有理张量空间，\(O\) 是 III.3.9(i) 用来定零点的结构层，\(B\subset V\) 是满秩格。相对行列式是 \(\det B\otimes(\det O)^{-1}\)。例如 \(B\subset O\) 的指数为 \(p^k\) 时，其未除维数的有符号 log-volume 是 \(-k\log p\)。在各原直和项上按权取正张量幂，再对每项除掉对应的结构层行列式，正是 Remark 3.9.5 (Ob3-1-1,2) 的处方。对常用的统一正幂 \(M\)，算术线 \(L\) 进入这个构造给出 \(L^{\otimes M}\)，最终两侧以同一个 \(M\) 除回。[结构层逆线与权](IUT-TEXT/III.txt#L7934) · [统一正幂的作用](IUT-TEXT/III.txt#L7964)

这决定了 §10 辅助迹商的使用条件。若把同一新参考格 \(O'\) 用在 \(B_\Theta,B_q\) 上，二者的相对行列式之商严格等于 \(\det B_\Theta\otimes(\det B_q)^{-1}\)；\(\det O'\) 各出现一次，完全约掉。若只给 Θ 侧除以 \(I_{m+a}/I_m\)，就须从 Θ 侧原包的格及其箭头中构造以该线为商的正合列，并辨认它的诱导度量。III.3.11(ii)(a) 给出每列整包的竖直同构，(ii)(b) 给出分裂幺半群的竖直同构，(iii)(c) 对横箭头陈述的是构造对自同构的等变性。在这些条款中，能直接辨认的逆因子是上面的 \((\det O)^{-1}\)。迹商的短正合列只在 §10 的辅助空间上已经构造。因此以下改从原 Θ 值自身提取 q，再检验提取操作能否作用在这些带格的对象上。[原竖箭头](IUT-TEXT/III.txt#L9306) · [原横向相容性](IUT-TEXT/III.txt#L9555)

### 11.2 从两个原 Θ 值恢复 q 的整个局部 Kummer 塔

固定同一坏位，写 \(k=K_v\)、\(O=\mathcal O_k\)、\(q=q_v\)。选 \(r^{2\ell}=q\)。II 给出的第 \(i\) 个值是整个轨道 \(\mu_{2\ell}r^{i^2}\)。所以 \(a_i=\theta_i^{2\ell}=q^{i^2}\) 与代表无关。取任意相邻非零标签 \(i,i+1\)，记 \(u=i^2,\ v'=(i+1)^2,\ A=2i+3,\ B=2i-1\)。直接展开得 \(Au-Bv'=1\)。因此

\[
 q=a_i^A/a_{i+1}^B,\qquad
 (q)=(a_i^A O:a_{i+1}^B O).
\]

后一式的冒号表示全体满足 \(x a_{i+1}^B O\subset a_i^A O\) 的乘数。这给出一个整理想。直接对未取幂的 \(\theta_i\) 使用同一式得到 \(rO\)，代表改变只乘单位。例如有标签 \(2,3\) 时，\(7\cdot4-3\cdot9=1\)，用这两个非首标签就能重建。最小的 \(\ell=5\) 可用 \(1,2\)。所有运算先在同一 \(K_v\) 内进行，再送往固定张量槽，避免对不同素位的元素做除法。[II 的实际赋值轨道](IUT-TEXT/II.txt#L4283) · [加权对角同时作用于除子与有理函数](IUT-TEXT/II.txt#L8821) · [仓库已有的对角像刻画](../LeanFormal/IUT/IUTIII/Theorem311/SourceLabelWeightedDiagonal.lean#L114)

这个恢复还能在取绝对值之前验证。对任意正整数 \(N\)，在 \(\bar k\) 中取满足

\[
 x^N=a_i,\qquad y^N=a_{i+1},\qquad x^{v'}=y^u
\]

的相容对。映射 \((x,y)\mapsto x^A/y^B\) 给出它们与 \(z^N=q\) 的根集的双射，逆为 \(z\mapsto(z^u,z^{v'})\)。确实 \(z^N=q\)，且 \(z^u=x^{Au}/y^{Bu}=x^{Au-Bv'}=x\)；同理 \(z^{v'}=y\)。两映射是整指数单项式，故与 \(G_k\) 作用、以及 \(N\mid N'\) 时的幂过渡同时交换。这个论证也覆盖 \(N\) 与 \(i(i+1)\) 有公共因子的层次。取 \(2\ell\) 层及其上方各层就恢复了原 q-pilot 所用的根轨道。第三个方程指定同一分支，不能把任意两个独立的根配成一对。这给出了相容对本身及其逆映射，**解决同一算术全纯实现中从 Θ 提取 q 的局部乘法数据**。经过两列后该数据在第一幂原输出中的作用仍须辨认。[II 讨论赋值对 Kummer 覆盖的相容性](IUT-TEXT/II.txt#L3400) · [III 对单位根轨道的处理](IUT-TEXT/III.txt#L10200)

### 11.3 在第 1 列每个原张量包里构造一个精确读成 \(h_q\) 的比较盒

取一个有理有限素数 \(p\)。在第 1 列选用原来的全纯呈现，对 \(b\mid p\) 使用论文选定的 \(v\mid b\)。置 \(L_b=r_b\mathcal O_{K_v}\) 于指定坏位，在其他位取规定的单位参考。\(r_b\) 的单位根歧义不影响 \(L_b\)。这是一族局部理想，不要求它由数域中的单一元素生成。对行 \(j\) 和原元组 \(t=(b_0,\ldots,b_j)\)，令 \(V_t=\bigotimes_{i=0}^j K_{v_i}\)（在 \(\mathbb Q_p\) 上），\(O_t\) 是它分解成域后各整数环的乘积。在任意一个固定槽 \(s\) 延拓 \(L_{b_s}\)，得 \(Q^{(s)}_{j,t}=L_{b_s}O_t\)。这一步使用环同态 \(x\mapsto1\otimes\cdots\otimes x\otimes\cdots\otimes1\)，其余位采用结构层参考。它也可在 \(j\) 行始终用实际的末槽 \(s=j\) 定义。[III 的实际选位、次数和张量权](IUT-TEXT/III.txt#L5409) · [原结构层取各分解域的整数环](IUT-TEXT/III.txt#L7041) · [q-pilot 的指定局部修正](IUT-TEXT/III.txt#L6645)

这个盒的读数可严格计算。若 \(x\in K_{v_s}^{\times}\) 生成该槽的理想，在 \(V_t\) 各分解域内，\(x\) 的绝对值均为同一个延拓 \(|x|_p\)。按 \(\mathbb Q_p\) 维数归一化的 log-volume 因而为 \(\log|x|_p\)。也可直接算乘法行列式 \(\mathrm N_{K_{v_s}/\mathbb Q_p}(x)^{\dim_{\mathbb Q_p} V_t/[K_{v_s}:\mathbb Q_p]}\)。写 \(\lambda_{p,b}=[(F_{\rm mod})_b:\mathbb Q_p]/[F_{\rm mod}:\mathbb Q]\)，则 \(\sum_{b\mid p}\lambda_{p,b}=1\)。III 的元组权为 \(\prod_i\lambda_{p,b_i}\)。对 \(i\ne s\) 先求和，得到

\[
 \sum_t\left(\prod_i\lambda_{p,b_i}\right)\mu_t(Q^{(s)}_{j,t})
 =\sum_{\substack{b\mid p\\b\ {\rm bad}}}\lambda_{p,b}\frac{\log|q_b|_p}{2\ell}.
\]

这里 \(\mu_t(O_t)=0\)。若在无穷位用 q 线的单位参考，径向归一读数为零。再对 \(p\) 求和、对 \(j\) 按原次序等权平均，正好是 q-pilot 的带符号算术次数 \(h_q\)。原文的“次数 = log-volume”用于第 1 列同一算术线。这个构造给出了所有固定行的比较对象，连混合元组 \(b_1\ne b_j\) 也有定义。两种槽所得的盒可以不同，它们的加权读数严格相等。仓库中固定槽的求和引理已经证明这一重排，无需另排任务。[III 的次数公式](IUT-TEXT/III.txt#L6963) · [原 procession 的等权要求](IUT-TEXT/III.txt#L7129) · [固定槽的加权求和](../LeanFormal/IUT/IUTIV/Estimates/StepVDistinguishedSlotAverage.lean#L23)

于是一个足够的几何证明可以直接以这些盒为标尺。有限位只需在每个域坐标找到一个**原** \(P_{j,p}\) 中的点，其该坐标的绝对值达到相应的 \(|r_{b_s}|\)（单位参考处为 1）。不同域坐标可用不同的合法呈现，因为取的是原允许像之并的最小盒；不需要在所有张量因子中同步选择一组“最好”的根。无穷位用相应径向半径。若有个别坐标未达标，只要这些坐标的带权损失被其他原坐标的实际增益补足，同样能推出原不等式。[原 hull 的最小性](IUT-TEXT/III.txt#L7654) · [坐标最大值供体](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldProductHull.lean#L63)

### 11.4 尝试把恢复出的 q 分支留在原 Θ 输出中

在一个指定坏位选同一呈现，用 \(\theta_j=r^d,\ d=j^2\) 代表允许的单位根轨道。构造固定的整代数 \(C=O[X]/(X^d-r^d)\)，记 \(x\) 为 \(X\) 的像，\(\pi:C\to O\) 为 \(x\mapsto r\)。若希望所有算式先摆脱代表的选择，可对同一个比较两侧同时取 \(2\ell\) 次幂，改用 \(q^d,q\) 计算，再把次数除回。§11.2 的两个原赋值也能在这一级指定分支。以下计算对每个 \(d\) 成立，包括剩余特征整除 \(d\) 的情形。

在 \(C\otimes_O k\) 里，\(r\) 分支的幂等元和一个整倍数分别为

\[
 e=\frac{x^{d-1}+rx^{d-2}+\cdots+r^{d-1}}{d\,r^{d-1}},
 \qquad w=d r^{d-1} e .
\]

因为 \(x^d-r^d\) 在特征零没有重根，\(e\) 在 \(r\) 分支取 1，在其他分支取 0。\(w\in C\)，且 \(xw=rw\)。在基 \(1,x,\ldots,x^{d-1}\) 中查看最高项系数可知，\(ce\in C\) 等价于 \(c\in d r^{d-1}O\)。因而对每个 \(m\ge1\) 都有精确等式

\[
 \pi\big((x^m C)\cap k e\big)=d r^{d-1} r^m O .
\]

理由是 \(x\) 在泛纤维可逆并保持 \(ke\)，在该线上作用为 \(r\)。这里的分支代价是固定的 \(d r^{d-1}\)，**与 \(m\) 无关**。例如原来最早出问题的 \(j=2\) 行，\(w=x^3+rx^2+r^2x+r^3\)，\(\pi(x^m w)=4r^{m+3}\)。除以 \(m\) 的对数趋于 \(\log|r|\)。即便 \(p=2\)，因子 4 也只付一次。若改在 \(m\) 个彼此独立的整代数中各投影一次，会错误地把同一费用付 \(m\) 次。

现在把它与原 hull 真正对接。固定原张量包的一个分解域 \(E\)，将上述算式沿指定槽嵌入 \(E\)。设该域坐标的原 hull 为 \(J\)（一个分式理想），\(J^m\) 指**同一第一幂 hull 理想的普通乘积**。若把 \(x^m w\) 送去实际坐标的过程能由 \(m\) 个原第一幂输出的乘积及整线性组合给出，则得到 \(d r^{d-1}r^m O_E\subset J^m\)。取赋值、除以 \(m\) 并令 \(m\to\infty\)，得到 \(rO_E\subset J\)。在 DVR 上，\(J\) 正是该坐标所有允许输出值生成的理想，故这个乘积判据只用原第一幂。没有对 Θ-pilot 的新张量幂套用 III.3.12。

为检验这个步骤，我把**实际已知**的第一幂作用提升到 \(C\)。III.3.4(ii) 中第 \(j\) 行的分裂乘数是 \(\theta_j\)。它在这个覆盖上的普通拉回是乘 \(x^d\)。于是 \(\pi((x^d)^m w)=d r^{d-1}r^{dm}\)。差的次数为 \((d-1)m\)，上述极限会原样把它留下。换用范数也能检查同一件事，\(\det_k(m_x)=(-1)^{d-1}r^d\)，而 \(\det_k(m_{x^d})=r^{d^2}\)。II 明确区分在 Kummer 塔中能开根和以何种第一幂穿过 Θ-link。普通拉回、范数、分支投影这三个自然操作，算到终点都不能自动给 \(x\) 以第一幂输出的资格。[实际作用的行与槽](IUT-TEXT/III.txt#L5974) · [II 对第一幂的限制](IUT-TEXT/II.txt#L6769) · [III 对张量幂的说明](IUT-TEXT/III.txt#L10954)

这里有一个可直接尝试的有限构造。选一个固定的有限自由 \(O_E\) 模及一组基，在源端把一个矩阵的每项写成该坐标第一幂允许赋值的整线性组合，使矩阵在泛纤维有特征值 \(r\)（乘单位也可）。由于每项属于 \(J\)，它的特征多项式第 \(i\) 个系数属于 \(J^i\)。若 \(|r|\) 大于 \(J\) 的半径，特征方程中的首项将严格支配其余各项，矛盾。这样一次矩阵构造就足够。上述 \(x\) 的伴随矩阵给了显式的特征多项式，困难在其移位项 1：这些 1 来自覆盖的基变换。要把该矩阵用于原问题，须将移位项在合适的整基中实现为**真正的第一幂输出的整线性组合**。原始分裂幺半群的单位只给 degree-zero 的自同构。将标量 \(r^d\) 共轭，仍得到同一标量。故对 \(j=2\) 来说，现在可以明确要求从末次 evaluation 的单位侧/值群侧写出四行的系数及其来源，再直接检查特征方程；没有必要另造一套根扩张或猜一个整体保测同构。

### 11.5 改走全局次数，只在一个好素数测量步长

这条路允许坏位上有些原盒比 §11.3 的比较盒小。设 \(D=[F_{\rm mod}:\mathbb Q]\)，用原文的非负局部数

\[
 R=\sum_{v\in V^{\rm bad}}[(F_{\rm mod})_b:\mathbb Q_p]\,
       \operatorname{ord}_p(r_v)\log p>0,\qquad h_q=-R/D .
\]

取一个奇有理素数 \(p_0\)，避开 \(K\) 的分歧和所有指定坏位。设 \(\eta<0\) 是在第 1 列共同的有序 Picard 群中，以原归一化计量的**某个实际允许输出**的 pilot 次数，并且该输出的行列式区域确实在原 hull 下，这样 \(\eta\le h_\Theta\)。这里需要随输出保留 III.3.9.5 的局部对象、全局对象及局部化同构。不能先在实数射线上挑一个 \(\eta\) 再给它安上一个 strip。[原文的局部—全局对象](IUT-TEXT/III.txt#L8449) · [IPL 输出及其 rigidification](IUT-TEXT/III.txt#L9711)

在这个输出 strip 里取 \(p_0\) 上方**每个**好位离散除子幺半群的正生成元，经自己的局部化在 Pic 中求和，记所得步长的绝对值为 \(d_{p_0}(\eta)\)。Remark 2.4.2(ii)–(v) 给出了它的公式。一个 \(b\mid p_0\) 的步长是 \([(F_{\rm mod})_b:\mathbb Q_{p_0}]\log p_0\,|\eta|/R\)；所有次数相加为 \(D\)。所以

\[
 d_{p_0}(\eta)=\frac{|\eta|}{|h_q|}\log p_0.
\]

于是对这个实际输出，**只要**在好素处测得 \(d_{p_0}(\eta)\le\log p_0\)，即得 \(h_q\le\eta\le h_\Theta\)，保留原常数 1。这个等式解释了为什么单个辅助好素数可以测量全部坏位的总量。选取的是只在 \(p_0\) 上方各位修改格的除子，其余有限位及无穷位保持同一参考；若改成全局有理函数 \(p_0\) 的主除子，它的全局次数为零，无法标定。[原文 \(r_v,\rho_v,\eta\) 的公式](IUT-TEXT/III.txt#L5132) · [同一 Pic 内不同 pilot 的位置](IUT-TEXT/III.txt#L5245)

现在真的算这个好素处的两个动作。在标准整 log-shell 上 \(u\mapsto u^{p_0}\) 经对数变成 \([p_0]:z\mapsto p_0z\)。张量只要在一个槽施此操作，就等于整个张量乘 \(p_0\)。所有这些槽给出同一个动作。好素不分歧时 \((p_0)^{-1}\log O_{K_v}^{\times}=O_{K_v}\)，张量整数环有限 étale，故用原 packet-normalization 计，从 \(H\) 到 \(p_0H\) 的长度恰为 \(\log p_0\)。这也可直接由 \(H(p_0S)=p_0H(S)\) 得到。相反，II.4.1(iv) 写出的**原 Gaussian 值群**的形式赋值在同一好素处送出 \((j^2\log p_0)_j\)，在单位部分限制为恒等。其通常的逐行算术表示有平均步长 \((\sum_j j^2/n)\log p_0\)。共同的加权行列式正幂同时放大输入及输出，除回后这两种步长仍不同。这个核算定位了不能把单位的 \(p_0\) 次幂动作直接当作输出离散值群生成元的原因。[II 的好位形式赋值，含逐行公式](IUT-TEXT/II.txt#L7743) · [原单位格标准化](IUT-TEXT/III.txt#L6997) · [III 对张量中整数作用的说明](IUT-TEXT/III.txt#L10739)

允许比“生成元等于 \([p_0]\)”弱的证明。沿原末次 evaluation、1 列 log-Kummer 和带结构态射的局部—全局范畴，考察上面的单步修改。在**一个确定的输出**的各好位，若它分解为该输出离散生成元的正整数倍 \(k_b\ge1\)，且无其他位或无穷位的附加修改，则由局部化相加得到 \(\log p_0\ge d_{p_0}(\eta)\)。如用共通的正幂 \(M\)，要对同一个 \(M\) 的生成元和修改作比较。构造时可以保留模 \(p_0^2\) 的相邻格 \(H\supset p_0H\supset p_0^2H\)，用单位 Kummer 箭头实际诱导的两层映射对照值群箭头；普通单位的 \(p_0\) 次幂在任一未分歧因子上把第一层送到第二层。接着用 Example 3.6(ii) 的整性定义检查分布在各 \(b\) 的修改确实属于同一个**输出**的离散除子数据，最后再实化并取次数。仅在所有下格组成的范畴里看到 \(p_0H\subset H\)，并不能给出这些正整数 \(k_b\)：任意带度量的 \(H\) 都有这个下格。仅在实化以后分解则只得到正实系数，推不出 \(k_b\ge1\)。[实际整态射的定义](IUT-TEXT/III.txt#L6271) · [原局部范畴的结构态射](IUT-TEXT/III.txt#L8425) · [局部同构类的缩放歧义](IUT-TEXT/III.txt#L10965)

还能把这个检验沿 IPL 指定的整条方块走一次。III.3.10.2 的两条平行路径都有 \({\rm env}\to{\rm gau}\to{\rm LGP}\to{\rm lgp}\)。从下层 LGP 逆走最初两箭头，会把加权对角生成元还原成 env 的形式生成元；经第一个竖直 Kummer 箭头后，上层的第一条求值箭头又把它送到 \((j^2\log p_0)_j\)，其余两箭头是 III.3.10(i) 的自然识别。在这段运算中，\(j^2\) 先被解码、再被编码；原图交代了两件事各发生在哪里。另一面，若 \(\beta\) 是商单位群上的任一条实际乘法同构，则 \(\beta(u^{p_0})=\beta(u)^{p_0}\)，故同一复合在单位侧保持 \([p_0]\)。在相同未分歧整格 \(W\) 上，二者的指数也可区分，\([W:p_0^aW]=p_0^{a\,{\rm rank}_{\mathbb Z_{p_0}}W}\)，其中普通步取 \(a=1\)，加权表示第 \(j\) 行取 \(a=j^2\)。所以继续重复原 strip 方块不会给出比较。剩余的具体函子性问题是，当对**带局部—全局结构态射的一个实际输出**取正规化行列式并进入原文的 ⊼ 范畴时，单位侧的单步下格是否确实给出该输出的正整除子修改。这个问题可以在好素处查，生成元与度量两者必须跟踪到同一对象。[III.3.10.2 的六条水平箭头](IUT-TEXT/III.txt#L9116) · [IPL 的复合次序](IUT-TEXT/III.txt#L9703) · [仓库已有乘法等变层](../LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean#L249)

这个整数倍还可以在保留 Kummer 覆盖时检验。对共同未实化的局部除子射线，若一个输出步与标准修改的次数分别是正整数 \(a,b\)，则 \(a\mid b\) 足以给出所需单向比较。用同一均匀化元的第 \(N\) 层根挠子表示两种修改，在 deck 群 \(\mu_N\) 上相应的幂字符是 \(\zeta\mapsto\zeta^a\) 与 \(\zeta\mapsto\zeta^b\)。前一字符的核包含于后一字符的核，对一切 \(N\) 成立，当且仅当 \(a\mid b\)：正向只需取 \(N=a\)，反向由幂的复合。故可以寻找**从前一字符像到后一字符像的群同态，使后一作用经前一作用分解**。这一靶点只涉及箭头对覆盖的作用，陈述不含 Θ 或 q 的 log-volume。它有明确的前提：两种修改须先落在同一条未实化的局部射线上，并用同一公共正幂清分母；单独一个实 Pic 自同构不会给出 \(a,b\)。应在抹去单位根的 \(\times\mu\) 商以前追踪这个字符，再核对它是原行列式线的字符。在单列未作 hull 的加权对角上，暂略共同倍数，取全 \(p_0\) 纤维的统一修改，均匀平均清分母后得到 \(a=\sum_{j=1}^n j^2,\ b=n\)，\(a>b\)。向量层有第一分量 1，因而忠实；行列式字符却杀掉整个 \(\mu_a\)，标准字符没有。这个演算把待找的因子分解定位在实际输出的行列式层，且给出了能识别错误替代的覆盖层。[II 的带权除子与有理函数](IUT-TEXT/II.txt#L8821) · [原文保留或除去扭元的位置](IUT-TEXT/II.txt#L10116)

### 11.6 允许逐位失败时，用全局整态射检验补偿

还有一种构造直接使用原全局有理函数。先以原始单列 Θ 的分式理想作算例，才能判断此法要从实际 hull 多取得多少空间。记 \(B=F_{\rm mod}\)、\(J_E\in B\) 为椭圆曲线的模数不变量，并置
\[
 \mathfrak d=\prod_{b\ {\rm bad}}\mathfrak p_b^{-\operatorname{ord}_b(J_E)}.
\]
在指定坏位，Tate 展开的首项为 \(q_b^{-1}\)，故 \(\log N\mathfrak d/D=2\ell|h_q|\)。把两侧共同提升 \(2\ell\) 次幂后，在第 \(j\) 行将局部 q 理想送入原始 \(q_b^{j^2}\) 理想，要在该行指定槽乘一个数域元素。设再取 \(m\) 次幂，所有指定坏位的整性条件、连同其余有限位的单位参考，恰好是
\[
  0\ne f_m\in\mathfrak d^{(j^2-1)m}.
\]
这是对原始局部理想计算的有限位条件。不同源列/目标列之间的识别仍单独追踪。[实际 q 阶数的塔归一化](#torsion-fiber) · [原文将全局整态射解释为有理函数](IUT-TEXT/III.txt#L6261)

这个 \(f_m\) 可以构造。取 \(B\) 的一组整基，对长度 \(D\)、每个整坐标在 \(0,\ldots,t\) 的向量按上面理想取余。取最小的 \(t\) 使 \((t+1)^D>N\mathfrak d^{(j^2-1)m}\)，两个不同向量的差给一个合格的非零 \(f_m\)。反过来，任何合格 \(f_m\) 的绝对域范数至少为 \(N\mathfrak d^{(j^2-1)m}\)。于是所有无穷嵌入上最小可达的最大对数满足
\[
 \inf_{0\ne f\in\mathfrak d^{(j^2-1)m}}\max_{\sigma:B\hookrightarrow\mathbb C}\log|\sigma f|
 =m(j^2-1)\frac{\log N\mathfrak d}{D}+O_B(1).
\]
上界常数只用固定整基在各嵌入下的大小。结论是，单靠主理想调节，全部有限位的余量可以做对；若一律采用单位参考，无穷位要承担的损失却随 \(m\) 线性增长。让 \(m\) 增大只消掉整基的常数。

换用**原输出**的行列式时，可以允许所有域因子和所有标签之间互相补偿。清去有限支撑上的有理权和局部阶数分母，固定同一个正幂 \(M\)。在第 1 列，取带度量的行列式线 \(\det^{\otimes M}(H)\) 相对于 q 线同度数幂的局部比。若在整格模型上有限位比给出 \(B\) 的一个分式理想 \(\mathfrak a\)，无穷位半径比分别为 \(R_\sigma>0\)，则允许的乘数是 \(\mathfrak a^m\) 中的元素。这个描述也可直接用于任何已经由原允许坐标见证给出的内盒。记 \(d_\sigma=1,2\) 为实、复位次数，每对复共轭取一位。则
\[
 \inf_{0\ne f\in\mathfrak a^m}
       \max_{\sigma\mid\infty}\log\frac{|\sigma f|}{R_\sigma^m}
 =m\left(\frac{\log N\mathfrak a}{D}
       -\frac1D\sum_{\sigma\mid\infty}d_\sigma\log R_\sigma\right)+O_B(1).
\]
下界由域范数立得。为证上界，在数域实嵌入空间取各轴半径 \(e^{m\gamma} R_\sigma^m\) 的实区间、复圆盘之积，\(\gamma\) 为括号内的量。此盒体积是仅依签名的常数乘 \(N(\mathfrak a)^m\)，而格 \(\mathfrak a^m\) 的余体积是 \(\mathcal O_B\) 的余体积乘 \(N(\mathfrak a)^m\)。取一个仅依 \(B\) 的放大倍数，使半盒体积超过余体积，将半盒模格投到基本域；两个同余点之差给所需非零格点。若 \(\gamma\le0\)，这些映射的无穷范数至多损失一个固定常数，取 \(m\) 次根便得到原带符号不等式；有限位中某一盒不够大也无妨。对 \(H\) 本身，判定 \(\gamma\) 的符号就是要做的次数比较。要用此法证明新内容，应把**具体原源箭头**所得的半径填入上式，证明它们的增益足以抵消前一段已精确算出的损失。单列原始理想和有理函数的构造已做到这一步，不能凭格点存在推出 \(\gamma\le0\)。

### 11.7 有限性、原证明的最后一步和本次结论

对单个原有限维包，若允许像有共同有界外格，并含一个正体积的局部区域，则最小盒每个半径都严格正且有界，log-volume 是实数。对复位的径向盒同理。几乎处处的不分歧奇素数满足 \(p^{-1}\log O_{K_v}^{\times}=O_{K_v}\)，因为剩余域单位为素于 \(p\) 的挠群且 \(\log(1+pO_{K_v})=pO_{K_v}\)。这些未分歧张量的整数环为有限 étale 整数环之积，标准格等于其 hull，读数为零。剩下有限多个包，局部上界、正体积内区域足以给出全局有限性。原文在 III.3.12 开头断言原允许族的紧性，并以这一步得到有限性。III.3.5(ii) 给出的是单位 Kummer 像的共同外壳；在坏位还要跟着原分裂乘数走，在无穷位要用规定的单位球和径向度量。若将论文的紧性陈述作为其证明中的步骤，有限性在这里结束。若要求完全从仓库已核定的对象出发，本次只核对了这条局部到全局推理及标准素数，未逐一实现原 \(P_{j,p}\) 与这些内外区域的识别。单位球本身的紧性不足以判断任意族的并。[原 hull 的定义域](IUT-TEXT/III.txt#L7662) · [Ind3 的局部内外关系](IUT-TEXT/III.txt#L6073) · [几乎处处的零读数](IUT-TEXT/III.txt#L8648) · [原文使用紧性的位置](IUT-TEXT/III.txt#L10408)

在有限位，局部有界性也能直接检验一大部分。在一份共同的原整格 \(I\) 上，所有保格的 \(\mathbb Q_p\)-线性同构保持每个 \(p^aI\)。若一组原单位输入都在 \(I\)，再施一个在每个分解域都非零的固定分裂乘数 \(g\)，有限维性给 \(gI\subset p^{-c}I\)，其后任意这类同构仍落在同一 \(p^{-c}I\)。一次未修改的满格输入则在乘 \(g\) 后含某个 \(p^kI\)，有正 Haar 测度。在几乎处处的标准位可取零修正。此论证的好处是无须把 Ind2 放大成任意线性变换；II 定义的 Ism 还要求对每个开子群都保相应单位格。真正要对照的是原表示中乘数所在层及 Ind3 各迭代的共同外格。[Ism 的准确作用域](IUT-TEXT/II.txt#L2193) · [III 对原分裂乘数与竖直 log-link 的相容范围](IUT-TEXT/III.txt#L6147)

最后回到 XI(e)–(f)。在共同 Pic 群中比较时，输入给一个点 \(h_q\)，所有输出经过上述行列式和有序次数读成下射线 \((-\infty,h_\Theta]\)。在两列可执行同一算法，以及值群 strip 的横箭头将标记 Θ 送到标记 q，这两项原文都有。若能把一个上述实际构造送进下射线并证它的次数至少为 \(h_q\)，或在同一固定输入、同一 hull 的幂中给出趋于该次数的下界，闭性随即给出 III.3.12；若 \(h_\Theta\ge0\)，有限性建立后由 \(h_q<0\) 直接结束。XI(e)–(f) 使用的正是“该下射线含有输入读数”的识别。在这次实算中，§11.2 完成了坏位局部 Kummer 塔的恢复，§11.3 完成了全行精确 q 次数，§11.4 的固定覆盖把**分支的整格损失**降到了零斜率。**我没有推出该分支受原第一幂输出控制，也没有在 §11.5 找到使正整数步长成立的实际输出。因此这份自然语言推导尚未证明原 III.3.12。** [XI(e)–(f) 原文](IUT-TEXT/III.txt#L10882) · [APT 的准确含义](IUT-TEXT/III.txt#L9763)

优先检查 §11.5 从实际输出进入带结构态射的行列式范畴这一步。它只用一个不分歧好素数，且只要求标准修改相对于一个输出有效。要比较的是好位上同一个输出在修改前后的局部化、单位的相邻商、以及非实化除子幺半群中的倍数。已有 strip 方块的三条自由边就能拼出下边，连下边的单位数据也已由共轭构造；这项不再安排。另一个名为 unconditional 的 Haar 接口以 q 球本身作为 possible images，并取几何条件为输入。它在所定义的球上给出的包含不能代替原第一幂 Θ 输出的证明。[三条箭头已足以构造方块](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceEvaluationUnitPortionConjugation.lean#L190) · [Haar 接口的实际定义](../tmp/sheaf/xif/paper/Mzk1Cor312UnconditionalStrictAcceptanceActual.lean#L87)

<a id="first-log-witness"></a>

## 12. 从原坏位的一个单位出发，直接算第一幂 Θ 的张量

本节固定 III.3.11 的一份合格数据、它的 \(\ell\) 及相异 theaters 构成的原格。\(n=(\ell-1)/2\)，第 \(j\) 行有 \(j+1\) 个槽，\(1\le j\le n\)。\(h_\Theta\) 取第 1 列全纯结构中原允许像之并的 hull，目标是 \(h_q\le h_\Theta\in\mathbb R\)。推导有三个可独立使用的结果。§12.2–12.4 从坏位的一个单位构造带第一幂乘数的张量。§12.7 在一族全局曲线上写出达到原 q 次数的整态射。§12.8 用所有有限扩张的单位格证明固定局部 Galois 群的算术 Ind2 完全由单位标量作用。原两列允许像的覆盖及全量词不等式仍待证明。[原目标](IUT-TEXT/III.txt#L10326)

### 12.1 好素数的普通一步，在行列式范畴里可以直接做

取 §11.5 的好素数 \(p_0\)。对一个实际 hull 产生的整行列式线 \(J\)，在 \(p_0\) 上方令 \(J'_v=p_0J_v\)，其余处令 \(J'_v=J_v\)。所有包含的结构态射均由同一个有理函数 \(1\) 给出。按 III 例 3.6(ii)，这就是一个全局整态射。对局部结构态射取规定的自同构轨道，再取该全局对象和它的局部化，正好得到 III.3.9.5(ix) 的带结构态射对象。从包上先作普通一步也可核算。在秩 \(d_t\) 的格上，\(\det(p_0H_t)=p_0^{d_t}\det(H_t)\)。张量各个整次幂后仍是由 \(1\) 给出的全局包含；按原规则除回维数、公分母并按次数权重平均，下降量为 \(\log p_0\)。这解决了上一节悬而未决的“普通修改能否放在真实行列式之下”。[全局态射的定义](IUT-TEXT/III.txt#L6254) · [结构态射及其局部化](IUT-TEXT/III.txt#L8424)

再算这一步在标记除子中的像。普通修改的清分母行向量是 \((1,\ldots,1)\)，II.4.1(iv) 在同一素数对原标记生成元给 \((1,4,\ldots,n^2)\)。在逐行算术表示中，整的等权和分别是 \(n\) 与 \(\sum_{j=1}^n j^2>n\)。取两侧共同正幂保留这个比值。带结构态射的范畴允许这两个对象同时存在，进入它的函子没有把普通修改提升成标记生成元的正整倍。故已有的全局整态射还不能在 §11.5 的公式里读作输出 strip 的一个标记步长。下面改为直接造张量点。[好位的原标记求值](IUT-TEXT/II.txt#L7743)

### 12.2 每个 \(p<\ell\) 的指定坏位，都有范数大于 1 的实际单位对数

固定 \(w\mid P\mid p\)，其中 \(P\) 在 \(F\)，\(w\) 是 \(K=F(E[\ell])\) 的指定提升。令 \(k=K_w\)，\(v_k(\pi)=1\)，\(e=v_k(p)\)，并用 \(v_p=v_k/e\)。记 \(q_P\) 为 Tate 参数，\(r^{2\ell}=q_P\)。本节写 \(a=v_p(r)\)，因而 q 在这个坏位的带符号读数为 \(-a\log p\)。Tate 商中的 \(\ell\)-扭点给出 \(q_P^{1/\ell}\in k\)，全 2-扭点给出平方根，合起来给出 \(r\)（详见 §8 的 Tate 商证明）。\(\ell\nmid v_P(q_P)\) 是原初始条件，故

\[
 \ell\mid v_k(q_P)=e(w/P)v_P(q_P),\qquad \ell\mid e(w/P),\qquad \ell\mid e .
\]

原条件中的全有理 3-扭点也排除了当地的非分裂二次扭曲。Tate 模型的 3-扭点模去 \(\mu_3\) 有商 \(\mathbb Z/3\)，非分裂扭曲使其 Frobenius 作用成为 \(-1\)，与全 3-扭点有理相抵触。仓库已有从完备化根到分歧整除性的引理。[I 的初始条件](IUT-TEXT/I.txt#L3176) · [实际根推出分歧整除](../tmp/sheaf/xif/paper/S1281KSideRootCompletionActual.lean#L215)

取任意均匀化元 \(\pi\)，令 \(u=1+\pi\)。对数级数中第 \(m\) 项的 \(v_p\) 为 \(m/e-v_p(m)\)。令 \(s=v_p(m)\)，在这个 \(s\) 下最小值恰由 \(m=p^s\) 取得。令 \(d_s=p^s/e-s\)，相邻差为 \(d_{s+1}-d_s=(p-1)p^s/e-1\)，且随 \(s\) 严格增加。两个最小项并列必须有 \(e=(p-1)p^s\)。指定坏位的 \(p<\ell\) 时，\(\ell\mid e\) 而 \(\ell\nmid(p-1)p^s\)，所以最小项唯一。级数的其余项不能消去其首剩余类，得到

\[
  v_p(\log(1+\pi))=\min_{s\ge0}(p^s/e-s)<0,\qquad
  b=-v_p(\log(1+\pi))\ge 1-p/e>0 .
\]

同一逐项估计给任何主单位 \(1+x\) 的对数下界 \(-b\)，因为 \(v_k(x)\ge1\)。任一单位取 \(p^f-1\) 次幂后是主单位，而 \(p^f-1\) 在 \(\mathbb Z_p\) 可逆，其中 \(f=[\kappa_k:\mathbb F_p]\)。所以此处还求出了整个格 \(L=\log(\mathcal O_k^\times)\) 的**最大范数** \(p^b\)，且 \(u\) 亲自取到它。使用的是未缩放的对数，未借用容器 \(I=(p^*)^{-1}L\) 额外的半径。[III 中两个格的定义](IUT-TEXT/III.txt#L2199) · [单位对数纯张量进入算术包及元组投影](../LeanFormal/IUT/IUTII/Kummer/SourceUnitLogTensorLanding.lean#L55)

同一个量在其余有限位也可从当地的整数环计算。取整数 \(N>e/(p-1)\)，这时 \(\log(1+\mathfrak m^N)=\mathfrak m^N\)，由收敛的 \(\exp,\log\) 互逆得到。选 \((\mathcal O_k/\mathfrak m^N)^\times\) 的单位代表。代表改变时对数之差在 \(\mathfrak m^N\) 内。于是 \(L\) 的最小 \(v_k\) 是 \(N\) 和这些对数模 \(\mathfrak m^N\) 的所有非零类的赋值中的最小者。计算代表时先取 \(p^f-1\) 次幂；对数级数只需保留 \(m-e\lfloor\log_p m\rfloor<N\) 的项，其余项全部在 \(\mathfrak m^N\) 中。这给出有限算法，也处理最小项相消和 \(p=2\)。

### 12.3 把同一个单位放进全部槽，并算每个域因子

先取齐次元组，即同一个 \(k\) 重复 \(j+1\) 次。这正包括 \(F_{\rm mod}=\mathbb Q\) 的有限位。标记槽乘论文第一幂的第 \(j\) 个值 \(r^{j^2}\)。在这个全纯实现里取

\[
  X_j(u)=\log u\otimes\cdots\otimes\log u\otimes (r^{j^2}\log u)
  \quad\in k^{\otimes_{\mathbb Q_p}(j+1)}.
\]

这里先对**单位** \(u\) 取对数，另用约定的分裂生成元乘标记槽。对张量积的任一域投影 \(\alpha\)，其在第 \(i\) 槽的限制是保 \(v_p\) 的域嵌入，纯张量投影为这些嵌入值之积，故

\[
    v_p(\operatorname{pr}_\alpha X_j(u))=j^2 a-(j+1)b .
\]

同一点同时给出所有域因子的这个值。按 III 的归一，一个因子的带符号半径读数是其赋值乘 \(-\log p\)，域因子次数权重之和为 1。第 \(j\) 行由这组算术点产生的最小盒遂有读数 \(((j+1)b-j^2a)\log p\)。\(b\) 的最优性同时给出上界。对角点集本身可以是 Haar 零集。这里取读数的对象是它生成的正半径乘积盒，III.3.9.5 对整个允许像族另有正体积及有界性的条件。[原张量的分解和指定槽嵌入](IUT-TEXT/III.txt#L5342) · [标记乘数的作用域](IUT-TEXT/III.txt#L5997) · [各因子的原 log-volume 归一](IUT-TEXT/III.txt#L6840)

还可以去掉“作用按域同构运输”这个过强要求。把同一 \(k\) 的各份局部实现各自识别作副本，取任意 \(\mathbb Q_p\)-线性同构 \(g_i\) 把未缩放单位对数格 \(L\) 带到相应的 \(L\)。保 III 的原单位壳的线性同构已经有这个性质，因为 \(L=p^*I\)。取 \(x\in L\)，考察各槽 \(g_i(x)\)，标记槽取 \(g_j(r^{j^2}x)\)。\(g_i\) 可彼此不同，也可以完全不保乘法。

记 \(p^m=|\mu_{p^\infty}(k)|\)。相对于 \(\mu(\mathcal O_k)=1\) 的加性 Haar 测度，
\[
 \mu(L)=p^{-f-m}.
\]
确实，取上述 \(N\)，\(\log\) 在 \(1+\mathfrak m^N\) 上双射。其在全单位上的核为挠群（取足够高次幂进入深主单位即知），故 \([L:\mathfrak m^N]=p^{f(N-1)-m}\)。乘上 \(\mu(\mathfrak m^N)=p^{-fN}\) 即得公式。保 \(L\) 的 \(g_i\) 保 Haar 测度。写 \(A=v_k(r)\)。格 \(g_j(r^{j^2}L)\) 的测度是 \(p^{-fj^2A-f-m}\)，因此它有元素满足
\[
  v_k(y)\le j^2A+1+\lfloor m/f\rfloor .
\]
否则它将装进测度更小的下一层极大理想幂。其余槽各有元素取到 \(v_k=-eb\)。这个证明也给出 IV.1.4(ii) 的未缩放单域体积，无需把该估计当作新的假设。[IV 的归一化与公式](IUT-TEXT/IV.txt#L658) · [Ism 保持的单位格](IUT-TEXT/II.txt#L2193)

**还可以在各槽使用同一个原单位。** 对非标记槽，令坏集为 \(g_i(x)\) 的赋值严格大于 \(-eb\) 的 \(x\in L\)。对标记槽，令坏集为 \(g_j(r^{j^2}x)\) 的赋值严格大于上述界的 \(x\)。每个坏集都是 \(L\) 的真开加法子群。每个真开子群都包含在一个模 \(p\) 超平面的逆像中，因为它的商是非零有限阿贝尔 \(p\)-群。维数 \(d=[k:\mathbb Q_p]\) 的 \(\mathbb F_p\) 空间里，\(s\le p\) 个超平面的并至多有 \(1+s(p^{d-1}-1)<p^d\) 个元素。因此 \(j+1\le p\) 时，可以从 \(L/pL\) 选一个类，取其任一提升 \(x\)，使**全部**槽同时达到各自的界。再取 \(\log u=x\) 的原单位 \(u\)。所有域投影的带符号半径至少为
\[
  \left(jb-j^2a-\frac{1+\lfloor m/f\rfloor}{e}\right)\log p .
  \tag{12.1}
\]
尤其无需各标签有独立的单位选择。

对任意长的行也有带误差的版本。在 \(L\) 上取概率 Haar 测度。对任一上面的整线性读数 \(f_i:L\to k\)（即 \(g_i\) 或 \(g_j\circ m_{r^{j^2}}\) 的限制），设 \(h_i=\min\{v_k(z):0\ne z\in f_i(L)\}\)。取到最小值的 \(x_i\) 在商 \(L/\{x:v_k(f_i(x))\ge h_i+t\}\) 中生成至少 \(p^{\lceil t/e\rceil}\) 个类。因此超出最小值 \(t\) 层的概率至多为 \(p^{-\lceil t/e\rceil}\)。从 \(t=1\) 求和得每槽期望超出量至多 \(e/(p-1)\)。对各槽相加，存在**同一个** \(x\)，使总超出量至多 \((j+1)e/(p-1)\)。故任意 \(j\) 的对角单位仍给出 (12.1) 减去 \((j+1)\log p/(p-1)\) 的下界。这个平均仅用于选择点，实际读数仍用原来的各行等权平均。

### 12.4 一个算到剩余类的局部 Tate 模型

取 \(p=3,\ell=5,q=27\)，基域的完备化取 \(\mathbb Q_3(i,\zeta_3)\)。它包含 \(\sqrt3\)，故 \(q^{1/6}\) 已在基域。加入全 5-扭点后得到 \(k=\mathbb Q_3(i,\zeta_3,\zeta_5,3^{1/5})\)。\(\zeta_5\) 的非分歧次数是 4，\(\zeta_3\) 给分歧次数 2，\(3^{1/5}\) 给分歧次数 5。因此 \(e=10,f=4,m=1\)，可取 \(\pi=3^{1/10}\)，\(r=\pi^3\)。§12.7 给出具有这个完备化、相同坏位深度及满 \(\mathrm{SL}_2\) 条件的全局曲线。使用该曲线时 \(r\) 可差一个单位，以下赋值相同。

对 \(u=1+\pi\)，按 \(v_k\) 计，第 1、3、9、27 项的赋值分别为 \(1,-7,-11,-3\)。第 9 项唯一最小，且 \(\pi^{11}\log(1+\pi)\equiv1\bmod\pi\)。两条原行的纯张量在**每个**域因子上的赋值分别为 \(3-22=-19\) 和 \(12-33=-21\)。换成上一节任意保单位对数格的线性同构，两行分别有对角单位见证使赋值至多为 \(3+1-11=-7\) 和 \(12+1-22=-9\)，因为每行槽数至多为 3。故两行等权后的带符号半径下界是 \(0.8\log3\)，当地 q 的读数为 \(-0.3\log3\)。这给出了与 q 同号约定下可直接检验的余量。计算只使用第一幂标记、各行原槽数、一次未缩放单位对数。

落到原允许像时，具体要追踪的是同一个选择的复合。在第 0 列取同一个单位 \(u\)，沿一次单位 log-link 进入原加法包，将分裂生成元作用在原标记槽，再经这一选择的 evaluation/Kummer 箭头在第 1 列投影。算术侧的前三个对象和每个局部投影已写出。III.3.5(ii)(a) 给出单位像进入容器，(c) 给出分裂作用及其在 log-link 定义域上的相容范围。把这两条陈述连接为**实际 pilot 允许像的成员**，需要它们在这一次 evaluation 中确实按上述次序配对。对非单位本身取 log 不在该箭头的定义域。这个问题可先在上例第二行检验，原 q 精度只需见到每个因子中一个模 \(\mathfrak m^4\) 非零的类（在 \(k/\mathfrak m^4\) 中取加法类）。上式实际给到赋值 \(-9\) 的界。可从 \(L/3L\) 取避开三个超平面的类，提升为单位，保留它的原输入标记，沿 evaluation 输出取相同的加法类。各因子可分别见证，因原 hull 逐因子取半径。[单位和分裂作用的原箭头](IUT-TEXT/III.txt#L6073) · [原 evaluation 的次序](IUT-TEXT/III.txt#L9703) · [APT 的定义](IUT-TEXT/III.txt#L9763)

在仓库所查的两处消费者，这一步有可以精确定位的差异。arithmeticUnitTupleLogTensor_mem_arithmeticTensorTupleLogRegion 产出的是**未乘标记的张量 log 区域成员**。S3139 的 sourceMultiradialPossibleImage 返回 Set ℝ；其上游 S3138 在每个选择上明确定义为单元素集合，且读数对选择恒定。它并不返回这两个局部剩余类。IV 的固定元组 possibleImages 则取 \(\phi(\varpi x)\)，其中 \(x\) 来自全纯单位参考。在上述模型中，原始 \(X_2\) 的全部因子赋值是 \(-21\)，而 \(r^4 O\) 的赋值下界是 \(12\)，故取恒等 \(\phi\) 不会生成这个见证。现有单位张量和投影可直接复用。应在它到原 evaluation 的连接处保留单位、标记和垂直步的同一来源。[实际张量 landing](../LeanFormal/IUT/IUTII/Kummer/SourceUnitLogTensorLanding.lean#L97) · [S3139 的值域](../tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean#L75) · [S3138 的单元素定义](../tmp/sheaf/xif/paper/S3138SourceProcessionProfileActual.lean#L67) · [固定元组的原代码](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L668)

### 12.5 同一有理素数上方有多个位时，换槽究竟带来多少

给 \(b\mid p\) 原权重 \(w_b=[(F_{\rm mod})_b:\mathbb Q_p]/[F_{\rm mod}:\mathbb Q]\)，其和为 1。在指定坏位置 \(x_b=v_p(r_b)\log p\)，其余位置 \(x_b=0\)。行内不改 \(j^2\)。在整包 \((\prod_{b\mid p}k_b)^{\otimes(j+1)}\) 的普通全纯实现里，在槽 \(s\) 放置由 \(r_b^{j^2}\)（好位放 1）乘标准整数环形成的区域。取这些区域在全部**槽置换**下的并及最小全纯盒。固定输出元组 \(t=(b_0,\ldots,b_j)\)，选将一个最浅的输入位置移至该输出元组相应槽的置换。域投影把纯张量送成嵌入值的乘积，故各域因子的最大半径正好为 \(\exp(-j^2\min_i x_{b_i})\)。逐投影选的置换可不同。这是关于上述具体轨道的等式。

令 \(F_p(s)=\sum_{x_b>s}w_b\)。原元组权重为 \(\prod_i w_{b_i}\)。所有槽同时深过 \(s\) 的总权重为 \(F_p(s)^{j+1}\)。以相邻深度差为长度作有限求和，就算出了这一轨道在全部有限位的读数
\[
  -\sum_p\int_0^\infty \frac1n\sum_{j=1}^n j^2 F_p(s)^{j+1}\,ds ,
  \qquad h_q=-\sum_p\int_0^\infty F_p(s)\,ds .
\]
例如每个 \(p\) 上入选坏位的次数权重至多一半，则这个轨道已经达到 q 的原系数，深度没有上限。确实 \(\sum_{j=1}^n j^2 2^{-j}\le n\)，其中 \(j=1\) 省下 \(1/2\)，\(j=3\) 多付 \(1/8\)，其余各项至多 1。更精确的逐层阈值是 \(\sum_{j=1}^n j^2\rho^j=n\) 的唯一正根。若整纤维只有同一深度，换槽收益为零，这才需要 §§12.2–12.4 的另一种构造。[原元组的次数权重](IUT-TEXT/III.txt#L5418) · [原逐因子 hull](IUT-TEXT/III.txt#L7661)

原 procession 确实允许行内置换，但比较对象还带有一个分裂乘数。交换槽 \(s,j\) 会同时把有标记的 \((t,j)\) 送到 \((\sigma t,\sigma j)\)；要取得上面的最浅值，须把不同标记的区域送入**同一个固定输出包**后再取 hull。若连同标记一起拉回，指定槽的深度仍为 \(x_{b_j}\)。I 的 capsule 定义及 III.3.11(i)(a),(b) 显示了这两种投影；仓库的 reindex 定理目标因子族也随置换改变。IV Step (v) 固定 \(i^\dagger=j\)，只在求加权平均后对指定槽对称化。对称平均不等于先逐坐标取最大。因此上面的全系数结论已证于具体槽轨道，尚未转记为 III 两列的子情形定理。[I 的 procession 态射](IUT-TEXT/I.txt#L6763) · [III 中整包与标记子模](IUT-TEXT/III.txt#L9176) · [仓库的重指标及目标类型](../tmp/sheaf/xif/paper/Ind1AutomorphismTensorActionActual.lean#L48) · [IV 在何时取平均](IUT-TEXT/IV.txt#L1733)

### 12.6 原不等式还差多大

在任一固定局部 Tate 实现，把 \(q\) 换成另一个 Tate 参数 \(q'=p^{6\ell k_0}q\)，其中 \(k_0\) 为正整数。它的 \(2\ell\) 次根可取 \(r'=p^{3k_0}r\)，其 \(\ell\)-扭点域及 6 次根所需的域都相同。单位对数格、上述最大范数、全部格指数保持相同。对齐次元组，保留同一族局部格箭头，标记乘数多出有理标量 \(p^{3k_0j^2}\)，它与每个线性箭头交换。因此这整族具体张量的第 \(j\) 行读数恰再降 \(3k_0j^2\log p\)，而当地 q 只降 \(3k_0\log p\)。这是局部变动，未把它当作一族全局合格输入或对原结论的反例。它精确说明了为何即使把本节的单位全部用尽，固定局部域的收益仍不能支付无限增长的 q 深度。单靠加深同一个单位或多写几次单位对数，不能补齐这个斜率差；一次以上有定义的普通 log 迭代，其最后一步的输入仍须是单位。[原 log-link 的定义域](IUT-TEXT/III.txt#L1648)

<a id="frey-depth-family"></a>

### 12.7 在无限族全局曲线上构造一条足额的整态射

令 \(d=3+30t\)，\(t=0,1,\ldots\)，\(A=3^d,\ B=1+432A\)。取有理椭圆曲线
\[
 E_t:\quad y^2+xy=x^3+A.
\]
这个整模型有 \(c_4=1,\ \Delta=-AB,\ j(E_t)=1/\Delta\)。它在各有限位半稳定（坏纤维是结点，\(c_4\) 是单位），各 \(t\) 的 \(j\) 不同。在 3 处约化的两条切线是 \(y=0,y=-x\)，故为分裂 Tate 曲线。取 \(F=\mathbb Q(i,E_t[6])\)，\(K=F(E_t[5])\)，\(F_{\rm mod}=\mathbb Q\)，指定坏位只选 3。其余有乘性约化的位在原定义中也可标为 good。\(F/\mathbb Q\) 是 Galois 扩张，次数整除 \(2\cdot6\cdot48=576\)，与 5 互素。[坏位选取及基域条件](IUT-TEXT/I.txt#L3139)

逐一核对这族的局部数据。由 \(j(q)=q^{-1}+744+\cdots\) 的整系数展开及 \(v_3(j(E_t))=-d\)，\(q=\Delta(1+3^d\mathbb Z_3)=-3^d u_t\)，\(u_t\in1+27\mathbb Z_3\)。这些 \(u_t\) 都有 6 次根和 5 次根，前者由 \(\log,\exp\) 及 \(v_3(\log u_t/6)\ge2\) 得到。因 \(d=3\bmod 6\)，在 \(\mathbb Q_3(i,\zeta_3)\) 中已有 \((-3^d)^{1/6}\)。由 Tate 的扭点描述，\(F\) 在 3 的完备化正是该域，\(\operatorname{ord}_P q=2d\) 与 5 互素。再取 5-扭点，因 \(5\nmid d\)，所得正是 §12.4 的 \(k\)，且 \(v_3(r)=d/10\)。所以前一节所说的深度增长在全局曲线上也实际出现。

满像可以独立核实。3 处惯性在 \(E_t[5]\) 上给一个非平凡转导矩阵，因为 \(\mu_5\) 非分歧而 \(q^{1/5}\) 的分歧次数为 5。2 处约化良好且模型与 \(t\) 无关。在 \(\mathbb F_{16}\) 上这条约化曲线有 16 个点。直接计数如下，取 \(\xi^4=\xi+1\) 的本原元。对 \(x=\xi^s\ne0\)，令 \(Y=y/x\)，方程化为 \(Y^2+Y=x+x^{-2}\)。右边的绝对迹为零恰在 \(s=0,3,5,6,9,10,12\)；各给两个点，另加 \(x=0\) 的一点和无穷点。若有 Galois 不变的 5-阶直线，其上 2 处 Frobenius 的阶整除 4；良好约化的素于 2 的 5-扭点遂在 \(\mathbb F_{16}\) 上给阶 5 的点，与计数不合。因此模 5 像不可约，某个共轭把上述转导矩阵的固定直线移开。两个转导矩阵的幂给出两个相反方向的全部初等矩阵，生成 \(\mathrm{SL}_2(\mathbb F_5)\)。限制到 \(F\) 后像是指数与 5 互素的正规子群，仍含这些 5 阶元素。此处核实的是初始数据的曲线、域、坏位及大像条件。单个选定坏位允许从当地 Tate 的 5-扭点选全局标记线及商的生成元；本节未另行构造各层 Hodge theater。[仓库已有的转导矩阵生成引理](../Iut/Tripod/SL2Generation.lean#L154) · [I 的局部覆盖与尖点条件](IUT-TEXT/I.txt#L3252)

现在动用这条曲线在**其他位**的算术数据。q 线的二十次幂在 3 的格为 \(3^{2d}\mathbb Z_3\)，其余有限位和无穷位取单位参考；这里写的是下降到有理带度量线的参考，拉到各指定完备化得到相同归一读数。原始 Gaussian 两行的指数均值是 \((1+4)/2\)。清去相同分母 20 后，它在 3 的格为 \(3^{5d}\mathbb Z_3\)。把最小判别式的去 3 部分 \(B\) 用三次，构造有理带度量线 \(J_t\)，在 3 用上述 Gaussian 格，在 \(s\mid B\) 用 \(s^{-3v_s(B)}\mathbb Z_s\)，其他地方用单位参考。给出一个具体有理数
\[
 f_t=\frac{3^{3d}}{B^3}.
\]
在 3 处，它将 q 格 \(3^{2d}\mathbb Z_3\) **满射到** \(3^{5d}\mathbb Z_3\)。在每个 \(s\mid B\) 它将单位格满射到 \(s^{-3v_s(B)}\mathbb Z_s\)。在其余有限位它是单位。在实位其绝对值为 \((3^d/B)^3<1\)。这就给出一个实际的全局整态射 \(Q_t^{\otimes20}\xrightarrow{f_t}J_t\)，且
\[
 \frac{\widehat{\deg}J_t}{20}-h_q
    =\frac3{20}\log(B/3^d)
    =\frac3{20}\log(432+3^{-d})>0.
\]
按 §11.6 的约定，有限格 \(s^a\mathbb Z_s\) 的带符号读数是 \(-a\log s\)。这个等式对任意 \(t\) 都成立，允许 \(d\) 无界。构造只用了这族自身的最小判别式和单位无穷度量。原 Θ 的有限位没有自动得到 \(J_t\) 的逆理想；上式给出的实物是足额的**比较线及来自原 q 线的态射**。这个方向允许在多个位付清同一份 q 次数，不要求原两行逐位都覆盖 q 盒。

### 12.8 从全部开子群的单位格直接确定固定群的 Ind2

**局部引理。** 对任意有限扩张 \(k/\mathbb Q_p\)，把 \(G_k\) 固定。在算术实现 \(\overline k\) 中，对每个有限扩张 \(D/k\) 记 \(L_D=\log\mathcal O_D^\times\subset D\)。任何 \(G_k\)-等变的 ind-拓扑加法自同构 \(g\)，若对每个 \(D\) 都有 \(g L_D=L_D\)，就在整个 \(\overline k\) 上等于乘同一个 \(\lambda\in\mathbb Z_p^\times\)。固定群的 II 例 1.8(iv) 恰要求每个开子群的**原单位群在商中的像**为保留的格。普通单位模挠通过对数正好实现为 \(L_D\)。任一代数元素先乘大 \(p\) 幂就能取指数，再对所得单位在代数闭包中开根，所以这些对数的并实现整个加法空间。对同态的连续性也可在此直接核实，\(g(p^a L_D)=p^aL_D\)，这些格构成 \(D\) 中的零邻域基。由加性和 \(\mathbb Q\) 的稠密性得到每个 \(D\) 上的 \(\mathbb Q_p\)-线性。仓库的 invariantImage 正是先取原单位不变量再映到商，IsKummerIsometry 对所有开子群保留这个像。[仓库中的定义](../LeanFormal/IUT/IUTII/Kummer/TimesMuIsm.lean#L72) · [II 定义 torsion quotient 与 Ism](IUT-TEXT/II.txt#L2161) · [III 的算术对数实现](IUT-TEXT/III.txt#L1270) · [仓库中实际单位商与对数像的同构](../LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithmKernel.lean#L83)

取 \(C=k(\mu_{p^\infty})\)。圆分群 \(\operatorname{Gal}(C/k)\) 是交换群，其圆分特征的像在 \(\mathbb Z_p^\times\) 中为开子群。事实上，\(\Phi_{p^s}(1+T)\) 为 Eisenstein 多项式，故有理 \(p\)-进圆分塔的群是 \(\mathbb Z_p^\times\)，而有限的 \(k\) 与此塔的交包含于有限层。故可固定 \(\gamma\) 使 \(\chi(\gamma)=1+p^c\)，其中 \(c\) 与随后选的层数无关。若 \(z\in C,\ z^{p^s}=w\in k^\times\)，令 \(\eta=\gamma(z)/z\in\mu_{p^s}\)。对 \(\sigma\in\operatorname{Gal}(C/k)\) 写 \(d_\sigma=\sigma(z)/z\)。交换 \(\sigma,\gamma\) 得
\[
  \frac{\sigma(\eta)}{\eta}=\frac{\gamma(d_\sigma)}{d_\sigma}=d_\sigma^{p^c}.
\]
于是 \(z^{p^c}/\eta\in k\)，从而 \(w^{p^c}\in(k^\times)^{p^s}\)。整个论证对 \(p=2\) 同样适用，取足够大的 \(c\) 即可。

取 \(x=\log u\in L_k\)，写 \(g(x)=\log v=y\)。对每个 \(s\) 取真正的有限扩张 \(D_s=k(\mu_{p^s},u^{1/p^s})\)。因 \(x/p^s\in L_{D_s}\)，保格及线性给出 \(y/p^s\in L_{D_s}\)。取当地单位 \(w_s\) 使 \(\log w_s=y/p^s\)。故 \(w_s^{p^s}/v\) 是一个单位根。其素于 \(p\) 的部分已可在自身生成的有限群中取 \(p^s\) 次根，阶为 \(p\) 幂的部分可在 \(C\) 中取根。这样得到
\[
             v^{1/p^s}\in C(u^{1/p^s}).
\]
在 \(C\) 上，这个扩张是循环 Kummer 扩张，令 \(\alpha=u^{1/p^s}\)。任取其内的 \(\beta\) 满足 \(\beta^{p^s}=v\)。扩张群在 \(\alpha,\beta\) 上的作用各给一个到 \(\mu_{p^s}\) 的字符。\(\alpha\) 的字符忠实，故 \(\beta\) 的字符是它的第 \(a_s\) 次幂（扩张次数也可以小于 \(p^s\)）。于是 \(\beta/\alpha^{a_s}\in C\)，对 \(v/u^{a_s}\) 应用刚证的下降公式。取对数（取得的 \(k\) 中之根是单位）得
\[
 p^c(y-a_s x)\in p^s L_k,\qquad
 y\in\mathbb Z_p x+p^{s-c} L_k\quad(s\ge c).
\]
所有右侧的交就是 \(\mathbb Z_px\)，因为它是有限秩格中的闭子模。故 \(g\) 保持**每一条**由 \(x\) 生成的直线。对 \(L_k\) 的一组基及两两基向量之和应用此结论，全部对角系数相等。保格且可逆使共同系数属于 \(\mathbb Z_p^\times\)。再对每个有限 \(D/k\) 以 \(D\) 为基域重复论证，其全部更高层单位格也在原条件之内。所得标量在 \(k\) 上必须一致。反向，每个 \(\lambda\in\mathbb Z_p^\times\) 的乘法与 Galois 作用交换并保持每个 \(L_D\)，故具体算术实现上的这个固定群正是 \(\mathbb Z_p^\times\)。

由此得到对原比较有方向的结论。固定原局部 Galois 群后，任意 Ind2 在一个局部加法因子上都只乘范数 1 的标量。张量各槽后，每个域投影的绝对值逐点保持。因此在已给定的算术实化间，两条覆盖同一群箭头、在单位格全塔上相容的线性同构，给**完全相同**的各坐标半径（取一条的逆和另一条复合）。§12.4 的 \(-19,-21\) 两个原始赋值经这种固定群 Ind2 精确保留。这个结论还给出一个本文前面宽松估计看不出的取舍。§12.7 在 \(s\mid B\) 所用的逆理想有正半径增益，固定群的 Ind2 在该处贡献恰为零，单靠选一个整格矩阵不能产生该增益。改变群识别的 Ind1、一次单位 log-link 与标记乘数的相互位置，以及全局算术线的局部化仍有独立的数学内容。[III 对 Ind1 与 Ind2 各自的定义](IUT-TEXT/III.txt#L9257)

对一条给定群同构还能从此证明中抽出一个具体的检验。写 \(D_s(u)=k(\mu_{p^s},u^{1/p^s})\)，\(W_s(u)=L_k\cap p^sL_{D_s(u)}\)。上面的下降证明对每个 \(y\in W_s(u)\) 逐层适用，给出
\[
 \mathbb Z_p\log u\ \subseteq\ W_s(u)\
 \subseteq\mathbb Z_p\log u+p^{s-c}L_k\quad(s\ge c),\qquad
 \bigcap_{s\ge1}W_s(u)=\mathbb Z_p\log u .
\]
左右夹住的是带长度的循环 \(\mathbb Z_p\)-子模。即使 \(\log u\) 可被 \(p\) 整除，也能恢复其整除次数。给定 \(\sigma:G_k\to G_{k'}\)，在目标取 \(\sigma(G_{D_s(u)})\) 的固定域 \(D'_s\)，便可直接构造 \(W'_s=L_{k'}\cap p^sL_{D'_s}\)。任一实现在单位格全塔上的箭头 \(g\) 都满足 \(W'_s=g W_s(u)\)，因而这些格的交精确恢复 \(\mathbb Z_p g(\log u)\)。

**把标记乘数也编码成开子群。** 在源中实际算 \(y=r^{j^2}\log u\)。取 \(M\) 使 \(v_p(p^M y)>1/(p-1)\)，令 \(w=\exp(p^M y)\)。用 \(D_s(w)\) 的开子群走同一条 \(\sigma\)，再将所得目标格除以 \(p^M\)，就恢复带标记的循环子模，误差包含于 \(p^{s-c-M}L_{k'}\)。这一步只在源中做一次乘法，目标上只需取有限扩张的单位格交、乘有理标量，故即使 \(g\) 不保乘法也适用。它编码的是**所选候选向量的像**。要作为原 Θ 输出，还须沿同一个原 pilot 的 evaluation 取得这条群箭头及其允许选择。

§12.4 的第二行甚至可以给出单一的有限精度。对 \(x=\log(1+\pi)\)，\(v_k(r^4x)=1\)，取 \(M=1\)，\(w=\exp(3r^4 x)\)。\(k\) 的绝对分歧指数 10 与 3 互素，且含 \(\zeta_3\)，故 \(k\cap\mathbb Q_3(\mu_{3^\infty})=\mathbb Q_3(\zeta_3)\)，上面的 \(\gamma\) 可取圆分特征为 4，即 \(c=1\)。现在只取 **\(s=6\)**。两份非标记槽计算 \(W'_6(u)\)，标记槽计算 \(3^{-1}W'_6(w)\)，允许各槽自己的群识别和同一 \(k\) 的目标副本。前两槽的误差在 \(3^5L_{k'}\subseteq\mathfrak m^{39}\)，后一槽的误差在 \(3^4L_{k'}\subseteq\mathfrak m^{29}\)。前两槽的整个近似格在 \(L_{k'}\subseteq\mathfrak m^{-11}\)，后一槽在 \(3^{-1}L_{k'}\subseteq\mathfrak m^{-21}\)。展开三因子乘积，在任一域投影下，每个含误差的项赋值至少为 \(\min(39-11-21,29-11-11)=7\)。这里 \(k/\mathbb Q_3\) 是 Galois 扩张，三重张量的每个域因子都是 \(k\) 的副本。故三个近似格的乘积与真正三个循环子模的乘积在 \(k/\mathfrak m^4\) 里给出同样的加法子模。源端恒等识别下，生成向量的赋值是 \(-21\)，其类确实非零。这样一般 Ind1 的一次具体候选可以在**两个指名的 \(3^6\) 次开根扩张**的固定子群上检验；同一 \(u\) 在两个非标记槽出现。运输到哪里与运输的类有无足够大小，可分开检查。

### 12.9 目前原目标究竟走到哪里

§12.8 消除了固定群 Ind2 对有限位半径的选择依赖。§12.4 在具体源单位上把第一幂带标记 evaluation 的问题缩到了一个剩余类。§12.7 额外给出一个对任意深坏位都足额的全局整态射族，且它在所有有限位上的作用已算完。通向原 III.3.12 仍还有一项原对象识别。算术张量的成员、辅助算术线的局部格，都要在第 1 列得到原 evaluation 的见证。S3138 的单元素实数读数已经丢弃这些数据。对混合元组，§12.5 的最浅槽也须经保留标记的原映射检验。深度无界时，在 §12.7 这族上可以直接追 \(f_t\) 的三个局部化（3、\(s\mid B\)、无穷位）；任何声称给出该比较的原箭头，都必须解释其在 \(s\mid B\) 处的增益来源，或者展示从别处得到同额次数的另一条实际箭头。对一般输入还需原始全局构造。**本次未推出原 III.3.12 的全量词不等式**，整族有限性的独立状态见 §11.7。按要求仅作单线程自然语言推导，未编译 Lean，未运行目标类型或公理验收。



<a id="marked-unit-artin"></a>

## 13. 让第一幂标记作用在两个实际单位之间

本节比较原 III.3.12 的 \(h_q=-|\log q|\) 与 \(h_\Theta=-|\log\Theta|\)。在 §12.7 的曲线 \(E_0:y^2+xy=x^3+27\) 上，下面给出两个具体构造。第一个用原坏位 3 上的两个普通单位把第二行的标记作用做成交换图，并算出换列以后仍能保住的半径。第二个在指定为 good 的 2333 处，直接把中性生成元 \(1\) 送到范数足够大的位置，并追踪这一操作在非交换 Galois 群上实际做到哪一层。前者处理局部单位和标记的配合，后者允许两行通过另一个素数共同支付差额。原可能像的定义及行平均均沿用论文。[III.3.12 的对象与符号](IUT-TEXT/III.txt#L10326)

### 13.1 从实际局部群箭头构造全部单位运输

取同一有理素数 \(p\) 上两个算术局部域 \(k,k'\)，以及其绝对 Galois 群的一条拓扑同构 \(\sigma:G_k\to G_{k'}\)。允许它来自非几何的局部箭头。写 \(J_k=\operatorname{im}(I_k\to G_k^{\rm ab})\)。局部互反在单位上给出拓扑同构 \(\operatorname{Art}_k:\mathcal O_k^\times\to J_k\)。仓库有它在任意有限 \(k/\mathbb Q_p\) 的单位群上的双射、有连续性、还有有限扩张上的转移公式。这比旧交接中给出的供体范围更大。[单位与阿贝尔惯性子群](../LocalClassFieldTheory/Reciprocity/ArtinInertia.lean#L246) · [拓扑直积分解](../LocalClassFieldTheory/Reciprocity/GaloisStructure.lean#L13) · [转移公式](../LocalClassFieldTheory/Brauer/ArtinTransfer.lean#L246)

先在群内识别惯性，才可限制 \(\sigma^{\rm ab}\)。野惯性 \(P_k\) 是 \(G_k\) 的最大闭正规 pro-\(p\) 子群。为核实，取最大驯商，其惯性为 \(T=\prod_{s\ne p}\mathbb Z_s(1)\)，商为 \(\widehat{\mathbb Z}\)，Frobenius 按剩余域基数 \(q_0\) 乘在 \(T\) 上。这一描述来自先取全部非分歧扩张，再对均匀化元取所有素于 \(p\) 次根，所需单位根都在非分歧塔中。商在 \(T\) 上作用忠实，因为对每个 \(n>1\)，\(q_0\) 模 \(q_0^n-1\) 的阶恰为 \(n\)。任何闭正规 pro-\(p\) 子群与 \(T\) 的交换子都落在两者的交内，因而中心化 \(T\)，从忠实性知它在驯商内平凡。最后，该驯商的闭交换子群为 \((q_0-1)T\)，其中心化子恰为 \(T\)，因为乘 \(q_0-1\) 在 \(T\) 上单射。因此 \(I_k\) 是一个由群本身恢复的原像，\(\sigma\) 将它送到 \(I_{k'}\)。

对每个有限 \(D/k\)，取 \(D'\) 为 \(\sigma(G_D)\) 的固定域。在这两个实际单位群上定义
\[
 b_{\sigma,D}(u)=\operatorname{Art}_{D'}^{-1}
       \big((\sigma|_{G_D})^{\rm ab}(\operatorname{Art}_D u)\big).
 \tag{13.1}
\]
此逆只取在 \(J_{D'}\) 上。源的普通单位、挠单位及各有限层的拓扑都被带到目标。若 \(D\subset E\)，单位包含在 Artin 一侧对应群转移 \({\rm Ver}_{G_D}^{G_E}\)。转移由有限陪集置换及其乘积定义，故同 \(\sigma\) 交换。这证明 \(b_{\sigma,E}|_{\mathcal O_D^\times}=b_{\sigma,D}\)。对共轭子域用相同的计算和 Artin 的域同构自然性，得到 \(b_{\sigma,\gamma D}(\gamma u)=\sigma(\gamma)b_{\sigma,D}(u)\)。更换基点引入的内共轭由这条公式处理。于是
\[
 g_{\sigma,D}(\log u)=\log b_{\sigma,D}(u)
\]
在 \(L_D=\log\mathcal O_D^\times\) 上定义良好，因为对数的核恰是挠单位。这是连续格同构，延拓成 \(D\to D'\) 的 \(\mathbb Q_p\)-线性同构，随 \(D\) 相容。取并得到一条保全部开子群单位格的算术箭头。§12.8 的刚性还说明，同一 \(\sigma\) 的其他全塔单位商实现至多差一个 \(\mathbb Z_p^\times\) 标量。我们由此取得一个代表，也取得选代表对半径的影响。原论文从局部拓扑群恢复乘法幺半群的出处及仓库的单位商消费引理见下。[II 的局部群重构](IUT-TEXT/II.txt#L2044) · [Artin 的共轭自然性](../LocalClassFieldTheory/Reciprocity/ArtinNaturality.lean#L229) · [单位商进入实际对数像](../tmp/sheaf/xif/paper/Mzk1Ind1UnitQuotientActual.lean#L26)

这个构造的量词是每条**算术拓扑群箭头**。把它接入仓库时，源应取原位的 \(K_v\) 及其绝对 Galois 群，或用点化的局部 Galois 范畴取纤维函子，将箭头在有限覆盖上的作用送到这两个群。抽象的 DPrimeStripEquiv 只存两条群同构和投影方块，单靠该类型取得不了这些算术基点。已有 localDPrimeStrip 实例的基域是 \(\mathbb Q_p\)，本节的两个完备化分别有次数 40 和 120。[抽象 strip 及其箭头](../LeanFormal/IUT/IUTI/HodgeTheater/PrimeStripCore.lean#L24) · [现有有理素数实例](../LeanFormal/IUT/IUTI/HodgeTheater/LocalPrimePlaces.lean#L49)

### 13.2 用实际单位记录第一幂乘数

固定源的一个分裂生成元代表，在第 \(j\) 行写 \(a=r^{j^2}\)。这里的第一幂指取一次原 Θ-pilot，\(j^2\) 是该原生成元在第 \(j\) 个标签的本来指数。III.3.4(ii) 的竖箭头从 \((0,-1)\) 到 \((0,0)\)，它将 \((0,0)\) 的分裂乘数拉回前一层的对数环，在带标记槽乘法作用。单位端可在前一层取普通单位、走一次对数。横向只用 \((0,0)\to(1,0)\) 的一个 link。沿具体代表 \(g\) 在加法包运输以后，标记的线性作用是 \(g\,m_a\,g^{-1}\)，其中 \(m_a(x)=ax\)。这已确定如何算它，无须把 \(g\) 当成保持域乘法的箭头。[III.3.4(ii) 如何拉回分裂乘数](IUT-TEXT/III.txt#L5965) · [III.3.11(i)(b) 中的乘法作用](IUT-TEXT/III.txt#L9195) · [原证明规定的单位与值群两层](IUT-TEXT/III.txt#L10485)

在源域 \(k\) 内，置 \(L=\log\mathcal O_k^\times\)，\(D_a=L\cap a^{-1}L\)。取商 \(\mathcal O_k^\times/\mu(k)\)，对数给它与 \(L\) 的同构。于是每个 \(x=\log u\in D_a\) 对应唯一单位类 \([v]\) 使
\[
                 \log v=a\log u.
\]
两边都是满格的有限指数子群。在 \(v_k(ax)>e/(p-1)\) 时还有指定的普通单位代表 \(v=\exp(ax)\)，其中 \(e=v_k(p)\)。对这对单位分别应用 (13.1)，得到
\[
          \log b_{\sigma,k}(v)
             =(g_{\sigma,k}m_a g_{\sigma,k}^{-1})
                 \log b_{\sigma,k}(u).
 \tag{13.2}
\]
这是单位群中一条可实际执行的对应。其指数已经读出标记的精确倍率。以 \(L\) 的 Haar 体积为 1，则
\[
 \frac{[L:D_a]}{[L:aD_a]}=|N_{k/\mathbb Q_p}(a)|_p .
\]
因为乘 \(a\) 使 \(D_a\) 的体积乘 \(|\det m_a|_p\)。两个指数在同一箭头下不变。此数记录了乘数在单位对应里的模数。原 \(h_\Theta\) 还对实际输出区域取 holomorphic hull 及 procession 平均。[对数核与单位商](../LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithmKernel.lean#L83) · [原 hull 定义](IUT-TEXT/III.txt#L7662)

### 13.3 在 3 处的第二行，两个单位可以同时写出来

沿用 §12.7 的 \(t=0,\ell=5\)。写 \(k=K_w\)，\(v=v_k\)，\(\pi^{10}=3\)，\(\mathfrak m=(\pi)\)。绝对分歧指数为 10，剩余域为 \(\mathbb F_{81}\)，\([k:\mathbb Q_3]=40\)。原坏位标记有 \(v(r)=3\)，故第二行 \(a=r^4\) 满足 \(v(a)=12\)。这一赋值对该轨道的每个挠倍数都相同。

写 \(U_h=1+\mathfrak m^h,\ L_2=\log U_2\)。对 \(u=1+t\pi^h\)、\(t\) 为单位，逐项看对数级数。项序号 \(n\) 的赋值为 \(hn-10v_3(n)\)，在 \(v_3(n)=s\) 的各项中最低的由 \(n=3^s\) 取得。这给出下表，其中剩余维数相对于 \(\mathbb F_3\)。

| \(h=v(u-1)\) | 对数的首层 | 该层可取的剩余维数 |
|---|---|---|
| 1 | \(-11\) | 4 |
| 2 | \(-4\) | 4 |
| 3 | \(-1\) | 4 |
| 4 | \(2\) | 4 |
| 5 | 至少 \(5\) | 第 \(5\) 层为 3 |
| \(h\ge6\) | \(h\) | 4 |

前四行的首项唯一，首系数是剩余域的 Frobenius 幂，因而取遍剩余域。在 \(h=5\) 的两项给 \(\bar t+\bar t^3\)。其核有三个元素，因为 \(-1\) 在 \(\mathbb F_{81}\) 中有平方根。自 \(h=6\) 起指数与对数互逆，故 \(\mathfrak m^6\subset L_2\)。任一单位可先除去 Teichmüller 部分，它的对数为零，所以表也给出整个 \(L\) 的过滤。

现在对所有 \(u\in U_2\) 直接定义普通单位
\[
                       F_a(u)=\exp(a\log u)\in U_8 .
\]
确实 \(v(a\log u)\ge 12-4=8>5\)。这是群同态，且 \(\log F_a(u)=a\log u\) 精确成立。在 \(U_1\setminus U_2\)，\(v(a\log u)=1\)，表中没有赋值为 1 的非零单位对数。因此模掉挠后，\(D_a=L_2\)，这是完整的可用单位子群。特别取 \(u=1+\pi^2\)，则 \(\log u\) 的第 3 项唯一最低，赋值 \(-4\)。\(F_a(u)\) 的对数赋值为 \(8\)。实际单位三元组
\[
                       (u,\ u,\ F_a(u))
\]
的三个对数所成纯张量，在 \(k^{\otimes_{\mathbb Q_3}3}\) 的**每一个**分解域中的赋值都是 \(-4-4+8=0\)。原因是 \(k/\mathbb Q_3\) 为 Galois，每个分量都是三个共轭的乘积。原 q 的门槛是 3。这个点保留了等式 \(\log F_a(u)=r^4\log u\)，三个槽都由真正的普通单位给出。仓库已有定理将这样的实际单位元组送入未标记的算术张量区域。[单位张量的实际成员定理](../LeanFormal/IUT/IUTII/Kummer/SourceUnitLogTensorLanding.lean#L97)

### 13.4 对三条不同的运输，一个源单位仍可达到 q 门槛

令 \(g_1,g_2,g_3\) 是到同一算术 \(k\) 的三个副本的单位格运输，分别允许选择 (13.1) 及固定群的单位标量。以下证明只用每个 \(g_i\) 是把 \(L\) 送满相应 \(L\) 的 \(\mathbb Q_3\)-线性同构。先证对 \(i=1,2\)，\(g_i(L_2)\) 有非零元素的赋值至多为 \(-4\)。由表，\(L_2=L\cap\mathfrak m^{-10}\)，它在 \(L\) 中的指数为 \(3^4\)。若 \(g_i(L_2)\) 有元素离开目标 \(L_2\)，它的赋值便是 \(-11\)。若全在其中，两格指数相同，所以相等，目标 \(L_2\) 本身取到 \(-4\)。

标记槽必须把 \(g_3(aL_2)\) 算到赋值 11 才足够。写 \(Z=aL_2\subset L\)，在 \(L/3L\) 中比较两个具体子空间。上表平移 10 给出 \(3L\) 在 16 以下的非零首层为 \(-1,6,9,12,15\)，维数分别为 \(4,4,4,4,3\)，且 \(\mathfrak m^{16}\subset3L\)。于是
\[
 \dim_{\mathbb F_3}((\mathfrak m^{12}+3L)/3L)
      =(4-4)+(4-0)+(4-0)+(4-3)=9 .
\]
另一方面，\(Z\) 在第 \(8,11,14\) 层都取得完整的四维剩余空间，来源分别是 \(a\log U_h\) 的 \(h=2,3,4\) 层。这三层在 \(3L\) 中均无首项。从每层拖出四个首系数独立的元素，任何模 3 非平凡的组合在最低涉及的层有非零首项，所以它们在 \(L/3L\) 中独立。因此
\[
                   \dim_{\mathbb F_3}((Z+3L)/3L)\ge12>9 .
\]
任意 \(g_3\) 都保持这个维数，故 \(g_3 Z\) 无法全部落入 \(\mathfrak m^{12}\)，它有元素的赋值至多为 \(11\)。

还要用同一个 \(u\) 同时实现这三项。在 \(L_2\) 中，导致前两槽各自赋值大于 \(-4\)、第三槽赋值大于 \(11\) 的三个集合分别是真开加法子群。每个都包含于一个模 3 超平面的逆像。\(d\) 维 \(\mathbb F_3\) 空间的三个过零超平面的并至多有 \(1+3(3^{d-1}-1)<3^d\) 个元素。选并集外的 \(x=\log u,\ u\in U_2\)，令 \(v'=F_a(u)\)。于是在每个分解域都有
\[
          v_k\big(\operatorname{pr}
              (g_1 x\otimes g_2 x\otimes g_3\log v')\big)
                    \le -4-4+11=3 .                    \tag{13.3}
\]
这给出第一幂第二行单位作用图在各因子上至少 \(-3\log(3)/10\) 的带符号半径，正好达到同一坏位的 q 读数。该结论对三条运输逐组成立，源单位允许随这组运输而选，两个未标记槽仍共用同一单位。

实际交接只需保留单位类模 \(81\) 次幂及挠群。三项真对数都在 \(L\subset\mathfrak m^{-11}\) 中，更换任一类代表带来的误差在 \(81L\subset\mathfrak m^{29}\)。每个含误差的三因子积的赋值至少 \(29-11-11=7\)。故同一个目标类在 \(k/\mathfrak m^4\) 中完全确定。用 (13.1) 可以在阿贝尔惯性群模挠及 \(81\) 次幂的有限商上直接运输两份 \(u\) 和一份 \(F_a(u)\)。式 (13.3) 已证明可得到非零类，§12.8 所用的两个 \(3^6\) 次开根扩张在此例可以省去。

### 13.5 对照原 evaluation，剩下的是哪一种成员关系

这一行已经有三个不同层次的实物。第一，选定的一次 Θ 的分裂生成元 \(a=r^4\)。第二，第 0 列一次竖移的单位 \(u\) 和 \(F_a(u)\)，以及由 (13.2) 运输的标记作用等式。第三，未标记算术单位区域里实际存在的三槽向量及其非零剩余类。第 1 列原 \(h_\Theta\) 对应的是指定 Θ-pilot 的允许像之并。III.3.5(ii)(a) 把单位像送入容器，(c) 提供分裂幺半群的作用；III.3.10.2 的 evaluation 则从 env 到 gau，再进 LGP 和 lgp。逐一查这几条箭头，得到的是乘数及作用，尚未得到“取任一上述单位三元组的作用值便得到该 pilot 的一个允许输出”这条集合包含。[单位像及分裂作用](IUT-TEXT/III.txt#L6078) · [原 evaluation 各箭头](IUT-TEXT/III.txt#L9116) · [原输出须可解释为 prime-strip 的区域族](IUT-TEXT/III.txt#L10412)

可以用刚算出的具体点判别这里的差异。取恒等算术坐标和 \(u=1+\pi^2\)。原生的第零次迭代参考理想 \( (1\otimes1\otimes a)\widetilde R\) 在每个域因子上赋值至少为 \(12\)，而该三元组的投影赋值为 \(0\)。把二者直接认作同一输出，在这个点上就会算错。要让一次迭代承担这份差额，应该从同一份原 pilot 的分式理想实现出发，在 III.3.10.2 方块中跟踪它的单位区域及标记，先将该**区域**作原允许的 Kummer 求值，再在第 1 列投到 \(k/\mathfrak m^4\)。此时有一项具体比较可做，即在这个有限精度下，将所得集合与 (13.2) 的图对照。任一在每个因子投出非零类的合法选择已经够用，各因子可取不同见证。S3139 的 possible image 在此接口取值为实数集合，不能从中反推张量坐标；仓库的非零标签模型另有“并等于第一行区域”的定理，原文保留第二行的 \(r^4\) 与原权重，两者有各自的消费者。[S3139 的返回类型](../tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean#L75) · [非零标签模型的第一行归约](../tmp/sheaf/xif/paper/Mzk1URThetaHullNonzeroActual.lean#L183) · [原文分别处理两列的区域](IUT-TEXT/III.txt#L11408)

还可以从第零次参考理想内的**实际点**逼近上面的向量，把所需的归一化算清。仍取 \(u=1+\pi^2,\ w=F_a(u),\ x=\log u\)。令
\[
 z=u^9-1,\quad z'=w^9-1,\quad
 C=z\otimes z\otimes az .
\]
这里 \(az=au^9-a\) 来自同一个原生标记理想的两个点，故 \(C\in(1\otimes1\otimes a)\widetilde R\)。直接展开得 \(v(u^3-1)=6\)，再立方得 \(v(z)=16\)。由于 \(w\in U_8\) 且 \(v(w-1)=8\)，同理 \(v(z')=28\)。在赋值至少 16 的球上，对数级数去掉线性项后的赋值至少是输入赋值的两倍。因此
\[
 v(z/9-x)\ge12,\qquad v(z'/9-ax)\ge36,\qquad
 v(az/9-z'/9)\ge24 .
\]
逐项展开，在每个域因子中 \(3^{-6}C\) 与 \(x\otimes x\otimes ax\) 的差赋值至少为 \(16\)：未标记槽的误差至少贡献 \(12-4+8\)，标记槽的误差至少贡献 \(24-4-4\)。这样，两组实际单位给出的向量甚至可由同一原生理想中的一个明确整张量，在指定归一化后重现到远高于所需的精度。\(v(\operatorname{pr} C)=60\)，除以 \(3^6\) 才降为零。这指出直接用原生理想作差的确切代价。允许像的 hull 对整倍数及加法稳定，向相反方向除以 \(3^6\) 需要来自原箭头的依据。III.3.9.6 对足够小的区域比较 log-volume，与把这个倍数在固定理想内约去是两个不同断言。[小区域的度量相容范围](IUT-TEXT/III.txt#L8634)

### 13.6 换一个地方支付差额，直接使用中性元 \(1\)

仍取同一曲线。\(1+432\cdot27=11665=5\cdot2333\)，\(p=2333\) 是素数（试除不超过 47 的素数即可）。这是有乘性约化而在原初始数据中标为 good 的位。此处 Θ 的局部参考是中性整格，所以可用其具体点 \(1\) 测试局部箭头。因 \(v_p(\Delta)=1,\ c_4=1\)，Tate 参数 \(q_p\) 有 \(v_p(q_p)=1\)。该结点分裂，因为 \(-c_6=1+864\cdot27\equiv-1\bmod p\)，而 \(p\equiv1\bmod4\)。\(i\) 已在 \(\mathbb Q_p\) 内。由 Tate 的 30-扭点描述，指定完备化为
\[
 k=\mathbb Q_p(\mu_{30},\varpi),\qquad \varpi^{30}=q_p .
\]
\(2333\equiv23\bmod30\) 的乘法阶为 4，故 \(k_0=\mathbb Q_p(\mu_{30})\) 非分歧次数为 4；在 \(k_0\) 上 \(X^{30}-q_p\) 为 Eisenstein，故 \(k\) 的 \(e=30,\ f=4\)。记 \(\mathfrak n=(\varpi)\)。这里 \(e<p-1\)，所以 \(L=\log\mathcal O_k^\times=\mathfrak n\)，指数和对数在全部主单位上互逆。在 \(L/pL\) 中
\[
                 S=p\mathcal O_k/p\mathfrak n
\]
是维数 4 的子空间。对任何保 \(L\) 的线性同构 \(g\)，有 \(g(\mathcal O_k)=\mathcal O_k\) 当且仅当 \(\bar g S=S\)，因为将两边乘 \(p\) 再模 \(p\mathfrak n\) 恰得到这项判别。

选 \(\mathcal O_{k_0}\) 的一组 \(\mathbb Z_p\)-基 \(\omega_1=1,\ldots,\omega_4\)。\(L\) 的一组基由 \(p\omega_s\) 和 \(\varpi^t\omega_s\ (1\le t\le29)\) 构成。取整线性变换
\[
                 b(p)=p+\varpi,\qquad
                 b(z)=z\quad\text{对其余基向量}.
 \tag{13.4}
\]
逆变换只需减去 \(\varpi\)。它也保持绝对迹，因 \(X^{30}-q_p\) 的次高系数为零，\(\operatorname{Tr}_{k/k_0}(\varpi)=0\)。如果只知道 (13.4) 在 \(L/pL\) 上的作用，仍有 \(v_k(g(1))=1-30=-29\)，因为 \(p g(1)=p+\varpi\bmod p\mathfrak n\)。这样每个中性槽的范数收益是 \((29/30)\log2333\)。对两个或三个槽同时取这同一个算术作用，各域投影的乘积都取到相应收益。两行平均是 \((29/12)\log2333\)。甚至只把 \(1\) 移出整格**一个**赋值层，若两行逐槽都这样做，平均也有 \(\log2333/12\)。另一方面，3 处原生第零次参考的两行平均为 \(-\frac{1+4}{2}\frac3{10}\log3\)，与当地 \(h_q=-\frac3{10}\log3\) 的差额仅 \(\frac9{20}\log3\)。因 \(2333>3^6\)，一个层的平均已足额。这项核算在原行数、槽数和 q 归一化下完成。下面检验 (13.4) 的来源。

**先提升到整个最大 pro-\(p\) 商。** 写 \(G=G_k,\ P=G_k(p)\)。局部对偶给 \(H^2(G,\mathbb F_p)\) 的对偶为 \(\mu_p(k)\)；这里 \(\mu_p(k)=1\)，因为含本原 \(p\) 次单位根的域的绝对分歧指数是 \(p-1\) 的倍数。令 \(N=\ker(G\to P)\)。\(H^1(N,\mathbb F_p)^P=0\)，否则一个非零不变字符的核正规于 \(G\)，由此得到比 \(P\) 更大的 pro-\(p\) 商。五项正合列给 \(H^2(P,\mathbb F_p)=0\)。局部互反给 \(P^{\rm ab}\simeq\mathbb Z_p^{121}\)，其中一维来自赋值，其余 120 维来自 \(L\)。[仓库的二次局部对偶](../LocalClassFieldTheory/Duality/DualityDeg2.lean#L589) · [赋值与单位的拓扑直积](../LocalClassFieldTheory/Reciprocity/GaloisStructure.lean#L13)

这里可直接说明 \(P\) 为什么是自由 pro-\(p\) 群。将模 Frattini 商 \(P/\overline{P^p[P,P]}\) 的基提升为生成元，以它们取极小自由满射 \(F\to P\)，设核为 \(R\)。若 \(R\ne1\)，可在 \(F\) 的某个有限 \(p\) 群商中看见其非平凡像 \(R_0\)。有限 \(p\) 群作用在 \(R_0/\Phi(R_0)\) 的非零对偶空间上有非零不变向量（对向量计固定点数模 \(p\) 即可）。拉回得到非零的 \(F\)-不变字符 \(R\to\mathbb F_p\)。极小性以及五项正合列却给 \(H^1(R,\mathbb F_p)^P\hookrightarrow H^2(P,\mathbb F_p)=0\)。故 \(R=1\)。现在选择自由基，令 \(x,y\) 在阿贝尔化中分别对应 \(\operatorname{Art}_k(\exp p)\) 与 \(\operatorname{Art}_k(\exp\varpi)\)，其余基元对应上面选的单位基与一个均匀化元。其像模 Frattini 构成基，因此可作这样的选择。自由基替换
\[
                  x\longmapsto xy,\qquad y\longmapsto y
\]
并固定其余基元；逆替换为 \(x\mapsto xy^{-1}\)。这给出 \(P\) 的实际连续自同构，阿贝尔化后恰为 (13.4)，且固定非分歧 \(\mathbb Z_p\) 商。因而 (13.4) 及它对 \(1\) 的效果，已经通过整个无限非交换 pro-\(p\) 塔的相容性检验。

**再保留整个驯分歧商。** 记 \(k(p)\) 为最大 pro-\(p\) 扩张，\(k^{\rm t}\) 为最大驯扩张。其交是非分歧 \(\mathbb Z_p\) 扩张，因为驯惯性的有限阶都素于 \(p\)。合成域的 Galois 群为
\[
 \operatorname{Gal}(k(p)k^{\rm t}/k)
    = P\times_{\mathbb Z_p}\operatorname{Gal}(k^{\rm t}/k).
\]
在左因子用上述基替换，右因子用恒等，就得到这个混合商的一条实际自同构。它同时保留全部驯惯性、Frobenius 商和 (13.4) 的首层作用。

**有非平凡驯作用的野层也可提升一批。** 任选次数素于 \(p\) 的有限 Galois 扩张 \(K'/k\)，且 \(\mu_p(K')=1\)，记 \(\Delta=\operatorname{Gal}(K'/k)\)。例如取非分歧二次扩张。相同的二次对偶证明 \(F'=G_{K'}(p)\) 自由。群 \(\operatorname{Gal}(K'(p)/k)\) 是 \(F'\) 被 \(\Delta\) 扩张，素于 \(p\) 的补群可选，故可写成 \(F'\rtimes\Delta\)。令 \(W=F'/\Phi(F')\)。余不变量 \(W_\Delta\) 经包含映到 \(P/\Phi(P)\) 是同构，因为 \(\Delta\) 阶素于 \(p\)，该半直积给出所有 \(k\) 上的指数 \(p\) 字符。由平均投影，\(W^\Delta\simeq W_\Delta\)。把 (13.4) 的模 \(p\) 作用放到 \(W^\Delta\)，在平均投影的核取恒等，得到与 \(\Delta\) 交换的线性同构 \(A\)。

将 \(A\) 提升到 \(\operatorname{Aut}(F')\) 可通过自由基替换完成。还可安排提升与 \(\Delta\) **确切交换**。约化 \(\operatorname{Aut}(F')\to{\rm GL}(W)\) 的核为 pro-\(p\) 群：在各特征的有限 \(p\) 群商上，恒等作用于 Frattini 商的自同构群是 \(p\) 群，例如沿下 \(p\)-中心列过滤，逐层核嵌入 \(\mathbb F_p\) 线性映射群。取一个提升 \(h\)。在 \(\operatorname{Aut}(F')\times\Delta\) 中，原 \(\Delta\) 作用的图与其经 \((h,1)\) 共轭的图，都在模 Frattini 后给同一个图；它们是这个图的原像中阶素于 \(p\) 的两个补群，故由上述 pro-\(p\) 核的一元共轭。这里的补群存在及共轭可在有限商上逐个极小正规初等阿贝尔 \(p\) 层提升：对 \(\Delta\) 平均使这类系数的正次数上同调消失，再由紧性取相容解。用该核元修正 \(h\) 即得所需的提升，和 \(\Delta\) 上的恒等一起作用于 \(F'\rtimes\Delta\)。例如在非分歧二次层，\(F'\) 的秩为 \(241\)。至此在每个上述混合商上，实际自同构都给中性元 \(1\) 所需的同一个模 \(p\) 检验，各商之间尚未选出共同的全群提升。

### 13.7 进入含 \(\mu_p\) 的圆分层，实际通过第一个带关系的商

令 \(K'=k(\mu_p)\)，\(\Delta=\operatorname{Gal}(K'/k)\)，\(\chi:\Delta\to\mathbb F_p^\times\) 为非平凡圆分特征。取平凡系数 \(H=H^1(G_{K'},\mathbb F_p)\)。固定 \(\mu_p\) 的一个生成元时，\(H^2(G_{K'},\mathbb F_p)\) 是 \({\rm Br}(K')[p]\) 扭以 \(\chi^{-1}\)，局部不变量在域自同构下不变。因此 cup 配对是取值于特征 \(\chi^{-1}\) 的非退化交替配对。它把 \(H^\Delta\) 与 \(H_{\chi^{-1}}\) 完美配对，其余特征空间同这两者正交。这里 \(p\) 为奇素数，且 \(\Delta\) 的阶整除 \(p-1\)，所以特征空间分解在 \(\mathbb F_p\) 上成立。限制把 \(H^1(G_k,\mathbb F_p)\) 识别为 \(H^\Delta\)。在它上面取 (13.4) 的字符拉回，在配对的 \(H_{\chi^{-1}}\) 上取相对于该配对的逆转置，其余部分取恒等，得到与 \(\Delta\) 交换且保持 cup 的 \(A\)。[一次局部对偶](../LocalClassFieldTheory/Duality/General.lean#L280) · [二次 Kummer 与 Brauer 不变量](../LocalClassFieldTheory/Brauer/KummerH2.lean#L12)

再核实 \(p\) 次幂的信息。令 \(\kappa=(\chi_{p^2}-1)/p\bmod p\) 为 \(G_{K'}\) 上的加法特征。它来自 \(G_k\) 上将圆分特征先除以其模 \(p\) 值的 Teichmüller 提升，再取同一公式所得的特征。剪切加入的基向量对应 \(\exp(\varpi)\)。其到 \(\mathbb Q_p\) 的范数为 \(\exp(\operatorname{Tr}\varpi)=1\)。由 Artin 的范数相容性，这个基向量在 \(\mathbb Q_p(\mu_{p^2})\) 上作用平凡，故 \(A\kappa=\kappa\)。平凡系数的 Bockstein \(\beta:H\to H^2(G_{K'},\mathbb F_p)\) 满足 \(\beta(z)=-\kappa\smile z\)（左作用上链约定）。确实，由 \(p\) 次幂诱导的 \(H^1(K',\mu_{p^2})\to H^1(K',\mu_p)\) 在 Kummer 坐标中就是从模 \(p^2\) 次幂到模 \(p\) 次幂的满射。相应短正合列的连接映射因此为零，系数在 \(\mu_{p^2}\) 上的作用 \(1+p\kappa\) 给通常的 Bockstein 多出 \(\kappa\smile z\)。这就证明 \(A\) 同时保持 \(p\) 次幂关系。[Artin 的范数公式](../LocalClassFieldTheory/Reciprocity/NormCompat.lean#L416)

这两项计算能提升为一个真正的非交换有限群自同构。令 \(Q=G_{K'}(p)\)，\(Q_2=\overline{Q^p[Q,Q]}\)，\(Q_3=\overline{Q_2^p[Q,Q_2]}\)，\(V=Q/Q_2,\ M=Q_2/Q_3\)。中心扩张 \(1\to M\to Q/Q_3\to V\to1\) 的关系可直接读出。五项正合列将 \(M^*\) 经转移上同调中的 transgression（即中心扩张的推前类，符号不影响子空间）识别为
\[
         \ker\!\big(H^2(V,\mathbb F_p)\longrightarrow H^2(Q,\mathbb F_p)\big).
\]
理由是 \(H^1(V)\to H^1(Q)\) 为同构，而 \(Q_2\) 上的不变字符正是 \(M^*\)。同 §13.6 的最大 pro-\(p\) 商论证，\(H^2(Q,\mathbb F_p)\) 单射到 \(H^2(G_{K'},\mathbb F_p)\)。有限初等阿贝尔 \(p\) 群 \(V\) 的二次类由一次字符的 cup 及 Bockstein 张成：在一个中心 \(\mathbb F_p\)-扩张中，选基的提升，所有交换子和 \(p\) 次幂决定该扩张。交换子给交替形式，\(p\) 次幂给线性形式（\(p\) 为奇数）；基底的各对 cup 和各个 Bockstein 正好给这些坐标的基。因此上面实际算过的 \(A\) 保持所示的核，并在 \(M^*\) 上诱导可逆作用。

对原扩张类逐个用 \(M\to\mathbb F_p\) 推前，所得正是这个 transgression。故在 \(M\) 上取相应的对偶作用，便使原 \(M\)-值扩张类在两端的变换下相容。有限维系数分量可分离所有二次类，由中心扩张分类即得 \(Q/Q_3\) 的自同构。它可修正到与 \(\Delta\) 确切交换：在 \(V\) 上为恒等的提升固定由交换子和 \(p\) 次幂生成的 \(M\)，其核嵌入 \({\rm Hom}(V,M)\)，是 \(p\) 群，故可用 §13.6 的素于 \(p\) 补群共轭。与 \(\Delta\) 的恒等合成后，就在 \((Q/Q_3)\rtimes\Delta\) 上实际得到了指定的模 \(p\) 剪切。该商同时检验了圆分作用、对偶配对、交换子和第一层 \(p\) 次幂。

### 13.8 全群与原输出的下一项检验

3 处的待检对象是 §13.5 的 **pilot 分式理想在原 evaluation 下的区域像**，精度为模 \(\mathfrak m^4\)。2333 处已可越过 §13.7 的 \(Q/Q_3\)。可从 \(Q_4=\overline{Q_3^p[Q,Q_3]}\) 入手，在 \(Q/Q_4\to Q/Q_3\) 的中心扩张类上检验提升。允许调整前一层提升在 \({\rm Hom}(V,M)\) 中的分量，可以保持对 \(1\) 的所需半径。这是一项带参数的扩张类相容问题，(13.4) 及其已检验的杯积关系提供具体输入。对其他有限混合商还要使选择相容。

具体的全群判据如下。取 \(N_m\) 为 \(G_k\) 的全部指数至多 \(m\) 的开子群之核芯的交。局部域有界次数扩张只有有限多个，故 \(N_m\) 开、特征且余终。也可先交上 \(G_k\to G_k^{\rm ab}/p\) 的核，使最低层直接保留 (13.4) 的检验。对每层记录诱导指定模 \(p\) 剪切的自同构，连边记录自然投影下的相容。每一层是有限集合；各商上的自同构保持较低层对应的特征核，或在记录时直接加上这些投影的相容条件。若每个有限高度均有一段相容提升，有限分支树有无限分支，极限就是整条 \(G_k\) 上的连续自同构及其连续逆。这明确了 §13.6 还没有检查的量词。即便获得这一局部自同构，原证明还须把它放进指定 procession 的真实箭头，核对中性区域在各行的同一次原表示，并保留其他位的参考。它对 \(E_0\) 的数值收益已经足额；对 §12.7 的无界深度族及一般初始数据，还要分别取得全局足额的收益。

**原目标的当前状态。** 第二行的单位作用图已经有达到 q 门槛的实际点，且一般算术局部箭头的单位实现已有 (13.1)。另一路在另一素数的多个真正 Galois 商上做出了足额剪切。尚未把前一个点登记为原 pilot 在第 1 列的允许像，也未把后一个剪切提升到原全过程。因此本节没有推出对全部初始数据的 \(h_q\le h_\Theta\) 或 ABC。整族的实数有限性仍按 §11.7 区分。以上为单线程自然语言证明和源文件核对，四项形式验收均未运行。

<a id="native-ideal-galois"></a>

## 14. 从原标记理想出发，构造能改变两行半径的 Galois 运输

2026-11-19（上海）。沿用 §12.7 的曲线 \(E_t:y^2+xy=x^3+3^{3+30t}\)、\(\ell=5\)、指定坏位 3。以下构造保留第 0 列第一幂的 \(r_t,r_t^4\)，逐行使用原来的两个、三个槽，在第 1 列同一全纯坐标内比较。结论有两个不同的适用范围。**源点**已在带标记的原生算术理想中。使它们达到所算半径的**箭头**已在 §14.5 指明的无限 Galois 商上构造。原 Ind1 的局部对象还看全部有限扩张。§14.6 给出它具体多检验了什么。[原初始数据和两列端点](IUT-TEXT/III.txt#L10326) · [原局部分式理想与 Θ-pilot](IUT-TEXT/III.txt#L6596)

### 14.1 沿 evaluation 找回共同的单位，再改从标记理想取点

在同一坏位的同一算术实现里，固定 II.3.5(ii) 的 value-profile。第一幂纤维的点有形状 \(y_j=s\,\zeta_j r^{j^2}\)，各行共享一个普通单位 \(s\)，\(\zeta_j\in\mu_{2\ell}\)。两行时，\(y_1^4/y_2=(\zeta_1^4/\zeta_2)s^3\)，所以 \(\log(y_1^4/y_2)/3=\log s\)。即使在 3 处，分子也确实在 \(3\log\mathcal O^\times\) 中。三行及以上时，\(y_1^3y_2^{-3}y_3\) 已给出 \(s\) 的模挠类，因为 \(3-12+9=0\) 且 \(3-3+1=1\)。这些比值在源的乘法群内计算，log 只施于消去标记后得到的单位。结果给出第一幂纤维上逐点的逆读数。III.3.5(ii)(c) 在各列给的是标记的乘法作用，III.3.10.2 的箭头仍须按其定义求值。从这项逆读数尚推不出 §13.5 的混合张量属于第 1 列的允许像。下面直接使用原生理想中的点，绕开对那个混合张量的依赖。[第一幂的对角单位与整个 Gaussian 幺半群](IUT-TEXT/II.txt#L5985) · [分裂乘数的作用域](IUT-TEXT/III.txt#L6128) · [IPL 的复合次序](IUT-TEXT/III.txt#L9702)

在 3 处用 \(k=U(\pi)\)，\(U/\mathbb Q_3\) 为非分歧四次扩张，\(\pi^{10}=3\)。取 \(v(\pi)=1\)，故 \(v(3)=10\)，剩余域为 \(\mathbb F_{81}\)。记 \(d=3+30t\)、\(v(r_t)=d\)。行 \(j\in\{1,2\}\) 的标记在末槽，原生全纯参考为
\[
  J_{j,t}=\iota_j(r_t^{j^2})\,\widetilde R_s,\qquad
  s=j+1,\qquad \widetilde R_s=\prod_{\lambda}\mathcal O_{k_\lambda}
                  \subset k^{\otimes_{\mathbb Q_3}s}.
\]
其中 \(\lambda\) 遍历这个张量代数的域因子。该算术实现的每个因子都同构于 \(k\)。\(J_{j,t}\) 在各因子的赋值下界均为 \(j^2d\)。特别地，末槽属于 \(r_t^{j^2}\mathcal O_k\)、其余槽分别属于 \(\mathcal O_k\) 的纯张量已在其中。仓库固定元组的 possibleImages 正是先在全纯参考上乘标记、后施指定 \(\phi\)。故可单独验证源成员，再追 \(\phi\) 的算术来源。原文的 hull 逐域因子取最小包含盒，因子的归一化约定为乘 3 减去 \(\log3\)。[原结构层的逐域归一化](IUT-TEXT/III.txt#L6854) · [hull 的原定义](IUT-TEXT/III.txt#L7656) · [仓库中乘标记与运输的次序](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L668)

### 14.2 在当地的实际三次扩张里，选出必须配对的两个单位

取 \(U\) 中本原十次单位根 \(\zeta\)，令
\[
 u=\frac{1+\pi}{1+\zeta\pi},\qquad x=\log u,\qquad
 L=\log\mathcal O_k^\times .
\]
\(u\) 到 \(U\) 的范数为 1，因为分子分母共轭。\(v(u-1)=1\)。对数级数中，固定 \(v_3(n)=i\) 后第 \(n\) 项的最小可能赋值为 \(3^i-10i\)，只在 \(n=3^i\) 取到。跨 \(i\) 的最小值是在 \(n=9\) 取到的 \(-11\)。因此 \(v(x)=-11\)。同一计算对任何主单位给 \(L\subset\mathfrak m^{-11}\)，而 log 与 exp 在 \(\mathfrak m^6\) 互逆给 \(\mathfrak m^6\subset L\)。这里 \(\mathfrak m=(\pi)\)。

现在在 \(U_{14}=1+\mathfrak m^{14}\) 中构造一个与 \(u\) 的三次 Hilbert 符号非平凡的单位。令 \(E=k(t_0)\)，\(t_0^3=u\)，\(h=t_0-1\)。\(h\) 的方程 \(h^3+3h^2+3h+1-u=0\) 是 Eisenstein 方程。\(E/k\) 全分歧三次且循环，\(h\) 是均匀化元，\(\mathcal O_E=\mathcal O_k[h]\)。取本原三次单位根 \(\eta\) 和 \(\sigma(t_0)=\eta t_0\)。以 \(v_E(h)=1\) 计，\(v_E(\eta-1)=15\)，故 \(v_E(\sigma(h)/h-1)=14\)。由导数 \(3t_0^2\) 得 different 指数 30。迹对偶遂给
\[
 \operatorname{Tr}_{E/k}\mathfrak m_E^m
       =\mathfrak m^{\lfloor(m+30)/3\rfloor}.
\]
确实，迹理想包含于 \(\mathfrak m^a\) 等价于 \(\pi^{-a}\mathfrak m_E^m\subseteq\mathfrak D^{-1}\)，即 \(m-3a\ge-30\)。

写 \(N(1+z)=1+\operatorname{Tr}z+
 ((\operatorname{Tr}z)^2-\operatorname{Tr}(z^2))/2+Nz\)。
当 \(1\le v_E(z)=m<14\) 时，\(Nz\) 的 \(k\)-赋值为 \(m\)，其他项均高于 \(m\)。剩余域上的单位范数是立方，为双射。因此一个范数落入 \(U_{14}\) 的元素，本身属于 \(1+\mathfrak m_E^{14}\)。在第 14 级，写 \(z/h^{14}\bmod\mathfrak m_E=c\)，用 \(\pi^{14}\) 作输出单位，所得剩余映射为
\[
                  c\longmapsto Cc+Dc^3 .
\]
\(C\ne0\) 由上式在 \(m=14,15\) 的迹理想不同得到，\(D=\overline{N(h)^{14}/\pi^{14}}\ne0\)。中间的二次项赋值高于 14。令 \(\gamma\) 为 \((\sigma(h)/h-1)/h^{14}\) 的剩余类。它非零且属于这个多项式的核，因为 \(\sigma(h)/h\) 的范数是 1。因此其像正是 \(D\gamma^3\{w^3-w:w\in\mathbb F_{81}\}\)。括号内是到 \(\mathbb F_3\) 的迹零超平面，\(1\) 的迹为 \(4\bmod3=1\)。取 \(b\in\mathcal O_U^\times\) 为 \(D\gamma^3\) 的 Teichmüller 提升，置
\[
                    y=b\pi^{14},\qquad w=\exp(y).
\]
\((w-1)/\pi^{14}\) 的剩余类刚好在上述像外，所以 \(w\) 不是 \(E/k\) 的范数。由局部互反，\(\operatorname{Art}_k(w)\) 在 \(E\) 上非平凡，即 \(\langle\bar w,\bar u\rangle\ne0\)。这里的配对是选 \(\mu_3\simeq\mathbb F_3\) 后的 Hilbert 配对。另有 \(\operatorname{Tr}_{k/U}y=0\)，因为 \(10\nmid14\)，故 \(N_{k/\mathbb Q_3}w=1\)。这个构造同时给出了单位、系数及其配对，不需要猜剩余域中的某个好方向。[互反的范数相容](../LocalClassFieldTheory/Reciprocity/NormCompat.lean#L416) · [局部一次对偶的仓库入口](../LocalClassFieldTheory/Duality/General.lean#L280)

在 \(V=k^\times/(k^\times)^3\) 上写加法，取辛变换
\[
             A(z)=z+\langle z,\bar u\rangle\bar u .
             \tag{14.1}
\]
它保持交替配对和模 3 的赋值字符。它还保持模 9 圆分字符的一阶项，因为 \(N_{k/\mathbb Q_3}u=1\)，由互反，\(\operatorname{Art}_k(u)\) 在圆分塔上作用平凡。经互反把 \(V\) 识别为最大 pro-\(3\) 群的初等阿贝尔商。以下构造 (14.1) 的一条连续群自同构提升，并使它在整条非分歧 \(\mathbb Z_3\) 商上恒等。由此得到的对数格作用 \(g\) 满足
\[
             g(y)=y+c\,x \pmod{3L},\quad c\in\{1,2\},
             \qquad v(g(y))=-11 .                 \tag{14.2}
\]
最后一个等号只用 \(3L\subset\mathfrak m^{-1}\)。单位上的挠与互反的符号约定均不影响该赋值。

若要交接一个连 Teichmüller 提升都不必求的代表，可固定 \(i^2=-1\) 于 \(U\)，取 \(\eta=(-1+i\pi^5)/2\)。置 \(\alpha=\overline{(u-1)/\pi}=1-\bar\zeta\)。由 \(h^3/\pi\equiv\alpha\)、\(N(h)=u-1\)，有 \(D=\alpha^{14}\)、\(\gamma=(\bar i/2)\alpha^{-5}\)，因而 \(D\gamma^3=\bar i/(1-\bar\zeta)\)。于是直接取 \(b=i/(1-\zeta)\) 便给同一非范数类，仍有 \(\operatorname{Tr}_{k/U}(b\pi^{14})=0\)。§14.4 的源点可全部用这个显式 \(b\) 书写。

### 14.3 把第一层的变换提升到整个最大 pro-\(p\) 群

给出逐层修正的证明。这同时处理 3 处和 §13.7 的 2333 圆分层。设 \(D\) 是下文用到的有限 \(p\)-进域，\(p\) 为奇素数，\(\mu_p\subset D\)，且 \(D(\mu_{p^2})/D\) 是分歧的 \(p\) 次扩张。令 \(P=G_D(p)\)、\(V=P/\Phi P\)。给定 \(V\) 上的变换，使其字符拉回保持 cup 配对、Bockstein 以及非分歧字符模 \(p\)，其中在一维的二次上同调上取恒等。则它能提升成 \(P\) 的自同构，并保持**整值**非分歧商 \(\nu:P\to\mathbb Z_p\)。

**先辨认需要保持的关系。** 取极小自由 pro-\(p\) 满射 \(F\to P\)，核为 \(R\)。\(H^1(P,\mathbb F_p)=H^1(G_D,\mathbb F_p)\)，且 \(H^2(P,\mathbb F_p)\hookrightarrow H^2(G_D,\mathbb F_p)\)，理由见 §13.6 的五项正合列。局部对偶给后一空间维数 1，非零 cup 已来自 \(P\)，故前一空间也有维数 1。再对 \(F\to P\) 用五项列，得到 \((R/\overline{R^p[R,F]})^*\) 维数 1。取其对偶商的生成元的一个提升 \(r\in R\)。它正规生成 \(R\)。否则在除去 \(r\) 的闭正规包后，可在有限 \(p\) 群商中看到剩余关系群的非零像。该像的 Frattini 商的对偶有非零不变字符，拉回即与 \(r\) 已生成上述一维商矛盾。[局部二次对偶](../LocalClassFieldTheory/Duality/DualityDeg2.lean#L589) · [Kummer 二次类](../LocalClassFieldTheory/Brauer/KummerH2.lean#L12)

用下 \(p\)-中心列 \(F_1=F,\ F_{n+1}=\overline{F_n^p[F_n,F]}\)，写 \(L_n=F_n/F_{n+1}\)。记 \(\Pi:L_n\to L_{n+1}\) 为取 \(p\) 次幂，括号为交换子。\(L_1=V\)。在 \(L_2\) 中，\(r\) 的像为 \(\Pi a+\Omega\)，其中 \(a\in V\)，\(\Omega\in\bigwedge^2 V\)。这一公式可在每对自由生成元的交换子和每个生成元的 \(p\) 次幂上读出。将中心核逐一推到 \(\mathbb F_p\)，两类坐标分别由 cup 和 Bockstein 检出。因此 \(\Omega\) 非退化，而 \(a\ne0\)。后一项也可直接由 §13.7 的 \(\beta(z)=-\kappa\smile z\) 看出，其中 \(\kappa=(\chi_{p^2}-1)/p\) 非零。这个恒等式给 \(a=\pm\Omega^\sharp\kappa\)，符号取决于括号与关系生成元约定。给定变换保持 \(r\bmod F_3\)。选 \(V\) 的基使 \(a=e_1\)，用 \(x_i\) 记相应自由基。给定变换可先提升为 \(F\) 的一个自同构 \(h\)，并安排 \(\nu h=\nu\)。具体地，先提升各基像，使其 \(\nu\) 值模 \(p\) 正确，再乘某个 \(\nu\) 值为 1 的元的 \(p\mathbb Z_p\) 次幂，逐个将差改成零。Frattini 商可逆保证所得是自由群的自同构。

**逐层修正。** 已有 \(h(r)=r\bmod F_n\)，\(n\ge3\)。把 \(x_i\) 改为 \(x_i z_i\)，\(z_i\in F_{n-1}\cap\ker\nu\)，写 \(Z_i\) 为其在 \(L_{n-1}\) 的类。这个修改作用在 \(r\) 上，在 \(L_n\) 中给
\[
        \Pi Z_1+\sum_i[Z_i,Y_i].                  \tag{14.3}
\]
这里 \(Y_i\) 是由 \(\Omega\) 的系数矩阵得到的一组基，\(\operatorname{span}_{i\ne1}Y_i=\ker\kappa\)。公式可对 \(r\bmod F_3\) 的表达式逐项展开。替换对 \(F_m\) 的误差在 \(F_{m+n-2}\)，故 \(F_3\) 部分对本层无贡献。对 \(p\) 次幂展开时，一重交换子的额外系数 \(\binom p2\) 被 \(p\) 整除，其余项已落下一层。由同样的交换子运算，\(\Pi\) 在分次空间上线性，且 \([\Pi X,Y]=\Pi[X,Y]\)。这些等式用到 \(p\) 为奇数，包含 \(p=3\)。

下面验证 (14.3) 确实能消去**每个**误差。记 \(\mathcal L_b(V)\) 为长度 \(b\) 的普通迭代括号所张成的部分。由 \(F_{n+1}\) 的定义和上述等式，\(L_n\) 由 \(\Pi^{n-b}\mathcal L_b(V)\ (1\le b\le n)\) 张成。这里无需假定这些部分独立。从最长的 \(b\) 降至 3。因为 \(Y_i\) 是基，\(\mathcal L_b=[\mathcal L_{b-1},V]\)，取 \(Z_i=\Pi^{n-b}W_i,\ W_i\in\mathcal L_{b-1}\)，即可修正长度 \(b\) 的任一项。所伴随的 \(\Pi Z_1\) 只有长度 \(b-1\)，下一步继续修正。此处所有 \(W_i\) 都是交换子，可取 \(\nu=0\) 的提升。

余下长度 1 和 2。令 \(V_0=\ker(\nu\bmod p)\)。误差在阿贝尔化上的长度 1 系数属于 \(V_0\)，因为现有映射保持整条 \(\nu\)。先选 \(Z_1=\Pi^{n-2}v_1,\ v_1\in V_0\)，消去这项。保留 \(Z_1\) 的取值，用其余 \(Z_i=\Pi^{n-2}v_i,\ v_i\in V_0\) 修正长度 2。它们张成 \(\Pi^{n-2}[V_0,\ker\kappa]=\Pi^{n-2}\mathcal L_2(V)\)。确实，非分歧字符与分歧圆分字符 \(\kappa\) 独立。两个不同超平面的外积张成 \(\bigwedge^2V\)，取其交的基再各补一个向量即可验证。每个 \(v_i\) 都可选 \(\ker\nu\) 中的代表。取误差的负值代入 (14.3)，就把 \(h(r)\) 修到了 \(r\bmod F_{n+1}\)。逐次的修正恒等于模 \(F_{n-1}\)，所以在每个固定有限层最终稳定。下 \(p\)-中心列对有限生成自由 pro-\(p\) 群余终，极限及其逆给保持 \(r\) 的连续自同构。下降到 \(F/\overline{\langle\!\langle r\rangle\!\rangle}=P\)，即得所求。

在 \(k/\mathbb Q_3\) 上，(14.1) 是 Hilbert 配对的辛变换，因而其对偶保持 cup，而圆分字符固定给出 Bockstein 的相容。\(k\) 的分歧指数是 10，加入 \(\mu_9\) 的三次扩张确实分歧。(14.2) 遂成为**整个 \(G_k(3)\)** 上的一条实际自同构的单位读数。群上无穷多层均已包含在这一步里。

### 14.4 原生两行的精确读数，以及更深曲线还差多少

先给无需分解张量环的源点。第 \(j\) 行在前 \(j\) 个槽放 \(y/3\)，末槽放 \(3^{m_j}y\)，其中
\[
       m_1=3t-1,\qquad m_2=12t .
\]
前槽的赋值为 4，末槽的赋值分别是 \(30t+4\) 和 \(120t+14\)，均至少是各自的 \(j^2d\)。把末槽除以原标记后仍是整数。所以这两个纯张量属于**用普通整张量环生成的原标记理想**。沿同一个 \(g\) 在全部槽作用，所有域投影的赋值分别为 \(30t-42,\ 120t-53\)，因为 \(v(g(y)/3)=-21\)。特别是 \(t=0\) 时，仅在第二行末槽用 \(g\) 便足够。具体取 \(1\otimes1\otimes y\)，源末槽在 \(r_0^4\mathcal O_k\)，输出赋值为 \(-11\)，第一行可保留原参考。这避免了把某个 log 张量从标记理想外搬进来的步骤。

在论文的全纯参考 \(\widetilde R_s\) 上还可求得精确值。先定任一保持对数格的算术运输 \(g'\)，在匹配的 \(k\) 坐标中令
\[
     T_{g'}(m)=\min_{0\ne z\in\mathfrak m^m}v(g'z).
\]
对实际完整局部群箭头，互反保持单位，诱导的模 3 变换保持 Hilbert 配对至非零标量，并保持非分歧字符的核。§14.3 的 \(g\) 也具备这些性质。于是对这两种情形均有
\[
     T_{g'}(m)\ \ge\ -11+10\left\lceil\frac{m-14}{10}\right\rceil ,
     \qquad\text{而 §14.3 的 \(g\) 对每个 \(m\) 都取等。}        \tag{14.4}
\]
证明只需核对 \(6\le m\le15\)，因为 \(T_{g'}(m+10)=10+T_{g'}(m)\)。\(6\le m\le14\) 时，\(\mathfrak m^m\subset L\subset\mathfrak m^{-11}\)，而 (14.2) 在每个这样的理想上取到 \(-11\)。在 \(m=15\) 时需要再用一个算术事实。令 \(\lambda=\eta-1\)。对 \(s_0\in1+\mathfrak m^{15}\)，以 \(1+\lambda Z\) 开三次根，所得整系数方程的剩余方程为 \(Z^3-Z-\overline{(s_0-1)/\lambda^3}=0\)，其导数非零。故所有的根都在非分歧扩张中，且取常数项有非零绝对迹便得到真正的非分歧三次扩张。于是 \(U_{15}\) 在 \(k^\times/(k^\times)^3\) 中的像正是那条非分歧 Kummer 直线。它是单位超平面在 Hilbert 配对下的正交补，因此被上述变换保持。取对数即得 \(g'(\mathfrak m^{15})\subset\mathfrak m^{15}+3L\subset\mathfrak m^{-1}\)。\(3y\) 对所构造的 \(g\) 取到 \(-1\)，证毕。

在本例中，域因子皆为 \(k\)。阈值为 \(D_0\) 的全纯乘积理想，由所有满足 \(\sum_i m_i\ge D_0\) 的 \(\bigotimes_i\mathfrak m^{m_i}\) 在 \(\mathbb Z_3\) 上相加得到。一边的包含由逐因子赋值立得。反向包含可用整数幂等元验证。先用非分歧环的分解 \(\mathcal O_U^{\otimes s}\simeq\prod\mathcal O_U\) 分开非分歧因子。在每一块上，记 \(\pi_i\) 为第 \(i\) 槽的 \(\pi\)。比值 \(\pi_i/\pi_0\) 的十次幂为 1。以 \(\zeta\) 的各次幂为特征值的傅里叶幂等元具有分母 10，在 3 处是单位。每一项都是各槽赋值之和为零的纯张量的整线性组合。把这些幂等元相乘即分开所有域因子。乘上第零槽的 \(\pi_0^{D_0}\mathcal O_k\) 就得到整个所称理想。此处只用了原参考的整数闭包，其生成元有具体表达。

因此在本例第零次迭代的原生参考上，即使各槽允许不同的上述运输，每个输出域因子中都成立以下**最小可能赋值下界**。同一个 \(g\) 在全部槽同时达到式 (14.5) 的界。
\[
       B_s(D_0)=-11s+10\left\lceil\frac{D_0-14s}{10}\right\rceil .
                                                        \tag{14.5}
\]
下界来自 (14.4)、\(\sum_i\lceil t_i\rceil\ge\lceil\sum_i t_i\rceil\) 和非阿基米德三角不等式。达到下界的一个原生点是 \(3^{\lceil(D_0-14s)/10\rceil} y^{\otimes s}\)。在源的每个域因子检查，它的赋值至少为 \(D_0\)，所以即便标量带分母，整个点在运输**之前**就已属于原标记理想。这与 §13.5 的 \(3^{-6}C\) 有不同的成员计算。

| 同一 3 进原参考 | 第一行 \(s=2,\ D_0=d\) | 第二行 \(s=3,\ D_0=4d\) | 两行等权的带符号读数 |
| --- | ---: | ---: | ---: |
| 恒等运输，各因子最小赋值 | \(3+30t\) | \(12+120t\) | \(-(\frac{15}{2}+75t)\log(3)/10\) |
| §14.3 的运输，各因子最小赋值 | \(30t-42\) | \(120t-63\) | \((\frac{105}{2}-75t)\log(3)/10\) |
| 同一坏位的 q | | | \(-(3+30t)\log(3)/10\) |

故两个具体深度 \(d=3,33\) 已在**这个 Galois 商的运输**下达到原 q 系数。较深的 \(d=33\) 仍多出 \(21\log(3)/20\)。对全部 \(t\)，若用 (14.5) 的原生运输，其他位或竖直表示还要补的正差额精确为 \(\max(0,90t-111)\log(3)/20\)。这是给其他分支的定量输入。每一行保留了自己的 \(j^2\)，且是在原权重下比较。该商上的自同构能否进入第 1 列原允许族，要看 §14.5–14.6 的提升。

### 14.5 怎样同时经过许多真实的扩张

**先把 2333 处的圆分层走完。** 沿用 §13.6 的 \(p=2333,\ k=k_{2333}\)，目标是让 \(p\) 在 \(L/pL\) 中变成 \(p+\varpi\)。令 \(D=k(\mu_p)\)、\(\Delta=\operatorname{Gal}(D/k)\)。§13.7 已在 \(H^1(D,\mathbb F_p)\) 上分别构造不变部分的作用、配对部分的逆转置，以及正交补的恒等。所得变换保持 cup、Bockstein 及非分歧字符。\(D/\mathbb Q_p\) 驯分歧，所以加入 \(\mu_{p^2}\) 的扩张分歧。§14.3 直接给整个 \(G_D(p)\) 上保持整条非分歧商的提升。还可在保持非分歧商的前提下调整这个提升，使它与 \(\Delta\) 交换。在保持 \(\nu\) 的自同构群内，恒等作用于 Frattini 商的核是 pro-\(p\) 群（在有限特征商上沿下 \(p\)-中心列过滤）。原 \(\Delta\) 作用的图与被提升共轭后的图在模 Frattini 时相同，在该图的原像内是两个阶素于 \(p\) 的补群，故可由核内元素共轭。逐个有限初等阿贝尔 \(p\) 层平均，再取紧极限，就得到这一补群共轭。这样在 \(\operatorname{Gal}(D(p)/k)=G_D(p)\rtimes\Delta\) 上获得实际作用，保留 \(v(g(1))=-29\)。原 §13.8 在此圆分域上提出的 \(Q/Q_4\) 及以后所有纯 pro-\(p\) 提升，现在均已由同一个自同构实现。

**再把两处的素于 \(p\) 底域合起来。** 此段分别用于 \(p=3\) 和 \(p=2333\)。让 \(M/k\) 遍历所有次数素于 \(p\) 的有限 Galois 扩张，\(\Delta_M=\operatorname{Gal}(M/k)\)。若 \(\mu_p\not\subset M\)，§13.6 的自由 pro-\(p\) 构造适用，取提升时可按 §14.3 的基选择固定整条 \(\nu\)。若 \(\mu_p\subset M\)，\(M\) 仍驯，圆分 \(p^2\) 层仍分歧。当 \(\mu_p\subset k\) 时，不变字符空间通过限制来自 \(k\)，其 cup 相对于 \(k\) 只乘 \([M:k]\in\mathbb F_p^\times\)。它非退化，故可以在其上用 (14.1) 的字符作用、在正交补用恒等。当 \(\mu_p\not\subset k\) 时，若 \(\chi:\Delta_M\to\mathbb F_p^\times\) 是圆分特征，则配对取值于 \(\chi^{-1}\)。平凡和 \(\chi^{-1}\) 两个等型部分完美配对，可照 §13.7 在第二部分取逆转置。对 \(\Delta_M\) 平均即可作分解，无需它是循环群。非分歧字符和一阶圆分字符均来自基域，后一字符在加入 Teichmüller 校正后作限制。两种情况下，§14.3 都给所需的提升，且由补群共轭可使它与 \(\Delta_M\) 交换。

这些构造可以同时选。写 \(M(p)\) 为 \(M\) 的最大 pro-\(p\) 扩张。若 \(M\subset N\)，则 \(M(p)\subset N(p)\)，因为任一有限 Galois \(p\) 扩张在基变换后仍为 \(p\) 扩张。一个在 \(N/k\) 上恒等的自同构保持 \(\operatorname{Gal}(N(p)/M)\) 的最大 pro-\(p\) 商，故可下降到 \(\operatorname{Gal}(M(p)/k)\)。在每一层取固定基域模 \(p\) 作用且在驯部分恒等的所有自同构。这是紧集，因为有关群有限生成，其自同构由有限特征商的逆极限给出。任意有限多个底域都有合成底域，刚构造的上层解同时限制到这些层。因此所有相容条件有有限交性质。所得极限给
\[
      \operatorname{Gal}\!\left(\left(\bigcup_{[M:k]\text{ 素于 }p}M(p)\right)
                                  k^{\mathrm t}/k\right)
                                                        \tag{14.6}
\]
的一条连续自同构，此处的 \(M/k\) 均为 Galois，\(k^{\mathrm t}\) 为最大驯扩张。能在 \(k^{\mathrm t}\) 上取恒等的理由是 \(M(p)\cap k^{\mathrm t}\) 正是 \(M\) 的非分歧 \(\mathbb Z_p\) 扩张，整条 \(\nu\) 被固定，所选补群也被逐元固定。故两边在交上确实一致。这给 3 和 2333 两个不同的局部域各自一条同时经过所有上述塔的箭头。

**在 3 处进入任意驯 Galois 底域上的第一层非交换野扩张。** 这是 (14.6) 留下的另一种相容性，可再向前推进。以下固定 \(p=3\) 和 §14.1 的 \(k\)。取任意有限驯 Galois 扩张 \(M/k\)，令 \(\Delta=\operatorname{Gal}(M/k)\)、\(I\triangleleft\Delta\) 为驯惯性、\(U_0=M^I\)。\(I\) 的阶素于 3，\(U_0/k\) 为非分歧扩张，允许其次数含任意 3 次幂。设 \(Q=G_M(3)\)，\(Q_2=\Phi Q,\ Q_3=\overline{Q_2^3[Q,Q_2]}\)。令 \(M_1,M_2\) 分别对应 \(Q/Q_2,\ Q/Q_3\)，并写 \(H_i=\operatorname{Gal}(M_i/k)\)。下述构造给**实际的 \(H_2\) 自同构**。例如 \(M/k\) 可取惯性 \(C_7\)、剩余三次、群为 \(C_7\rtimes C_3\) 的驯扩张，因为 \(81\bmod 7=4\) 的阶是 3。这里补群共轭论证不能直接用于整个 \(\Delta\)。

1. **先确定 \(H_1\) 上的作用。** 在 \(V_M=Q/Q_2\) 上以 \(I\) 平均，写 \(V_M=V_0\oplus V'\)，其中 \(V_0=V_M^I\)，\((V')^I=0\)。两项都对 \(\Delta\) 稳定。写 \(U_1/U_0\) 为最大初等阿贝尔 3 扩张，\(B=\operatorname{Gal}(U_1/k)\)。\(H_1/V'=\Delta\times_{\Delta/I}B=:D_0\)。确实，\(M/U_0\) 全驯且次数素于 3，\(U_1M/M\) 的群由 \(V_M\) 的 \(I\)-余不变量给出。可对 \(\operatorname{Gal}(M_1/U_0)\) 的正规 3 核取阿贝尔化、再杀 \(I\)，或用互反的范数验证。\(H_1/V_0=:D'\) 是 \(V'\) 被 \(\Delta\) 扩张，且可写为 \(V'\rtimes\Delta\)，因为 \(H^2(\Delta,V')=0\)，先对 \(I\) 平均即可。于是 \(H_1=D_0\times_\Delta D'\)。\(U_0\) 在其次数素于 3 的非分歧子域 \(U_*\) 上是 Galois 的 3 扩张，故 \(U_0(3)=U_*(3)\) 已在 (14.6) 中。用 (14.6) 诱导的 \(B\) 自同构、\(\Delta\) 上的恒等及 \(D'\) 上的恒等，得到 \(h_1\in\operatorname{Aut}(H_1)\)，它保留 (14.1)。

2. **核对所有二次障碍，而不只检验一个 cup。** 对平凡系数 \(\mathbb F_3\)，\(H^2(H_1,\mathbb F_3)\) 中每个类都是从 \(B\) 和 \(D'\) 拉回的两个类之和。为看清这一点，用刚选的分裂将 \(H_1\) 写为 \(V'\rtimes D_0\)。一个中心扩张在 \(V'\) 上的限制由交换子交替形式及三次幂线性形式决定。后者若 \(\Delta\)-不变则为零，因为 \(((V')^*)^I=0\)。前者给某个不变交替形式 \(b'\)，它在 \(D'=V'\rtimes\Delta\) 上由二余圈
   \[
        ((z,\alpha),(z',\beta))\longmapsto
                    \tfrac12 b'(z,\alpha z')
   \]
   实现（符号按交换子约定选取）。扣除这个拉回类，剩余扩张在 \(V'\) 上分裂。分裂在 \(D_0\) 的共轭下所差的是一个取值于 \((V')^*\) 的一余圈。\(I\) 正规于 \(D_0\)，阶素于 3 且在对偶上无不变量，故 \(H^1(D_0,(V')^*)=0\)。修正分裂后它对 \(D_0\) 等变，剩余扩张遂从 \(D_0\) 拉回。再对 \(D_0\to B\) 的核 \(I\) 平均，得 \(H^2(D_0,\mathbb F_3)=H^2(B,\mathbb F_3)\)。这证明了所需分解。

3. **把证据变成实际群箭头。** 设 \(\pi_1:G_k\to H_1\) 为自然满射，\(f_1=h_1\pi_1\)。对 \(D'\) 来的类，二者的拉回相同。对 \(B\) 来的类也相同。后者的理由是作用来自 \(P_*=\operatorname{Gal}(U_*(3)/k)\)，而 (14.6) 在 \(H^2(P_*,\mathbb F_3)\) 上恒等。确实，限制到素于 3 次的底域 \(U_*\) 为单射，那里的一维二次空间由来自 \(k\) 的非零 cup 生成，(14.1) 保持它。因而 \(f_1^*=\pi_1^*\) 在全部平凡系数二次类上成立。扩张 \(H_2\to H_1\) 的核 \(Y=Q_2/Q_3\) 是有限初等阿贝尔群，作用经 \(\Delta\)。\(\pi_1\) 和 \(f_1\) 在 \(\Delta\) 上相同。对每个等变 \(\lambda:Y\to\mu_3\simeq\mathbb F_3\)，推前扩张类再沿 \(f_1\) 拉回为零，因为自然 \(\pi_1\) 已有提升。局部二次对偶以**全部这些 \(\lambda\)** 分离 \(H^2(G_k,Y)\) 的类，故 \(Y\)-值障碍本身为零。由扩张的二余圈描述得到连续提升 \(f_2:G_k\to H_2\)。其在 \(G_M\) 上的像模 Frattini 是全体 \(V_M\)，故覆盖 \(Q/Q_3\)，在 \(\Delta\) 上也满射。最后，\(G_M\to Q/Q_3\) 的任何同态都杀去定义 \(M_2\) 的核，因此 \(f_2\) 下降为有限群 \(H_2\) 到自身的满射，即自同构。[所用的有限模二次对偶](../LocalClassFieldTheory/Duality/DualityDeg2.lean#L589)

此结论对所有有限驯 \(M/k\) 同时有一个相容选择。\(M\subset N\) 时 \(M_2\subset N_2\)，限制到 \(M\) 所对应子群后，其最大满足 \(Q_3=1\) 的 3 商是特征商。与 (14.6) 相同的有限交论证给 \(\operatorname{Gal}(\bigcup_{M/k\ {\rm tame\ Gal}}M_2/k)\) 上的一条自同构。两项无限结论分别有相容选择。目前为它们共同核实的是同一个基域模 3 作用。更高野层与全部驯底域同时出现时的选择见下一节。

### 14.6 放回原 procession，给出尚待跨过的那一步

I.3.8.1(iii) 把每个非阿基米德 \(D_v^\dashv\) 定义为 \(G_{K_v}\) 的连通有限 étale 覆盖范畴。I.4.1(iv) 的 strip 态射是逐位的一族态射。I §0 的 capsule-full 映射在给定标签单射上允许所有分量同构，I.4.10 的相邻行箭头则收集全部这类映射。因此一旦给定**完整** \(G_k\) 的局部自同构，同一处每个有标签的副本均可用选定的识别把它共轭过去，其他位取恒等，行号和标记槽都可以固定。沿相邻行预复合或后复合这种逐分量同构，只是双射地重排该条箭头所收集的映射。这样得到了原 procession 上的代表，且同一有限位能在两行的每个槽使用同一作用。II.4.10(iv) 还把所得 \(D^\dashv\) 两列之间的 poly-isomorphism 明文给成 full。这里解开的是 procession 的覆盖问题。把这个代表施于一次原 IPL/Kummer 输出时，仍须沿所选的同一横箭头记录原始区域与目标全纯参考的识别。[局部范畴](IUT-TEXT/I.txt#L5130) · [逐位态射](IUT-TEXT/I.txt#L5427) · [capsule-full](IUT-TEXT/I.txt#L1697) · [procession 态射](IUT-TEXT/I.txt#L6763) · [两列的 full 同构](IUT-TEXT/II.txt#L10503) · [原 Ind1 与原张量包](IUT-TEXT/III.txt#L9256)

现在可以把下一次的群论检验落到一个指定的域和一个指定的二次类。仍取 3 处的 \(M=k^{\rm ur,3}(\pi^{1/7})\)，这里 \(k^{\rm ur,3}/k\) 专指**次数 3** 的非分歧扩张。它含 \(\mu_7\)，于是 \(\Delta=C_7\rtimes C_3\)。令 \(Q_4=\overline{Q_3^3[Q,Q_3]}\)，考察在 \(H_2\) 上由 \(Q/Q_4\to Q/Q_3\) 决定、带核 \(Q_3/Q_4\) 的扩张。对每个 \(\Delta\)-等变 \(\lambda:Q_3/Q_4\to\mu_3\)，把扩张类推成标量二次类。对 §14.5 的 \(h_2\) 可先加一个取值 \(Y\) 的一余圈来改变提升，再检验这些类沿 \(h_2\pi_2\) 的拉回是否全零。上一层已说明为什么这项检验充分。新的项来自旧层的混合交换子，例如 \(V_0\) 与非平凡惯性特征的括号再与逆特征配对，乘积可以回到平凡特征。因此 §14.5 第 2 步对 \(H_1\) 的二次类分解不能直接照抄到 \(H_2\)。若能给这项修正一个适用于所有深度和所有有限驯底域的构造，才可按 §13.8 的紧性论证取得完整 \(G_k\) 的箭头。任意有限 Galois 扩张在其野惯性的不动域上为 \(p\) 扩张，所以这个量词覆盖了所需的全部有限扩张。

对原 III.3.12 还须同时完成两项数学连接。第一，把完整局部箭头作用到**同一份**第 0 列第一幂源经同一 IPL 的区域，在第 1 列用其固定全纯坐标核对。§14.4 的张量给出具体的源成员、分母与目标赋值，可在这条复合上一项项追踪，直接读出 (14.5)。第二，对一般输入保留全部位与原行权。即便在 §12.7 这一族上，\(t\ge2\) 已有明确正差额，另一位的收益要来自原允许像。可先按 §12.7 的 \(B=1+432\cdot3^d\) 逐个考察 \(p\mid B\)，只记由其当地群和中性参考 \(1\) 实现的带符号收益，再与 §14.4 的差额比较。收益按 §14.7 的中性区域作用计算。

有限性也可从原生层先做一部分。对固定初始数据，除去 2、分歧位和全部指定坏位。在其余有限位 \(p\)，\(L_v=p\mathcal O_{K_v}\)，跨匹配同构运输 \(L_v\) 便严格运输 \(\mathcal O_{K_v}\)。非分歧整数环的张量是有限 étale 的 \(\mathbb Z_p\)-代数，恰为各域因子整数环的乘积。因此这些位的中性原生参考经任意上述槽运输，仍等于标准参考，归一读数为零。对除去的有限多个素数，槽运输落在两个固定单位格之间的同构紧集中（选基即为 \(\mathrm{GL}_d(\mathbb Z_p)\) 的平移），有限槽的张量和有限个标记参考的像一致有界。原生理想满秩，取一个代表已给正 Haar 测度。因此**第零次迭代这些原生轨道的有限位部分**确有有限实读数。推广到原全部允许像，还要对竖直迭代得到相同的几乎处处标准性及例外位的统一界，并控制无穷位。

### 14.7 实际做一次跨位补偿，再把深度放开

先保持 §12.7 的**同一族曲线**。设 \(p>31\) 是 \(B=1+432\cdot3^d\) 的素因子，\(b_p=v_p(B)\)，置 \(e_p=30/\gcd(30,b_p)\)。这些 \(p\) 均为 \(1\bmod4\)，因为 \(B=1+(4\cdot3^{(d+3)/2})^2\)。曲线在 \(p\) 乘性约化，\(-c_6=1+864\cdot3^d\equiv-1\bmod p\)，结点分裂。\(p\) 在初始数据中标为 good，因此 Θ 的原生参考在此为中性。Tate 描述给指定完备化 \(\mathbb Q_p(i,\mu_{30},q_p^{1/30})\)，且 \(v_p(q_p)=b_p\)。开 30 次根时单位部分只需非分歧扩张（先在剩余域开根，再用 Hensel），值群部分给分歧指数 \(e_p\)。若 \(e_p=1\)，该处的原生轨道保持整格。

设 \(e=e_p>1\)，以 \(U_p\) 记此完备化的最大非分歧子域。可取均匀化元 \(\varpi\) 满足 \(\varpi^e\in p\mathcal O_{U_p}^\times\)。为此从任一均匀化元出发，把其 \(e\) 次幂除以 \(p\) 后的单位分成剩余域代表和主单位，后者有 \(e\) 次根。因此 \(\operatorname{Tr}_{k_p/U_p}\varpi=0\)。这里 \(e<p-1\)，所以 \(L_p=\log\mathcal O_{k_p}^\times=\mathfrak m_p\)。在 §13.6 所用的整数基中可把 \(p\) 和 \(\varpi\) 同时列为基元。取 \(p\mapsto p+\varpi\)，其余基元固定。§13.6 的自由群替换和 §14.5 的素于 \(p\) 底域提升在此适用，因为所加入方向的指数 \(\exp(\varpi)\) 的绝对范数为 1，整非分歧商固定。在 (14.6) 型实际商上得到 \(v(g_p(1))=1-e\)。于是在同一中性源的 \(1^{\otimes2},1^{\otimes3}\) 上，全部域投影的两行等权收益为
\[
                         \frac52(1-1/e_p)\log p .
\]
这还是中性全纯理想在上述类型槽运输下可取得的最大值。任一运输保持 \(\mathfrak m_p\)，故保持每个 \(p^n\mathfrak m_p\)，从而 \(v(g_p z)\ge v(z)-(e-1)\)。在整数闭包中用 §14.4 相同的分解，阈值零的理想由总赋值非负的纯张量张成。在各非分歧块上 \((\varpi_i/\varpi_0)^e\) 可以是不同单位。其 \(e\) 个共轭单位根值之差是单位，作分解的拉格朗日幂等元仍只有单位分母。这里局部域为 Galois，根都在同一分解域，归一化不增加额外损失。故每个 \(s\) 槽投影的赋值至少为 \(-s(e-1)\)，上述中性点同时取到。不同 \(p\) 是不同 strip 分量，对固定曲线只涉及有限多个 \(p\)。因此在这些局部商及匹配的原生参考上，所得确实可以相加，给出显式的
\[
                G(d)=\frac52\sum_{\substack{p\mid B\\p>31}}
                           (1-1/e_p)\log p.             \tag{14.7}
\]
每一项都由中性源点产生，重素因子的作用通过 \(e_p\) 计入。原指定坏位仍只有 3。

**固定曲线上的核算。** 取 \(t=2,\ d=63\)。\(293\) 是素数，\(B\bmod293^2=69441=237\cdot293\)，故 \(e_{293}=30\)。在 3 处保留两行原始标记、使用**恒等**运输，跟当地 q 相差 \(3d\log(3)/20=189\log(3)/20\)。在 293 处只用上段的中性点，得到 \(29\log(293)/12\)。因 \(293>3^5\) 且 \(145/12>189/20\)，这一处已经补足。其余地方均用原生恒等参考。这里使用了同一 \(E_2\)、同一个 5、同两行和同一指定坏位。甚至在 3 处那条尚待升到全群的箭头，都可以从**这一例**的消费链中删除。余下只须在 293 处解决完整局部箭头以及同一原 IPL 的输出识别。

还能把对完整群的要求继续削弱。两行都取同一个普通整点 \(z\) 的纯张量。若 \(v(gz)=-k_0\)，则收益为 \(k_0\log(293)/12\)。精确门槛是 \(k_0=22\)，因为 \(293^{105}<3^{567}<293^{110}\)。无需指定 \(z=1\)，也无需指定任何剪切矩阵。在 \(L/pL=\mathfrak m/\mathfrak m^{31}\) 中置
\[
             S=p\mathcal O/pL,\qquad W=\mathfrak m^9/pL .
\]
\(293\bmod30=23\) 的阶为 4，所以这个向量空间维数是 120，\(S,W\) 的维数分别为 4、88。对任何算术箭头，\(\bar g(S)\not\subset W\) 等价于存在所需的整点 \(z\)，只须取 \(\bar g(pz)\) 的赋值至多为 8 即可。这是在原实系数上算出的一个有限子空间检验。

实际攻这个条件时，也可放开各 Galois 层的选择。设 \(N_m\) 是全部指数至多 \(m\) 的开子群之核芯的交，再交上最大初等阿贝尔 \(p\) 商的核。\(G_k/N_m\) 有限，且这些商的自同构可向下限制，因为相应低层核在高层仍由同一组指数条件和初等阿贝尔化特征地定义。每层保留在模 \(p\) 的互反坐标中保持单位子空间、且把 \(S\) 的某个向量移出 \(W\) 的自同构。若每一高度有这样的代表，有限分支树就给一条相容的无限分支，其逆极限为完整局部群的连续自同构。所移的向量、补群和高层修正均可随有限高度选择。§14.5 已在 (14.6) 的整个混合塔上实现这个检验，尚待覆盖一般驯底域的全部野层。对下面的大好素数族，门槛进一步降为 \(\bar g(S)\ne S\)。

**任意深度也可以直接构造出跨位足额的曲线。** 此处让曲线随输入选择，说明上述现象能在无界深度上实现。给定任一 \(d=3+30t\)。选素数 \(p>3^{2d}\)、\(p>31\)、\(p\equiv1\bmod4\)。存在性只需取一个大于两下界的整数 \(n\)，选择 \((2n!)^2+1\) 的任一素因子即可。用中国剩余定理取正整数 \(c\)，满足
\[
             c\equiv1\bmod54,\qquad
             432\cdot3^d c\equiv p-1\bmod p^2 .
\]
令 \(A=3^d c\)、\(E:y^2+xy=x^3+A\)，沿用 \(F=\mathbb Q(i,E[6]),\ K=F(E[5])\)，只将 3 标为 bad。\(c\equiv1\bmod27\) 使 §12.7 的 3 进根、完备化和深度完全相同。\(c\) 是奇数，故 2 处良好约化的点数检验不变，3 处的 5 阶转导矩阵仍在，给同一个满 \(\mathrm{SL}_2(\mathbb F_5)\) 检验。\(c_4=1\) 保证半稳定。新设的 \(p\) 上 \(1+432A\) 赋值恰为 1，结点分裂，故 \(e_p=30\)。这些核对与 §12.7 一样落在曲线、数域及标记层。

对这条曲线，3 处恒等原生参考的两行差额仍为 \(3d\log(3)/20\)。在 \(p\) 处只要把中性 \(1\) 移出整数环**一层**，两个、三个槽等权所得已达 \(\log(p)/12>d\log(3)/6>3d\log(3)/20\)。上面实际构造的商作用将它移出 29 层。故对每个给定深度都已有一条实际曲线，其局部商运输把**原系数的全局数值比较**走通。这给出一条只在一个中性好位追完整群作用的途径，深度可以任意大。对事先指定的一般初始数据，相同的比较必须使用该输入实际具有的好位、竖直允许输出和原权重。式 (14.7) 及固定 \(d=63\) 的核算正为此保留了同一输入。

原 III.3.12 的全量词不等式、整族有限性及 ABC 均未由本节推出。附带的精确算术复核遍历了 \(\mathbb F_{81}\) 的全部元素，范数首项有 27 个像，指定 \(b\) 在像外。另核对了 \(t=0,\dots,50\) 时 (14.5) 对所有槽赋值模 10 组合的极小值、\(B\bmod293^2\) 和门槛 22 的两个整数幂比较。全程单线程自然语言，Lean 编译、证明体验证、内核闭包和原目标验收均未运行。

<a id="finite-workload"></a>

## 15. 要验证多少，以及在哪里停

这里固定原 III.3.12。对 III.3.11 的**每一组**合格输入 \(T\)，用同一表示中无 Ind 的 q 读数 \(q_s(T)\)，和有 Ind1–3 的 Θ 全部允许像的 hull 读数 \(H(T)\)，证明 \(q_s(T)\le H(T)<+\infty\)。左右两边各有自己的量词。下界允许按输入挑见证，取逐因子 hull 时见证甚至可以因因子而异。有限性要管同一输入的**全部**允许像。要覆盖全部 \(T\)，没有逐曲线验证的最后一条曲线。[原声明及量词](IUT-TEXT/III.txt#L10326) · [hull 的逐因子定义](IUT-TEXT/III.txt#L7656)

| 验证对象 | 现在能给出的工作量 | 完成这项以后得到什么 |
|---|---|---|
| 指定曲线 \(d=63\)，在 293 已给完整算术箭头 | 一张 \(32\times4\) 的模 293 矩阵找一个非零元。可预先固定一个单位和一个字符，只求一次非零配对 | 在匹配的局部单位坐标中足以支付该曲线的差额 |
| 同一例，已给原第 1 列允许输出 | 两行各读一个域投影。两次整数赋值之和 \(\le-110\)，配合下述算术对称性即可通过下界 | 直接接触该例原 Θ 的下界，可绕过指定群箭头的构造 |
| 从有限群商反过来寻找完整群箭头 | 每层有限。目前没有从域参数算出的成功截止层 | 某层全体候选失败可淘汰这条构造，正向结论须靠全层定理或完整箭头证书 |
| 指定族中每个 \(d\) 的中性好位总收益 | 固定 \(d\) 只做一次判别式整数比较。全族要证一个带明确指数的增长估计，见 §15.4 | 衡量这类源点究竟能贡献多少，即使局部运输全部成功也需支付此项 |

以位数衡量这一个样本也很小。\(d=63\) 时 \(B\) 只有 109 个二进制位，(15.3) 中的 \(J(B)^5\) 有 15412 位。§15.2 的两个有限剩余模各有 \(293^{60},293^{88}\) 个元素，但指定一个元素分别用 492、722 位即可编码，验收只比较给出的剩余坐标。找到一个确实出自原允许族的元素，其难度并不由这些位数决定。

### 15.1 有限维读数为什么没有给出群塔的停止层

在 \(p=293\) 处沿用 §14.7 的 \(V=L/pL,\ S=p\mathcal O/pL,\ W=\mathfrak m^9/pL\)。维数依次是 \(120,4,88\)。取 §14.7 的有限特征商 \(G_k/N_m\)。令 \(A_m\) 为在互反坐标中保持模 \(p\) 单位子空间，并保持该层已经可见的全部非分歧 \(p^r\) 次商之核的自同构。具体包括所有 \(p^r\le m\) 的这些核。这样取逆极限时确实保持整个 \(p\) 进单位部分。若某项构造要求固定整条非分歧商，可相应要求在每个这样的商上作用为恒等。令 \(T_m\) 是模 \(p\) 作用所给的所有 \(a(S)\) 的线性张成。限制映射给 \(S\subseteq T_{m+1}\subseteq T_m\subseteq V\)。故最多出现 \(116\) 次**严格降维**。若某层 \(T_m\subseteq W\)，所有满足所选条件的完整箭头都过不了这条测试。若每层都有 \(T_m\not\subseteq W\)，所有层的成功者组成有限分支树，紧性给出相容的完整箭头。连续两层甚至一百层同维，都没有说明下一次降维何时发生。

这个区别有任意长的明白例子。取 \(G=\mathbb Z_p\oplus\mathbb Z/p^a\)。当 \(m\le a\)，\(G/p^mG\) 允许交换两个标准生成元。到 \(m=a+1\)，第二个生成元的像因阶整除 \(p^a\)，其第一坐标必被 \(p\) 整除，模 \(p\) 再也不能把那条挠直线移出自身。\(G\) 本身也保持挠子群。这里 \(a\) 任意。这个例子说明单凭有限维和持续稳定无法估算停止层。特定的 \(G_k\) 仍可能有特殊的有限判据，目前工作树中的推导没有给出这样的层数。

### 15.2 固定 293，将成功证书压到一个单位，或原输出的两个数

**一个实际单位和一个实际扩张。** 记 \(U=\mathbb Q_{293}(\mu_{30})\)，取 \(\varpi^{30}=q_p\in\mathbb Q_p,\ v_p(q_p)=1\)，\(k=U(\varpi)\)。\(U\) 的剩余次数为 4。取 \(\xi=\zeta_5,\ \omega=1+\xi,\ u_*=1+p\omega\)。\(\bar\xi\) 的四个共轭是剩余域的一组基，因为 \(293\bmod5\) 的阶为 4，且 \(X^4+X^3+X^2+X+1\) 是极小多项式。它们之和为 \(-1\)。换成 \(1+\bar\xi^j\) 的基变换行列式是 \(-3\)，模 293 可逆。因此 \(\omega\) 的四个共轭乘 \(p\) 后张成 \(S\)。同时 \(\log u_*\equiv p\omega\bmod pL\)，因为误差在 \(p^2\mathcal O\subset pL\) 中。

每个 \(V/W\) 中的类唯一写成 \(\sum_{i=1}^{8}c_i\varpi^i\)，系数在 \(\mathbb F_{p^4}\)。取线性泛函
\[
 \lambda\!\left(\sum c_i\varpi^i\right)
   =\operatorname{Tr}_{\mathbb F_{p^4}/\mathbb F_p}
        \left(\bar\omega\sum_{i=1}^{8}c_i\right).
\]
用 \(\lambda\circ\log\) 在主单位上定义阶 \(p\) 的加法字符，在 Teichmüller 单位和 \(\varpi\) 上取零，局部互反给 \(G_k\) 的字符 \(\chi_\lambda\)，其核给一个确定的循环 \(p\) 次扩张。以 \(U_n=1+\mathfrak m^n\) 计，其导子指数正好是 9。这里 \(e=30<p-1\)，所以 \(\log U_n=\mathfrak m^n\) 对所有 \(n\ge1\) 成立，且 \(\lambda\) 在第 8 层确实非零。[互反与范数的仓库接口](../LocalClassFieldTheory/Reciprocity/NormCompat.lean)

为什么一个字符足够？取实际域自同构 \(\tau(\varpi)=\zeta_{30}\varpi\) 固定 \(U\)，以及固定 \(\varpi\) 的剩余 Frobenius \(F\)。把检测器预复合 \(F^s\tau^h\)，其中 \(0\le s<4,\ 0\le h<8\)。若这 32 个读数全为零，先用四个共轭的 \(\bar\omega\) 及迹配对的非退化性，得到 \(\sum c_i(\bar\zeta_{30}^h)^i=0\) 对八个 \(h\) 成立。除去一个 \(X\) 后，次数至多 7 的多项式有八个不同的根，所以全部 \(c_i=0\)。另一方面，同一组域自同构可以把 \(p\omega\) 的共轭逐个放到输入端。这些前后复合都由真实域同构诱导，不增添虚构的 Ind 自由度。于是完整群轨道移出 \(W\)，等价于能找到一个保持单位部分的完整群自同构 \(\sigma\) 满足
\[
           \chi_\lambda\bigl(\sigma^{\rm ab}(\operatorname{rec}_k u_*)\bigr)
                   \ne 0 .                                             \tag{15.1}
\]
也可检验 \(\chi_\lambda\) 的轨道能否达到导子指数 31。达到时必在 \(U_{30}/U_{31}\) 非零，给输入端预复合上述 Frobenius 即得 (15.1)。反向则因 \(u_*\in U_{30}\) 且所有阶 \(p\) 字符都杀掉 \(U_{31}=U_1^p\)。这给出了寻找成功证书时应搬动的具体循环扩张和单位。原流程为条件接口提供任意连续线性自同构，并不能据此算出 (15.1)。

**更靠近原目标的读法。** 在 293 的同质 \(s\) 槽，\(k^{\otimes_{\mathbb Q_p}s}\simeq\prod_{\operatorname{Gal}(k/\mathbb Q_p)^{s-1}}k\)。两行有 \(120+120^2=14520\) 个域因子，但乘法投影 \(\mu_s(x_1\otimes\cdots\otimes x_s)=\prod x_i\) 只取其中一个。其他槽上独立的**域自同构**传递地置换这些因子，保持中性标记、Haar 归一化和赋值。这些算术同构是原 capsule-full 逐槽箭头。对于已在固定目标坐标中、按这些箭头饱和的原允许像族，一个投影的证人经后复合就在其他各投影得到同样的赋值。hull 逐因子包住整族，允许各因子取不同的证人。[逐槽同构](IUT-TEXT/I.txt#L1697) · [procession](IUT-TEXT/I.txt#L6763) · [Ind1 的原作用域](IUT-TEXT/III.txt#L9256) · [逐因子 hull](IUT-TEXT/III.txt#L7656)

具体地，在 3 处用恒等参考、其他位保持 §14.7 的参考，设 \(m_s=v_k(\mu_s(Y_s))\)，其中 \(Y_2,Y_3\) 来自同一初始数据的原允许输出，取 \(v_k(\varpi)=1\)。两行给的增益至少为 \(-(m_2+m_3)\log(293)/60\)。原差额是 \(189\log(3)/20\)。由 \(293^{109}<3^{567}<293^{110}\)，**整数门槛恰是 \(m_2+m_3\le-110\)**。例如分别到 \(-44,-66\) 就够。对任意原输出可直接测它的乘法投影在 \(k/\mathfrak m^{1-22s}\) 中是否非零。对 §14.7 特定的中性轨道还有 \(m_s\ge-29s\)，故这两个测试分别落在长度 15、22 的有限剩余模中。\(m_2,m_3\) 也可不按上述比例分摊。至此，固定例的数值验收只需两次投影。仍须给出 \(Y_s\) 沿同一 IPL 从第 0 列到第 1 列的实际出处以及上述后复合在该坐标中的实现。单有商群上的矩阵不能完成这项验收。

**原 IPL 实际要比较到什么精度？** 令 \(x\) 为匹配算术坐标中候选的槽输出，\(-29\le v_k(x)\le-22\)。若原输出的乘法投影可写成 \(\prod_i w_i+\eta_s\)，其中 \(v_k(\eta_s)\ge1-22s\)，则对 \(s=2\) 只需 \(v_k(w_i-x)\ge-14\)，对 \(s=3\) 只需 \(\ge-7\)，就能证 \(\mu_s(Y_s)\equiv x^s\bmod\mathfrak m^{1-22s}\)。逐槽换一个因子作差，其余 \(s-1\) 个的赋值都至少 \(-29\)，故每项误差的赋值至少是 \(-14-29=-43\) 或 \(-7-58=-65\)。而 \(v_k(x^s)\le-22s\)，所需剩余类非零。两行统一地只查 \(p w_i\bmod\mathfrak m^{23}\) 已足够，因为 \(v_k(p)=30\)。若直接给出投影，上述纯张量近似也可省去。

**把原 IPL 的六箭头实际算短。** 在 III Remark 3.10.2 的图中，四列从左到右是 env、gau、LGP、lgp。以下排横箭头 \(a_1,a_2,a_3\)、上排横箭头 \(b_1,b_2,b_3\) 及竖直 Kummer 箭头 \(v_0,\ldots,v_3\) 记之。图中每个方块满足 \(b_i v_{i-1}=v_i a_i\)。对这张图中一组相容的代表，原书用于 IPL 的指定六箭头复合在 prime-strip 层就是
\[
 b_3 b_2 b_1 v_0 a_1^{-1}a_2^{-1}
   = b_3 b_2 v_1 a_2^{-1}
   = b_3 v_2
   = v_3 a_3 .                                                   \tag{15.1a}
\]
最后的 \(a_3\) 是 III.3.7(iv) 的下排自然识别，\(v_3\) 是 III.3.10(i) 在 lgp 的 Kummer 同构。这样在一组相容代表上已消去四条箭头。对 poly-isomorphism 的所有独立选择不能逐个形式约去。下界可以选择一个相容代表，但随后仍须在第 1 列的固定坐标里读取它携带的**带标记区域**。原图陈述在 prime-strip 层，单独从该等式不能推出每个区域的点在两条路上的读数相同。[原交换图](IUT-TEXT/III.txt#L9069) · [各箭头的定义](IUT-TEXT/III.txt#L9116) · [原六箭头及终端的符号与区域条件](IUT-TEXT/III.txt#L9702)

其普通单位部分可以继续算完。对 \(u\in U_1\)，选 \(\alpha^p=u\)，则 \(\gamma\mapsto\gamma(\alpha)/\alpha\) 给 \(\kappa_p(u)\in H^1(G_k,\mu_p)\)，换根只改一个余边界。在固定算术实现中，其单位像精确记住 \(U_1/U_{31}\)。因为 Kummer 核为 \(p\) 次幂，而 \(\log\) 将 \(U_1^p\) 识别为 \(pL=\mathfrak m^{31}\) 的指数像。也可从这个类无歧义地读出
\[
        [u]\longmapsto p^{-1}\log u\bmod L
                 \quad\text{于 }p^{-1}L/L=\mathfrak m^{-29}/\mathfrak m .
\]
若两个主单位在 \(k^\times/k^{\times p}\) 中相等，其比是一个主单位的 \(p\) 次幂，因为剩余域乘法群阶素于 \(p\)，故除以 \(p\) 后只差 \(L\)。于是 **一次指数为 \(p\) 的 Kummer 即已携带这两行所需的全部单位精度**，无须算 \(p^2,p^3,\ldots\) 次开根。等价的单位测试是实际输出类在 \(U_1/U_9\) 非零，此时代表 \(u'\) 满足 \(v_k(p^{-1}\log u')\le-22\)。这个单位读数由局部算术算出，作为原区域坐标还要核实其归一化。仓库已有选根余边界与 Kummer 核的证明体。[选根及单位同态](../LeanFormal/IUT/IUTII/Frobenioid/LocalUnitKummerMap.lean#L12) · [Kummer 余圈](../tmp/sheaf/xif/paper/TauCetiPort/TauCeti/FieldTheory/GaloisCohomology/Kummer.lean#L276) · [幂类的核](../tmp/sheaf/xif/paper/TauCetiPort/TauCeti/FieldTheory/GaloisCohomology/Kummer.lean#L320)

在两端使用同一个算术识别试算，\(u_*\in U_{30}\)，\(p^{-1}\log u_*\equiv\omega\bmod L\)，而 \(\omega\) 为单位。因此这个相容代表的普通单位读数赋值为 **0**，两行纯张量的乘法投影也都是 0 赋值。换 Kummer 根不改变它，域自同构及 §12.8 的固定群 Ind2 也保持该赋值。希望得到的改变量已经定位到**原第 0 列与第 1 列之间的算术比较作用在这份区域上**，单纯重排交换图不能把 \(U_{30}\) 移出 \(U_9\)。所以应直接查能否让另一实际代表把 \(\kappa_p(u_*)\) 送进所需剩余类，同时带出上述原区域，或者直接给两个合格行投影。原文在同一 Θ-link 上区分单位部分与值群部分，且要求有关输出是能解释为 prime-strip 的区域族。这里未把普通单位类的计算当作该区域的成员证明。[单位部分和值群部分](IUT-TEXT/III.txt#L10437) · [允许区域的条件](IUT-TEXT/III.txt#L10412)

### 15.3 群塔向前一步，同时处理全部驯底域及任意野幂指数

固定 §14 的一种模 \(p\) 单位作用，\(k/\mathbb Q_p\) 绝对驯，\(p\) 为奇素数，并使用 §14.3–5 已在次数素于 \(p\) 的 Galois 底域上提升、固定整条非分歧商和模 \(p\) cup 配对的情形。它涵盖上述 293 的剪切及 §14 的 3 进例。对每个有限驯 Galois \(M/k\)，记 \(M^{[2]}\) 为 \(M\) 的最大**普通幂零类至多二**的 Galois pro-\(p\) 扩张。下面给出
\[
          \operatorname{Gal}\!\left(\bigcup_{M/k\ {\rm tame\ Gal}}
                                     M^{[2]}/k\right)
                                                               \tag{15.2}
\]
上的一条相容自同构，固定驯底域并实现上述基域模 \(p\) 作用。类二允许交换子和生成元有任意大的 \(p\) 幂阶。§14.5 在一般驯底域上的结果只走到首个非交换的下 \(p\)-中心商。这里的证明同时消去无限多个幂指数，不要求逐一计算三进、293 进或 \(p^r\) 次的提升。

1. **在每个底域构造完整阿贝尔层的作用。** 可取包含 \(k'=k(\mu_p)\) 的共尾底域。写 \(\Delta=\operatorname{Gal}(M/k)\)，\(J=I(M/k')\triangleleft\Delta\)，\(D=M^J\)。\(J\) 的阶素于 \(p\)，且它固定 \(\mu_p\)。\(D/k'\) 非分歧。取其最大素于 \(p\) 次子域 \(D_*\)，则 \(D_*/k\) 是次数素于 \(p\) 的 Galois 扩张，且 \(D(p)=D_*(p)\)。最后这个等式来自 \(D/D_*\) 本身是 Galois \(p\) 扩张。§14.5 中可在每个含 \(\mu_p\) 的素于 \(p\) 次底域上同时要求作用固定其一维二次 cup 空间。其构造采用配对上的等距变换；下降到较小此类底域时限制为单射，因为限制后再转移乘素于 \(p\) 的次数。故这些闭条件同样满足 §14.5 的有限交论证。特别地，所得作用在 \(P_*=\operatorname{Gal}(D_*(p)/k)\) 的 \(H^2(P_*,\mu_p)\) 上为恒等，限制到 \(D_*\) 即可检验。

   令 \(Q=G_M(p), A=Q^{\rm ab}\)，\(H_A=\operatorname{Gal}(M^{\rm ab,p}/k)\)，\(B_0=\operatorname{Gal}(D^{\rm ab,p}/k)\)。在有限生成 \(\mathbb Z_p\) 模 \(A\) 上按 \(J\) 平均，写 \(A=A^J\oplus A'\)。由局部互反，\(A\) 的挠部为 \(\mu_{p^\infty}(M)=\mu_p\)，因为 \(M/\mathbb Q_p\) 仍驯，故 \(A'\) 自由且没有 \(J\) 不变量。这里 \(H_A/A'=\Delta\times_{\Delta/J} B_0=:D_0\)。具体地，\(M/D\) 素于 \(p\) 次，范数在阿贝尔 pro-\(p\) 化上将 \(J\) 余不变量识别为 \(D\) 的阿贝尔 pro-\(p\) 化。转移和范数在不变量上的合成是乘 \(|J|\)，可逆。另一方面 \(D'=H_A/A^J\simeq A'\rtimes\Delta\)。这是因为 \(H^2(\Delta,A'/p^rA')=0\) 对每个 \(r\) 成立，先对 \(J\) 平均，所得不变量为零；各有限层的分裂取紧极限。于是 \(H_A=D_0\times_\Delta D'\simeq A'\rtimes D_0\)。§14.5 的作用从 \(P_*\) 下降到 \(B_0\)，它固定 \(D\) 所对应的子群及其特征阿贝尔 pro-\(p\) 商。在 \(D'\) 和 \(\Delta\) 上用恒等，便得到 \(H_A\) 上的 \(h_A\)，在基域仍给指定的模 \(p\) 作用。

2. **计算提升真正要保持的二次类。** 系数取带圆分作用的 \(\mu_p\)。\(H^2(H_A,\mu_p)\) 中每一个类都是 \(B_0,D'\) 两边拉回类之和。理由如下。把代表扩张限制到 \(A'\)，由其交换子得到 \(\Delta\)-等变交替形式 \(b'\)。交换子为零时限制扩张是阿贝尔 pro-\(p\) 群扩张，对自由 \(\mathbb Z_p\) 模 \(A'\) 的一组基选提升即得分裂。一般的 \(b'\) 已可在 \(D'\) 上用余圈 \(((a,\delta),(a',\delta'))\mapsto \tfrac12 b'(a,\delta a')\) 实现，此处将 \(\mu_p\) 作加法记号。扣去这一项，扩张在 \(A'\) 上分裂。不同分裂之差在 \(\operatorname{Hom}_{\rm cont}(A',\mu_p)\) 中。核 \(J\triangleleft D_0\) 在该模上无不变量且阶可逆，故 \(H^1(D_0,\operatorname{Hom}_{\rm cont}(A',\mu_p))=0\)。修正分裂成 \(D_0\)-等变的分裂，剩余扩张从 \(D_0\) 拉回。再对 \(D_0\to B_0\) 的核 \(J\) 平均，它就来自 \(B_0\)。这也解释了为什么必须分出惯性作用平凡的一整块。

   以 \(\pi_A:G_k\to H_A\) 为自然满射，\(f_A=h_A\pi_A\)。在 \(D'\) 两个复合相同。在 \(B_0\) 两个复合经 \(P_*\) 分解，第一步已在 \(P_*\) 上固定二次类。由分解可得
   \[
       f_A^*=\pi_A^*\quad\text{于 }H^2(H_A,\mu_p).
   \]

3. **用同一个对偶论证提升任意阶。** 令 \(H_2=\operatorname{Gal}(M^{[2]}/k)\)，其到 \(H_A\) 的核是 \(C=\gamma_2Q/\gamma_3Q\)，其中 \(\gamma_i\) 取闭下中心列。\(C\) 由有限多生成元两两的交换子拓扑生成，是有限生成阿贝尔 pro-\(p\) 群，共轭作用经 \(\Delta\)。对任意 \(r\ge1\)，拉回扩张 \(H_2/p^rC\to H_A\)，障碍在 \(H^2(G_k,C/p^rC)\)。对每个等变 \(\lambda:C/p^rC\to\mu_{p^r}\)，由于 \(G_M\) 在定义域上平凡，其像属于 \(\mu_{p^r}(M)=\mu_p\)。所以推到标量后，只需上一步已经控制的系数 \(\mu_p\)。沿自然 \(\pi_A\) 的障碍为零，因为它有自然提升；沿 \(f_A\) 也是零，因为两者拉回每个标量二次类相同。局部二次完美对偶用全部这些 \(\lambda\) 分离障碍，因此 \(C/p^rC\) 值障碍本身为零。此处复用的是仓库的有限模对偶，其余为本节的自然语言推导。[局部二次对偶](../LocalClassFieldTheory/Duality/DualityDeg2.lean#L589)

   每个 \(r\) 的连续提升构成非空有限集。两次提升相差一个有限模一余圈，而局部域对固定有限模的一余圈只有有限多个，可从局部群的拓扑有限生成看出。紧性给同时兼容所有 \(r\) 的 \(G_k\to H_2\)。它在 \(G_M\) 上模 Frattini 满射，遂覆盖 \(Q/\gamma_3Q\)，在 \(\Delta\) 上也满射。其限制于 \(G_M\) 必经过最大类二 pro-\(p\) 商，故下降成 \(H_2\) 的满自同态。\(H_2\) 拓扑有限生成，满自同态为自同构。最后，让 \(M\) 同时变化。上层底域所得自同构固定驯商，故保持下层底域对应子群及其特征的最大类二 pro-\(p\) 商。有限多个 \(M\) 可在它们的合成域同时处理。固定基域模 \(p\) 作用的自同构集是紧的，再用有限交性质给出 (15.2)。这与 (14.6) 的构造共同固定指定的基域作用；两条大商上的箭头在整个交商上相同，仍须另证才可以拼接。

**能据此停在哪里？** (15.2) 可以停止按幂指数搜索。若坚持沿此支到整个 \(G_k\)，尚有**幂零类数 \(c\)** 一个无界参数。精确的归纳目标如下。以 \(H_c\) 记每个 \(M\) 上的最大类 \(c\) 商连同驯底群，\(\pi_c:G_k\to H_c\)。定义线性泛函
\[
  \eta_{M,c}=\operatorname{inv}_k\circ\pi_c^*:
        H^2(H_c,\mu_p)\longrightarrow
        \tfrac1p\mathbb Z/\mathbb Z .
\]
若所选 \(h_c\) 保持 \(\eta_{M,c}\)，同第三步的对偶已足以让它升到 \(c+1\)，因为 \(\gamma_{c+1}Q/\gamma_{c+2}Q\) 仍是共轭作用经 \(\Delta\) 的有限生成阿贝尔 pro-\(p\) 模。真正缺的归纳步是**在这些提升中选到一个仍保持 \(\eta_{M,c+1}\) 的提升**，对任意 \(M,c\) 使用同一证明。保持泛函指在其整个定义空间上相等，空间的维数可增长。上面证了阿贝尔层的保持及其类二提升，未证后一提升具备下一层的保持性。若做出这样的归纳，有限交论证同时处理底域和类数，因为每个有限 Galois 扩张在其野惯性的不动域之上是有限 \(p\) 扩张，每个有限 \(p\) 群的幂零类有限。故逐次验证 \(c=3,4,5,\ldots\) 不列为余下计划。

### 15.4 即使群箭头全部成功，全局还要付多少

**指定原族的一次整数比较。** 取 §12.7 的 \(d=3+30t,\ t\ge0,\ B=1+432\cdot3^d\)。在 §14 的第零次迭代中，只动坏位 3 和整除 \(B\) 的中性位 \(p>31\)，其他地方用恒等参考。定义
\[
 J(B)=\prod_{\substack{p\mid B\\ p>31}}
                p^{\,30-\gcd(30,v_p B)}.
\]
它有一个与选择局部箭头无关的算术含义。取有限 étale 代数 \(A_B=\mathbb Q[X]/(X^{30}-B)\) 的**最大整序**，\(J(B)\) 就是其绝对判别式的 \(p>31\) 部分，允许 \(A_B\) 有多个域因子。确实，在这样的 \(p\) 处，先作非分歧基变换补足单位的三十次根和单位根，各因子的驯分歧指数都是 \(e=30/\gcd(30,v_pB)\)。分歧指数在该基变换下保持。归一化后的不同理想指数为 \(e-1\)，剩余次数满足 \(\sum_i e f_i=30\)。故判别式指数为 \(\sum_i f_i(e-1)=30-\gcd(30,v_pB)\)。\(p\nmid B\) 时为零。取多项式幂基序只给 \(30^{30}B^{29}\) 的绝对判别式，其中混有整序指数的平方，会高估可用收益。[仓库的驯不同理想等式](../LeanFormal/IUT/IUTIV/Estimates/DifferentTameEquality.lean#L170)

将 \(e_p\) 代入 (14.7)，所有这些中性好位在匹配商模型下能提供的最大增益恰是 \(\log J(B)/12\)。3 处用 §14.4 最佳原生参考之后，尚差 \(3(d-40)_+\log(3)/20\)，其中 \(x_+=\max(x,0)\)。若 3 处只用恒等，则差 \(3d\log(3)/20\)。因此两种方案各自的**精确数值验收**为
\[
  J(B)^5\ge 3^{\,9(d-40)_+},
  \qquad
  J(B)^5\ge 3^{\,9d}\quad\text{（3 处恒等）}.                    \tag{15.3}
\]
即使未来得到了每个局部完整群的箭头，以及它们的原 IPL 实现，这条指定参考路线对**全部** \(d\) 仍须达到相应的 (15.3)。因为 \(J(B)\le\operatorname{rad}_{>31}(B)^{29}\)，第一种已要求 \(\operatorname{rad}_{>31}(B)^{145}\ge3^{9(d-40)_+}\)。在这族指数型整数上，需要根基随深度至少按给出的速率增长。这一代价只属于指定的第零次参考及补偿规则，原允许像还可能从别的区域或迭代贡献下界。

可以先消去一整类数值输入。令 \(B_{\le31}=\prod_{p\le31}p^{v_pB}\)。对 \(1\le b\le14\)，整数不等式 \(30-\gcd(30,b)\ge2b\) 成立；\(b\le10\) 用 \(\gcd(30,b)\le b\)，其余四值直接代入。因此只要 \(B_{\le31}\le B^{1/10}\) 且 \(p>31\) 的每个正重数至多 14，便有
\[
   J(B)^5\ge(B/B_{\le31})^{10}\ge B^9>3^{9d}.
\]
这对满足上述可判条件的**全部输入**完成了数值部分。小素数还可沿一个无限等差数列完全消去。\(B=1+(4\cdot3^{(d+3)/2})^2\)，故 \(p\le31\) 只可能有 \(5,13,17,29\)。当 \(56\mid t\)，指数增量 \(30t\) 是 \(20,12,16,28\) 的公倍数，模 \(25,13,17,29\) 的情况都与 \(t=0\) 相同，故 \(B_{\le31}=5\)。大素数重数的条件仍须独立处理。对原定 \(d=63\)，一次完整分解给
\[
 B=5\cdot293\cdot1013\cdot16057\cdot20749675857108533084861,\qquad
 J(B)=(B/5)^{29}.
\]
这次核算覆盖该例**全部**中性好位，无需为这条曲线继续寻找别的素数。

**对不同局部域的行和元组也可统一。** 在匹配的中性算术坐标中，固定奇 \(p\)，假设参与的各 \(k_b/\mathbb Q_p\) 的 \(e_b<p-1\)，令 \(\lambda_b\) 为归一局部权重。每槽 \(L_b=\mathfrak m_b\)，保此格的 \(\mathbb Q_p\)-线性同构同时保所有 \(p^a\mathfrak m_b\)，故最多损失 \(e_b-1\) 个当地整赋值层。多槽张量代数的整数闭包由 \(\bigotimes_i\mathfrak m_i^{a_i}\) 中 \(\sum_i a_i/e_i\ge0\) 的这些格之和生成。可在有限非分歧扩张上验证这条格等式。先分裂剩余域及所需单位根，调匀化元使 \(\pi_i^{e_i}=p\)。驯单位根群的幂等投影的分母可逆，按字符分成秩一的单项式 \(\prod_i\pi_i^{a_i}\)，\(0\le a_i<e_i\)。每个单项式在所有域投影的归一赋值都是 \(\sum_i a_i/e_i\)，故其整格恰为该单项式乘 \(p^{-\lfloor\sum_i a_i/e_i\rfloor}\mathcal O^{\rm ur}\)，此处 \(\mathcal O^{\rm ur}\) 表示所取的有限非分歧扩张整数环。这些格都在上述和中，由忠实平坦下降得到原等式。

于是每个元组的归一位移至多 \(\sum_i(1-1/e_{b_i})\log p\)。在 §14.7 类型的匹配商上，各处令 \(p\mapsto p+\pi_b\)（\(e_b=1\) 取恒等），中性 \(1^{\otimes s}\) 在所有域投影同时取到。按 \(\prod_i\lambda_{b_i}\) 求期望，\(s=j+1\) 个槽只给 \(s\) 倍单槽期望，再平均 \(j=1,\dots,(\ell-1)/2\)，得到
\[
       \frac{\ell+5}{4}
          \sum_{b\mid p}\lambda_b(1-1/e_b)\log p .                     \tag{15.4}
\]
这消去了按标签、槽数和连续多个合格中性素数逐项重做证明的工作。式中达界的断言限于上述商运输，其余情形该格计算给出上界。带原标记及跨 IPL 的读数仍应按原来源核对。[原元组](IUT-TEXT/IV.txt#L1612) · [槽权的仓库恒等式](../LeanFormal/IUT/IUTIV/Estimates/StepVDistinguishedSlotAverage.lean#L25) · [行平均](../LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean#L54)

### 15.5 剩余工作应怎样才有终点

1. **先做直接关系到下界的那次有界检验。** 在 §15.2 已约简的 \(v_3a_3\) 上，保留原第 0 列到第 1 列的选择和固定目标坐标。只追 \(1+293(1+\zeta_5)\) 的一次 \(p\) 级 Kummer 类**连同**其所在的中性参考。恒等算术识别所得赋值已是 0。要另一个原代表在 \(U_1/U_9\) 非零且确实给出这份区域的行输出，或者不分解槽，直接取得两个乘法投影。交付其原始出处及赋值之和，此和至多 −110 就结束这个例子的下界实验。若 \(v_3a_3\) 在区域层的求值不能由 prime-strip 层恢复，须给出在何种对象上还要保留哪一个局部识别。只在群商上找到剪切不通过此项。推广时再明确证明中哪些步骤适用于任意 \(T,j,v\)。

2. **再判定采用哪一种全局下界。** 若证明依赖 §15.4 的中性补偿，要给出从每个已指定输入产生的统一收益估计。在本族上，(15.3) 已是可独立攻击的整数命题。若原 IPL 的投影能直接在有标记的坏位给足 q，或从其他原输出给足加权总量，应改从这些源输出证明同一输入的带权下界，便可省去 (15.3) 这项特定代价。完整 \(G_k\) 只在选定构造真的需要它时才构造；该支的正向停止证书是一次给出全群自同构及逆，或 §15.3 对所有类一次成立的归纳。固定输入的整数检查、完整群构造与全局泛化有不同的交付物。

3. **有限性另外用一个覆盖所有迭代的界收口。** 对每个固定 \(T\)，可沿原箭头传播一个共同容器。有限位上，足够证明例外集外所有有标记的允许像均在标准参考内，有限个例外位各有一个与竖直迭代次数无关的界，无穷位另给统一半径；结合原满秩参考给出的正体积，行数和每位的元组数均有限，即得有限实读数。界允许依赖 \(T\)，可求和的尾界也足够。III.3.5(ii)(a) 已经把普通单位经过任意竖直 log 迭代的像放在同一 shell 中，(b) 给无穷位的单位与指定闭球。应追的是加标记和最后 evaluation 对这些界的影响。仓库已有从容器包含导出有限性的消费者，其中包含关系是输入。IV Step (vi) 在解释 Ind3 时回引 III.3.12 的证明 Step (x)，不可将这项回引直接充当独立证明。[所有迭代的普通单位](IUT-TEXT/III.txt#L6078) · [hull 有限性的消费者](../LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean#L95) · [IV 的回引](IUT-TEXT/IV.txt#L1804)

   在非阿基米德位，有一种可实施的容器证书。选固定目标图表中的有限组格 \(L_i\)。为每一类**实际可复合**的箭头从分量 \(i\) 到 \(j\) 计算整数 \(w_{ij}\)，使它把半径格 \(p^{-r}L_i\) 送进 \(p^{-r-w_{ij}}L_j\)，对所需半径成立。线性箭头在 \(r=0\) 查一组整基即可，多个输入求和使用超度量不等式。非线性 evaluation 要直接检查带标记区域的像。若每个可达有向环的总权都 \(\le0\)，则删去路径中的环只会增大该路径的界。于是有 \(N\) 个格时，各迭代的共同半径只需求长度至多 \(N-1\) 的简单路径最大值，加上相应起始半径。这个充分判据可一次覆盖无限次迭代。若图表或权值没有从原箭头导出、或某个粗估环为正，就仍须改进格与权值；这种粗估不能判定实际输出发散。

**本次工作量判断。** 给出一份统一证明后，检查这份具体证明是有限工作。现在能预先计数的，是固定样本的整数算术、有限矩阵、一次 \(p\) 级单位 Kummer 及两个投影的验收；尚不能预先计数的是找到一般证明所需的商层数、曲线数或人天数。最值得继续的工作是原箭头对带标记区域的一次可复核求值，以及可复用的全局加权与迭代界。单纯增加样例的数量不进入这条验收链。

实际复核包含 \(\mathbb F_{293^4}\) 上共轭基秩 4、32 个检测泛函秩 32、阈值两侧的整数幂、两行误差和剩余模长度、\(d=3,33,63\) 的整数分解和 (15.3)。素因子的素性逐级用 \(n-1\) 的完全分解和模幂证书复核。群提升、判别式解释和原端点分析为自然语言研究。Lean 编译、证明体、内核闭包和原目标验收四项均未运行。

<a id="finite-slot-certificate"></a>
## 16. 有确定终点的计算，以及它距原 III.3.12 有多远

原目标对**每一组指定的** III.3.11 数据 \(T\)，用同一表示中的固定 q 和 Θ 的全部允许像，证明 \(q_s(T)\le H_{\rm orig}(T)<+\infty\)。本轮得到两个可以交接的数学结果。第一，在已有具体区域中，把一批明确给出的点做成可以算出**准确余量**的下界。第二，证明一整类输入达到系数 1，包括坏位深度任意大的例子。对原目标，本轮把证书的来源追到最后一次带标记的求值，并明确辨认出目前两个项目接口各自保留了什么。以下 \(H_{\rm lit}\) 专指仓库中所有槽先取并再取 hull 的具体读数。\(H_{\rm orig}\) 专指原文。两者有不同的来源。[原命题及两端](IUT-TEXT/III.txt#L10326) · [具体区域](../Iut/Concrete/ThetaRegion.lean#L170) · [两种标签读法的定理方向](../Iut/Concrete/Literal.lean#L19)

### 16.1 仓库实际提供的运算

取 \(\ell\ge5\) 为素数，\(n=(\ell-1)/2\)。第 \(j\) 行有 \(s=j+1\) 个槽，\(1\le j\le n\)。固定有理素数 \(p\)。\(b\) 遍历 \(F_{\rm mod}\) 在 \(p\) 上的**全部**位置，沿给定截面取 \(K\) 中的位置，局部域记 \(k_b\)。赋值归一到 \(\operatorname{ord}_p(p)=1\)。记

\[
 \lambda_b=\frac{[(F_{\rm mod})_b:\mathbb Q_p]}{[F_{\rm mod}:\mathbb Q]},\qquad
 a_b=\operatorname{ord}_p(r_b),\qquad
 A=\sum_p\log p\sum_{b\mid p}\lambda_b a_b .
\]

权重逐 \(p\) 和为 1。\(r_b\) 是项目选出的 Tate 参数的 \(2\ell\) 次根，在标记集外为 1。每个 \(a_b\ge0\)。具体模型中 q 一侧恰是 \(-A\)。这里有一条真正的桥，源码先证明一个槽乘 \(r_b^e\) 的体积改变量，再对截面和元组求和，得到 \(F\) 上 q 除子的读数。用 \(F_{\rm mod}\) 的局部次数给元组加权、用 \(F\) 的剩余次数计 q 除子，是这条定理已经处理的两个环节。根里已经有 \(2\ell\) 的分母。[每位根及其方程](../Iut/Concrete/ThetaLocalConstruct/Data.lean#L281) · [截面权重](../Iut/Concrete/Container.lean#L139) · [两个归一化之间的证明](../Iut/Wall/QPilotRegion.lean#L220) · [全局 q 区域的读数](../Iut/Wall/QPilotRegion.lean#L321)

一个元组 \(c=(b_0,\ldots,b_j)\) 的权是 \(\prod_i\lambda_{b_i}\)。在具体 Θ 区域中可以取恒等的局部线性作用，依次把带标记的乘数放在每个槽 \(i\)。所得的真实子集是

\[
   \bigcup_{i=0}^{j}\iota_i(r_{b_i}^{\,j^2})\,L(c),\qquad
   L(c)=\operatorname{span}_{\mathbb Z_p}
                \{y_0\otimes\cdots\otimes y_j : y_i\in L_{b_i}\}.
\]

\(L_b\) 是普通单位的归一化 log 像。取 \(p^*=p\)（奇 \(p\)）和 \(2^*=4\)，即 \(L_b=(p^*)^{-1}\log U_1(k_b)\)。源码写成 \((2p)^{-1}\log U_1\)，在奇素数处两者相差一个 \(\mathbb Z_p^\times\) 因子，定义同一个格。特别地 \(1\in L_b\)，可取 \(u=\exp(p^*)\) 得到；若直接按代码写分母就取 \(\exp(2p)\)。这里的源单位有非零对数。槽交换同时重排元组及其张量因子。在一行枚举 \(s\) 个换位就遍历了标记可落的槽。各元组取 hull 时可以用不同的见证，一次全局置换在每个元组上的最佳性没有被用作前提。[归一化 log 的定义](../Iut/Concrete/LocalConstruct/LocalLogShell.lean#L39) · [原始张量格](../Iut/Concrete/LocalConstruct/Theory.lean#L120) · [恒等作用](../Iut/Concrete/LocalConstruct/Theory.lean#L289) · [标签与元组共同重排](../Iut/Concrete/Ind1Invariance.lean#L592)

本仓早已指出取并会引入槽赋值的最小值，历史样本还代入过固定分布。下面新算的是具有实际位置权重、允许同一 \(p\) 上多个不同深度、并保留普通单位贡献的精确公式。作为外部复用核对，已将本地这条路线所用的七份上游源码与提交 `553076af459e7a401bfee63a4607814d1c854477` 比对，统一换行后内容相同。七份是 ThetaRegion、Literal、LocalConstruct/IndAut、WallEquiv/VcI、Wall/QPilotRegion、Wall/Ind3、Cor312/Statement。上游的 Cor312Variant 是带指定读数的命题，ABC 装配使用它作为输入。[本仓先前的最小值计算](LITERAL-RECALC.md#L5) · [上游具体张量区域](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Concrete/ThetaRegion.lean#L165-L183) · [上游命题的量词](https://github.com/lana-agents/iut/blob/553076af459e7a401bfee63a4607814d1c854477/Iut/Cor312/Statement.lean#L28-L52)

### 16.2 把每个输入算到一个确定的数

令 \(\rho_b=-\min_{0\ne y\in L_b}\operatorname{ord}_p(y)\ge0\)。对每个槽选一个达到最小赋值的 \(y_i\)；其存在性和未乘标记时的最小 hull 都已有证明。先把 \(r_{b_i}^{j^2}\) 放进固定槽 \(i\)，取这组 \(y\) 的纯张量。在张量代数的每个域因子中，投影是各域嵌入的像的乘积，赋值为 \(j^2a_{b_i}-\sum_k\rho_{b_k}\)。每个域嵌入保持 \(\operatorname{ord}_p\)。反过来，任一格中纯张量的赋值都至少为此数，对 \(\mathbb Z_p\) 线性组合使用超度量不等式仍成立。这同时给出包住像的盒和达到每个半径的点。再对 \(i\) 取并，每一域因子中的最小半径盒就确定了。按分量实维数归一化后的局部带符号读数恰为

\[
  \left(\sum_{i=0}^{j}\rho_{b_i}-j^2\min_{0\le i\le j}a_{b_i}\right)\log p. \tag{16.1}
\]

原始张量格可能在整闭包中有非平凡指数。(16.1) 计算的是这族点的 **hull**，整闭包的测度只用于给盒的读数归一化。全程保留了原始张量格。[最大半径见证](../Iut/WallEquiv/VcI.lean#L469) · [见证的纯张量及其最小盒](../Iut/WallEquiv/VcI.lean#L529) · [归一化读数](../Iut/WallEquiv/VcI.lean#L603)

**这些点还能同时放进一组正测度的算术区域。** 对 \(z\in\mathcal O_{k_b}\)，直接取普通单位 \(\exp(2p z)\)。所以 \(\mathcal O_{k_b}\subset L_b\)，这一包含也已有源码证明。取 \(R(c)\) 为各槽整数环生成的原始张量整序。它是满秩紧开格，含 1，在每个域投影落入整数环，因此其 hull 恰是整闭包的单位盒。任给一行及一个固定换位，在每个 \(p,c\) 同时取 \(\iota_i(r_{b_i}^{j^2})R(c)\)。每个局部区域都在相应的具体 Θ 区域内，且具有正的有限测度。在未标记、奇且非分歧的素数上 \(R(c)\) 就是整闭包，两种参考一致。无穷位取半径 1 的张量欧氏闭球，它包含 \(1^{\otimes s}\)。这些集合按元组取积给出一份具体的 adelic 区域。每行只需 \(s\) 份这种全局区域，覆盖所需各槽。在一个元组的投影上择优，不会迫使不同位置的局部箭头作任意拼接。此构造消除了「孤立点体积为零」和「各处所选点拼不成算术区域」两个疑问。原跨列求值是否产生这些区域是 §16.5 的另一项检查。[整数环确实在因子 log-shell 内](../Iut/Concrete/LocalConstruct/LocalLogShell.lean#L78) · [整序包含于原始张量 log-shell](../Iut/Concrete/LocalConstruct/LogShell.lean#L334) · [非分歧时的整序等式](../Iut/Concrete/LocalConstruct/Prop14Lattice.lean#L277)

对每个 \(p\)，将正的 \(a_b\) 去重排序为 \(0<x_1<\cdots<x_h\)，置 \(x_0=0\)、\(\Delta x_k=x_k-x_{k-1}\)、\(\beta_{pk}=\sum_{b:a_b\ge x_k}\lambda_b\)。因为元组取乘积权，所有 \(s\) 个槽均达到 \(x_k\) 的权重恰为 \(\beta_{pk}^{s}\)。于是 \(\mathbb E\min_i a_{b_i}=\sum_k\Delta x_k\beta_{pk}^{j+1}\)，而单槽的 \(\mathbb E a_b=\sum_k\Delta x_k\beta_{pk}\)。这两个等式对带重复位置的元组同样成立。定义

\[
 K_n(z)=\frac1n\sum_{j=1}^n j^2z^j,\quad
 D=\sum_p\log p\sum_k\Delta x_k\,\beta_{pk}\bigl(K_n(\beta_{pk})-1\bigr),
 \qquad \bar s=\frac{n+3}{2}=\frac{\ell+5}{4}.
\]

在无穷位取各槽的数 \(2\)，其纯张量在半径 \(\pi^s\) 的张量度量球中，每个域投影的绝对值均为 \(2^s\)。取这个点生成的半径盒，仅在取 hull 之后使用该盒。有限位用 (16.1)。记

\[
 C=\bar s\left(\log 2+\sum_p\log p\sum_{b\mid p}\lambda_b\rho_b\right).
\]

**这组指定的见证给出的盒的读数为 \(-A+C-D\)，因此 \(H_{\rm lit}-q_s\ge C-D\)。** 恒等作用已实现整个计算。也可以在每个有限槽只用 \(y=1\)、在无穷位只取 1，此时同一计算给出更简单的余量 \(-D\)。每组见证都明确指定了在哪个集合里取点。若 \(C-D<0\)，这个差值给出本组盒尚欠的数额。[无穷位的纯张量度量](../Iut/Concrete/LocalConstruct/ArchLogShell.lean#L215) · [无穷位 shell 的半径](../Iut/Concrete/LocalConstruct/ArchLogShell.lean#L277)

**工作量。** 输入是指定的数域、标记集、截面及其局部数据的有效表示。只需枚举标记素数、2 和 \(K\) 的分歧素数，其他素数的 \(a_b=\rho_b=0\)。若 \(p\) 上有 \(m_p\) 个位置，给定 \(a,\rho,\lambda\) 后，排序和用递推逐项计算 \(K_n\) 共用 \(O(\sum_p m_p\log m_p+n\sum_p m_p)\) 次有理数运算，无需枚举 \(m_p^{j+1}\) 个元组。\(C-D\) 只有有理系数乘 \(\log p\)。清分母后比较 \(\prod_{E_p>0}p^{E_p}\) 与 \(\prod_{E_p<0}p^{-E_p}\)，每个整数的位长不超过 \(1+\sum_p |E_p|\lceil\log_2p\rceil\)。相等也能精确识别。这个界从局部数据已给定开始计算；由数域方程取得分歧分解、Tate 深度及一组局部整基的成本须另计。

野分歧位的 \(\rho_b\) 也有预先可写的截断界。用整数赋值 \(v(\pi_k)=1\)，置 \(e=v(p)\)、\(f=[\kappa:\mathbb F_p]\)、\(N=\lfloor e/(p-1)\rfloor+1\)。深单位对数给出 \(\log U_N=\mathfrak m^N\)。取剩余域的一组 \(\mathbb F_p\) 基的提升 \(t_i\)。按 \(U_h/U_{h+1}\simeq\kappa^+\) 逐级消去首项，\(1+t_i\pi_k^h\)（\(1\le h<N,1\le i\le f\)）生成 \(U_1/U_N\)。因而 \(m_{\log}=\min\{N,\;v(\log(1+t_i\pi_k^h))\}\)，取零对数时把赋值视作 \(+\infty\)。\(\rho_b=(v(p^*)-m_{\log})/e\)。每次只要算模 \(\mathfrak m^N\)。在 log 级数中，令 \(B=\max(16,4e^2,2N)\)。对 \(k\ge B\)，第 \(k\) 项的赋值至少 \(k-e v_p(k)\ge k-e\sqrt{k}\ge N\)。所以每个至多用 \(B-1\) 项，运算前可把整分子算到 \(\mathfrak m^{N+e\lfloor\log_p B\rfloor}\) 再除。奇 \(p\) 且 \(e<p-1\) 时直接有 \(\log U_1=\mathfrak m\)、\(\rho_b=1-1/e\)。只使用 \(y=1\) 的版本连这批局部 log 也可以省去。

### 16.3 一整类达到系数 1 的输入和一个无界深度的例子

**命题。** 对每个 \(p\)，若有正 Tate 深度的位置在该纤维内总权重至多 \(1/2\)，那么对任意这些位置的深度和任意素数 \(\ell\ge5\)，具体的全槽读数满足 \(q_s\le H_{\rm lit}<+\infty\)。下界只用各槽的 \(1\)。有限性在本模型中来自每个分量的有界可容许区域、几乎处处的单位参考以及有限的行数，这些均已写进区域构造。[逐分量可容许性](../Iut/Concrete/ThetaRegion.lean#L185) · [几乎处处的单位区域](../Iut/Concrete/ThetaRegion.lean#L274)

证明很短。每个尾权重 \(\beta_{pk}\le1/2\)。对 \(j=1,2,3,4\)，\(j^2/2^j\) 依次为 \(1/2,1,9/8,1\)，以后逐项下降。因此任意前 \(n\) 项的平均至多 1，第三项多出的 \(1/8\) 已由第一项支付。\(K_n(\beta_{pk})\le1\)，每一项 \(\Delta x_k\beta_{pk}(K_n(\beta_{pk})-1)\le0\)。故 \(D\le0\)，即得结论。它只限制标记在同一素数上的**分布**，允许 \(\operatorname{ord}_p(q)\) 任意大。

**还可以预先算出最少要移几次标记。** 每行先保留原指定位置。只使用 \(t_j\) 个不同候选位置时（\(1\le t_j\le j+1\)），同一证明把该行的 \(\beta^{j+1}\) 换成 \(\beta^{t_j}\)，因为事件只涉及选定的 \(t_j\) 个坐标。对给定输入，增加一个位置，尚待支付的 q 代价减少

\[
 G_j(t_j)=\frac{j^2}{n}\sum_{p,k}\log p\,\Delta x_k(1-\beta_{pk})\beta_{pk}^{\,t_j}.
\]

每行的 \(G_j(1),\ldots,G_j(j)\) 自前往后不增。先全取 \(t_j=1\)，总是选下一项收益最大的行，直到 \(-D\) 的相应版本非负，或已取尽。这个次序在**只用整序见证、以新增候选位置个数计成本**的范围内是最优的。证明是把每行的收益降序表合并，前 \(k\) 大收益总可取为各表的前缀，其和是做 \(k\) 次所能得到的最大改善。并列时取同一行较早的项即可。总共至多 \(n(n+1)/2\) 个候选增量，行间收益之差是有理系数的 \(\log p\) 之和，可用整数幂比较。不够时直接报出该候选族的最大值。对尾权重均至多 \(1/2\) 的一般输入，还有事先固定的较短清单。\(n\ge3\) 时前三行分别用 \(2,3,4\) 个位置，\(j\ge4\) 只用 \(1+\lceil\log_2(j^2)\rceil\le j+1\) 个。每个 \(j\ge4\) 的项满足 \(j^2\beta^{t_j-1}\le1\)，第三行多出的 \(1/8\) 可由第一行吸收。所需位置总数为 \(O(n\log n)\)。在 \(n=2\) 时只用 \(1,3\) 个位置就够。这个计数约束的是显式区域数，原跨列构造的证明工作另计。

这条不等式还能精确标出槽置换的适用范围。在所有允许的 \(\ell\) 中，统一的最大尾权重门槛为 \(r=0.5204100118\ldots\)，其中 \(r+4r^2+9r^3+16r^4+25r^5=5\)。证法是 \(1/2<r<0.53\)，\(K_2(0.53),K_3(0.53)<1\)，\(K_5(r)=1\)。从第六项起 \(36(0.53)^6<1\)，后面项的比值至多 \((7/6)^2\,0.53<1\)。剩下的 \(n=4\) 对应的 \(\ell=9\) 不在范围内。超过 \(r\) 时 \(\ell=11\) 的这一系数已超过 1。此处的锋利性只指这条逐尾系数判据。若固定 \(d_F=[F_{\rm mod}:\mathbb Q]\)，且每个有标记的 \(p\) 上至少还有一个位置 \(a_b=0\)，还有另一个直接结论。此时 \(\beta\le1-1/d_F\)。由 \(\sum_{j\ge1}j^2 z^j=z(1+z)/(1-z)^3\)，只要 \(n\ge d_F(d_F-1)(2d_F-1)\)，每个 \(K_n(\beta)\) 也至多为 1。这里的 \(\ell\) 始终是所给数据的 \(\ell\)。

**实际曲线族。** 取 \(k_0=\mathbb Q(\sqrt{13})\)、\(\alpha=(1+\sqrt{13})/2\)、\(d=3+30t\)（\(t\ge0\)），令 \(u=\alpha^d\)，取

\[
 E_d:\quad y^2+xy=x^3+u,\qquad c_4=1,\quad \Delta=-u(1+432u),\quad j(E_d)=1/\Delta.
\]

\(N(\alpha)=-3\)，3 分裂成 \((\alpha)\) 及其共轭。在前者判别式的赋值为 \(d\)，模 3 的节点有相异切线 \(y=0,y=-x\)，故为分裂乘性约化。在共轭位判别式为单位。\(j\) 在这两个位置的赋值不同，所以 \(\mathbb Q(j)=k_0\)。这条整模型在所有坏位的 \(c_4\) 都为单位，故曲线半稳定。只标记 \((\alpha)\) 符合原文选取坏位集合的规则。取 \(\ell=5\)，坏纤维的两个权重各 \(1/2\)，根深度分别是 \(x=d/10\) 和 0。第一行的平均代价是 \(x/4\)，第二行是 \(4x/8=x/2\)，q 侧是 \(x/2\)。两行平均后余量为

\[
 \left(\frac{x}{2}-\frac{3x}{8}\right)\log 3
       =\frac{d}{80}\log 3 .
\]

其他素数用各槽的 1 已经够用。这样任给 \(t\) 都有同一套源点和严格正的、随 \(d\) 线性增长的余量。大像条件在此例也有独立的算术检查。2 在 \(k_0\) 惰性，\(\bar\alpha\in\mathbb F_4^\times\) 的阶为 3，故 \(u\bmod2=1\)。约化曲线来自 \(\mathbb F_2\)，在那里有 4 个点。平方 Frobenius 在 5 扭点的特征多项式为 \(X^2+3X+4\bmod5\)，判别式为 \(3\bmod5\)，从而表示不可约。在 \((\alpha)\) 用 Tate 曲线，\(5\nmid d\) 给出惯性上的非平凡阶 5 剪切。不可约性给出固定线不同的一条共轭剪切，取幂生成上下初等矩阵，故像包含 \({\rm SL}_2(\mathbb F_5)\)。再取正规扩张 \(F=k_0(i,E[6])\)，次数整除 \(2\,|{\rm GL}_2(\mathbb F_2)|\,|{\rm GL}_2(\mathbb F_3)|=576\)。因为商的阶与 5 互素，所有这些阶 5 元素都留在限制像里。归一到 \(\operatorname{ord}_3(3)=1\) 也使根深度在提升位置后保持 \(d/10\)。这部分构造了曲线、标记、局部深度和大像见证。它并未构造两个相邻 Hodge theater 的实际区域。[原文对标记集的许可](IUT-TEXT/I.txt#L3144) · [两种剪切产生大像的现有证明](../Iut/Tripod/SL2Generation.lean#L156)

若目标只是达到 q，在这个族上能把**最少工作量**写成三个数。这里只计整序见证，单位 log 和无穷位的额外收益都取 0。第一行始终固定，代价 \(x/2\)。第二行允许的位置数从 1 变到 2 再变到 3，代价依次为 \(2x,\ x,\ x/2\)。两行平均相应为 \(5x/4,\ 3x/4,\ x/2\)，均以 \(\log3\) 为单位。q 正好是 \(x/2\)。一个新位置最多把第二行代价从 \(2x\) 降到 \(x\)；若用在第一行，收益更少。故从两个初始固定位置出发，**两个新增位置是达到 q 的最小数目，且可全部用于第二行**。这两个全局换位是 \((2,0),(2,1)\)，又由固定标记槽的 \((0,1)\) 共轭。若原求值对该未标记两槽的交换自然，那么只用证明一条换位的区域级公式，另一条随共轭给出。这准确说明了一份原来源证明能替代多少逐例检查。

**回看曾经耗去最多时间的 293。** 在 §14.7 的同一 \(d=63\) 样本中，293 是中性素数，\(e=30<292\)。直接取 \(u=\exp(\varpi)\)，则 \((p^*)^{-1}\log u=\varpi/293\)，整数赋值为 \(-29\)。两行各取这个点的纯张量，恒等作用就在具体 log-shell 中给出 \(\frac52(1-1/30)\log293=\frac{29}{12}\log293\)。这超过以前 3 处算出的全部差额 \(\frac{189}{20}\log3\)，比较整数 \(293^{145}>3^{567}\) 即可。在旧实验中源参考是最大整序，在这里源参考是实际单位 log 张量格；这是所得结论的语义差别。值得从中移植到原文的是明确写出的普通单位和它的标记求值，原文源对象的选取仍须按 §16.5 核对。[两行的旧门槛](#finite-workload) · [驯情形现有精确公式](../Iut/WallEquiv/VcI.lean#L435)

### 16.4 若单组证书不足，可以算完这个具体模型

上游具体模型在每个因子允许保持 \(L_b\) 的**所有** \(\mathbb Q_p\) 线性可逆映射。利用这个已明确的群，下面甚至可以消去它的全称枚举。给定一个候选标记位置 \(b\) 和行 \(j\)，置 \(x=r_b^{j^2}\)，计算整数

\[
 m_{b,j}=\max\{h\in\mathbb Z:x L_b\subset p^h L_b\}.
\]

把「乘 \(x\)」写在 \(L_b\) 的任一组 \(\mathbb Z_p\) 基中，\(m_{b,j}\) 是非零矩阵元素赋值的最小值。于是全槽、全模型允许线性作用的**准确**局部 hull 读数为

\[
 \left(\sum_i\rho_{b_i}-\min_i m_{b_i,j}\right)\log p . \tag{16.2}
\]

上界来自 \(xL_b\subset p^mL_b\)，所有允许作用保持右边的格。为达到上界，在 \(xL_b\) 里取 \(p^m v\)，使 \(v\) 在 \(L_b/pL_b\) 非零。取最大半径向量 \(y\in L_b\)，它也在 \(L_b/pL_b\) 非零，否则 \(y/p\in L_b\) 的半径更大。两个本原向量均能扩为整基，故有一个格自同构送 \(v\) 到 \(y\)。别的因子取恒等及其最大半径向量。所得一个真实的纯张量在每个域投影同时达到声称半径。对槽取并即得 (16.2)。在奇素数 \(e<p-1\) 的情形，\(L_b\) 是分式理想，故 \(m_{b,j}=\lfloor j^2a_b\rfloor\)。允许这些自同构后，单个槽较恒等的额外收益恰为 \((j^2a_b-m_{b,j})\log p\)。[允许线性作用的确切定义](../Iut/Concrete/LocalConstruct/IndAut.lean#L210) · [仓库已有的固定槽体积差](../Iut/WallEquiv/Gap.lean#L747)

举一个局部算例。取 \(k=\mathbb Q_7(\varpi)\)、\(\varpi^2=7\)、乘数 \(x=\varpi\)。这里 \(L=\varpi^{-1}\mathcal O_k\)。在基 \((\varpi^{-1},1)\) 中，乘 \(x\) 的矩阵是 \(\bigl(\begin{smallmatrix}0&7\\1&0\end{smallmatrix}\bigr)\)，故 \(m=0\)。恒等时 \(xL=\mathcal O_k\)，半径 1。交换两基向量是具体模型允许的整线性作用，把 \(xL\) 中的 1 送到 \(\varpi^{-1}\)，所得半径为 \(\sqrt7\)。这直接实现了公式里的额外 \(\tfrac12\log7\)。

一般 \(p\) 的矩阵计算也有输入精度界。沿用 §16.2 的整数赋值，设 \(t=m_{\log}-v(p^*)\)、\(g=N-v(p^*)\)、\(\nu=v(x)\)。有 \(\mathfrak m^g\subset L_b\subset\mathfrak m^t\)，且后一格的最小赋值在 \(L_b\) 达到。于是

\[
 \left\lfloor\frac{\nu+t-g}{e}\right\rfloor
     \le m_{b,j}\le \left\lfloor\frac{\nu}{e}\right\rfloor .
\]

§16.2 的有限单位对数和深理想的一组基生成整个 \(L_b\)。对上述有限个候选 \(h\)，检验每个生成元乘 \(p^{-h}x\) 是否属于 \(L_b\)，只须在 \(\mathfrak m^t/\mathfrak m^g\) 判断剩余类（赋值低于 \(t\) 直接失败）。已知 \(\nu\) 时，取 \(x\) 到模 \(\mathfrak m^{\nu+g-t}\) 足够，因为乘上任意 \(L_b\) 元素后的误差都在 \(p^h\mathfrak m^g\)。当 \(t=g\) 时赋值本身已经足够。有限位全局求和可逐 \(j\) 排序 \(m_{b,j}\)，用 §16.2 的尾权重公式取最小值的期望。若最小值为负，先减去最小值使列表从 0 起算，最后加回常数。

无穷位也有一个闭式。设一个元组有 \(s\) 个因子，其中 \(k\) 个为复因子，其余为实因子。给每个复因子取实正交基 \(1,i\)，实因子取 1。每个域投影把乘积基送到 \(\pm1,\pm i\)。当 \(k\ge1\)，实部和虚部各有 \(2^{k-1}\) 个符号项，支撑不交，故投影的欧氏算子范数为 \(2^{(k-1)/2}\)；在 \(k=0\) 时为 1。每个投影在闭球上达到这个范数。允许的符号、共轭作用保持球，因此 hull 的准确归一化读数是 \(s\log\pi+\tfrac12\max(k-1,0)\log2\)。全复情形的这个数也已出现在上游的自然语言计算，代码给出对应的粗界。[张量度量](../Iut/Concrete/LocalConstruct/ArchLogShell.lean#L208) · [无穷位作用](../Iut/Concrete/LocalConstruct/ArchIndAut.lean#L197) · [已证界与上游的精确计算说明](../Iut/WallEquiv/VcI.lean#L70)

因此，在给定可有效读出的局部域、标记根和截面的前提下，**每一份固定数据的具体全槽模型比较都有终止的判定程序**。用 (16.2) 和精确无穷位公式，清分母后只需比较 \(\pi^u M\) 和 \(N'\)，\(u>0\)、\(M,N'\) 为正整数。用 \(16\arctan(1/5)-4\arctan(1/239)\) 的交错级数给 \(\pi\) 夹出有理区间，直到两边分开。\(\pi\) 的超越性排除了相等，所以必停。此精确版本没有在本轮给出可用的先验精度上界。通常先做 §16.2 的证书，那里连最后的位长都事先有界。这里用到的超越性只处理数值相等，已有独立的形式化证明。[Isabelle AFP 的 \(\pi\) 超越性定理](https://isa-afp.org/entries/Pi_Transcendental.html)

### 16.5 原 III.3.12 接到哪一步，在哪里停止

1. **在两端都能写出的最小对象是「带标记的乘数作用在 1 上」。** 具体模型取 \(y_i=1\) 得 \(\iota_i(r_{b_i}^{j^2})\)。本仓 Step V 也有真正的张量点接口，成员证据是 \(\exists\phi\in\Phi,\ x\in O_{\rm hol},\ z=\phi(\varpi x)\)。在含恒等的指定作用族上，取 \(\phi=\mathrm{id}, x=1\) 得到该接口中相同形状的点。故稀疏族迁移回原文时，连整个 \(L(c)\) 的比较都可以省去。沿原来源要认出的是这个点在指定第 1 列的投影绝对值 \(|r_{b_i}|^{j^2}\)，以及固定 q 的 \(-A\) 权重。\(F_{\rm mod}\) 的截面、\(K\) 的完备化以及项目某个 base tensor 的位置必须沿同一输入追踪。[Step V 实际成员类型](../LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean#L668) · [具体 q 的求和定理](../Iut/Wall/QPilotRegion.lean#L220)

2. **定位到原文的运算。** III.3.5(ii)(a) 给普通单位的 Kummer 像落入 shell。III.3.11(i)(b) 给 splitting monoid 在有标记的有理张量空间上的乘法作用。(ii)(a) 的局部同构保持同一列的 log-volume。跨到相邻列时，最后一次 evaluation 连着符号条件、乘积公式及直接乘积区域的相容性。将固定列的标记发生元作用于参考 1，沿该复合映到目标列，再在 \(c\) 的任一域因子投影；要读出其标记赋值，并给出它所来自的同一合格区域。每行的换位只作用于整条源数据。只要每个所用投影都由一个合法全局输出实现，取并后逐投影做 hull 本来就容许不同投影选不同输出。故无需另造「为每个元组任意独立选一个箭头」的全局作用。[普通单位的 Kummer 包含](IUT-TEXT/III.txt#L6078) · [标记作用](IUT-TEXT/III.txt#L9190) · [procession 的作用范围](IUT-TEXT/III.txt#L9256) · [列内同构](IUT-TEXT/III.txt#L9321) · [最后求值及全局条件](IUT-TEXT/III.txt#L9703)

3. **这次源码核对已经给出一个确定结果。** 原文侧的 `sourceMultiradialPossibleImage` 确实能产生 `Set ℝ` 并证明非空、Ind1/2 识别和 Ind3 上比较。继续追到**取商以前**，选择的数据类型是「剧场指标 × 自然数」，区域读数按定义恰为单点集 \(\{\text{该剧场的 thetaPacket.logVolume}\}\)，且对所有选择恒定。于是任何只以这个标量为自变量的函数，都给两种标记选择同一个值。第 4 项的两个实际投影绝对值不同。因此增加选择次数、迭代层或商关系，均无法**从这份读数恢复所需的逐标记投影**。另一个入口保存了张量点及 \(\phi,x\)，其来源是 Step V 的算术输入。此外 S1951 已有三个角拼出跨列方块的实际代码，结果是 strip 同构和单位作用，其专用位置类型为 `FinitePrimePlace 2 7`。在所查接口中没有给出由这条箭头在**本例**第 1 列产生指定张量区域的映射。原文要求进入的是可解释成 prime-strip 的区域族。原区域代表必须在取上述恒定读数以前另行取得。这项核查到此已经结束。[取商前的选择](../tmp/sheaf/xif/paper/S3138SourceProcessionCoreActual.lean#L52) · [单点定义和恒定性](../tmp/sheaf/xif/paper/S3138SourceProcessionProfileActual.lean#L67) · [取商后的输出](../tmp/sheaf/xif/paper/S3139SourceMultiradialQuotientActual.lean#L75) · [S1951 的实际方块](../tmp/sheaf/xif/paper/S1951KummerEvaluationSquareActual.lean#L305) · [原文要求的区域](IUT-TEXT/III.txt#L10412)

4. **原文层的下一次验收可以固定在一个元组上。** 在 §16.3 的分裂素数 3 上取第二行的 \((b_{\rm good},b_{\rm bad},b_{\rm bad})\)，槽按 \(0,1,2\) 排列，**默认标记槽 2 是坏槽**。在同一目标元组比较默认位置和换位 \((2,0)\)。参考 1 在好槽给三个 1 的纯张量，所有域投影绝对值为 1；默认位置则给 \(3^{-4d/10}\)。可直接定 \(d=3\)，两个读数是 \(1\) 和 \(3^{-6/5}\)。这个全例只有 \(2^2+2^3=12\) 个有序元组，真正从增加位置而获益的第二行元组只有 \((好,坏,坏),(坏,好,坏),(好,好,坏)\)。§16.2 已给出每个换位在所有位置同时使用的全局算术区域。检查原箭头时，取**一次** III.3.10.2 的带标记求值，记录源元组按换位拉回的坐标，从合格的同一全局区域到第 1 列，取得好槽分量的成员证据。下界只要求该成员在各域投影绝对值至少 1；若已证明投影整，验收就是在剩余域中非零。原 I.4.10 已把各级 capsule 间的箭头定义为全部 capsule-full poly-morphisms，裸标签重排有出处。还要核的是带乘数、带区域的求值是否按该重排进入 \(U_{2,3}\)。若原过程只允许先固定标签取 hull 再计算，就在这一个混合元组上结束这条移植。若给出对元组自然的换位公式，通过未标记槽的交换可覆盖另一换位，并逐一覆盖上述三种元组，配合未改动的第一行达到 q。一个孤立成员只证明自己的那一项。[procession 态射的原定义](IUT-TEXT/I.txt#L6763) · [标签换位如何搬动元组](../Iut/Concrete/Ind1Invariance.lean#L592) · [原文的逐行逐位允许像](IUT-TEXT/III.txt#L10376)

5. **全量词目标还有两个独立范围。** 当一个有标记的 \(p\) 上所有位置深度相同且为正时，\(\min a=a\)，所有槽置换均给同一个整序读数。特别是 \(F_{\rm mod}=\mathbb Q\) 的有理 Frey 输入，每个有标记的 \(p\) 上只有一个位置，全部落在这一分支。(16.1) 给出普通单位在具体模型中实际贡献多少，(16.2) 给出扩大到全格自同构时该处的准确值。实际 Ism 的作用范围由原文决定。另一方面，原上界 \(H_{\rm orig}<+\infty\) 量化于全部原允许像，包括所有相关竖直迭代。一批见证的紧性只给这批见证的有限性。向原文继续的证据应分别是有来源的正向成员和覆盖原全部像的容器，两者均需独立于 IV 和 ABC 的后继消费者。[上游对扩大作用群的说明](../Iut/Concrete/ThetaRegion.lean#L38) · [原文的有限性断言](IUT-TEXT/III.txt#L10404)

**判断。** 可以投入有确定规模的工作去核算一组输入，或者交付 §16.3 的整族结论。即使只准用恒等线性作用，已经有上述两类正结果。对于原 III.3.12，下一项有辨别力的工作是 §16.5 第 4 项这个指定成员的来源检查。逐层寻找完整 Galois 群的新箭头已退出当前工作。全体原数据的证明长度、原有限性及由原 III 接 IV、ABC 的全链，本次均未得到上界或完成证明。本轮工作是自然语言推导、源码对照和有限算术核对。Lean 的 statement_compiles、proof_body_checked、kernel_closed、target_accepted 四项均为 NOT_RUN。

数值复核用了 20 组有理权重与行数的组合，比较尾权重公式与完整元组枚举；用 240 个候选次数预算核对最少换位算法和穷举的最优值。另核对了 \(\mathbb F_2,\mathbb F_4\) 的曲线点数、四个深度的余量、293 的整数幂不等式及门槛 \(r\) 的有理上下界。

### 16.6 全局对数路线能否代替单点来源检查

先把算术模型里的全局量写到同一归一化下。取 §16.3 的 \(d=3\) 例，\(x=d/10=3/10\)、\(\ell=5\)、两行分别有 2、3 个槽，两个位置的权重各为 \(1/2\)。固定 q 侧为

\[
 q_s=-\frac{x}{2}\log 3=-\frac{3}{20}\log 3.
\]

全取槽的 literal 模型平均读数为

\[
 H_{\rm lit}=-\frac12\left(\frac{x}{4}+\frac{x}{2}\right)\log 3
           =-\frac{3}{8}x\log 3=-\frac{9}{80}\log 3,
 \qquad H_{\rm lit}-q_s=\frac{3}{80}\log 3.
\]

若第一行保持原槽、第二行再纳入另外两个候选槽，平均读数恰等于 \(q_s\)。这些等式是 §16.2 的尾权重平均在这个有限输入上的完整算术结果；它们不用逐个手算十二个元组，也显示了全局平均确实能把模型侧的缺额算清。它们的左端仍是 \(H_{\rm lit}\)，并未因此变成 \(H_{\rm orig}\)。

这个有限例不必把 §16.5.4 的单点测试扩成十二个元组的逐项箭头。第一行保留原指定槽（该行 \(j=1\)，槽为 0、1）；第二行只需比较整条源数据的三个版本：原槽 2、全局换位 \((2,0)\)、全局换位 \((2,1)\)。例如目标元组 \((好,坏,坏)\) 在 \((2,0)\) 下的源坐标是 \((坏,坏,好)\)；目标元组 \((坏,好,坏)\) 在 \((2,1)\) 下也拉回到 \((坏,坏,好)\)。第三个获益元组 \((好,好,坏)\) 分别拉回到 \((坏,好,好)\) 或 \((好,坏,好)\)。这正是「换位作用于整条源数据」而非为每个元组任意拼箭头。若这些有限个整数据输出（包括第一行既有输出）都在原允许族内，且原 hull 按同一 procession 权重接收它们，§16.3 的两新增位置计算就给出本例的整体下界；若只在具体模型内合法，仍只是 \(H_{\rm lit}\) 的证书。未标记槽的交换若要把两次换位缩成一次，仍须给出原求值的区域级自然性公式，不能只用裸标签置换代替。

现有的全局标量接口也不能补上这一步。按 §16.5.3，取商前的选择读数恒为同一个 \(L=\text{thetaPacket.logVolume}\)。因此对任意函数 \(f\) 和任意选择权重，\(f(L)\) 及其平均都不依赖标记选择；但 §16.5.4 的同一目标元组中，好槽与默认坏槽的投影绝对值分别是 \(1\) 与 \(3^{-6/5}\)，其对数相差 \(\frac65\log3\)。所以只从这个常值读数出发，做更多选择、迭代或平均，都不能恢复原输出所需的标记投影。此处排除的是**标量接口上的聚合路线**，不是排除一切全局度数论证。

全局度数论证仍可能绕开指定投影成员，但它必须给出一份独立于该投影的原文证书：对同一个 \(p=3,\ell=5,d=3\) 输入，从原允许的 evaluation 直接定义 procession 归一化的整体度数/对数读数 \(D\)，逐项核实两行权重、元组权重和行平均，并由原输出定义证明 \(q_s\le D\le H_{\rm orig}\)，或直接证明 \(q_s\le H_{\rm orig}\)。若只构造出 §16.2 的算术区域，再把它的读数称为 \(D\)，缺的仍是该区域如何进入原允许输出及 hull 的比较方向；这只是把 §16.5.4 的来源桥换了名字。

**Checkpoint.** 当前完成的是固定例的模型侧全局数值，不是原文全局度数桥。下一步只检验上述固定输入：优先核实标记槽 2 的原评估及两次整数据换位，能否各自给出原允许输出中的正测度区域，并且这些输出的 hull 读数是否按上述行、元组权重比较到 \(H_{\rm orig}\)。若能闭合，结论仅登记为该输入的整体下界；若必须逐个目标投影补来源，回到 §16.5.4 的指定成员检查；若只剩 \(L\)，记录该接口不含所需标记信息并停止这条路线。直接全局度数证书仍是替代路径，但须证明同一归一化下的 \(q_s\le D\le H_{\rm orig}\)，而不是把 \(H_{\rm lit}\) 政名为 \(D\)。无论哪种结果，均不推出全输入量词或原允许像的整体有限性。

<a id="abc-only-reduction"></a>
## 17. 只求标准整数 ABC，弱中间命题需要多少强度

目标仍是每个 \(\varepsilon>0\) 都有独立于互素正整数三元组的 \(C_\varepsilon\)，使 \(a+b=c\) 时 \(\log c\le(1+\varepsilon)\log\operatorname{rad}(abc)+C_\varepsilon\)。固定一个指数 \(1.1\) 完成的是一个不同的目标。本节削减的是为获得所有 \(1+\varepsilon\) 所需处理的对象、输入和精度。以下两个从中间命题到 ABC 的推导均可走完。本文还证明了它们各自的一段上游估计，并指出当前未取得的统一界。[本仓 ABC 的量词](../LeanFormal/IUT/ABCBridge/Statement.lean#L32) · [本仓 Frey 高度消费者](../LeanFormal/IUT/ABCBridge/Bridge/ABCEllipticHeightCriterion.lean#L61)

### 17.1 复用现有的扭点域，删掉两列 Θ 区域

固定紧性条件 \(\mathcal C\) 和次数界 \(d\)。取仓库紧集路线中足够高的 Legendre 点 \(x\)，置 \(h=\log q_{\rm all}(x)\)，即**全部有限位**的 q 高度。该具体模型中 \(h/6\) 与 tripod 的目标高度在 \(\mathcal C\) 上相差有界。取 \(B=F_{\rm tpd}=\mathbb Q(\lambda)\)（按仓库的域同构）、辅助域 \(F\)、\(K=F(E[\ell])\)。记 \(Q\) 为去掉 2 和 \(\ell\) 后选中的 q 高度。对于所需证明，只须在已有的选素数范围内，对**每个点至少选出一套**合格数据。选择应同时保证

\[
 \sqrt h\le\ell\le C_d\sqrt h\log(2C_d h),\qquad
 0\le h-Q\le C_{\mathcal C}+6\sqrt h\log(2C_d h).
\]

现成源码的使用顺序尤其重要。Corollary22 先选 \(\ell\) 和收集具体数据，然后才首次调用 3.12 假设，最后的 q 遗漏量另行由选素数性质得到。所引用的前段可独立使用。为覆盖紧集外的有理点，要用已有的一般位置定理。这要求紧集上的命题覆盖**每个固定次数界**。只做有理点的一个紧集不足以调用它。[选素数与首次使用 h312](../Iut/Implication/Corollary22.lean#L443) · [实际数据及遗漏量](../Iut/Implication/Corollary22.lean#L530) · [具体数据的构造](../Iut/Tripod/Main.lean#L84)

定义 \(D_L=[L:\mathbb Q]^{-1}\log|\operatorname{disc}(L)|\)。令 \(S\) 为 \(B\) 上入选的有限位，\(N_S=[B:\mathbb Q]^{-1}\sum_{v\in S}\log{\rm N}v\)。**一个足够的中间估计**是

\[
                         Q/6\le D_K+o_{d,\mathcal C}(h). \tag{17.1}
\]

小 \(o\) 的量词是对每个 \(\eta>0\) 有统一高度阈值，阈值以上的误差至多 \(\eta h\)，也允许加上一个只依赖 \(d,\mathcal C,\eta\) 的常数。可以为不同的点选不同的合格 \(\ell\)。\(K\) 始终是这个点的指定扭点域。选任意高判别式数域会破坏下面的上界。[归一化 different 的定义](../Iut/Concrete/Invariants.lean#L178) · [局部和与 \(D_K\) 的等式](../Iut/Tower/LogDK.lean#L123)

**从 (17.1) 到 ABC 的证明。** 现有域塔估计给 \(D_K\le D_B+N_S+2\log\ell+21\)。这条定理的输入是实际域塔的分歧事实和有限支集。它的证明不使用 hCor312。又有 \(D_B+N_S\le\log{\rm diff}(x)+\log{\rm cond}(x)\)。于是 \(h/6\le\log{\rm diff}+\log{\rm cond}+o(h)+O_{d,\mathcal C}(1)\)。若右端总误差为 \(\eta h+C\)，取 \(6\eta\le\varepsilon/(1+\varepsilon)\) 后移项，就得到高度系数至多 \(1+\varepsilon\)。低高度点和既有有限例外给出一个统一加法常数。对每个 \(d,\mathcal C\) 得到 StatementII，接已有的 StatementII → StatementI → 标准整数 ABC。这条接线复用了仓库 `Iut/`、`Genl/` 的一般位置和有理点证明。在 `LeanFormal/` 的最终目标上可直接用相同的正整数与 log／幂等价作终端转换。[域塔上界](../Iut/Tower/Different.lean#L390) · [实际导子比较](../Iut/Tripod/LogCond.lean#L196) · [一般位置定理](../Iut/Tripod/GeneralPosition.lean#L269) · [整数 ABC 出口](../Iut/Tripod/ClassicalAbc.lean#L286) · [紧集上的高度比较](../Iut/Tripod/Height.lean#L789)

**(17.1) 的局部部分现在能证明多少。** 对 \(v\in S\)，记 \(k_v=-v(j(E))>0\)，采用 \(v(\varpi_v)=1\)，\(\omega_v=\log{\rm N}v/[B:\mathbb Q]\)。有 \(N_S=\sum_v\omega_v,\ Q=\sum_v k_v\omega_v\)。后一式来自 \(w\mid v\) 时 \(k_w=e(w/v)k_v\) 及全纤维 \(\sum e f=[F:B]\)。在任一这样的 \(w\) 上，选素数条件给 \(\ell\nmid k_w\)。在 \(W\mid w\) 的 \(K\)-完备化里实际 \(2\ell\) 次根的整数赋值为 \(e(W/w)k_w/(2\ell)\)。因此 \(\ell\mid e(W/w)\)，也有 \(e(W/v)\ge\ell\)。每个局部相对 different 指数满足 \(\delta(W/v)\ge e(W/v)-1\)。把 \(\delta(W/v)/e(W/v)\) 用局部次数在 \(W\mid v\) 上平均，乘 \(\omega_v\)，再用 different 塔公式，得到

\[
       D_B+(1-1/\ell)N_S\ \le\ D_K\
       \le D_B+N_S+2\log\ell+21. \tag{17.2}
\]

这两边都是对合格算术数据的结论。左边只用选素数、根的赋值和 different。它也说明了这条捷径的极限。\(N_S\le Q\le h\)，所以 \(D_K\) 和 \(D_B+N_S\) 在本路线容许的精度内已相同。单靠改选窗口内的合格 \(\ell\)，在 \(N_S\) 固定时最多能改变 \(O(h/\ell+\log\ell)\) 量级，无法凭空支付固定比例的 \(h\)。[标记根的真实赋值](../Iut/Concrete/ThetaLocalConstruct/Data.lean#L420) · [Tate 深度与 \(j\) 极点](../Iut/Tripod/Height.lean#L560) · [全纤维导子支集](../Iut/Tripod/LogCond.lean#L179) · [different 塔公式](../Iut/Tower/Different.lean#L45)

把真正欠的部分算出来。令

\[
 P=\sum_{v\in S}\frac{(k_v-6)_+}{6}\omega_v,\qquad
 L=\sum_{v\in S}\frac{(6-k_v)_+}{6}\omega_v,\qquad
 J=D_K-D_B-(1-1/\ell)N_S .
\]

这里 \(x_+=\max(x,0)\)。由 (17.2)，\(0\le J\le N_S/\ell+2\log\ell+21=o(h)\)。逐项展开得到

\[
                   Q/6-D_K=P-L-D_B+N_S/\ell-J. \tag{17.3}
\]

所以所有 \(k_v\le6\) 的贡献已经付清，浅极点的余量 \(L\) 和基域判别式 \(D_B\) 还可以支付深极点。对于 \(P\le L+D_B\) 的输入，(17.1) 已经成立。普遍情形只剩统一控制 \((P-L-D_B)_+\) 相对 \(h\) 的增长。这一剩余量可以在 **\(B\) 上**算，连构造 \(K\) 后再试许多根的工作都可以省去。反过来，(17.2) 也证明仅用域塔上下界无法进一步估计这项差额。另一条全局算术关系必须用到 \(\lambda\) 与 \(1-\lambda\) 的加法关系或等价信息。对于 \(B=\mathbb Q\) 的 Frey 模型，奇素数 \(p\mid abc\) 处 \(k_p=2v_p(abc)\)，于是这个分界恰是原整数中的三次幂。2 和无穷位在无紧性限制的有理点上可很大，在此处必须保留上述紧集／一般位置步骤。[实际 Frey 的奇位赋值](../LeanFormal/IUT/ABCBridge/Arithmetic/ABCInvariantLocalValuations.lean#L229) · [有理点与紧性条件](../Iut/Tripod/ClassicalAbc.lean#L42)

**若仍想利用 §16 的张量对象，甚至可以只估最高一行。** 设 \(j=(\ell-1)/2,\ s=j+1,\ M=Q/(2\ell)\)，\(R_j\) 取具体模型的**固定标记槽**全局 hull 读数。逐行上界给出

\[
 \frac{R_j+j^2M}{s}
 \le D_K+\frac{\log s^{\mathbb Q}}s+
 4(1+1/s)\,l_{\rm mod}\log s^{\le}+\log(\sqrt2\,\pi).
\]

这里 \(\log s^{\mathbb Q}\) 是 distinguished primes 的 \(\sum\log p\)。已有 Step (iii) 使其不超过 \(2d(D_B+N_S)+5+\log\ell\)，而小素数项由已有素数计数界给 \(O_d(\ell+1)\)。因此一个替代下界 \(R_j\ge -j^2M/3\) 就足以接 ABC，甚至可在右边再减 \(s\,o_{d,\mathcal C}(h)\)。因为此时左边至少为
\[
 \frac{j^2}{3\ell(j+1)}Q
 =\frac16\!\left(1-\frac{3\ell-1}{\ell(\ell+1)}\right)Q.
\]
与 \(Q/6\) 的差为 \(O(Q/\ell)\)，上界中另有 \(O_d((D_B+N_S)/\ell)\) 的相对损失，及 \(O_d(\ell+1)=o(h)\) 的加法损失。一行可以保留其原二次收缩代价的三分之一，仍有足够的高度系数。原文的全行平均下界本身没有给这条指定行下界。优先做 (17.3) 的原因是连这一个新张量下界也可以省掉。§16 在混合纤维上把标记放到最有利的槽所获益处不能直接进入此处的固定槽上界。[逐行上界](../Iut/Implication/LogVolumeBound.lean#L199) · [小素数项](../Iut/Implication/Theorem110.lean#L185) · [已有域塔的两条算术上界](../Iut/Concrete/Invariants.lean#L294)

**若沿用已有全部行，允许的亏损也能精确量化。** 写 \(H\) 为上述固定槽具体模型的各行 \(R_j\) 的算术平均。在 Corollary22 已选出的数据上，\(H\) 有实数读数和逐行上界。设 \(\bar s=(\ell+5)/4\)。由 \(\operatorname{avg}j^2=\ell(\ell+1)/12\)，直接平均刚才的上界，给出
\[
 H\le \bar s D_K-(\ell+1)Q/24+
        \log s^{\mathbb Q}+4(\bar s+1)l_{\rm mod}\log s^{\le}
        +\bar s\log(\sqrt2\pi).
\]
这一步在源文件首次使用 h312 之前。将下界削到 \(H\ge-\delta\,\ell Q\)，除以 \(\bar s\)，再用前面两条算术上界，左边 \(Q\) 的系数是 \((\ell+1)/(6(\ell+5))-4\delta\ell/(\ell+5)\)。于是若固定 \(0\le\delta<1/24\)，在其余误差消失后，这个计算给目标高度的极限乘数 \(1/(1-24\delta)\)。对于一个指定的 \(\varepsilon\)，选 \(\delta<\varepsilon/(24(1+\varepsilon))\) 已有足够余量。对于全部 \(\varepsilon\)，在每个紧集、每个次数界上，只须每个高点能选一组数据使 \(\max(0,-H)=o(\ell h)\)。例如 \(H\ge-\sqrt{\ell}\,Q\) 就足够，容许的负值绝对量是具体 3.12 所要求的 \(Q/(2\ell)\) 的 \(2\ell^{3/2}\) 倍。这个放宽量是从已有的逐行上界推出来的。放宽后的下界对全部所选数据仍待证明。它可以用来直接评估一个已有区域见证的强度。[先求和、后使用 h312 的源码](../Iut/Implication/Theorem110.lean#L276) · [具体模型的 q 侧定义](../Iut/Cor312/LeftHandSide.lean#L88)

### 17.2 直接在整数上缩小输入，只研究两个端点是平方的 Frey 三元组

这条路线保留全体 \(\varepsilon\) 并省掉一般位置定理、辅助数域及 Θ 区域。取互素 \(0<u<v\)，构造
\[
 A=u^2,\qquad B'=v^2-u^2=(v-u)(v+u),\qquad C=v^2,\qquad
 P(u,v)=uv(v-u)(v+u).
\]
它们满足 \(A+B'=C,\ \gcd(A,B')=1\)，且 \(\operatorname{rad}(AB'C)=\operatorname{rad}P(u,v)\)。这类 Frey 曲线带有一个显式的有理四阶点
\[
 E:y^2=x(x-A)(x+B'),\qquad
 Z=(u(u+v),uv(u+v)).
\]
直线 \(y=(u+v)(x-A)\) 与此三次曲线的交点方程化为 \((x-A)(x-u(u+v))^2=0\)，所以 \(2Z=(A,0)\)。这个对象在 \(\mathbb Q\) 上即可构造。使用椭圆曲线工具时，可将曲线范围缩至这族有指定四阶点的曲线。下面的整数推导只用三个整数。[仓库中同一个 Frey 三次式及其二阶点](../LeanFormal/IUT/ABCBridge/Geometry/FreyTwoTorsion.lean#L55) · [实际奇导子到 ABC 的接口](../LeanFormal/IUT/ABCBridge/Bridge/FreyOddConductorHeightCriterion.lean#L358)

**受限命题推出全部 ABC 的证明。** 假设对每个 \(\eta>0\)，这族上有统一的 \(2\log v\le(1+\eta)\log\operatorname{rad}P(u,v)+C_\eta\)。给任意原三元组，直接取 \(u=a,\ v=c\)。则 \(v-u=b,\ v+u=c+a<2c\)，所以 \(\operatorname{rad}P(a,c)\le2c\,\operatorname{rad}(abc)\)。移项得
\[
 (1-\eta)\log c\le(1+\eta)\log\operatorname{rad}(abc)+C_\eta+(1+\eta)\log2 .
\]
取 \(\eta=\varepsilon/(2+\varepsilon)\) 恰得 \(1+\varepsilon\)。反之，标准 ABC 当然适用于这些平方三元组。因此这是对标准 ABC 的等价限制。曲线范围缩到了平方端点且带指定四阶点的族。在这个族上取得统一上界仍有 ABC 的算术强度。通过多项式变换把 ABC 限制到特殊三元组，在 Ellenberg 的同余限制论文中也有先例，该论文研究的是另一种限制。[Ellenberg 的原论文](https://people.math.wisc.edu/~ellenberg/CongruenceABC.pdf)

### 17.3 给受限问题一个可下手的全局估计

在整数二进区间 \(X\le v<2X\)（\(X=2^k\)）定义一个有限的非负和
\[
 \mathcal M_m(X)=
 \sum_{\substack{X\le v<2X\\1\le u<v,\ (u,v)=1}}
       \left(\frac{v^2}{\operatorname{rad}P(u,v)}\right)^m .
\]
目标可取为对无界的一组正整数 \(m\)，有 \(\mathcal M_m(X)\le C_m X^3\)，\(C_m\) 与 \(X\) 无关。它允许不同输入贡献很不均匀，也免去了逐曲线给出一个区域见证。固定一个 \(\varepsilon\)，只要其中一个 \(m\ge3(1+\varepsilon)/\varepsilon\)。证明是取 \(u=a,v=c\) 对应的单项，由非负性得 \(c^2\le C_m^{1/m}c^{3/m}\operatorname{rad}P(a,c)\)。再用上面的 \(2c\,\operatorname{rad}(abc)\) 并移项，指数为 \(1/(1-3/m)\le1+\varepsilon\)。反向可直接从平方三元组上的 ABC 得到。使用 ABC 的 \(\eta=1/(2m)\) 得每一项至多 \(O_m(X)\)，总共 \(O(X^2)\) 项，故所提的三次方预算不会排除 ABC 所允许的情形。

**现已能无条件消去绝大多数候选。** 记 \(N_X(T)\) 为区间中满足 \(\operatorname{rad}P(u,v)\le T\) 的有序整数对 \((u,v)\) 的个数。对每个固定 \(\delta>0\)，有
\[
                         N_X(T)\ll_\delta X^\delta \sqrt T. \tag{17.4}
\]
这是一个不依赖 ABC 或 3.12 的计数上界。证明如下。四个正整数 \(u,v,v-u,v+u\) 除了后两者可能共用素数 2 外，两两互素。因此四个 radical 的乘积至多 \(2T\)，最小两个的乘积至多 \(\sqrt{2T}\)。任取两条不同的线性式，系数行列式绝对值为 1 或 2，所以从它们的值可以唯一恢复 \((u,v)\)。对 \(0<\sigma\)，有
\[
 \sum_{n\le4X}\frac1{\operatorname{rad}n}
 \le (4X)^\sigma\prod_p
 \left(1+\frac{p^{-1-\sigma}}{1-p^{-\sigma}}\right)\ll_\sigma X^\sigma .
\]
欧拉乘积收敛由 \(\sum_{n\ge2}n^{-1-\sigma}<\infty\) 得到。对每一种二式选择，满足 \(\operatorname{rad}m\,\operatorname{rad}n\le\sqrt{2T}\) 的数对个数至多 \(\sqrt{2T}(\sum_{n\le4X}1/\operatorname{rad}n)^2\)。取 \(\sigma=\delta/2\)，加上六种选择即得 (17.4)。

所以每个区间 \(O(X^2)\) 个输入中，可能有 \(v^2/\operatorname{rad}P>1\) 的至多 \(O_\delta(X^{1+\delta})\) 个。其余对任意 \(m\) 的总贡献都至多 \(O(X^2)\)。实际枚举时，先筛出 \(1,\ldots,4X\) 的 radical 并排序，用 \(T=4X^2\) 枚举两个 radical 乘积至多 \(\sqrt{2T}\) 的数对，对六种二式反解，检查整数性、互素和另两条式，去重。固定 \(\delta>0\) 时，在通常整数运算模型下，每个区间的生成、排序和核对均可在 \(O_\delta(X^{1+\delta})\) 次运算内完成。这个数是固定高度区间的工作量。它对任意大的区间都正确，单独取很多区间不能证明统一高阶矩。

**剩下的算术操作。** 将四个 radical 按二进区间分组，在已选的两条小 radical 线性式上保留另外两条式的联合限制。例如已选 \((u,v)\)，对 \(v-u,v+u\) 指定奇数幂因子 \(d_-,d_+\)，二者互素。于是每个给定 \(u\) 对应一个确定的 \(v\bmod d_-d_+\)，其两条同余分别为 \(v\equiv u\bmod d_-\) 与 \(v\equiv-u\bmod d_+\)。固定 \(u\) 的区间内至多 \(1+X/(d_-d_+)\) 个这样的 \(v\)。大模数下剩下的那一次可能命中，正是不能用平均密度抹去的极端解。证明高阶矩需要对这些命中同时使用另外两条式的 radical 限制。两个界的差距可以直接比较。若 \(v^2/\operatorname{rad}P\ge X^\alpha\)，(17.4) 只给 \(O_\delta(X^{1-\alpha/2+\delta})\) 个，拟证矩界会给 \(O_m(X^{3-m\alpha})\) 个。因此在 \(m\alpha>3\) 时须对充分大的 \(X\) 全部排除。读到这一行即可判断某个新的筛法究竟是否逼近标准 ABC。只提高固定样本数量、或只取得一个恒正幂次的计数上界，均未解决这一项。

这里能把一个矩实际算下来。互素性给 \(\operatorname{rad}P\ge\operatorname{rad}u\,\operatorname{rad}v\)，故上面的欧拉乘积直接给 \(\mathcal M_1(X)\ll_\delta X^{2+\delta}\)。若目的是寻找**原整数三元组**中最难的输入，有一个更省的筛法。三个数 \(a,b=c-a,c\) 两两互素，其中最小的两个 radical 之积至多为 \(\operatorname{rad}(abc)^{2/3}\)。它们的整数值唯一确定三元组，只需指定所选的是哪两个位置。重复 (17.4) 的二数计数，在 \(X\le c<2X\) 中得到
\[
 \#\{(a,b,c):\operatorname{rad}(abc)\le T\}\ll_\delta X^\delta T^{2/3}.
\]
此处仍只计互素正整数三元组。因此给定 \(\varepsilon>0\)，连乘法常数取 1 时，可能违反 \(c\le\operatorname{rad}(abc)^{1+\varepsilon}\) 的候选也至多 \(O_{\varepsilon,\delta}(X^{2/(3(1+\varepsilon))+\delta})\)。该指数是候选**个数**的上界。用普通筛生成到 \(2X\) 的 radical 表仍有线性的预处理开销。标准 ABC 要用一个 \(C_\varepsilon\) 统一控制所有高度上余下的候选。

### 17.4 把剩余算术压在一条固定曲线的二次扭曲上

这个椭圆曲线构造给出 §18.4 所检验的三种换元。它可以直接从两个互素整数算出来，所有输入只用一次倍点。写成唯一的 \(P(u,v)=d t^2\)，其中 \(d>0\) 无平方因子，\(t>0\)。令
\[
 E_d:\ y^2=x^3-d^2x,\qquad
 Z=\left(\frac{dv}{u},\frac{d^2t}{u^2}\right).
\]
代入即得 \(Z\in E_d(\mathbb Q)\)。所有 \(E_d\) 都是 \(y^2=x^3-x\) 的二次扭曲，\(j=1728\)。记 \(B\) 为 \(x(2Z)\) 的既约正分母。切线公式给出
\[
 x(2Z)=\frac{(x(Z)^2+d^2)^2}{4y(Z)^2}
       =\left(\frac{u^2+v^2}{2t}\right)^2,\qquad
 \boxed{\ \operatorname{rad}P(u,v)=\operatorname{rad}(2d B)\ }. \tag{17.5}
\]
证明后式时，任一奇素数 \(p\mid P\) 只能整除 \(u,v,v-u,v+u\) 中的一项。代入各情形可见 \(p\nmid u^2+v^2\)，所以奇素数 \(p\mid t\) 一定留在既约分母里。其余整除 \(P\) 的奇素数都整除 \(d\)。反向包含从 \(B\mid 4t^2\) 立得。素数 2 对所有互素 \(u,v\) 都整除 \(P\)。式中取 radical 自动处理 \(d\) 与分母相交的素数。

高度也有同样精确的读法。记 \(h_{\mathbb Q}(r)=\log\max(|\operatorname{num}r|,\operatorname{den}r)\)。有
\[
 \frac{x(2Z)}d=\frac{(u^2+v^2)^2}{4P(u,v)},\qquad
 \left|h_{\mathbb Q}(x(2Z)/d)-4\log v\right|\le\log4 . \tag{17.6}
\]
分子减分母等于 \((v^2-2uv-u^2)^2\)。奇素数不会约分。一偶一奇时约分因子是 1，两数皆奇时是 4。于是既约分子介于 \(v^4/4\) 和 \(4v^4\) 之间，与 \(d\) 无关。比如 \(a=1,b=242,c=243\)，所得 \(d=366,t=198,\ x(2Z)=(29525/198)^2\)，(17.5) 两侧都是 \(4026\)。在这里，单看扭曲参数会漏掉素数 11。

**实际要攻的估计可以用好素数表述。** 对 \(p\nmid 2d\)，此方程在 \(p\) 有好约化，点 \(2Z\) 约化到无穷远点 \(O\) 恰当且仅当 \(p\mid B\)。这是良好 Weierstrass 模型上坐标整性对无穷远点的判别。因而 \(\operatorname{rad}P=\operatorname{rad}(2d)\prod_{p\nmid 2d,\ \overline{2Z}=O}p\)。所要研究的仅是以上显式点，足够的且系数准确的估计为，对每个 \(\eta>0\) 存在与 \(u,v,d\) 无关的 \(C_\eta\)，使
\[
 \sum_{\substack{p\nmid 2d\\\overline{2Z}=O}}\log p
 \ \ge\ \frac{2}{1+\eta}\log v-\log\operatorname{rad}(2d)-C_\eta. \tag{17.7}
\]
将坏素数项加回去，由 (17.5) 就是 §17.2 已推至 ABC 的平方端点估计。凡 \(\operatorname{rad}(2d)\ge v^{2/(1+\eta)}\) 的输入，以 \(C_\eta=0\) 即可。小 \(d\) 上少数素数以很高重数进入 \(B\)，才会使按分母大小的普通高度界失效。对 \(p\nmid2d\)，也可把条件写成 \(Z\bmod p\in\{O,(0,0),(d,0),(-d,0)\}\)。这样可以逐个判断任何拟用的约化定理究竟给出多少**不同**的素数。仓库已有二等分多项式在实际点的求值和二阶挠性判别，可作这一步的底层供体。[二等分多项式求值](../EllipticCurves/Torsion/DivisionPolynomialEval.lean#L145) · [二阶挠性检测](../LeanFormal/IUT/ABCBridge/Galois/EllipticTorsionAlgebraicity.lean#L131)

**每个原输入最多看三个扭曲点，其中一个成功就足够。** 交换 \(a,b\) 后设 \(a<b\)，\(a=b=1\) 单独处理。置 \(g=\gcd(b-a,c)\in\{1,2\}\)。可在下列三对中选取 \((u,v)\)。

| 整数对 \((u,v)\) | 在 \(abc\) 支集外提供新素数的整数 \(L_i\) |
| --- | --- |
| \((a,c)\) | \(2a+b\) |
| \((b,c)\) | \(a+2b\) |
| \(((b-a)/g,c/g)\) | \(b-a\) |

记 \(R=\operatorname{rad}(abc)\)，\(\operatorname{rad}_{>2}(n)\) 是 \(n\) 的不同奇素因子之积。三对均互素，\(v\ge c/2\)，每对都有精确等式 \(\operatorname{rad}P_i=R\,\operatorname{rad}_{>2}(L_i)\)。前两对直接展开。第三对有 \(P_i=4abc(b-a)/g^4\)，奇素数支集由此立即得到，且互素对的 \(P_i\) 总是偶数。每个 \(L_i\) 与 \(abc\) 的公因子只能含 2，这来自 \(\gcd(a,b)=1\)。故三对都满足 \(\operatorname{rad}P_i\le2cR\)。若对其中**一对**取得 (17.7)，就有 \(2\log(c/2)\le (1+\eta)\log(2cR)+O_\eta(1)\)，§17.2 的同一个 \(\eta=\varepsilon/(2+\varepsilon)\) 仍然得到全部 ABC。例 \(1+8=9\) 在第一对上的 \(\operatorname{rad}P_1=30<81\)，第二对给 \(\operatorname{rad}P_2=102>81\)，已付清系数 1 的平方端点预算。

三次选择还有一条可供研究的整体关系。由这三条线性式的两行行列式绝对值都是 3，同一素数 \(p>3\) 在三个新增支集中至多出现一次。更具体地，令 \(k=\gcd(b-a,2a+b)\in\{1,3\}\)，则 \(((b-a)/k,(2a+b)/k,(a+2b)/k)\) 本身是另一个互素正整数三元组。它的前两项仍按从小到大排列，变换矩阵 \(\left(\begin{smallmatrix}-1&1\\2&1\end{smallmatrix}\right)\) 的平方等于 \(3I\)。因此把同一变换作两次再约去公因数，恰好回到原输入。这个构造的轨道长度最多为二。三个新的奇素数支集以及它们与原支集在 3 以外的互素性都可以同时使用。一个精确的研究目标是下式的正部在 \(c\to\infty\) 时一致为 \(o(\log c)\)：
\[
       2\log c-\log R-\max_{L\in\{2a+b,\,a+2b,\,b-a\}}
                                  \log\operatorname{rad}_{>2}(L).
\]
取最大值明确允许一条甚至两条支路失利。由这个目标和 \(L<2c\) 可以移项得到 ABC，反过来由 ABC 应用于平方三元组也能给这个目标。矩阵和互素性已经给出证明，目前没有从这两项事实推出所需的一致界。

仓库中恰好有这三个因子的几何来源。令 \(U=abc,\ V=(b-a)(2a+b)(a+2b),\ I=a^2+ab+b^2\)。现有 Frey 定理给 \(c_4=16I,\ c_6=-32V,\ \Delta=16U^2\)。因此
\[
 4I^3=27U^2+V^2,\qquad j=\frac{256I^3}{U^2},\qquad
 j-1728=\frac{64V^2}{U^2}.
\]
故所有新素数 \(p>3\) 都是**原 Frey 曲线有好约化且 \(j\equiv1728\bmod p\) 的素数**，反向也成立。原三元组变到上述第二个三元组时，\((U,V,I)\) 变成 \((V/k^3,\,27U/k^3,\,3I/k^2)\)，故两个实际的 \(j,j'\) 满足 \(1728/j+1728/j'=1\)。研究这条路可直接从仓库已知的 \(c_6\) 分解出发。将这些好素数按三个线性因子分组，不计重数，最大的那组所需补足的是 \(2\log c-\log R-o(\log c)\)，去掉 2、3 只影响有界常数。一个给出 \(\log|c_6|\) 或给出 \(\operatorname{ord}_p(j-1728)\) **带重数总和**的结果，还须控制同一素数内的重复幂，才能用于这个估计。[Frey 曲线的 \(c_4,c_6,\Delta\)](../LeanFormal/IUT/ABCBridge/Geometry/FreyWeierstrassCurve.lean#L86) · [仓库已有的 \(j-1728\) 三个分歧因子](../LeanFormal/IUT/ABCBridge/Geometry/LegendreJFunctionDivisor.lean#L300)

用素幂还能把第一个待研究子族选得更窄。把 \(t=t_{\rm bad}t_{\rm good}\) 按素数是否整除 \(2d\) 分拆，有逐点恒等式
\[
 \frac{v^2}{\operatorname{rad}P}
 =\frac{v^2}{\sqrt P}\,
   \frac{\sqrt d}{\operatorname{rad}(2d)}\,
   t_{\rm bad}\,\frac{t_{\rm good}}{\operatorname{rad}(t_{\rm good})}.
\]
例如 \(v/3\le u\le 2v/3\) 时 \(P\ge (5/27)v^4\)。在这段上，若 \(t_{\rm bad}\,t_{\rm good}/\operatorname{rad}(t_{\rm good})\le\sqrt d\)，便已经得到 \(v^2\le\sqrt{27/5}\operatorname{rad}P\)。未处理的情况在公式中表现为坏素数上的深度、好素数上的重复幂，或 \(u/v\) 接近 0、1 时的实高度损失。对这些情况，(17.7) 的统一估计仍开放。§17.3 的高阶矩是对同一余量的另一种处理方式。

**工作量判断。** 只求标准 ABC，原 IPL 跨列区域的成员来源、原 hull 对全部迭代的有限性、每个原输入的精确 R1/R2 都可退出这条任务。保留域塔时，(17.3) 已精确标出必须补的深极点总量。这条有理数归约以 (17.5) 的固定曲线扭曲族为对象，以 (17.7) 的统一系数作验收。§18 记录了后续检验及取代这一优先方向的连分数路线。两条归约都没有从 ABC 恢复原 III.3.12 的步骤。平方构造、分母支持、所需高度系数、两个候选计数界已有自然语言证明。(17.7) 本身与标准 ABC 等强。减少的构造可逐项点名，取得最终一致界的工时仍无已知上界。

核对范围为八个区间 \(X=2,4,\ldots,256\) 内的全部 79,595 个互素 \((u,v)\)。以精确有理数核对曲线、切线、倍点、既约分母和高度公式，并逐区间对比六种二式与三种二式反解的候选集和直接枚举。其中 39,797 个满足 \(a<b\) 的原三元组另核对了三个扭曲支集、归一化对合、Frey 不变量及两个 \(j\) 的关系。单线程自然语言研究，未编译 Lean，四项形式验收均未运行。

<a id="abc-route-decision"></a>

## 18. 只求整数 ABC，哪一段值得做，做到哪里结束

**立项判断（2026-11-19）。** 整数 ABC 这条线，采用 §18.1 的重复素幂分解和连分数。对每组指定素幂，它能在预先可算的步数内查清全部高度，并能直接给出一批素数和赋值都可变化的输入上的统一界。这个研究包已经走完。上次把三个 \(c_6\) 因子列为主攻，依据不足。§18.4 已穷尽那一类二次换元，建议结束该支路。若验收只接受完整 ABC，目前应保留 §18.1 的全局商数估计作为数学研究题，已有证据不足以把完整证明排入 Lean 实施。整条归约都不调用 R1、R2 或 hCor312。

### 18.1 对每一组重复素幂，一次欧几里得算法查清全部高度

取正整数 \(a+b=c,\ \gcd(a,b)=1\)，记 \(U=abc,\ R=\operatorname{rad}(U)\)，约定 \(\operatorname{rad}(1)=1\)。终点要求每个 \(\varepsilon>0\) 有一个 \(K_\varepsilon>0\)，对全部三元组有 \(c\le K_\varepsilon R^{1+\varepsilon}\)。按实际量词，\(K_\varepsilon\) 先于三元组选择。[仓库锁定的 ABC 目标](../LeanFormal/IUT/ABCBridge/Statement.lean#L32)

**把重数保留在哪一项记录下来。** 对每个数 \(m\)，取 \(D(m)=\prod_{v_p(m)\ge2}p^{v_p(m)}\)，包括这些素数的全部幂次。置 \(A=D(a), B=D(b), D=D(c)\)，写 \(a=Ax,\ b=By,\ c=Dz\)，\(P=\operatorname{rad}(ABD)\)。由本原性，\(A,B,D\) 两两互素，\(x,y,z\) 全部平方自由、两两互素且与 \(ABD\) 互素。因此
\[
                  R=Pxyz,\qquad \frac cR=\frac{D}{Pxy},\qquad
                  Ax+By\equiv0\pmod D .
\]
固定 \(A,B,D\) 后，只要 \(D\le P\)，这整个族都满足 \(c\le R\)。以下设 \(D>P\)，这时 \(P\ge2\)。在 \(1,\ldots,D-1\) 中取 \(k\equiv-AB^{-1}\bmod D\)。

**为什么候选清单完整。** 一个有 \(c>R\) 的输入必满足 \(Pxy<D\)。因 \(y\equiv kx\bmod D\)，写 \(t=(kx-y)/D\)，便有
\[
       0<\frac{k}{D}-\frac{t}{x}=\frac{y}{Dx}
                    <\frac{1}{P x^2}\le\frac{1}{2x^2}.
\]
任意同时整除 \(t,x\) 的数都整除 \(y\)，所以 \(t/x\) 已既约。仓库已有的 Legendre 有理逼近定理保证 \(t/x\) 是 \(k/D\) 的一个连分数渐近分数，且它从下方逼近 \(k/D\)。这一步把二元搜索变成了一张可列完的清单。[仓库的 Legendre 渐近分数定理](../.lake/packages/mathlib/Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean#L56)

**可执行步骤与停止次数。**

1. 对 \(k/D\) 作一次欧几里得算法。对每个严格小于 \(k/D\) 的渐近分数 \(t/x\) 取 \(y=kx-Dt\)，仅保留 \(Pxy<D\)。
2. 还原 \(a=Ax,\ b=By,\ c=a+b\)。检查 \(\gcd(a,b)=1\) 及 \(D(a)=A,\ D(b)=B,\ D(c)=D\)。保留下来的正是这一组重复素幂下全部 \(c>R\) 的三元组。余下的所有高度都有 \(c\le R\)。
3. 若给定 \(\varepsilon\)，对保留项的 \(c/R^{1+\varepsilon}\) 和 1 取最大值，就得到这一组满足 \(K\ge1\) 的**最小** ABC 常数。对任意实 \(\varepsilon>0\)，这个有限表达式成立。对正有理 \(\varepsilon\)，比较可以全部用整数幂完成。分母每两步至少翻倍，故至多检查 \(2\lceil\log_2 D\rceil+2\) 个渐近分数。这个界计算候选个数，素数分解和平方自由检查另计，均可用有上界的整数试除完成。

例如 \(A=1,B=125,D=128\)，\(P=10,\ k=43\)。\(43/128=[0;2,1,42]\) 的下方渐近分数只有 \(0/1,1/3\)。前者还原 \(y=43\)，因 \(10\cdot43\ge128\) 被筛掉。后者还原 \(y=1\)，得 \(3+125=128,\ R=30\)。这是这组重复素幂中**全部高度上唯一**的 \(c>R\) 输入。对任意 \(\varepsilon>0\) 其常数就等于 \(\max(1,128/30^{1+\varepsilon})\)。

连 \(A,B\) 都不用指定，也有一个全局可计算的范围。若只规定 \(D(c)\le H,\ H\ge2\)，任何违反 \(c\le R^{1+\varepsilon}\) 的三元组必满足 \(c^{\varepsilon/(1+\varepsilon)}<c/R=D/(Pxy)\le H/2\)（\(D=1\) 已直接通过）。故只须枚举 \(c<(H/2)^{(1+\varepsilon)/\varepsilon}\)。这给出了所有 \(A,B\) 同时变化时的有限停止高度。完整目标要求进一步让 \(H\) 也任意变化并共用同一常数。

**跨不同素幂也能直接证明的一段。** 取任意正整数 \(u,v\) 满足 \(uB\equiv vA\bmod D\)。由原同余及 \(B\) 可逆，\(D\mid ux+vy\)，从而 \(D\le ux+vy\le(u+v)xy\)。于是整组都满足 \(c/R\le(u+v)/P\)。例如 \(A\equiv B\bmod D\) 可统一取 \(u=v=1\)，立刻覆盖任意满足这个同余的组，常数为 1。更一般地，给定 \(P,D\)，依次试 \(1\le v<P\)，取 \(u\equiv vAB^{-1}\bmod D\) 的最小正代表。一次取得 \(u+v\le P\) 就同时证明了该组全部高度上的 \(c\le R\)。未取得时，回到上面的有限连分数清单即可。

这些组可以带着**任意指定的大素数和深度**实际造出来。例如选三个不同的素数 \(p,q,r\ge7\) 和任意 \(s\ge2\)，置 \(D=r^s\)。令 \(h,j\ge2\) 为 \(\varphi(D)\) 的任意正倍数，\(A=p^h,B=q^j\)，便有 \(A\equiv B\equiv1\bmod D\)。取 \(a=m,b=m+1,c=2m+1\)。在模 \(900=4\cdot9\cdot25\) 处取 \(m\equiv1\)，并分别令 \(m\equiv p^h\bmod p^{h+1}\)、\(m+1\equiv q^j\bmod q^{j+1}\)、\(2m+1\equiv r^s\bmod r^{s+1}\)。中国剩余定理给出 \(m=m_0+Lt,\ 0\le m_0<L,\ L=900p^{h+1}q^{j+1}r^{s+1}\)。另外每个素数 \(w\ge7\) 至多排除模 \(w^2\) 的三个 \(t\) 类。对 \(1\le t\le X\)，可能出现的 \(w\le2\sqrt{LX}\)（\(X\ge2\)），故被排除数至多
\[
    3X\sum_{i\ge7}i^{-2}+6\sqrt{LX}<X/2+6\sqrt{LX}.
\]
其中 \(\sum_{i\ge7}i^{-2}<\int_6^\infty s^{-2}\,ds=1/6\)。取 \(X=576L\)，至少 \(X/4\) 个 \(t\) 通过筛选，试完这有限段一定构造出所要求的本原三元组。令 \(X\) 增长则有无穷多组。三项都可以有很深而不同的重复素数，整族的 ABC 常数仍为 1。

**完整 ABC 的验收可以精确到欧几里得算法里的一个商。** 对一个保留下来的渐近分数 \(t/x\)，记下一部分商为 \(h\)。相邻渐近分数的行列式绝对值为 1。用下一完整商 \(\gamma\) 写 \(k/D=(t\gamma+t')/(x\gamma+x')\)，其中 \(t'/x'\) 为上一个渐近分数（初始处取 \(x'=0\)），就得
\[
     h\ \le\ \frac D{xy}=\gamma+\frac{x'}x\ <h+2.
\]
因此，对全部通过平方自由、互素检查的候选，证明
\[
      h\le C_\varepsilon\,P\,c^{\varepsilon/(1+\varepsilon)}
      \quad\text{且同一 }C_\varepsilon\text{ 适用于所有 } A,B,D
\]
就足够。事实上 \(c/R=D/(Pxy)\)，移项得到 \(c\le(C_\varepsilon+2)^{1+\varepsilon}R^{1+\varepsilon}\)。反过来，完整 ABC 也给这个商数界。每一组的清单长度与最大例外已经可以验收。随 \(A,B,D\) 变化的**商的大小**是尚待证明的统一算术内容。

### 18.2 两个不必枚举连分数的范围

**第一步有显式常数，可以直接用整数运算验收。** 置 \(e(t)=t/\operatorname{rad}(t)\)，把 \(e(a),e(b),e(c)\) 从小到大排成 \(e_1,e_2,e_3\)。对任意输入都有
\[
 \frac{c}{R}=\frac{e_1e_2e_3}{ab}\ \le\ \frac{e_1e_2}{\min(a,b)}. \tag{18.1}
\]
三个整数两两互素，给出等号。每个 \(t\ge2\) 满足 \(e(t)\le t/2\)，且 \(e(1)=1\le c/2\)，所以 \(e_3\le c/2\)。再用 \(ab\ge\min(a,b)c/2\) 即得不等号。因此只要两个较小的重复幂部分之积至多为 \(\min(a,b)c^{\varepsilon/(1+\varepsilon)}\)，便已得到 **\(c\le R^{1+\varepsilon}\)，常数为 1**。特别地，全部重复素因子集中在三项中的任意一项时，直接有 \(c\le R\)。允许素数随输入任意改变，也允许该项含任意多个重复素数。这一步只用互素性和整数分解。

**第二步允许重复幂散布在三项。** 预先任选有限素数集 \(S\)，置 \(U_S=\prod_{p\in S}p^{v_p(U)}\)，\(P_S=\prod_{p\in S}p\)，\(E_{\bar S}=\prod_{p\notin S,\,p\mid U}p^{v_p(U)-1}\)。对每个 \(0<\delta<1\)，存在只依赖 \(S,\delta\) 的 \(A_{S,\delta}\ge1\)，对全部高度都有
\[
 U_S\le A_{S,\delta}\,ab\,c^\delta,\qquad
 c\le A_{S,\delta}\,R\,E_{\bar S}\,c^\delta . \tag{18.2}
\]
这里使用一个独立的经典定理，即含有限素数处的子空间定理。对本原向量 \((a,b)\)，实数处用 \(X,Y\)，其绝对值乘积为 \(ab\)。对每个 \(p\in S\)，三条线性式 \(X,Y,X+Y\) 至多一条取非单位值。取这一条和任意另一条，三条都取单位值时取 \(X,Y\)。两个形式线性独立，其 \(p\)-进绝对值乘积恰为 \(p^{-v_p(U)}\)。一共至多 \(3^{|S|}\) 个固定选择系统。对每个系统，设 \(H=\max(a,b)\)，子空间定理把这些乘积在全部所选地方的总积小于 \(H^{-\delta}\) 的原始整向量放进有限多条过原点的有理直线。若 \(ab/U_S<c^{-\delta}\)，因 \(H\le c\)，这个向量就在其中。每条直线至多贡献一组本原正整数对。在这些有限例外上对 \(U_S/(ab\,c^\delta)\) 和 1 取最大值，便证明第一式。恒等式 \(U=U_S\operatorname{rad}_{\bar S}(U)E_{\bar S}\) 以及 \(\operatorname{rad}_{\bar S}(U)\le R\) 给第二式。[Evertse，含有限素数处的子空间定理](https://www.numdam.org/item/CM_1996__101_3_225_0/)

取 \(E_{\bar S}=1,\ \delta=\varepsilon/(1+\varepsilon)\)，便有
\[
 c\le A_{S,\delta}^{1/(1-\delta)}R^{1+\varepsilon}.
\]
因此只要重复出现的素数落在一个预先固定的有限集里，便获得每个 \(1+\varepsilon\) 的指数。集合外的一次素因子可以有任意多个、任意大，集合内的赋值可以无界。更一般地，若 \(E_{\bar S}\le c^\eta\) 且 \(\delta+\eta<1\)，同样得到指数 \(1/(1-\delta-\eta)\)。这一证明给存在常数，未计算例外直线上的最大高度。项目若只接受仓库已有基础，(18.1) 仍可独立使用，(18.2) 的经典子空间定理属于外部输入。

### 18.3 从固定素数集推广到全部，常数到底要好到什么程度

一条有明确终点的算术任务是给出同一个 \(C_\delta\)，使每个有限 \(S\) 和每个本原三元组都满足
\[
 U_S\le C_\delta\,ab\,c^\delta P_S^{\,1+\delta},\qquad 0<\delta<1. \tag{18.3}
\]
**充分性可以算到最后。** 取 \(S\) 为 \(abc\) 的全部素因子，约去 \(ab\)，得到 \(c^{1-\delta}\le C_\delta R^{1+\delta}\)。代入 \(\delta=\varepsilon/(2+\varepsilon)\) 恰得 \(c\le C_\delta^{1/(1-\delta)}R^{1+\varepsilon}\)，覆盖仓库目标的全部量词。反过来，标准 ABC 取指数 \(1/(1-\delta)\) 给出 \(c/R\ll_\delta c^\delta\)。逐素数有 \(U_S/P_S\le U/R\)，于是连 (18.3) 中 \(P_S\) 的指数 1 都够。这个双向推导表明，(18.3) 承担完整 ABC 的难度。逐个 \(S\) 给出的常数个数、例外直线条数，均不提供 (18.3) 所需的高度控制。

**对最直接的格构造可以算出它的能力。** 写 \(M=U_S\)。向量 \((x,y)\) 在每个 \(p\in S\) 满足与 \((a,b)\) 同样的线性同余至模 \(p^{v_p(U)}\)，恰等价于 \(M\mid ay-bx\)。当 \(p\) 分别整除 \(a\)、\(b\)、\(c\) 时，该条件依次化为 \(x=0,\ y=0,\ x+y=0\) 模相应素数幂。设 \(h(x,y)=\max(|x|/a,|y|/b)\)。任何与 \((a,b)\) 线性无关的解满足 \(h\ge M/(2ab)\)。反过来，Bézout 给一个 \(ay-bx=M\) 的整解，将它加上整倍的 \((a,b)\)，可以让 \(x/a,y/b\) 的中点落在 \([-1/2,1/2]\)，于是 \(h\le M/(2ab)+1/2\)。因此直接取第二个格点、再用行列式下界，只能把 \(M/(2ab)\) 在常数精度内读回来。要推进 (18.3)，新输入须控制跨素数同时命中的本原点高度。单纯换格基或改善取整精度的支路到此结束。

### 18.4 三个 Frey 因子的搜索范围已经跑完

考虑所有有理二次映射 \(f:\mathbb P^1\to\mathbb P^1\)，要求 \(f^{-1}\{0,1,\infty\}\) 的几何支集保留 \(0,1,\infty\)，且至多增加一个点。特征零下二次映射有两个简单分歧点，分别在不同纤维。三个纤维的不同点数等于 6 减去落在它们上方的分歧点数，故必须恰有四个点，两处分歧值都在这三个值内。置分歧值于 \(0,\infty\)，它们唯一的原像均有理。以这两个原像为坐标零点与极点，映射是 \(\lambda z^2\)。剩下两个原像互为相反数，且有理（四点的集合在 Galois 下稳定，已知其中三个有理）。再缩放便得四点 \(\{0,\infty,1,-1\}\)。重排的交比只有 \(-1,2,1/2\)。取 \(x=a/c\)，第四点分别给出 \(a+c,\,2c-a,\,|2a-c|\)，正是仓库 Frey 曲线 \(c_6\) 的三个因子 \(2a+b,\,a+2b,\,|a-b|\)。在这个精确范围再找第四种换元，结果已经由分类决定。[Frey 的 \(c_6\) 分解](../LeanFormal/IUT/ABCBridge/Geometry/FreyWeierstrassCurve.lean#L86) · [仓库的三个 \(j=1728\) 原像](../LeanFormal/IUT/ABCBridge/Geometry/LegendreJFunctionDivisor.lean#L420)

还能直接检验“三个新增因子中总有一个几乎不损失 radical”的想法。给定 \(0<\alpha<1/3\)，取 \(\beta=(1-3\alpha)/2\)，写 \(a=1,b=m,c=m+1\)。以 3、13 为底各取首个达到 \(T^\beta\) 的素数幂，以 5、7、11 为底各取首个达到 \(T^\alpha\) 的素数幂，分别记 \(q_p\)。它们的积 \(N\) 满足 \(T\le N\le15015T\)。用中国剩余定理在 \([N,2N)\) 中取 \(m\)，令 \(m,m+1,m+2,2m+1,m-1\) 分别被 \(q_3,q_{13},q_5,q_7,q_{11}\) 整除。由 \(q_p\mid t\Rightarrow\operatorname{rad}(t)\le pt/q_p\) 得
\[
 R\ll c^{\,1+3\alpha},\qquad
 \max_i\operatorname{rad}_{>2}(L_i)\ll c^{\,1-\alpha}.
\]
令 \(T\) 走向无穷，对任意固定 \(\eta>0\) 先选 \(3\alpha<\eta\)，在 \(R\le c^{1+\eta}\) 的范围内也能让三个新增因子同时损失固定正幂。这排除了靠某一新增因子单独补足近乎全部 \(\log c\) 的证明。§17 所需的联合量 \(R\max_i\operatorname{rad}_{>2}(L_i)\) 仍可受新的算术关系控制，本构造没有否定该联合估计。

### 18.5 导入新理论前，哪一个小结论能检验它带来了独立信息

先在 \(1+(2^n-1)=2^n\) 上检验，写 \(M_n=2^n-1,\ s_n=\operatorname{rad}(M_n),\ d_n=\log(M_n/s_n)\)，\(n\ge2\)。三个新增因子恰为 \(2M_{n-1},\,2^n+1,\,M_{n+1}\)。因 \(M_n\) 与 \(2^n+1\) 互素，§17 的最优支集精确为
\[
 R\max_i\operatorname{rad}_{>2}(L_i)
   =2\max(s_ns_{n-1},\,s_{2n},\,s_ns_{n+1}).
\]
每个新增 radical 至多为 \(2c\)，所以 §17 的损失至少为 \(d_n-\log4\)。标准 ABC 在这一族上要求 \(d_n=o(n)\)。§18.1 在此也有精确读数。写 \(B=D(M_n),\ y=M_n/B\)，则 \(A=1,\ D=2^n,\ k=y\)，从下逼近的 \(0/1\) 就还原原三元组，下一商是 \(\lfloor2^n/y\rfloor\)。这说明真正困难的商可以出现在第一步，继续展开更多项于此无益。仓库早有底数 3 的幂族测试。[仓库既有的幂族检验](ABC-ROUTES-SCREEN.md#L64)

**重复幂可以无条件消去两部分。** 对 \(p\mid M_n\)，记 \(r_p=\operatorname{ord}_p(2)\)，\(w_p=v_p(2^{r_p}-1)\)。因 \(r_p\mid n,\ r_p\mid p-1\)，奇素数的提升指数公式给 \(v_p(M_n)=w_p+v_p(n)\)，且 \(w_p=v_p(2^{p-1}-1)\)。于是
\[
 d_n=\sum_{r_p\mid n}(w_p-1)\log p+
             \sum_{\substack{p\mid n\\r_p\mid n}}v_p(n)\log p .
\]
第二项至多 \(\log n\)。对每个 \(r\mid n\)，同秩素数的 \(\prod_{r_p=r}p^{w_p-1}\) 整除 \(2^r-1\)。记 \(\tau(n)\) 为约数个数，\(k=\lceil\log(n+2)\rceil\)。第一项中所有 \(r_p\le n/(k\tau(n))\) 的总贡献至多 \(n\log(2)/k\)。这两个误差除以 \(n\) 均趋于零。剩余项只含大阶且 \(p^2\mid2^{r_p}-1\) 的素数，即相应的底数 2 Wieferich 素数。这一赋值分解与已有文献一致。[仓库的阶整除引理](../.lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean#L270) · [仓库的提升指数引理](../.lake/packages/mathlib/Mathlib/NumberTheory/Multiplicity.lean#L390) · [关于 radical 损失的分解，§6](https://arxiv.org/abs/2609.00039)

**可单独验收的新理论测试。** 证明对无穷多个奇素数指数 \(\ell\)，存在 \(p\parallel 2^\ell-1\)（整除一次）。它是完整 ABC 的必要后果，只要求无穷多个指数上各有一个一次因子，数量要求低于对所有指数证明 \(d_n=o(n)\)。理由是完整 ABC 用 \(\varepsilon=1/2\) 已给充分大时 \(s_\ell>\sqrt{M_\ell}\)，而每个素因子都至少平方整除将给 \(s_\ell^2\le M_\ell\)。这些 \(p\) 的阶等于 \(\ell\)，不同 \(\ell\) 给不同 \(p\)，提升指数公式还给 \(2^{p-1}\not\equiv1\bmod p^2\)。因此这项测试已经触及无穷多个底数 2 非 Wieferich 素数的问题。把它写进接口当作输入不会推进证明。[Silverman 关于 ABC 与非 Wieferich 素数的原文](https://doi.org/10.1016/0022-314X%2888%2990019-4) · [Graves–Murty 对该问题的研究](https://mast.queensu.ca/~murty/Wieferich.pdf)

这个测试有一条可以实际执行的算术路径。若 \(p\mid M_\ell\)，则 \(\ell\mid(p-1)/2\)。欧拉判别法给 \((2/p)=1\)，故 \(p\equiv1,7\bmod8\)。因 \(M_\ell\equiv7\bmod8\)，至少一个 \(7\bmod8\) 的素因子出现奇数次。它或者只出现一次，或者至少出现三次。因此在给定 \(\ell\) 上，只须检查 \(1<d\le\lfloor M_\ell^{1/3}\rfloor\)、\(d\equiv7\bmod8,\ d\equiv1\bmod\ell\) 的整数。若全部满足 \(2^\ell\not\equiv1\bmod d^3\)，已经证明该指数有一次素因子，连完整分解都可省去。跨越无穷多个指数所需的新信息可以是一个排除这些三次整除在无穷多个 \(\ell\) 上出现的定理，也可以由奇重数的奇偶性在有三次整除时检测出另一个一次因子。检出某次三次整除只会使前一判据无结论。这个测试提供了评审一个新估计的较小入口，单独通过仍不推出完整 ABC。

| 交付件 | 验收标准 | 本次结论 |
| --- | --- | --- |
| 指定重复素幂后的完整计算 | 每组须列全全部高度上 \(c>R\) 的输入，给出终止上界和最小 \(K\ge1\) | §18.1 给出证明，至多 \(2\lceil\log_2D\rceil+2\) 个渐近分数。正系数同余还对成族变化的素幂给出 \(K=1\) |
| 受限输入上的 ABC | 覆盖任意高度，每个 \(\varepsilon>0\) 都给 \(1+\varepsilon\)，常数的依赖逐项标明 | (18.1) 的显式常数域及 (18.2) 的固定 \(S\) 域已有自然语言证明 |
| 继续沿三个 \(c_6\) 因子投入 | 新论证能跨高度控制重复素幂。在上述幂族上先交付无穷多个指数的一次因子证明，或直接交付更强的统一估计 | 分类与 CRT 检验已结束。已有三种替换及有限样本未达到这一标准，结束本轮搜索 |
| 完整标准整数 ABC | §18.1 的下一商对全部合格候选一致受控，或 (18.3) 对全部 \(S,a,b,c\) 一致，或直接证明仓库锁定的量词。原 III.3.12 另按 §16 的对象验收 | 本次没有给出该统一证明 |

核对使用一个线程，未编译 Lean。对 \(2\le c\le720\) 的全部 157,693 个有序本原三元组，直接枚举与 3,038 组重复素幂的渐近分数清单逐组一致，共有 50 个 \(c>R\)。另对 2,297 组给定素幂，无高度截断，穷举整个有限范围 \(Pxy<D\)，再与连分数结果逐组核对。另以精确整数复核 24 个交比排列、九组 CRT 构造，以及 \(2\le n\le60\) 的赋值分解和三个支集读数。对 \(3\le\ell\le73\) 的全部 20 个奇素数指数，按上述两个同余筛选后核对了 74,724 个整数，均通过该指数的三次整除排除检验。全称结论取自文字证明。四项形式验收均未运行。

## 19. 2026-11-19 本轮暂停交接：用仓库 Lean 供体承接原 III.3.12

本节是本轮在用户要求暂停前的完整交接。目标仍然锁定在本文件 §16.5--16.6：固定模型 \(p=3,\ell=5,d=3\)，从已有仓库 Lean 定理和原 III.3.10.2/3.11 的语义，推出原 III.3.12 的 xi-e \(\Rightarrow\) xi-f。没有把论文中的跳步改名为证明，也没有从论文开头重新审查；以下只记录已查到的 Lean 供体、它们真正能证明的自然语言步骤，以及最先缺失的原文来源桥。

### 19.1 本轮最重要的固定结论

1. **模型侧的算术下界已经算清，但它仍是 \(H_{\rm lit}\)，不是 \(H_{\rm orig}\)。** 固定例读数为
   \[
      q_s=-\frac{3}{20}\log 3,\qquad
      H_{\rm lit}=-\frac{9}{80}\log 3,
      \qquad H_{\rm lit}-q_s=\frac{3}{80}\log 3.
   \]
   第一行保留默认槽；第二行只加入原槽 2、整数据换位 \(\tau_{20}=(2,0)\)、整数据换位 \(\tau_{21}=(2,1)\)。逐元组先取 hull、再按真实行权重和元组权重求和后，第二行读数由固定槽的 \(-3/5\log3\) 改为 \(-3/20\log3\)，总和恰为 \(q_s\)。三个获益元组各贡献 \(3/40\log3\)，总增益为 \(9/40\log3\)；按局部格指数写，所需的加权指数乘积是 \(3^{18/5}\)。这只证明具体 `ThetaRegion` 的 literal 模型下界。

2. **取商前的 scalar profile 不能恢复标记投影。** `tmp/sheaf/xif/paper/S3138SourceProcessionProfileActual.lean:59` 的 `sourceStepXILogVolume_eq` 证明所有 source choices 的读数相同；`sourceStepXIProfile` 的 `possibleImage` 因而是同一个 `thetaPacket.logVolume` 的单点集，并且 Ind1/Ind2 只是在这个标量上作不变性。固定目标元组时，好槽投影为 \(1\)，默认坏槽投影为 \(3^{-6/5}\)，二者相差 \(6\log3/5\)。因此增加选择数、迭代层、权重平均或对该常值再施函数，均不能从 S3138 的标量接口恢复 §16.5.4 所需的带标记投影。继续追 scalar profile 不是这一步的证明路线。

3. **Ind1 的整数据换位可以一次性覆盖元组，不需要为每个元组拼一个箭头；但仍须证明它是原允许求值。** `Iut/Concrete/Ind1Invariance.lean:592` 的 `image_thetaFiniteOn_ind1Reindex` 给出整族区域重指标；`Iut/Concrete/ThetaRegion.lean:185` 的 `thetaComponentOn_admissible` 给出具体区域的非空可容许性。对第二行目标元组，源坐标表为

   | 目标元组 | \(\tau_{20}=(2,0)\) 拉回的源元组 | \(\tau_{21}=(2,1)\) 拉回的源元组 |
   |---|---|---|
   | \((G,B,B)\) | \((B,B,G)\) | \((G,B,B)\) |
   | \((B,G,B)\) | \((B,G,B)\) | \((B,B,G)\) |
   | \((G,G,B)\) | \((B,G,G)\) | \((G,B,G)\) |

   两个换位都把原标记槽 2 搬到好槽。若原求值允许整条 capsule 连同嵌入、区域和 strip 代表一起运输，则一次换位自然性可以同步处理全部元组；还可用 \(\tau_{21}=\eta\tau_{20}\eta\)、\(\eta=(0,1)\) 关系减少重复构造。但若固定的自然子胶囊嵌入必须保持不动，\((2,0)\) 不保持该嵌入，裸标签置换不够，必须证明带 capsule 的运输方块。

4. **普通单位的局部 witness 已有真正的仓库定理。** 坏位满足 \(v_3(r_{\rm bad})=3/10\)。取 \(y=6/r_{\rm bad}\)，则 \(v_3(y)=7/10>1/(3-1)=1/2\)。`Iut/Concrete/LocalConstruct/LogLattice.lean:361` 的 `exists_padicLog_eq_of_norm_le_rpow` 给出某个 \(u=1+a\in U_1\)，使
   \[
       \operatorname{padicLog}(u)=6/r_{\rm bad},
       \qquad r_{\rm bad}^{-1}=\frac16\operatorname{padicLog}(u).
   \]
   `logShell` 的分母正是 \(2p=6\)，所以这证明了普通单位对数的标量 shell 成员。它没有证明该单位被放入带标记 tensor、没有构造 `thetaFiniteOn` 到原 output carrier 的映射，也没有证明 III.3.10.2 的合格输出。

### 19.2 已有 Lean 供体能承接的 xi-e \(\Rightarrow\) xi-f 逻辑

1. `tmp/sheaf/xif/paper/S1447ReportFMarkedTraceActual.lean:354` 的 `s1447Comparison_of_outputReadoutProjection` 是最干净的实数逻辑骨架。给定原允许输出族 \(P\)、读数 \(\nu\)、目标 q 读数 \(Q\) 和 hull 上界 \(H\)，若
   \[
      \forall D\in P,\ \nu(D)\le H
   \]
   且有精确见证 \(D\in P,\nu(D)=Q\)，则 \(Q\le H\)。若只有
   \[
      \forall\varepsilon>0,\ \exists D\in P,
          Q-\varepsilon\le\nu(D)\le H,
   \]
   则用 \(\varepsilon=(Q-H)/2\) 反证，仍得 \(Q\le H\)。因此原文的“perhaps only up to some sort of approximation”必须具体化成精确覆盖或上述 epsilon 覆盖；仅说 IPL/SHE 可表达不够。

2. `tmp/sheaf/xif/SourceXiFConstruction.lean:49,61,73` 的 `sourceQPilotPoint_mem_hull`、`sourceQPilotLogVolume_eq_gauss`、`sourceXiFInclusion_of_bounded` 在**值层模型**中确实给出同样的集合论链：\(j=1\) q-pilot 点进入定义的 image set，进入其 least hull，再用 `le_csSup` 得 q 读数不超过 hull 上确界。这个 Lean 链是可复用的证明形状，但不是原 paper xi-f，因为它依赖额外的 `SourceImageRealization`，而 `OriginalInput` 只含 initial Theta data、theater family、index equivalence 和 arithmetic alignment，不含 Theorem 3.11 的 evaluation 输出或 output readout。

3. 更严重的是，值层 hull 不能冒充 paper 的有限 hull。`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean:379` 的 `sourceHolomorphicHull_logDegree_unbounded` 以及相关 `sourceHullVolume_eq_top_of_degreeFaithful` 表明，在当前 value-monoid scaling units 和 pointwise degree-faithful 假设下，值层 hull 的读数无上界、体积可为 \(\top\)。因此不能用 `sourceXiFInclusion` 加一个“当前 hull 有界”名字就声称原 III.3.12 已闭合；paper 的有限性必须在正确的实际 \(O\)-module/\(IQ\)/允许输出载体上重建。

### 19.3 原文来源桥的精确形状

固定第二行目标元组 \(c_t=(G,B,B)\)，取 \(\tau=\tau_{20}=(2,0)\)，源元组为 \(c_s=(B,B,G)\)。literal 区域中已有点级证据：好槽取参考元 \(1\)，恒等作用、标签 0 和 shell 元素 1 给出 `1 ∈ thetaFiniteOn({2}, c_s)`（具体定义见 `Iut/Concrete/ThetaRegion.lean:170`，换位公式见 `Iut/Concrete/Ind1Invariance.lean:592`）。原文层的最小缺口不是这一个点，而是：

1. 从同一固定输入的 III.3.10.2 evaluation 构造一个带积分数据的实际输出 \(D_\tau\)，并给出其 carrier 与 literal tensor 的结构态射/重排；
2. 至少证明点级来源
   \[
      E_\tau(1)\in U_{2,3},
   \]
   更强、更适合取 hull 的证明是
   \[
      E_\tau\bigl[\operatorname{thetaFiniteOn}(\{2\},c_s)\bigr]
         \subseteq U_{2,3};
   \]
3. 证明这个 \(D_\tau\) 真属于固定输入对应的原允许族 \(P_C\)，而不是仅属于自造的 value-layer `allowedOutputSource` 或静态 `OrigXiFPaperOutputRegion`；
4. 证明原文 readout \(\nu(D_\tau)\) 与该标记投影的对数、张量秩归一化和 procession 权重一致，至少达到所需的 \(Q-\varepsilon\)；
5. 证明每个实际输出都满足 \(\nu(D)\le H_{\rm orig}\)，再调用 S1447 的 exact/epsilon coverage 定理。

当前源码中，`SourceKummerEvaluationArrows.lean` 和 `SourceFTimesMuPrimeStripPolyIsomorphism.lean` 只提供条件式 strip/evaluation-arrow 接口或交换方块数据；`S1951KummerEvaluationSquareActual.lean` 的实际示例绑定 `FinitePrimePlace 2 7`，不实例化本例 \(p=3,\ell=5,d=3\)。`OrigXiFIndeterminaciesActual.lean` 的静态 `OrigXiFPaperOutputRegion` Ind1 不变性也只说明静态区域的重排不变，不提供 evaluation 到该区域的来源映射。`SourceAllowedOutputActualAttempt.lean` 的 `SourceAllowedOutput` 还要求实际 donors、C3/C4 数据、Haar 数据及 witness；现有 `tensorLanding` 只记录 q landing，未记录单位保持、槽重排和 T11 identification。

### 19.4 不能继续采用的短路

- 不能把 `sourceStepXILogVolume_eq` 的恒定单点读数当成带标记 projection readout；它在定义层已经丢失槽信息。
- 不能把 `SourceXiFConstruction` 的 value-layer hull 当成原文有限 hull；已有 unbounded/top 结果正好反驳该替换。
- 不能把 `thetaComponentOn_admissible`、`image_thetaFiniteOn_ind1Reindex` 或静态 `OrigXiFPaperOutputRegion` 不变性当成“原 evaluation 输出成员”定理。
- 不能把 `SourceKummerEvaluationArrows` 的 strip 同构、单位作用或交换方块接口当成已经由算法操作产生的原 III.3.10.2 evaluation。
- 不能把 `q_le_hull` 等已有条件字段换名为原文来源桥；其消费者仍需要实际输出族、读数识别和有限性。

### 19.5 暂停点、验收和下一动作

- 本轮只读研究后新增的是本交接文字、审计摘要和状态/队列记录；没有修改 Lean 数学文件，没有新增 `sorry`，没有创建新 axiom。
- `statement_compiles`：未运行；`proof_body_checked`：未运行；`kernel_closed`：未运行；`target_accepted`：未运行。Lean 按仓库规则应通过 watchdog；本轮没有把直接 `lake env lean` 的结果冒充验收。
- 下一次只做一个辨别力最高的包：固定 \(p=3,\ell=5,d=3\)、目标 \(c_t=(G,B,B)\)、\(\tau=(2,0)\)，在已有 literal `thetaFiniteOn` 点证据之上，构造实际 evaluation carrier map 并证明 \(E_\tau(1)\in U_{2,3}\) 或区域包含。若这一步不能从现有 `OriginalInput`/evaluation 结构得到，就把它登记为正式 `statement` 缺口，不再继续堆 scalar profile 或值层 hull。
- 若该点级来源桥闭合，再用整数据换位自然性覆盖 \(\tau=(2,1)\)，接入三元组表和 \(3^{18/5}\) 的全局格指数计算，最后调用 S1447 的 epsilon/精确覆盖定理。即使成功，也只先接受固定输入；不自动推出全体 III.3.11 输入的量词或原允许像的有限性。

本节交接完成后按用户要求暂停。后续恢复时从本节 19.3/19.5 开始，不从论文开头重审；先读本节和 §16，再查列出的 Lean 供体。
