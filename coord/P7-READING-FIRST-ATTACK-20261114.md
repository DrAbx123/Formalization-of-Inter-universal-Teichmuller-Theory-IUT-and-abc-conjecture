# P7 当前五项缺口：从实际 reading 接线，消掉多余强条件

日期：2026-11-14。负责人：本 chat root，单线程研究。用户要求：给关键数学思路、完整交接，不编译、不重复派工、不用新增困难假设冒充无条件完成。

本报告对应节点 `p7-reading-first-attack-20261114`。当前只改研究文档；未改任何 Lean 文件，未启动构建。源码中的已有证明、在写证明、条件接口与本报告的自然语言证明分别记录。各条源码的交接时哈希保存在节点中；活跃 owner 仍可能继续修改源码。

实际消费者：原 `qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3`、实际 L-side reading、`Thm110DisplayInputs.hSlack`、`Ind1ShellTransportForRequired`、`LogShellQFECardinalityHypothesis`。SHEAF 阶段：目标分解和数学证明；下面没有给全部 source 构造宣布阶段 1 完成。

## 0. 先给本次的新结论

用户列出的五项仍不能合在一起报“原目标已闭合”。但其中有三处可以明确缩短，而不是继续堆条件接口：

1. **Thm 1.10 的额外 `logQ bound` 可以由现有形状的 `hCor312` 吸收推出。** 原文 Thm 1.10 自己排除 `l=5`，所以实际范围正是本计算需要的 `l≥7`。不需要为这个 slack 再另造解析估计。完整证明见 §4。
2. **reading 不必追求 G2/G3 两个强等式，更不必先证 `normRatio=1`。** 用同源、同索引的两个单向比较即可；`normRatio≥1` 对有符号 q 读数提供有利方向。已有 actual root-hull 包含供体可以直接消费，不能只用弱的 paper 标量求和。见 §2。
3. **#C 应直接数实际的 `U/(1+p^s O)`。** 当前 A 接口把它接到 `O/(p^s)^e`，和实际同余层不相配；只修 B 的指数还不够。正确中间对象为 `O/(p^s)=O/𝔪^(e_K s)`。A/B 的完整数学构造和可绕过商环接口的直接计数路线见 §6。

另一个源端缩减是：有实际等变乘法箭头时，**先取不动点、再模挠、再取无限可除子群**，可以构造单位层作用，而不用事先把单位层同构放进假设。只有 DPrimeStrip 的一般箭头仍须取得实际 realization；这一点不能省略。见 §5。

“无条件”在此指：除原论文允许的合格初始数据外，不再增加目标不等式、自由 transport、自由 norm/degree/measure 字典或任意 `Nonempty`。原文 Thm 1.10 本有的 15-torsion 条件不是本报告新增的假设。

## 1. reading 的精确断点：目前实际连接的是哪些量

### 1.1 四种量必须分开

在 `BadPlacePaperNormalizedComparisonActual.lean`，令

\[
 S_Q=\sum_b w_b c_b^{\rm paper}\log p_b,
 \qquad
 S_\Theta=\sum_b w_b\frac{c_b^{\rm paper}}{2\ell}\log p_b.
\]

当前定义直接给出

\[
 S_\Theta=\frac{S_Q}{2\ell}.
\]

所以这两个 paper sums 的比较，单看定义，尚未承载原文所有 `j²`、procession、tensor 槽、Ind 作用及实际 hull 的几何内容。已有证明应保留，但不能单凭这条求和比较宣布原 reading 已接通。

在 `S3137QThetaPilotLogVolumeReadingsActual.lean`：

\[
 Q_{\rm old}(P)=-|\log\|P.line.C3.q.q\||,
 \qquad
 H_{\rm old}(C3)=\log\bigl(\mu_{C3}(\thetaPilotHull(C3))\bigr).
\]

这里右侧是 **raw signed Haar log**，并没有自动减单位区域的 log mass，也没有自动除 tensor 维数。该文件同时定义的 ENNReal 体积不是这个实数 reading，不能混用截断后的量。

而 `PaperLevelXiFTargetActual.lean` 的 `actualThetaHullLogRoot` 是按实际 bad-place 权重求和的 **normalized** 局部 root-hull log。其 `actualQPilotMagnitudeClassical` 名字虽有 Classical，正文使用的仍是 `qVFamNormalizedCoefficient`；不能根据名字把它认作 default norm 的量。

L-side 的 `thetaReadActual` 仍是 raw log；`thetaNormReadL` 只减 `log actualUnitMassL`。它也不能自动等同于所有其他文件里的“每维 normalized log”。

### 1.2 还存在局部与全局、输入与输入的区别

当前字典的 `I`、`place`、`T` 是分开传入的。`T` 上的所有 Bad 求和不能无证明地等于单个 `place` 的读数。原 reading 的参数 `P` 与另一个参数 `C3` 也不是仅凭类型就自动来自同一局部 packet。

因此，不能用“全局和已比较”推出每个局部 reading；也不能通过重新选一个有利的 `T`、把 Bad 缩成单点或把一个局部 q 设成全局和的指数来填 G3。

**正确切分：**先对原 source 产生的同一个局部 packet 证明读数关系；全局原文消费者需要求和时，再沿原文索引和权重汇总。当前字面目标若是局部的，就消费已有的局部包含定理，不绕到全局后再强求等式回来。

### 1.3 已有新 wrapper，勿再派发同类任务

本次核对时已出现 `Mzk1ActualReadingTargetActual.lean`。它把

\[
 H_{\rm old}=-\mathrm{actualThetaHullMagnitudeRoot},\qquad
 Q_{\rm old}=-\mathrm{actualQPilotMagnitudeClassical}
\]

作为 G2/G3 输入，调用 `actualPaperXiFTarget`。这是正确的条件归约形状，不是 G2/G3 的构造。该文件处于活跃编辑中，本 chat 没有验证其当前编译状态；不能根据文件中的 PROVED 行把它算作本次 green。

接下来不需要另写一个同样的 `of_identifications`。需要的是下面的实际单向构造。

## 2. reading 主线：同源的单向运输，复用实际 hull 包含

### 2.1 所需关系比两个等式弱

用三个中间量表示同一 packet 的读数：

\[
 Q_{\rm src}\le Q_{\rm norm}
 \le H_{\rm root}\le H_{\rm target}.
 \tag{R}
\]

第一箭头来自同一 q 的 norm 实例比较；第二箭头已有实际 root-hull 包含供体；第三箭头来自原 source 区域到目标 hull 的包含及准确的体积校准。

如果最后两端已严格校准为冻结的原 reading，传递性就给原目标。这条路线无需全局 tensor 与根域 product 的代数等价，也不要求所有中间量恰好相等。

必须强调：本报告并未把 (R) 的缺失箭头作为最终新假设。下面逐一说明它们应由哪些真实对象构造，哪些步骤已有供体，哪些仍需证明。

### 2.2 第一箭头：保留 norm correction 就够了

已有 `Mzk1P0QVFamNormBridgeDonorActual`：

\[
 n_b^{\rm norm}=(n_b^{\rm def})^{1/d_b^F},
 \qquad 0<n_b^{\rm def}<1,\quad d_b^F\ge1,
\]

以及已经写出的 `qVFamNormRatio_ge_one`。因此

\[
 r_b:=n_b^{\rm norm}/n_b^{\rm def}\ge1,
 \qquad
 \log n_b^{\rm def}
 =\log n_b^{\rm norm}-\log r_b
 \le\log n_b^{\rm norm}.
 \tag{R1}
\]

这正是 q-reading 为负时需要的方向。无需使两个 norm 相等。

在同一权重的全局层，令

\[
 C=\sum_b w_b\log r_b\ge0.
\]

已有 `s13Q_eq_paperNormalized_sub_normRatio` 给

\[
 Q_{\rm norm}^{\rm signed}=-S_Q+C.
\]

已有 `actualPaperXiFTarget` 的实际包含路线给

\[
 -S_Q+C\le H_{\rm root}.
\]

于是可直接得

\[
 -S_Q\le H_{\rm root}.
 \tag{R2}
\]

这没有从弱的 `S_Theta≤S_Q` 反推更强的 actual target；用的是已经存在的 actual hull 包含证明，再利用修正项的有利符号。

同理，`Mzk1P0QThetaReadoutNormCorrectionActual.paperQDegree_le_closedForm_sub_one_sub_correction` 已给 degree-weighted 版本。配合实际 norm bridge 和 `r_b≥1`，其减掉的 correction 非负，可直接推出对应上界；不必走该文件后面的 `of_fields`，后者要求更强的 S45 correction-zero。

**适用边界：**上述每次求和左右必须使用同一权重。`w_b=1/[K_w:F_v]` 与 `s1915LocalDegree` 不能互换。qhat 的 norm equality 也必须指向同一个 `rootBase`/normalized norm 实例；不能把 `norm_algebraMap` 的结论读成另一个 default norm 等式。

### 2.3 第二箭头已经有实际集合供体

复用：

- `RootHullContainmentInequalityActual.qPilotClassicalRegion_subset_rootHull`；
- `RootNormalizedContainmentActual.qPilotNormRegion_subset_rootNormHull`；
- `qPilotNormLog_le_rootNormHullLog`；
- 全局消费者 `PaperLevelXiFTargetBridgeActual.actualPaperXiFTarget`。

其证明是具体的：实际 fractional lattice 对系数反向单调；取已构造的 `oneLabel`，其 Gauss exponent 为 1；`c_norm/(2l)≤c_norm` 给 q 区域落入这个 theta 分支，再落入 closure hull。正测度和有限测度允许应用有符号 normalized log 的单调性。

不再为这条数值比较新建一个“实际 hull 上界/下界假设”。目前欠缺的是其区域与论文实际源区域之间的运输。

这里的 `j=1` 是现有局部 union-hull 证明中的合法分支。不能因此把原文对所有 j 的 procession average 换成 j=1，更不能把一个局部 region 当成所有可能像的共同区域。

### 2.4 第三箭头的实际构造：只需要一个可证明进入原 hull 的子区域

先固定原文给出的实际局部 packet，按以下顺序工作：

1. **同一个 q。** 从原输入的 q-comparison witness 追到当前 `qVFamily`、P 的 q 和 theta root。证明具体嵌入后元素相等，不新选一个 Tate 参数。若已有原 P 构造还欠 `NativeC1PaperSource` 或 `SourcePilotRegionDonors`，先补其实际源构造；一个 P 参数并不证明它存在。
2. **同一个标签。** 证明上述 oneLabel 对应原 packet 内允许的 theta 分支；利用实际 theta/root 关系，明确标量是 q 的哪一个幂。不能只借用抽象 `SignedLabel` 的一个元素。
3. **从点扩到格。** 仅证明 theta 点属于 H 不够。要由原 hull 的实际闭包/模性质，证明该点生成的整个所需整数格属于 H。若 hull 是 `O_hol`-稳定的，证明相应 `a·O_hol⊆H`；若只有加法格闭包，逐个生成元及其整数线性组合给出证书。
4. **载体不相同就用真实映射与有限指数。** 在同一个公共闭包中构造已有根域到原文 `K_v` 的嵌入；已有交接 §8 的 torsion/Tate 下降路线给这一节点的证明方案。若目标仍在较小的 base tensor，计算实际逆像格或像格及其指数，不能声称有限度数不同的域或 tensor 自动等价。
5. **使用测度单调性。** 在目标同一个 Haar 空间中，得到实质性的 `J⊆H_target` 后，计算 `log μ(J)` 并比较。这是把已有标量证明接入真实 hull 的地方。

例如在共同局部扩张中，若 `α^(2l)=q` 且 `α` 整，则

\[
 qO_L\subseteq\alpha O_L.
\]

对真实域嵌入 `ι:F_v→L` 取逆像得到

\[
 qO_{F_v}\subseteq J:=\iota^{-1}(\alpha O_L).
\]

J 是可计算的 DVR 分式理想，其指数由真实 valuation 的取整给出。这一步是实际构造；但 **J 被原 source hull 接受** 仍须由原 hull 的定义/生成元证明，不能把该包含再次当作自由字段。

这条路线只为下界选一个原文允许的子区域，不需要先证明所有 Ind1 作用都保格。若选取的区域与跨列运输本身依赖一般 source arrow，相关 provenance 仍要证明。IV Box 的上界则必须覆盖全部允许像，不能沿用下界的单分支缩减。

### 2.5 可检验的有限证书，代替全局 carrier 等价

若同一个目标 tensor 上已有满格 `R` 和实际生成元格 `J`，取 R 的基，写出 J 的生成矩阵，计算 Smith 指数或 determinant。

当 `J=M R` 且 M 可逆时，

\[
 \log\mu(J)-\log\mu(R)=\log|\det M|_p.
\]

一般有限指数格用指数公式得到相同的 log-volume 关系。真正的新证据是：每个生成向量由原 source 的 theta/单位/允许操作产生，且矩阵的 valuation 预算足以给目标比较。

这样，A1 所需对象被降为“实际子格 + 生成证书 + 显式余体积”，不需要构造不适配的 `BlockProductAlignmentData`。

## 3. object lock：如何避免把 B、unitMass、sign 再当输入

### 3.1 degree 只走真实塔公式

`ProcessionNormalizationWeightsActual.localCompletionDegree` 是
`[K_w:(F_mod)_v]`；`s1915LocalDegree` 是根域对 `Q_p` 的维数。这不是同一种 degree。

这里记 F_v=(F_mod)_v；根域若先以 F 的某个完备化为基域，须把该中间层一并放进同一个塔。若已构造相容的域塔

\[
 \mathbb Q_p\subset F_v\subset L_b\subset K_w,
\]

令

\[
 d_F=[F_v:\mathbb Q_p],\quad d_L=[L_b:\mathbb Q_p],
 \quad n=[K_w:F_v],\quad m=[K_w:L_b].
\]

正确的无条件塔公式为

\[
 m d_L=n d_F.
 \tag{D}
\]

因此不能仅凭塔存在就填当前 lock 要求的 `d_L=B*n`、`B:Nat`。用 (D) 直接改写实际 volume/weight 的中间消费者；需要比例时用这些正整数之比，保留 d_F 和 m。

**这只修改过强的中间接口，不授权修改原目标。** 目标的原权重仍须由原文 procession/divisor 定义推出。没有同源域嵌入时，连 (D) 的实例也还不能使用。

### 3.2 先统一符号，不让 hlock 与 theta_sign 两条路线互相替代

当前 `PaperS3137ObjectLock.theta_sign` 要求

`thetaNormReadL = -thetaNormReadProduct`，

而 `Mzk1P0LNormComparisonConditionalActual` 的 hlock 要求

`thetaNormReadL = thetaNormReadProduct`。

另一方面，`thetaNormReadProduct` 的正文是

\[
 \log\mu(H_{\rm product})-\log\mu(O_{\rm product})
 =\sum_b d_b\log r_b
 =\mathrm{s1915ClosedForm}-1.
\]

它本来就是有符号的 log-volume。只有从 signed log 转到“正 magnitude”时才取负号。两个接口不能靠同一个未经证明的“符号约定”同时填充；应从上述实际测度公式逐项推，不把 `theta_sign` 当原始构造数据。

### 3.3 unitMass 不必等于 1，但必须把常数和维数带回原目标

取同一个正有限测度参考格 R，定义

\[
 V_R(H)=\frac{\log\mu(H)-\log\mu(R)}{d},\quad d=\dim_{\mathbb Q_p}A>0.
\]

则恒有

\[
 \log\mu(H)=d V_R(H)+\log\mu(R).
 \tag{M}
\]

若改用计算方便的 `ν=μ/μ(R)`，最后仍须按 (M) 恢复 raw reading。原目标右边的 `Measure.addHaar` 不能擅自换成 ν。

Mathlib `MeasureTheory/Measure/Haar/Basic.lean` 中 `addHaar` 来自对 `PositiveCompacts` 的任意选择；“它是 Haar”没有附带“指定单位球质量为 1”。从这个一般性质也推不出 `log unitMass≥0`。

此外，减掉单位 mass 与除 d 是两次不同操作。即使已经证 `V_R(H)≥log||q||`，当 `log||q||<0`、d>1 时，也不能直接推出 `log μ(H)≥log||q||`。

应使用精确的比较预算。若实际构造给出

\[
 Q_{\rm target}=-aS_Q+c_Q,
 \qquad H_{\rm target}\ge-aS_\Theta+c_H,\quad a\ge0,
\]

则充分条件是

\[
 c_Q-c_H\le a(S_Q-S_\Theta).
 \tag{B}
\]

这里 c_Q、c_H 必须由实际 Haar 参照、determinant、degree、有限指数和源运输算出；不能定义成两端的差再把 (B) 作为假设。

例如若某个实际局部计算给出 `Q_target=-t`、`V_R(H)≥-t/(2l)`，则按 (M)，真正还需核算的是

\[
 \log\mu(R)+(1-d/(2\ell))t\ge0.
\]

这显示为什么单位常数与维数不能丢掉。若同一个原文归一化使两端 c 相同，常数直接抵消，这是最干净的路线；若当前 raw target 只有右端携带任意 Haar 常数，则必须补其实际校准依据。

**本报告不承诺一个未经校准的 raw target 必然可证。** 要完美解决原论文问题，必须让冻结目标包含论文要求的参照语义。若发现当前定义与原文不一致，应提出具体的语义修正并重审消费者，不能凭本报告自行改目标或把新 normalized statement 算作旧 target 已证明。

## 4. Thm 1.10：可以消去独立 logQ/slack 输入的完整计算

### 4.1 原文范围本身排除 l=5

本地原文：`papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt`，L1255–1292，印刷页 22。

Thm 1.10 的实际条件包括 E 的 `(3·5)`-torsion 在 F 上有理，并明确说明由 IUT I Definition 3.1(c) 得 `l≠5`。因此 `PrimeGeFive` 加这份实际 IV 初始数据给 `l≥7`。

内部证明也很短：若 l=5，则 E[5]⊂E[15]，所以实际 canonical mod-5 Galois representation 是平凡的；但已有 `SourceClauseC.image_contains_SL2` 与 `representation_eq_canonical` 要求其像包含 SL₂(F₅)。取非恒等的上三角幺幂矩阵即矛盾。这里须把 IV 的实际曲线/基域与 Clause C 的曲线作原文要求的识别，不能仅给一个口头 torsion 条件。

因此不应该再为原文 Thm 1.10 新开“l=5 的独立 logQ 估计”任务。泛化到任意 `PrimeGeFive` 的数值引理若保留 l=5，是另一个更强问题。

### 4.2 精确展开现有 display

记

\[
 L=\ell,\quad d=d_{\rm mod},\quad
 X=\log d_{F_{\rm tpd}}+\log f_{F_{\rm tpd}},\quad
 Y=e^*_{\rm mod}L+\eta_{\rm prm},\quad Q=\log q.
\]

实际来源给

\[
 L\ge7,\quad d\ge1,\quad X\ge0,\quad Y\ge0.
\]

`S3171IUTIVSection1DisplayActual` 定义

\[
 M=(1+12d/L)X+10Y,
\quad R=(1+20d/L)X+20Y,
\quad G=2Q/L^2.
\]

其 `hCor312` 正是

\[
 Q/6\le M+2Q/L^2.
 \tag{C}
\]

先移项，而不是另找关于 Q 的外部定理：

\[
 \frac{L^2-12}{6L^2}Q\le M,
 \qquad
 Q\le\frac{6L^2}{L^2-12}\bigl((1+12d/L)X+10Y\bigr).
 \tag{A}
\]

分母正，因为 L≥7。到此没有使用待证的最终 display。

### 4.3 从 (A) 推出现有消费者要的 hQ

要证

\[
 Q\le4dLX+5L^2Y.
 \tag{Q}
\]

分别比较 X、Y 系数即可。

X 系数的差等于

\[
 4dL-\frac{6L^2+72dL}{L^2-12}
 =\frac{2L\bigl(2dL^2-60d-3L\bigr)}{L^2-12}\ge0.
\]

最后一个非负性完全初等：因为 `2L²-60>0`、d≥1，

\[
 2dL^2-60d-3L\ge2L^2-3L-60.
\]

写 L=7+t、t≥0，右侧是 `17+25t+2t²≥0`。

Y 系数的差为

\[
 5L^2-\frac{60L^2}{L^2-12}
 =\frac{5L^2(L^2-24)}{L^2-12}\ge0.
\]

乘 X≥0、Y≥0 相加，得到 (Q)。再消费现有
`Mzk1Thm110SlackActual.thm110Slack_of_logQ_bound`，即得

\[
 G\le R-M,\qquad Q/6\le R.
\]

所以 hQ、hSlack 不需要作为最终 actual theorem 的独立输入。

### 4.4 查重及本次不能宣称关闭的部分

本次交接过程中现有 lane 已开始写
`Mzk1IVThm110LogQActual.logQ_bound_of_hCor312`，不要再派第二份同证明任务。上面给的是完整数学证明和适用范围；当前源文件的证明体、编译与公理检查由原 owner 后续验收，本 chat 未运行。

仍须构造 actual display terms：d 来自 `[F_mod:Q]`，X 来自实际有效 different/conductor 除子的归一化 degree，Y 来自论文的 ramification 常数及 η，Q 来自同一 q-pilot 除子。不得给一个数值相等但来源独立的 `Thm110DisplayTerms`。

真正剩下的数学箭头是 **actual hCor312**。原文 L1350–1385 的 C_Theta 候选形状为

\[
 C_\Theta=
 \frac{L+1}{4|\log(q_{\rm small})|}
 \left[M-\frac16(1-12/L^2)Q\right]-1,
 \qquad |\log(q_{\rm small})|=Q/(2L).
\]

从真实 Box/局部估计证明这个候选常数适用于同一个 theta-pilot，再使用真正 3.12 的 `C_Theta≥-1`；前面的因子为正，就推出 (C)。不能只是定义一个 C_Theta 再假设它适用。

因此工作图应为：

`同源的 3.12 reading + 实际 IV Box/常数识别 → actual hCor312 → 上述吸收 → actual final display`。

不应再把一个与目标接近的独立 logQ 上界插在 hCor312 之后当新算术输入。这项剪枝不等于 actual hCor312 已完成。

## 5. Ind1/Ind2：先下降，再取单位层的源构造路线

### 5.1 新的可用代数刻画

对实际有限扩张 F/Q_p，令

\[
 A_F=F^\times/\mu(F),\qquad W_F=O_F^\times/\mu(F),
\]

其中 μ(F) 是全部乘法挠元。改用加法记号，固定整数 r≥2 且 `(r,p)=1`，定义

\[
 D_r(A_F)=\bigcap_{n\ge0}r^n A_F.
\]

则

\[
 D_r(A_F)=W_F.
 \tag{U}
\]

完整证明：实际离散 valuation 降到 `A_F→Z`，核为 W_F。若 x 属于所有 r^n A_F，其 valuation 被每个 r^n 整除，故 valuation 为零，x∈W_F。反过来，实际单位对数把 W_F 识别为有限秩 Z_p 格；r 是 Z_p 单位，乘 r 是双射，故每个 x∈W_F 都可除以所有 r^n。因此有反向包含。

这不依赖选 uniformizer 分裂。任何群同构 `A_F≃A_F'` 都保持各 r^n 的像，故自动把 D_r 运到 D_r。对同一 residue prime，可取 r=2（p≠2）或 r=3（p=2）。

若两端 residue prime 尚未识别，先取与 p、p' 都互素的 r，同样得到 W_F≃W_F'。若 p≠p'，乘 p 在 W_F' 上是双射，在正秩的 Z_p 格 W_F 上却不是双射，矛盾。因此实际乘法商同构还迫使 p=p'；不能从任意尚未实化的 DPrimeStrip 直接套这个结论。

**意义：**只要实际源箭头已下降到整个 `F^×/μ`，不需要另外给它“保整数单位”的假设；单位层是上述内在子群。

### 5.2 如何从现有 isoMon 到有限局部域乘法群

当前实际 `localFPrimeStrip.Mon v` 是代数闭包的乘法群，不是 O_F 的单位群。正确做法不是给这两个群造等价，而是取实际不动点。

设原 source 确实给出等变乘法同构

\[
 \psi_a:\Omega^\times\xrightarrow\sim(\Omega')^\times
\]

以及 Galois 箭头 `a_G`。在 Ω 中固定实际有限局部域 F，对应子群 H_F；在目标取 F'、H_F'。先从实际 source 的 place/decomposition 数据证明 `a_G(H_F)=H_F'`。

若 x 被 H_F 固定，任意 h'∈H_F' 可写成 a_G(h)，由等变性

\[
 h'\psi_a(x)=\psi_a(hx)=\psi_a(x).
\]

因此 ψ_a 限制到两个不动点群；逆映射同样限制，所以是同构。实际代数闭包的固定域定理将这两个群分别识别为 F^×、F'^×。

之后依次做：

1. 用挠子群的函子性取商，得到 `A_F≃A_F'`；
2. 用 (U) 限制为 `β_a:W_F≃W_F'`；
3. 接现有 `unitLogQuotientEquivOfMulEquiv`；
4. 接已经构造的 log、perfection、有理化及 Q_p 线性后半段；
5. 用真实 ψ_a 的自然性证明消费者需要的 square 和 shell 保持。

这允许 ψ_a 是乘法群的 source 同构，不需要假定它由有限域上的域自同构给出，更不要求它是恒等。

### 5.3 顺序不能反过来：先模挠再取不动点会丢掉整数格

若先把 Ω^× 除掉全部 roots of unity，再取 Galois 不动点，会出现额外元素。

例如 x∈F^×、α^n=x，则任意 σ∈G_F 有 σα/α∈μ_n。所以 `[α]` 在 `Ω^×/μ(Ω)` 中被 G_F 固定，即使 α 不属于 F。

这个操作会引入 F^× 的有理分幂；它不能直接恢复 W_F 的 Z_p 格。故应从现有 `toF.isoMon` 层做固定点下降，再使用 `isoTimesMu`/torsion quotient 的兼容性。不能只对 `timesMu` 对象取不动点后声称它是实际单位商。

### 5.4 一般 DPrimeStrip 的剩余责任是什么

`PrimeStripCore.lean` 的 `DPrimeStripEquiv` 只有 `isoPi`、`isoG`、投影兼容。它没有上面的 ψ_a、实际 Ω 作用或 H_F 的标识。因此 §5.2 不是从任意该抽象结构直接构造 β 的证明。

对已经来自真实 `SourceFTimesMuPrimeStripEquivalence` 的 source representatives，其 `toF.isoMon` 和 `compatAction` 是可消费的供体。必须证明：这些 representatives 实际覆盖消费者要求的一般 Ind1/Ind2 箭头，以及 realization 是同一个原文局部域的实际 Galois 作用。

对只有 DPrimeStrip 的一般箭头，优先级有两种：

- 若原 procession 的构造本来就产生 full F-strip representative，只是当前 erasure 丢了它，回到构造端保留该代表，证明 erasure 等于原箭头；不要重新造一次全部算术。
- 若原文一般箭头确实只给 D 数据，继续此前报告 §7.2/7.3 的惯性阿贝尔像或有限 Kummer 系统路线。需要内部证明单位层重构和箭头自然性；不能在此新增“存在 lift”字段并宣布完成。

有限 Kummer 路线的具体输出应是每层单位商的实际映射和相容方形；证明 valuation-zero 的 Kummer 子群被箭头保存，再取逆极限。仅有 Kummer 注入/核定理不提供这个保存性，也不提供所需的全部 H¹ 满射。

### 5.5 provenance 怎样验收才不是 σ=1

对实际要求的每个箭头 a，β_a 必须由 a 的实际作用诱导，满足原单位嵌入/quotient 的交换方形，且有

\[
 \beta_{ba}=\beta_b\beta_a,\qquad\beta_1=1.
\]

Ind2 的 place/label 重排要运输到相应目标纤维，不能固定原纤维后把所有作用设成 id。证明不必强求每个 β 非恒等；某些实际箭头可以确实平凡。但“取一个 σ=1 的实例”没有覆盖一般箭头的 provenance。

§5.1–5.3 给出的下降和单位子群刻画是本次可交付的数学证明。所有要求箭头的 source realization/覆盖仍开放。此前 §7.1.1 关于实际有限秩 W 的自动连续性复核仍适用；这里不把它误用到任意 DPrimeStrip 或整个 Ω^×/tors。

## 6. #C：修正中间对象后，A/B 有完整计数路线

### 6.1 锁定实际群、理想、三个不同的指数

固定实际有限局部域 K/Q_p，O=O_K，极大理想 m=(π)，k=O/m，q=#k，令

\[
 e_K=v_K(p),\quad s=\begin{cases}2&p=2,\\1&p\ne2,\end{cases}
 \quad c=p^s,\quad N=e_Ks\ge1.
\]

当前 `logShellCongruenceUnits` 的定义是

\[
 U_c=\{u\in O^\times:\|u-1\|\le\|c\|\}=1+cO.
\]

所以真正要数的是

\[
 C=O^\times/U_c,
 \qquad I=(c)=(p^s)=m^{e_Ks}.
 \tag{I}
\]

当前 `MissingCongruenceUnitsEquiv e` 的右侧却是 `(O/(c^e))^×`，左侧仍是固定 U_c。除特殊情形外，这是不同的同余层。修正 B 成 `(q−1)q^(e_K s e−1)` 只能正确描述右侧的新商环，不能让 A 自动成立。

`Mzk1IutIVTruncatedUnitsCardCorrectedActual` 已把那个商环的正确指数写成显式目标，但尚未证明计数，也没有修好上述 A 的配对。此文件不应被当成 #C 已消除。

**推荐接口：**A 直接接 `(O/(logShellScale p))^×`，不再把 ramification 指数作为该元素的额外幂。B 用独立的 m-adic 参数 N。最后由 (I) 代入 N=e_Ks。

### 6.2 A：构造实际单位商等价

考虑自然映射

\[
 \rho:O^\times\longrightarrow(O/I)^\times.
\]

证明分三步。

**核的识别。** `ρ(u)=1` 当且仅当 u−1∈I。因为 c≠0，

\[
 \|u-1\|\le\|c\|
 \iff\|(u-1)/c\|\le1
 \iff (u-1)/c\in O
 \iff u-1\in cO.
\]

所以 `ker ρ=logShellCongruenceUnits`。这一步甚至不必先引入 uniformizer；现有实际整数环的 norm 判据已经足够。

**满射。** 给一个商环单位，取其代表 a∈O 和逆元代表 b；有 ab−1∈I⊂m。若 a 不是 O 的单位，则 a∈m，故 ab∈m，结合 ab−1∈m 得 1∈m，矛盾。所以 a 本来就是 O 的单位，它映到给定商环单位。

**取商。** 对这个实际满同态用第一同构定理，得到

\[
 O^\times/(1+cO)\simeq(O/(c))^\times.
 \tag{A_C}
\]

这是真正的映射、核和满射证明，不需要把 `Nonempty equiv` 作为最终输入。

### 6.3 B：单位数来自商环数与唯一极大理想的数

对任意 N≥1：

\[
 \#(O/m^N)=q^N,
 \qquad \#(m/m^N)=q^{N-1}.
\]

第一式不必从零重证。当前 Mathlib
`Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean:152`
已有 `cardQuot_pow_of_prime`：在 Dedekind domain 中，对非零素理想 P 给 `cardQuot(P^N)=cardQuot(P)^N`。应用到实际 DVR O 的 m，需要供应真实 DVR/Dedekind 实例、m 非零/素、有限 residue field；不能只把这些写成新的全局假设。

第二式可由乘 π 的同构 `O/m^(N−1) ≃ m/m^N` 得出，或用实际 quotient exact sequence 数出纤维。商环 O/m^N 是局部环，其非单位恰为 m/m^N，因此

\[
 \#(O/m^N)^\times=q^N-q^{N-1}=(q-1)q^{N-1}.
 \tag{B_C}
\]

代入 N=e_Ks，再与 (A_C) 连接：

\[
 \boxed{\#C=(q-1)q^{e_Ks-1}}.
\]

N≥1 必须保留；不能把 N=0 塞进带自然数截断减法的同一公式。

### 6.4 更短的备选：直接单位过滤计数，可把 A 从 #C 证明依赖中剪掉

若 actual `U_c` 的子群 API 比 quotient-ring units 好接，直接设

\[
 U_n=1+m^n\quad(n\ge1),\qquad U=O^\times.
\]

先由 reduction 证明 `U/U_1≃k^×`。对每个 n≥1，定义

\[
 U_n\longrightarrow(k,+),\qquad 1+\pi^n a\longmapsto\bar a.
\]

它是群同态：乘法中的交叉项 π^(2n)ab 属于 m^(n+1)，因为 2n≥n+1。满射由任意 residue 代表 a 给出 `1+π^n a`，这是实际单位；核恰为 U_(n+1)。所以

\[
 U_n/U_{n+1}\simeq(k,+),\qquad [U_n:U_{n+1}]=q.
\]

有限指数沿实际子群链相乘，得到

\[
 [U:U_N]=(q-1)q^{N-1}.
\]

由 `U_c=U_(e_Ks)` 得到同一个 #C 结论。这条路线不需要先完成整个 `(O/m^N)^×` 等价 API；若下游只消费 #C，可以直接构造既有 `LogShellQFECardinalityHypothesis` 的计数字段。

已有商环等价文件保留给其他消费者，但不要强制让 #C 的闭合依赖一个对象配错的中间接口。q=p^f 的实际 residue-degree 字典仍需接现有真实 f；不能改成 residue-one。

### 6.5 本次状态

A 的数学构造、B 的计数证明和直接过滤路线均已写清；Lean 的实际实例/同态/商 API 实现仍由现有 #C owner 完成。本 chat 不编译，也没有创建第二套计数源码。

先前交接的数学式 `(q−1)q^(es−1)` 使用 e=v_K(p)，该数学式保留。本次更正的是后来接口把这个 e 再作用到 `p^s` 上，导致实际理想发生变化；不能把数学式的 e 与任意额外幂混为一谈。

## 7. 具体推进顺序、复用边界与交接验收

### 7.1 当前最值得先做的一包

**reading owner：固定一个实际原 packet，交出同源 q 的单向 norm 读数公式，以及一个实际 theta 子格进入目标 hull 的生成证书。** 同时写出该 packet 的完整 `raw = degree·normalized + reference log mass` 公式。

这一包应能明确回答：原 qReading 是否已由同一个 q witness 得到？参考格是哪一个？目标 hull 接受哪一个实际子格？所用 degree 和 constant 是多少？若答案仍是一个自由 hlock/G2/G3，则没有交付这包的核心。

局部完成后再按原索引汇总；不先试图填一张局部=全局的总字典。

历史交接已经定位旧 C3 carrier 的问题，本包不重复该审计，也不安排旧结构的 inhabitant 任务。源对象构造沿已选的忠实 core/L/native 实现推进；若冻结的旧 reading 类型仍引用不适用的旧结构，其源语义与类型迁移须单列审查，不能用空类型消去或悄悄改定义充当原文消费者完成。

### 7.2 五项缺口对应的最小实际动作

| 缺口 | 建议动作 | 可以停止重复的工作 | 尚未消掉的责任 |
|---|---|---|---|
| 原 3.12 reading | 同源局部单向比较 + 实际子格进入 hull + 精确测度校准 | 再写 `of_identifications` 或仅 paper sums 包装 | P/source inhabitant、源区域识别、原 target 语义 |
| IV 1.10 | 从实际条件导出 l≠5；hCor312 后直接吸收 | 独立外部 logQ/slack 估计 | actual display terms、实际 hCor312 |
| Ind1/Ind2 | full source arrow 的 fixed-points→torsion→D_r；D-only 另补 reconstruction | σ=1/self bridge、重复 log/perfection 后半段 | 一般允许箭头的实际 realization/覆盖 |
| object lock | 用真实塔公式及有限指数体积关系，保留 raw 常数 | 强求整数 B、unitMass=1、任意 sign 等式 | 实际 source generator transport 与测度预算 |
| #C | 同余层固定为 1+p^sO，直接数 m^(e_Ks) | 证明错误配对的 A；仅修高次商环 B | 实际 DVR/群商 API 的实现与验证 |

这些是对已有 owner 的建议，没有新派发任务。现有状态记录中 mainline、qpilot、hull、stepxi 等 lane 的归属不变。

### 7.3 本次复用调查的范围

本次只核对用户列出的近端消费者、它们的必要供体、本地论文 Thm 1.10 和相关既有交接；没有重新全仓审查，也不声称读过仓库全部定理。

已有内容不重复安排：qhat Haar 缩放及 root q 范数供体；actual root-hull 包含；norm-ratio≥1；S1915 乘积质量公式；StepV hull 上界及两种平均；Ind1 单位 log/perfection 后半段；Mathlib prime ideal 幂的 quotient-cardinality。

本轮发现现有 `Mzk1IVThm110LogQActual` 已开始承接吸收计算、`Mzk1ActualReadingTargetActual` 已写 G2/G3 条件桥、`Mzk1IutIVTruncatedUnitsCardCorrectedActual` 已登记一般幂指数。都应沿原 owner 接着推进，不重新创建同义文件。

### 7.4 验收事实

- `statement_compiles`：NOT_RUN。
- `proof_body_checked`：NOT_RUN。
- `kernel_closed`：NOT_RUN。
- `target_accepted`：NOT_RUN。
- 本报告的数学计算/构造：单人自然语言自审，非独立审查；实际 source 未完成的步骤已经单列。
- 最终 target comparator、传递公理检查、实际版本构建：遵用户要求均未运行。

本次减少的是明确的证明负担：原文 l=5 分支、额外 logQ/slack 输入、q-side correction-zero 强条件、错误的高次同余商接口，以及 full multiplicative source 存在时额外的单位保持假设。原 3.12 和 IV 1.10 的 source-to-reading 主链仍须按上述实际对象构造完成，不能以这份路线文档代替证明。
