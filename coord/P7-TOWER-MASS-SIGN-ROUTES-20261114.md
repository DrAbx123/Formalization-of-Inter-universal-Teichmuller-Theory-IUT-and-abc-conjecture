# Tower、unitMass、theta sign：同源域塔与相对体积的消缺路线

日期：2026-11-14。Owner：当前 chat / root，单线程。

本包只做数学路线、必要源码与本地原文核对；不修改 Lean，不编译，不派发其他线程。目标是消除源端的额外 lock 输入，保持原文目标；不把新接口或条件定理记成完成。

实际消费者：`PaperS3137ObjectLock` / `RelativeFactorTowerData`、`Mzk1P0LNormComparisonConditionalActual`、`LPaper312Statement`，以及最终 q reading ≤ theta hull reading 的同源连接。阶段为 SHEAF 1；源码版本见 `dag/nodes/p7-tower-mass-sign-routes-20261114.json`。

## 0. 建议：把三个 lock 字段换成可推导的三个连接

| 旧要求 | 建议真正证明的连接 | 为什么能推进 |
|---|---|---|
| `d_L=B*n`、`B:Nat` | 实际 completion 塔及 `m*d_L=n_0*d_0`，体积消费者保留正有理比例 | 不再为额外的整数整除条件造对象 |
| `actualUnitMassL = productUnitMass` | 同一个区域/参考格对的相对 Haar 体积；必要的参考格差用实际指数计算 | Haar 比例可抵消，不要求两个独立 Haar 选择相等 |
| `thetaNormReadL = -thetaNormReadProduct` | 同源、同权重的 signed 读数运输；需要下界时只证同向单边比较 | 负号只在明确的 magnitude/dual 操作中出现，不能从名字或符号补出来 |

本次新增的具体发现有五项：

1. **当前所谓 true tower 仍混用了两个基域。** `rootBaseQpDegree` 用 F 的 completion；`localCompletionDegree` 用 K/Fmod。必须显式保留中间 F/Fmod 的局部次数。
2. **独立选 place 的前半段可以修。** 原输入已有 F/Fmod Galois 性；Mathlib 已有上方素理想的 Galois 传递性。因此能先构造 F-completion → K-completion，关闭相对次数整除的数学责任；根下降是另一项。
3. **归一化 Haar 运输已有真正供体。** `NormalizedHaarTransport.relative_log_mass_image_eq` 已经消掉未知 Haar 比例，不应重做一套 unitMass=1 理论。
4. **原文 `−|log(Θ)|` 不是可直接翻译成 Lean `-abs` 的表达式。** Cor.3.12 证明开头允许该 signed quantity 非负，再把非平凡分支限制到负值。
5. **当前 L-region 与满格须分清。** 它定义为纯张量的像；已有 `tensorLogShellLattice` 才是整数张成的满格。这关系到体积正性及原文 hull 的对象语义，不能只靠改 sign/mass 消去。

以上给出实际修改方向，不声称三个原 lock 已有 inhabitant。特别是对原目标引用的区域、测度或归一化作修改，须连同目标做语义复核；本文没有实施这种修改。

## 1. 先固定一个源，区分五个容易混用的对象

所有构造必须来自同一个原文合格初始数据。当前函数允许独立的 `I`、`place`、`T` 作为参数；类型本身不保证它们是同一个算术 packet。最终应由实际 source constructor 同时生成这些输入，并证明各投影相容，不能给任意独立 I/T 追加一个读取相等假设。

固定 bad moduli place v，记：

\[
F_0=(F_{\rm mod})_v,\quad F_1=F_u,\quad K_1=K_w,
\quad L_b=F_1(\alpha),\quad \alpha^{N}=q,\quad N=2l.
\]

还要区分 tensor carrier A：

\[
A=\bigotimes_{\mathbf Q_p,i}K_i.
\]

项目名中的“L carrier”指 `SourcePilotRegionDataL` 及其 tensor block，并不意味着 A 等于根域 `L_b`。`C3LogShellTensorBlockL` 当前仍由 **Fmod 的 completions** 构成；`rootNormedExtension` 则从 F 的 completion 加根。

维数、测度、符号的比较都必须先经过这张对象图；相同的 “L / Actual / theta” 名称不能提供同一性。

## 2. Tower 第一段：已有 Galois 性可以解决独立 place 的 completion 嵌入

### 2.1 当前代码究竟给了什么

`VbadPlaceIndexingActual` 中：

- `nativeBadToFPlace T b` 是在 F 中独立选取的 u；
- `nativeBadToKPlace T b` 是在 K 中独立选取的 w；
- 两者各自 comap 到同一个 Fmod-place v；尚未给 `w|F=u`。

但 `InitialThetaArithmeticData` 已有

\[
F_{\rm mod}\subset F\subset K,
\qquad F/F_{\rm mod}\text{ 有限 Galois},\quad K/F\text{ 有限 Galois}.
\]

这比“两个 place 只在同一个 p 上”强得多，可以利用。

### 2.2 具体构造，不要求两个 Classical.choose 相等

令 `u'=w|F`。因为 u、u' 均在 v 上方，选

\[
\sigma\in\operatorname{Gal}(F/F_{\rm mod})
\]

使它把 u 搬到 u'。已有 Mathlib 供体：

`.lake/packages/mathlib/Mathlib/NumberTheory/RamificationInertia/Galois.lean`

中的 `exists_smul_eq_of_isGaloisGroup`，L127；其精确条件是有限群在整数环上的 `IsGaloisGroup` 作用及两个 primes 的 lies-over。应实例化到整数环与当前有限 Galois 扩张，不能只从名字直接调用。

这个 σ 保持对应的 place valuation，经 completion 的延拓性质得到

\[
\widehat\sigma:F_u\xrightarrow\sim F_{u'}.
\]

再接实际 completion inclusion：

\[
F_u\xrightarrow{\widehat\sigma}F_{u'}\longrightarrow K_w.
\]

操作步骤：先在稠密的 F 上证明 σ 把 u 的绝对值送到 u' 的绝对值；由 uniform continuity 延拓；对 σ⁻¹ 做相反延拓；在稠密子域上验证复合恒等。最后运输到 `NormalizedCompletion / CommonPrimeCompletion` 的 Qp 模型。

由此得到真实有限域塔及

\[
[K_w:\mathbf Q_p]=[K_w:F_u]_{\widehat\sigma}\,[F_u:\mathbf Q_p].
\]

因此 `RelativeFactorTowerData` 的数值整除要求有一条实际证明路径，**不需要先得到根 α**。其 B 应是这条实际嵌入下的 `[K_w:F_u]`，而不是现有 `localCompletionDegree=[K_w:F_0]`。

本段不自动证明 q 的 transport：σ 运输了域与 place，还须核实实际 Tate parameter 随之如何运输。这一点放在下面的 source 对齐中处理，不能用“norm 相同”替代根方程相容。

### 2.3 对原文指定 place，优先直接复用 source section

`S1444ReportAKPlaceQActual` 已有：

- `sectionFPlace`、`sectionKPlace`；
- `sectionKPlace_comap` 与 `sectionKPlace_comap_fmod`；
- `sectionFQ`、`sectionQ` 及 `sectionQ_q`；
- 原 clause-(b) Tate comparison 的 section-place 实例。

它已经选择 `u=w|F`，能直接构造 F₀→F₁→K₁。真正的 paper packet 应先沿这一指定 section 构造，不要新选一套地方再要求它们定义相等。

现有 S1915 product 使用另一组 choices 时，有两种诚实处理：证明 choice transport，或先在指定 section 上做同一构造再证明它的数值/索引读数与旧 product 相同。后者至少须证明实际 q 的范数及权重相容；不能假定所有独立选出的 Tate witnesses 本身相等。

### 2.4 q 的 choice transport 也有具体证明：从同一个 j 恢复参数

这里不必停在一个新的 `q_compatible` 字段。原 `SourceClauseA.field_of_moduli` 给实际 `SourceFieldOfModuli.jModuli∈Fmod`，并证明它映到曲线的 j-invariant。因此同一 moduli place v 上，所有 completion 中的 j 都来自同一个 `j₀∈F₀`。

对实际收缩 Tate 参数 x，q-series 给

\[
j(x)=x^{-1}+h(x),\quad h\in\mathbf Z[[X]],\qquad
f(x):=1/j(x)=x+x^2g(x),\quad g\in\mathbf Z[[X]].
\]

这提供两个层次的连接：

1. **只要 scalar log-volume 时**，`|x|<1` 使 `x⁻¹` 严格支配其余整系数项，故 `|j(x)|=|x|⁻¹`。于是 `log|q_u|=-log|j₀|`，与上方 place、Tate witness 的 choice 无关。
2. **要实际 root embedding 时**，证明 f 在开单位盘单射。若 `|x|,|y|≤r<1`，整系数展开给 `f(x)-f(y)=(x-y)(1+ε)` 且 `|ε|≤r<1`，故 `|f(x)-f(y)|=|x-y|`。再在 F₀ 内用 `x↦j₀⁻¹-x²g(x)` 的压缩映射，在半径 `|j₀⁻¹|<1` 的闭球上构造唯一解 q₀。它在所有上方 completion 中仍满足同一方程，故每个实际 Tate 参数都等于 q₀ 的像。

这样 §2.2 的 completion 嵌入固定 F₀，必把 native q 送到目标 K-place 的实际 q。之后 §3 的根下降可以用于原 `rootNormedExtension`，无需更换预选根或假定独立 choices 相等。

需要实现的解析叶子很明确：实际 Tate j 的整系数 Laurent 展开、收敛半径、上述差商估计与压缩映射。它们不依赖 3.12 或 root-in-K 结论。已有 `TateJInvariantNorm.lean` 的直接 norm 定理在已读部分只覆盖 canonical prime-label 参数；不能把它误算成任意局部域/任意收缩 q 的完整供体。若只做加权体积字典，第一层 norm 证明已经足够；完整域嵌入才使用第二层唯一性。

## 3. Tower 第二段：如何把根域 L_b 实际放进 K₁

### 3.1 先明确已有的、还缺的

`S2223TateBridgeActual` 已接 `S1550` 的 K-side Tate point comparison；它自己说明，缺的是 torsion class 在 completion 中的代表/下降，而非完全没有 Tate comparison。

`S1647/S1660/S1668` 已有 section-place、根在代数闭包存在、valuation 分解及条件 root 组合，不应再重做这些代数包装。应补的核心是如下 Galois 固定性证明，并将所需**代数闭包层的等变 Tate 商**接到已存在的 comparison。只有 K₁-rational points 上的比较，还不足以直接消费下面的 α。

### 3.2 原合格 torsion 数据给 E[N] 的局部有理性

原输入的 `torsion23_rational` 给 E[2] 的有理性；`kernel_field_identification` 与实际 l-torsion representation 给 E[l] 在 K 上有理。

因为 l 为奇数，取整数 a,b 满足 `a*l+2*b=1`。对 `P∈E[2l]`：

\[
P=a(lP)+b(2P),\qquad lP\in E[2],\quad 2P\in E[l].
\]

故 E[N] 全部在 K 上有理。再沿 K→K₁ 和实际 torsion 的 base-change/局部 Galois 限制得到 `G_{K₁}` 在 E[N] 上作用平凡。这是必须落地的运输定理，不能把 torsion basis 当成自动完成了该运输。

### 3.3 固定性证明：用范数消掉 q^Z 的歧义

在同一局部代数闭包 Ω 内取 `α^N=q`。等变 Tate uniformization 将其类 `[α]∈Ω^×/q^Z` 送到 E[N]。

对任意 `g∈G_{K₁}`，上述 torsion 有理性给 `g[α]=[α]`，于是有整数 k：

\[
g(\alpha)/\alpha=q^k.
\]

局部 Galois 作用保持绝对值，故左边范数为 1；又 `0<|q|<1`，所以 `|q|^k=1` 迫使 `k=0`。因此每个 g 都固定 α，固定域定理给

\[
\alpha\in K_1.
\]

这个论证对 **每一个** N 次根成立，故也解决任意预选 root 的根单位歧义。无需另加“单位部分是 N 次幂”的假设；其可除性是完整 torsion 条件的结论。

若现有 uniformization 只有 completion-rational points 的商描述，应补“实际代数闭包上 E[N] 的 Tate torsion 描述及 Galois 等变性”。只在所有有限 torsion 层证明所需部分即可，不必为本任务先完成所有 C_p 解析点的理论。

### 3.4 从根下降到当前 rootNormedExtension 的嵌入

先固定 `F₁→K₁` 及同一个 q。把 `AlgebraicClosure F₁` 嵌入 Ω，延拓基域映射；当前选定的 `rootNormedElement` 被送到 Ω 中一个 N 次根，§3.3 证明其像在 K₁。

由 adjoin 的泛性质限制出

\[
\iota_b:L_b=F_1(\alpha)\hookrightarrow K_1.
\]

这比“在 K₁ 找到任意一个 N 次根就直接给 adjoin hom”更严谨：`X^N-q` 可能可约，任意两根不一定有同一最小多项式；通过共同代数闭包及全根固定性避免这一缺口。

在统一的 Qp 绝对值模型上，该有限局部域嵌入为等距。不要将这句话用于原始 adic norm 而漏掉归一化幂：`sectionQ_norm` 自身有 `completionNormDegree` 因子，应先运输到共同 `|p|=p^{-1}` 的模型。

然后令 `m_b=finrank L_b K₁`，有限性由 K₁/Qp 有限及上述中间域得到，正性由域非平凡和有限维得到。m 不再是自由 Nat 字段。

## 4. 正确的 degree 公式与 B 的替代

记全部来自实际塔的次数：

\[
\begin{aligned}
d_0&=[F_0:\mathbf Q_p],& c&=[F_1:F_0],& d_1&=c d_0,\\
t&=[K_1:F_1],& n_0&=[K_1:F_0]=tc,& d_K&=n_0d_0,\\
r&=[L_b:F_1],& d_L&=r d_1,& m&=[K_1:L_b].
\end{aligned}
\]

从实际两条塔逐次用 finrank 乘法，得到

\[
t=mr,\qquad
\boxed{m d_L=t d_1=n_0d_0.}
\tag{T}
\]

与当前代码的映射是：

- `rootBaseQpDegree = d₁`；
- `localCompletionDegree = n₀`；
- `s1915LocalDegree = d_L`；
- `kPlaceQpDegree = d_K`。

所以当前 `TrueTowerDataSource` 将 `dF_eq=rootBaseQpDegree` 与 `n_eq=localCompletionDegree` 组合成 `m*dL=n*dF`，**尚不是正确的原对象塔式**：右侧需要 d₀，或把 n 改成 t。这个问题应在写 inhabitant 前纠正。

`relativeFactorTowerData_of_tower` 若用 `kPlaceQpDegree=n₀*rootBaseQpDegree`，也混入同一个 c 因子；正确是 `d_K=t*d₁`，所以该接口中的整数 B=t。

另一个 legacy lock 的条件是 `d_L=B*n₀`。与 (T) 合用只得到

\[
B=d_0/m.
\]

没有理由把这个正有理数预设为 Nat。若坚持旧 lock，要额外证 `m|d₀`；这不是域塔自动给的条件。建议移除中间消费者对这一 Nat B 的依赖，直接使用 (T) 及正有理比例。

具体要消费的等式不是 B 本身，而是：对 `λ∈L_b^×`，令

\[
V_L(\lambda)=\log\frac{\mu_L(\lambda O_L)}{\mu_L(O_L)}
=d_L\log|\lambda|,
\]

\[
V_K(\iota\lambda)=d_K\log|\lambda|=mV_L(\lambda).
\]

于是原文的 K/Fmod 权重给

\[
\boxed{\frac1{n_0}V_K(\iota\lambda)
=\frac{m}{n_0}V_L(\lambda)
=\frac{d_0}{d_L}V_L(\lambda)
=d_0\log|\lambda|.}
\tag{W}
\]

这正是绕开旧整数 B、直接恢复原权重的可用公式。注意此处比较的是 `λ O_L` 与 **扩张理想** `ιλ O_K`；不是把低维集合 `ι(λO_L)` 用 K 的 Haar 测量。

## 5. unitMass：用区域与参考格一起运输，不追求两个质量相等

### 5.1 已有的通用供体已经足够

`LeanFormal/IUT/Foundations/LocalFields/NormalizedHaarTransport.lean` 中的

`relative_log_mass_image_eq`

证明：实际拓扑加法群同构 e 与两侧 Haar μ、ν 下，只要 S、C 有正有限质量，

\[
\log\nu(eS)-\log\nu(eC)=\log\mu(S)-\log\mu(C).
\tag{H}
\]

Haar uniqueness 的未知比例同时出现在分子、分母，严格抵消。**它不要求保测，也不要求 μ(C)=ν(eC)=1。**

应做的是实例化实际 e 和同一个参考格 C；不要再新建 `unitMass_eq` 结构让调用者填写。不同维数之间不存在这种群同构时，使用 (W) 的理想扩张公式，不能假装 e 存在。

### 5.2 先用真正的 tensor field-product 分解

已有 `Mzk1P3TensorCoreActual.tensorCore_fieldProduct` 给实际 tensor

\[
e:A\simeq_{\mathbf Q_p}\prod_\tau E_\tau.
\]

有限维给连续性及连续逆，进而可消费 (H)。这里的 `E_τ` 是实际 tensor 的场因子，**不能把它们直接指定成 S1915 的 root fields**。

取一个实际参考格 C，例如 tensor 整数格、tensor log-shell 格，或 `e⁻¹(∏O_{Eτ})`。把区域与 C 一起送到 product，比较相对体积。若 e(C) 不是 product unit ball，则保留它；下一段再精确计算参考格更换。

`Mzk1DetHaarDegreeFactorActual` 只有自由 `detB:Real` 与比例数据，不是已算出的实际 determinant。不能把这一结构的 inhabitant 当成上面 e 的体积计算。

### 5.3 当前单位球与算术参考格的差，化成有限指数

当前 `actualUnitBallL={x:‖x‖≤1}` 来自 `finitePadicTensorCoordinates` 拉回的坐标范数。它是一个实际坐标 Zp 格 U；不自动等于 tensor 整数格，也不自动对应 `∏O_E`。

设 C、U 都为同一 A 内的满 Zp 格，令 `J=C∩U`。它们紧开，因此两个指数有限。由有限个平移不交的分解：

\[
\mu(C)=[C:J]\mu(J),\qquad
\mu(U)=[U:J]\mu(J).
\]

从而

\[
\boxed{\kappa(C,U):=\log\mu(C)-\log\mu(U)
=\log[C:J]-\log[U:J].}
\tag{K}
\]

该值与 Haar 的倍数选择无关。用 U 的基表示 C，若 `C=M U`，则也可写为

\[
\kappa(C,U)=\log|\det M|_p=-v_p(\det M)\log p.
\]

这给出具体执行办法：用 actual integral/log-shell bases 构造 M；由格的包含与有限商求指数，或用 Smith 指数求和。不要只定义“未知 κ”再把符号估计当条件交给最终消费者。

`Mzk1P3HaarScaleFactorLogActual` 可处理 raw Haar 常数的日志项；(K) 更适合当前参考格之间的精确校准，不需要先补齐任意场同构的 determinant API。

### 5.4 tensor 与 root product 的真正连接是 determinant 乘法

令 `dim K_i=d_i`、`D=∏_i d_i`，在每个 factor 中有满格 `C_i` 与实际线性同构 `f_i`，记 `J_i=f_i(C_i)`。取 tensor 格 `C=⊗C_i`、`J=⊗J_i`，则

\[
\det(\otimes_i f_i)=\prod_i\det(f_i)^{D/d_i},
\]

因此

\[
\boxed{\frac1D V_A(J;C)=\sum_i\frac1{d_i}V_{K_i}(J_i;C_i).}
\tag{Tensor}
\]

当 `f_i` 是乘 `λ_i` 时，右侧是 `Σ_i log|λ_i|`。根域侧先用 (W) 或按维数归一化的 scalar 公式，就可以把这些数值送入正确 tensor bookkeeping，而不要求 root product 与 A 等维。

`thetaNormReadProduct=Σ_b d_{L,b}log r_b` 已经是带 degree 的**原始 product 和**。不能不经系数转换就把它当成 `(Tensor)` 的右侧。已有 `productNormalizedLogPerDim_weighted` 可复用，但它的 dimension 权重也必须与原文 place/procession 权重逐项对齐。

原文的 j、`j+1` tensor factor 数、地方纤维和 procession average 均须保留。尤其 S1915 已取最大半径的读数不能自动恢复 `λ_{b,j}=α_b^{j²}` 的完整 j 平均。补回这些索引是源消费的一部分，不是任意重加权。

## 6. 一个必须在应用 Haar 比值前处理的实际区域问题

`Mzk1C3LogShellTensorLActual.actualC3LogShellTensorRegionL` 调用的

`tensorIntegralRegion S = tprod '' (∏ S_i)`

是**纯张量像**，不是它的整数张成。该文件目前证明 compactness，没有因此证明正 Haar 质量；Qp-span 为整个空间也不意味着原集合有正测度。

在至少两个维数大于 1 的 factor 上，纯张量满足矩阵 flattening 的 2×2 minors 全为零，落在真代数子集，不能用满维 Haar 格体积公式计算。当前 concrete tensor 使用多个重复 completion factor，因此这不是只有抽象泛化才可能遇到的问题；本包不将某个特例的零测度断言标为已形式化。

**可复用的修复对象已经有了：**

- `FinitePadicIntegralTensorLattice.tensorLogShellLattice`；
- `tensorLogShellRegion_subset_lattice`；
- `isCompact_tensorLogShellLattice`；
- `isOpen_tensorLogShellLattice`；
- 更一般的 `FinitePadicSubmoduleTensor.submoduleTensorSpan` 及 basis/map/open 定理。

因此正确推进是：从原文实际允许的 theta image 生成这些格，证明它们进入原 holomorphic hull，再在有正体积的格/hull 上做 (H)–(Tensor)。已有 `Mzk1BoxReadoutLocalActual.PacketHullData` 与 `packetHull` 可作为相应 hull 消费入口，不能把另一个球或格直接宣布为原 hull。

还要注意，当前 L-region 的定义没有用 theta 根值；roots/thetaPacket 字段存在于 record 中，不等于区域已经消费它们。必须给出真正的 scalar/action/possible-image 连接。

若锁定 target 正好引用旧 pure-tensor region，本包不擅自换定义，也不利用 `Real.log 0=0` 去得到形式上轻易的比较。应提交原文 hull 与其区域定义的语义修订，并连同 target 重审。这一项只定位必要修复，不重开整仓审计。

## 7. theta sign：原文已经说明应该保留 signed 读数

### 7.1 原文的精确方向

本地 IUT III 文本 L10324–10415，Cor.3.12，把 `−|log(Θ)|` 定义为某个 procession-normalized log-volume，并允许其属于 `R∪{+∞}`。紧接着的证明说明：若它非负，则目标已成立；因此只需研究负的分支。

这说明不能把该记号定义成一个自动非正的 Lean `-abs`。安全的命名是独立 signed 数 `S_Theta`，并保留

\[
S_q\le S_\Theta.
\]

根 product 侧已经有

\[
S_{\rm prod}=\sum_b d_{L,b}\log r_b.
\]

它也是 signed 数。源区域、参考格、维数与权重对齐后，同向运输得到的是同号关系，必要时带明确 κ/degree 因子；不会凭空生成负号。

### 7.2 当前负号 lock 应如何退出主线

不要再尝试从 raw log-volume 推出

`thetaNormReadL = -thetaNormReadProduct`。

优先给真正的中间读数 `R_Theta`：由 (W)、(Tensor)、(K) 及原文权重显式计算的 signed 数。然后证明

\[
R_q\le R_\Theta\le S_\Theta
\]

或实际对象确实相等时证明 `R_Theta=S_Theta`。右侧单边方向来自**构造的源合法子格包含于同一个原文 hull**，不是自由 `hbound`。

这一路线不要求先把整个 root product 与整个 L-region 认成同一个对象。旧 positive-sign `hlock` 也不能直接宣称成立；它仍缺对象/权重校准。

若非平凡分支已证明 `S_Theta<0`，可以定义 magnitude `M_Theta=-S_Theta=|S_Theta|`。此时

\[
S_q\le S_\Theta\iff M_\Theta\le M_q
\]

（q 侧亦取对应 magnitude）。负号出现在 signed↔magnitude 的转换处，两边和不等号方向一起处理。不能只翻 theta 一边的符号。

### 7.3 只有真实 duality 才能在两个体积之间产生负号

若某一原文 source 运输确实指向对偶格，可用 trace-dual 解释负号。对非退化 trace pairing，令 C^∨ 为 C 的对偶。若 `Λ=gC`，则

\[
\Lambda^\vee=g^{-t}C^\vee,
\qquad V(\Lambda^\vee;C^\vee)=-V(\Lambda;C).
\]

局部域中 `O_L^∨=different^{-1}`，因此改用同一个 O_L 作两侧参考时还要保留 different 项。

这是一条可用的严格负号机制，但目前没有发现当前 `thetaNormReadL` 定义含有这个 dual 操作。不能为了让旧 lock 可填而人为给 theta 对象加对偶；主线仍建议采用 §7.2 的 signed 运输。

## 8. 根下降暂时未落地时，怎样用共同扩张继续做体积

这是备选推进法，不把它算成 `L_b→K₁` 已构造。

从同一个实际 `q∈K₁` 出发，在其代数闭包中取 α，定义有限扩张 `E=K₁(α)`。如果还要保留已给的 L_b，则先把共同基域及 L_b、K₁ 嵌入同一代数闭包，取复合域 E；这些嵌入必须尊重同一个 q。

令 `a=[E:L_b]`、`s=[E:K₁]`，则真实公式为

\[
a d_L=s d_K.
\]

principal fractional ideal 的按维数相对 log-volume 在扩张中不变：

\[
\frac1{d_L}V_L(\lambda O_L;O_L)
=\frac1{d_E}V_E(\lambda O_E;O_E)
=\log|\lambda|.
\]

若需要把实际区域降到 K₁，取**逆像格**

\[
J=K_1\cap\lambda O_E.
\]

写 `v_E(λ)=h`、`e=e(E/K₁)`，则

\[
J=\pi_{K_1}^{\lceil h/e\rceil}O_{K_1},
\]

\[
\frac1{d_K}V_K(J;O_K)
=\log|\lambda|-\delta,\qquad
\delta=\left(\lceil h/e\rceil-h/e\right)\frac{\log p}{e_{K_1}},
\]

\[
0\le\delta<\frac{\log p}{e_{K_1}}.
\]

这就是可计算的取整损失，已有 A1/C0 contracted-lattice 路线可以复用。若 `λ=α`、`α^N=q` 且 `|α|<1`，可证明 `qO_K⊆J`；但对 `λ=α^{j²}`，不能不检查指数就照搬该包含。procession 的大 j 可能改变方向，必须保留真实 exponent 与 hull 的允许操作。

用此路线进入最终不等式时，所有 δ 要按真实 degree、factor、place 和 j 权重累计。只有从实际生成元/格指数计算出足够余量才能吸收；不能把“余量大于损失”定义成新的假设然后称已消缺。

此路线的价值是：构造共同对象和计算测度可以先推进；如果 §3 的根下降成功，则 α 已在 K₁、对应取整损失为零，回到精确运输路线。

## 9. 回到原 raw target：必须带回的完整等式

设 A 的维数为 D，U 是当前代码的单位球，C 是实际算术参考格，μ 是当前 raw Haar。定义 `s(H;C)=V(H;C)/D`，则

\[
\boxed{\log\mu(H)=D\,s(H;C)+\kappa(C,U)+\log\mu(U).}
\tag{Raw}
\]

所以若原锁定 target 是 `qReadActual≤log μ(H)`，就必须证明同源构造的下界满足

\[
qReadActual\le D\,s_{\rm lower}+\kappa(C,U)+\log\mu(U).
\]

这是一张精确的计算清单，不是建议新增一个自由 budget 假设。D、κ、原 q reading 的维数/参考格解释及 μ(U) 的归一化来源都要实际给出。

Mathlib `Haar/Basic.lean` L577–581 明确把 `addHaar` 定义为对任意 `PositiveCompacts` 选择的 Haar。仅从 `IsAddHaarMeasure` 推不出指定 U 的质量等于 1，或 `log μ(U)≥0`。

原文 comparison 应在同一标准与归一化下读 q 和 theta。正确消费是先从该原文标准证明 q 的同一参考格/维数读数，再使用同一 affine 转换：若 `Q_raw=D Q_norm+c` 且 `Theta_raw=D Theta_norm+c`，D>0，则归一化不等式等价于 raw 不等式。

但当前 q reading 是 `log‖q‖`，而 theta 是独立 raw Haar log。不能在没有这两条实际字典的情况下声称常数已抵消。若当前 raw 定义缺了原文标准，此处需要目标定义的语义修订及验收；本文不偷偷把它换成 normalized target。

## 10. 最小执行顺序：哪些是真新增，哪些不再重做

| 顺序 | 实际产出 | 复用内容 | 尚须证明的部分 |
|---|---|---|---|
| 1 | 同一源的 F₀→F₁→K₁，实际 c,t,n₀ | ArithmeticData Galois tower；S1444 section；Mathlib prime transitivity；field_of_moduli 的 j₀ | completion 延拓；§2.4 的 inverse-j 唯一性或较弱 norm 连接 |
| 2 | actual α∈K₁、`L_b→K₁`、m | clauseC torsion；S1550/S2223 Tate comparison；既有根方程 | 局部 torsion 有理性、代数闭包 torsion 商的等变性、固定域下降 |
| 3 | `m*dL=n₀*d₀` 及 (W) | finrank tower、S1915 scalar Haar formula | 精确 carrier/tower 实例；不再要求 Nat B=d₀/m |
| 4 | 同一个 source 的格/hull 与参考格对 | tensorLogShellLattice、submoduleTensorSpan、PacketHullData | theta scalar/action 到该 hull 的实际生成元连接；不是纯张量集合替代 |
| 5 | 相对 log-volume 与 κ | NormalizedHaarTransport、P3 product/average、Haar log factor | actual basis/index、地方和 procession 权重 |
| 6 | signed 同向比较及原 raw 字典 | 已有 root-side signed 计算；原文 3.12 的方向 | 同源 q reading、最终区域语义与 (Raw) 校准 |

前 1、3 的次数工作可在根下降前先完成与 F₀/F₁/K₁ 有关的部分。第 4 的满格与第 5 的参考格计算也不需要等待根下降的所有实现。用户当前只要求思路，本 chat 不启动这些证明任务或构建。

### 不应再新增的任务

- 从头证明两 Haar 归一化比值不变：已有 `relative_log_mass_image_eq`。
- 重新定义 section K-place 与 q base-change：已有 S1444。
- 再写一个 `m/dF/unitMass/sign` 自由字段结构：并未减少源端责任。
- 强求两个 tensor/root carriers 同构或同维：使用实际场分解、(W)、(Tensor)。
- 为旧负号 lock 寻找符号技巧：先按原文 signed 读数修正中间消费者。

## 11. 状态、历史更正与一个具体下一步

本包最先建议做的具体动作是：**把当前 degree 字典按 d₀、d₁、c、t、n₀ 分开，并由 Galois-place transport 或已有 section 构造 F-completion → K-completion。** 这一步可以明确产出实际 B=t 的 `RelativeFactorTowerData` 来源，且不会被根下降阻塞。随后沿 §3 构造 root embedding/m。

此前报告 §3 的“真实塔公式”在把 d_F 定义为 Fmod 的 completion degree 时成立；当前 `Mzk1ObjectLockDataActual` 把它实例为 `rootBaseQpDegree` 后漏了 F/Fmod 因子，不能直接复用该实例。本文保留历史而补正准确范围。

此前“负号需要 magnitude convention”应进一步精确为：原文 `−|log(Θ)|` 本身只是 signed quantity 的命名；只有在已经限制到负值分支后，才可以把其相反数当非负 magnitude。原文并不提供当前两个 signed readouts 互为相反数的定理。

四项验收 `statement_compiles / proof_body_checked / kernel_closed / target_accepted` 全为 **NOT_RUN**。本轮只有源码、定义、原文与自然语言证明的单人复核；没有独立审查，没有新 green 声明。source torsion/tower 实例、原 hull 生成元连接及最终 raw 校准仍未机器闭合，不能把文档交付视作 3.12 已证明。
