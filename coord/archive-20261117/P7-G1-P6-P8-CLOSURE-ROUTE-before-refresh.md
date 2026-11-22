# G1／P6／P8：面向无条件 ABC 的实际构造路线图

日期：2026-11-16。节点：p7-g1-p6-p8-closure-route-20261116。负责人：当前 chat，单线程。

本文件接续已接受的 P1、P4、P5、P7、H1a/H1b 和 P6/P8 消费者，重新安排剩余 producer。接受状态按本次用户给定范围保留；以下只核对新连接所需的定义，不重新审计这些节点。本文替代上一版路线的 G1/P6/P8 收口部分，旧文保留为历史。

**推荐主线：两个仿射图构造真实 Fermat 曲线 → 显式微分得到典范线丛 → 原文的“多点归一到一个普通值”构造实际 noncritical map → 有限族映射与局部紧性给统一受控区域 → P5 下界与独立局部解析上界夹逼推出 hCor312，再经 P6 推出局部高度上界 → 实际 different/height 运输 → P8 producer → 已有 ABC 等价。**

最终定理不接受 hCor312、FreyHeightBound、Nonempty P8Producer、自由高度比较或 source compatibility 作为附加输入。文中待实现的节点都是要从实际对象证明的责任，不是最终定理的新假设。单线程、只用本地源码和原文；本轮不编译，不修改 Lean。

## 1. 目标、依赖与本次查重的实质修正

最终仍是现有 ABCFreyJProductHeightCriterion：

\[
\forall\varepsilon>0\ \exists B_\varepsilon\ \forall(a,b,c)\text{ primitive},\
a+b=c:\quad
h(j(E_{a,b}))\le6(1+\varepsilon)\log\operatorname{rad}(abc)+B_\varepsilon.
\tag{F}
\]

B_ε 必须在三元组之前确定。最后应用已有
ABCEllipticHeightCriterion.abcConjecture_iff_freyJProductHeightCriterion；
不另起一个与 ABC 等强的 producer 接口充当证明。

本次有以下会改变工作量或方向的查重结果：

| 核对项 | 当前源码实况 | 路线处理 |
|---|---|---|
| closed subscheme API | 本地 Mathlib 已有 Scheme.IdealSheafData.subscheme、subschemeι；ClosedImmersion 文件已有对应实例 | 旧“frozen API 不存在”的注释不能直接作为当前缺失结论。缺 Fermat 理想层实例及其图，不是整个一般 API |
| 实际 affine Fermat | Mzk1G1FermatAffineSchemeActual 已构造 Spec(AdjoinRoot)，monic 给 Module.Finite，导数公式已有 | 从这张图扩展第二张图并粘合，不从 Set 点集继续包装 |
| 所谓 all-compact criterion | Mzk1G1AllCompactActual 实为 x²/(m+2) 在 ℚ 的紧集上一致趋零 | 这个已证辅助结论不是原文的高度紧性入口。P8 改用下文的实际局部高度 criterion |
| S2953 certificate | 结构同时要求 hupper 和 hCTheta，即“上界成立”及“上界系数恰等于实际体积比”；lower-bound consumer 实际只消费 hupper 等字段 | 主线直接证明同读数上界再夹逼，不要求不必要的最优等号 |
| P6 A/B 最新供体 | Mzk1P6PhiActionFamilyActual、Mzk1P6PhiActionSourceActual 已给保格族及非空性；Mzk1P6RootParameterWeightActual 已给根关系推出赋值公式 | 不重证 family／ord 代数；补实际 source arrow 入该族与实际根数据实例 |
| Prop 1.6 最新供体 | Section2.lean:409 已有 iutIVProp16_primeCounting_le_four_thirds_eventually，且 θ 双侧估计已有 | 直接复用，不再新派 PNT 或 Chebyshev 证明；旧文件头 machine-gap 是历史状态 |
| G1 新 chart-ring 供体 | Mzk1G1FermatChartRingActual2 的两个环分别是 xⁿ=λ、yⁿ=1−λ 的单根扩张及其基 | 复用它们的 tensor/iterated-root basis；它们不是已经粘好的两张 projective charts |

另有两个明确的对象区别：

- Mzk1G1NoncriticalMapActual.noncriticalMap_exists 的有限集 S 被送入 {0,1}，它是 Belyification 的 branch-set 输入，**不是**“protected set 被避开”的证明。
- homogeneous quotient 是仿射锥的坐标环；其 Ω 模不是 projective curve 的 Ω。光滑曲线的 Ω_Y/ℚ 秩为 1；n−3 是典范线丛 O_Y(n−3) 的 twist，不是微分模的秩。

已定位的可复用底层路径：

- .lake/packages/mathlib/Mathlib/AlgebraicGeometry/Gluing.lean：Scheme.GlueData.glued、OpenCover.glueMorphisms。
- 同目录 IdealSheaf/Basic.lean、IdealSheaf/Subscheme.lean、Morphisms/ClosedImmersion.lean。
- 同目录 Morphisms/Finite.lean：IsFinite.SpecMap_iff；Morphisms/Proper.lean：有限映射为 proper。
- 同目录 Morphisms/Smooth.lean 与 RingTheory/Smooth/StandardSmooth.lean。
- RingTheory/Kaehler/Polynomial.lean、JacobiZariski.lean：真实商环的微分计算。
- tmp/sheaf/xif/paper/AG_FLT_ProvedTheoremsPromotionActual.lean：已有带精确实例条件的 Serre/Weil/Čech 供体；实际 Fermat 实例仍需构造，不能只 import 后当已实例化。
- Mzk1BoxConstantAuditActual、S2715CThetaPaperScaleActual、S3171IUTIVSection1DisplayActual：系数、正性、hCor312→display 的末端代数复用。

数学依赖分成两条，最后汇合：

\[
\begin{array}{c}
\text{accepted P4/P5/P7}
\to\text{同源读数识别＋不依赖 hCor312 的实际 hull 上界}
\to hCor312\to\text{受控区域上的高度不等式};\\[2mm]
Y_n,\pi,\omega_Y,\text{实际 noncritical maps}
\to\text{统一局部区域＋height/different 运输}.
\end{array}
\]

两条同时完成后才产生 (F)。P6 的 R≤Box 本身不直接推出 ABC。

## 2. G1-A：用两个仿射图构造实际 Y_n 与 π

固定整数 n≥4。先在 k=ℚ 上做，涉及几何点时一起 base change 到代数闭包；不改变对象。

### 2.1 两张图及实际商环

取

\[
A_0=k[x,y]/(x^n+y^n-1),\qquad
A_\infty=k[r,s]/(1+s^n-r^n).
\]

令 U₀=Spec A₀、U∞=Spec A∞。第一张图直接复用现有 AdjoinRoot 呈现：
A₀=k[x][y]/(yⁿ+xⁿ−1)。第二张图同样取 AdjoinRoot。用商环的普遍性质证明这两套呈现与多元 quotient 相同，不另外选择一个任意 Scheme。

在 D(x)⊂U₀、D(r)⊂U∞ 上定义

\[
r=x^{-1},\quad s=y/x;\qquad
x=r^{-1},\quad y=s/r.
\tag{A1}
\]

逐项代入关系验证 ring hom；乘法和逆元关系给两边互逆。只有两个图，cocycle 退化为 identity/inverse 的有限检查。调用 Scheme.GlueData.glued 得到真正的 scheme Y_n。

与 projective 方程的关系也实际证明：U₀ 对应 [x:y:1]，U∞ 对应 [1:s:r]。若 X=Z=0，方程迫使 Y=0，故 D(X)∪D(Z) 覆盖 Fermat hypersurface。这解释为什么两张图足够。

### 2.2 实际映射到 ℙ¹

目标 ℙ¹ 使用已有两张标准 affine charts，坐标 λ、t，重叠 t=λ⁻¹。定义

\[
\lambda=x^n\quad\text{on }U_0,\qquad
t=r^n\quad\text{on }U_\infty.
\tag{A2}
\]

由 A1，重叠上 rⁿ=x⁻ⁿ，所以两个 Spec.map 相容。用 glueMorphisms 得到

\[
\pi:Y_n\longrightarrow\mathbb P^1,\qquad
[X:Y:Z]\longmapsto[X^n:Z^n].
\]

必须证明 π⁻¹(A¹_λ)=U₀、π⁻¹(A¹_t)=U∞；这由 t、λ 的可逆 locus 与 A1 计算，不能只给两个局部公式而略去目标图的原像。

### 2.3 finite、degree n² 与 proper

在 λ 图上把 A₀ 改写为

\[
k[\lambda][x,y]/(x^n-\lambda,\ y^n-(1-\lambda)).
\]

先添 monic 根 x，再添 monic 根 y。最新 Mzk1G1FermatChartRingActual2 已给这两个单根环及 power bases：在同一 k[λ] 上取二者 tensor product，或把第二个 monic polynomial base change 到第一个环，再添根。商环普遍性质识别所得环为 A₀。把已有 power bases 作 tensor product，得到明确自由基

\[
\{x^iy^j:0\le i,j<n\}.
\]

基的构造复用现有供体；只补 natDegree=n 及上述实际 ring equivalence 的运输，不重写 monic/power-basis 证明。于是 Module.Free 与 rank=n² 是真实环上的定理。∞ 图同理，基为 r^i s^j。局部基经 A1 运输，这也给有限局部自由的相容图。

IsFinite.SpecMap_iff 将 module finiteness 变成局部 finite morphism；finite 对目标 Zariski 局部，故 π finite。其 generic rank=n² 即 deg π=n²，不再定义一个数值 degree 然后 rfl。

已有“finite ⇒ proper”及 ℙ¹→Spec k proper，复合得到 Y_n proper。这一证明不必等待一般 homogeneous quotient 的 Proj functor。

### 2.4 smooth、维数及几何连通性

A₀ 的关系 F=xⁿ+yⁿ−1，偏导为 n x^{n−1}、n y^{n−1}，且

\[
xF_x+yF_y=n.
\]

n 在 ℚ 中可逆，故两偏导生成单位理想。D(x)、D(y) 覆盖 A₀；在 D(y) 上相对 k[x] 的 monic 方程 yⁿ+xⁿ−1 的导数是单位，给 standard étale，再复合 A¹_k→Spec k 的 smooth；D(x) 对称。∞ 图同样用 n r^{n−1}、n s^{n−1}，给 SmoothOfRelativeDimension 1。这里只补实际 ring presentation 到现有 smooth API 的实例。

几何整性可直接证明：在 k̄[y][x] 中，xⁿ+(yⁿ−1) 对素元 y−1 满足 Eisenstein，因为 yⁿ−1 在 y=1 处是简单零点。故不可约、A₀⊗k̄ 为整环。∞ 图与其有非空稠密重叠，Y_n⊗k̄ 整，因而几何连通。

**本包出口：**Y_n:Scheme、π、实际 finite rank n²、SmoothOfRelativeDimension 1、IsProper、geometrically integral。出口不出现 MissingFermatClosedSubschemeAPI 之类的未构造输入。

## 3. G1-B：用显式微分得到典范线丛，剪去一般 RH 前置

### 3.1 真正的绝对微分与过渡函数

在 A₀ 上，商环微分呈现为

\[
\Omega_{A_0/k}
=(A_0\,dx\oplus A_0\,dy)/
 (n x^{n-1}dx+n y^{n-1}dy).
\]

在 y≠0 的开集取

\[
\omega_0=\frac{dx}{n y^{n-1}},
\]

在 x≠0 的开集用等价表达式 −dy/(n x^{n−1})。关系保证它们粘合，且各自是 Ω 的基。∞ 图取

\[
\omega_\infty=-\frac{dr}{n s^{n-1}},
\]

s=0 时用 ds 的对应表达式延拓。由 r=x⁻¹、s=y/x，

\[
\omega_\infty=x^{n-3}\omega_0.
\tag{A3}
\]

这正是 O_Y(n−3) 在 X/Z 两图上的过渡函数。因此从局部 rank-one module 的实际等价与 cocycle 构造

\[
\boxed{\Omega^1_{Y_n/k}\simeq O_{Y_n}(n-3).}
\tag{A4}
\]

这里仅需微分的局部化、商环关系和 rank-one module 粘合；不需要先形式化任意曲线的 adjunction theorem。

### 3.2 分歧与 log-canonical 恒等式

在 λ=0 上，x 是实际 uniformizer，λ=xⁿ；在 λ=1 上，y 是 uniformizer，1−λ=yⁿ；∞ 图在 r=0 上有 t=rⁿ。其余处局部导数非零。因此 π 的三个 boundary fibers 都有 ramification index n。

令 E=(π⁻¹{0,1,∞})red。E 是 XYZ 在 Y 上的 reduced divisor；每条坐标线与曲线相交于 n 个不同几何点，故

\[
O_Y(E)\simeq O_Y(3),\qquad \pi^*O_{\mathbb P^1}(1)\simeq O_Y(n).
\]

结合 A4 得到实际线丛同构

\[
\boxed{\omega_Y(E)\simeq\pi^*\omega_{\mathbb P^1}(0+1+\infty).}
\tag{A5}
\]

若消费者需要 RH 形式，局部 dλ=n x^{n−1}dx 给
div(dπ)=(n−1)E，从而 K_Y=π* K_P¹+(n−1)E。它是实际 differential 的 divisor 等式，而非把 genus 定义成某个数字后验证等式。

deg O_Y(1)=n 可由 Z=0 的 n 个简单交点证明，于是 deg K_Y=n(n−3)。只有消费者确实需要 genus 时，再用实际 H¹ 或 RR 得 g=(n−1)(n−2)/2；当前高度主线只消费 A4、A5，可以不等 genus 的独立接口。

### 3.3 三种 different 不混用

后续需要区分：

1. Ω_Y/k：秩 1 的绝对微分，定义 canonical line；
2. Ω_Y/ℙ¹：支撑在分歧点的 torsion sheaf；
3. O_L/O_K 的 arithmetic different：控制点域判别式。

三者有相容关系，但不相等。对有限可分曲线映射，在完备局部参数 t=u^e a(u) 中计算 dt/du，其阶 e−1（特征零、a(0)≠0）；算术不同则由 trace-dual/DVR different 定义。后面逐处分别调用，禁止用锥的 Ω 模代替其中任何一个。

### 3.4 主线以外的两个真实构造备用

两图粘合是推荐实现。若其当前接口运输成本过高，另外两路与它采用不同的对象构造机制：

- **理想层路线。** 在 ℙ² 的标准图上分别用 F/X_iⁿ 生成 principal ideal；重叠上二生成元相差可逆的 n 次幂，故理想相同。把这些理想沿 affine refinements 粘成 IdealSheafData，调用 subscheme、subschemeι 及已有 closed-immersion instance。proper 由闭浸入和 ambient proper 得到。它直接构造真实 equation ideal sheaf，不从 closed subset 随意选一个 subscheme。只有确有消费者要求 Proj quotient 呈现时，才另外证明它与 Proj(k[X,Y,Z]/(F)) 的标准图相同。
- **函数域 normalization 路线。** 构造有限可分扩张 k(λ)(x,y)，xⁿ=λ、yⁿ=1−λ；对 k[λ]、k[t] 分别取 integral closure，利用 localization 与 integral closure 交换在重叠上粘合。有限性由一变量有限可分扩张的 integral-closure finiteness 证明，regular local dimension 1 给 DVR，特征零上 regular curve 给 smooth。现有 Normalization.lean 可复用其粘合和普遍性，但它的 integral morphism 不能未经 finite-generation 证明就宣称 finite。最后用 A₀/A∞ 已证明的 normality 识别两模型，运输实际 π 与微分。

三路均产出同一原文所需曲线；不用把三路一起实现，也不安排整仓 AG 基础重建。



## 4. G1-C：实际 noncritical scheme morphism，按原文先把多点变成一个值

这里采用本地原文 Noncritical Belyi Maps，Theorem 2.5 的构造。它比“为每个受保护点分别安排一个多项式条件”短，而且能直接接现有 finite-beta 供体。

输入是上面真正构造的 Y=Y_n，以及互不相交的有限几何点集 S、T；在 ℚ 上使用时取 Galois-stable 集合。输出是实际非恒定 scheme morphism φ:Y→ℙ¹，满足：

\[
\operatorname{Branch}(\phi)\subset\{0,1,\infty\},\quad
\phi(S)\subset\{0,1,\infty\},\quad
\phi(T)\cap\{0,1,\infty\}=\varnothing.
\tag{B1}
\]

“noncritical”不能只用多项式存在性命名替代 B1。

### 4.1 用两个实际截面构造第一段 ψ

在 T 中加入额外点，避开 S，使 reduced divisor
D_T=∑_{t∈T}[t] 满足 deg D_T≥deg K_Y+3。加入整个 Galois orbit，保持在 ℚ 上定义。可从 π 的无限多个普通有理值的 fibers 选点；避开有限禁集，故这个扩大过程有具体来源。

令 L=O_Y(D_T)，s₀ 为其 canonical section，零除子正是 D_T。对每个几何点 x，

\[
\deg(K_Y-D_T+x)\le-2.
\]

负次数线丛没有非零截面：非零截面给 effective 零除子，其 degree 非负，与负 degree 矛盾。实际 Serre 对偶给 H¹(L(−x))=0，短正合列给几何点处 evaluation 满射。因此全局截面空间中，“在 x 消失”的部分是真子空间。

在 ℚ 上下降时要注意一个细节：若 x 是高次数闭点，不能未经检查就声称 H¹(L(−x))=0。这里先在代数闭包逐个几何点证明，再用 H⁰ 的域扩张相容性，得到在每个闭点的 evaluation **不是零映射**。其核是 ℚ 上真线性子空间；不需要它满射到整个高次数 residue field。

有限多个真子空间不能覆盖有限维 ℚ 向量空间。选 s₁，使 s₁ 在 D_T 的每一点都非零。于是：

- D_T 外 s₀ 非零；
- D_T 上 s₁ 非零；
- (s₀,s₁) 没有共同零点。

在 s₁≠0 的开集用函数 s₀/s₁，在 s₀≠0 的开集用 s₁/s₀；在重叠上互为倒数，粘成实际

\[
\psi=[s_0:s_1]:Y\to\mathbb P^1.
\]

它满足 ψ*O(1)≃L。由于 s₀ 的零点全是简单零点，

\[
\psi^{-1}(0)=D_T,\qquad \psi\text{ 在整个 }0\text{ 纤维上无分歧}.
\tag{B2}
\]

这比只在原 T 上导数非零更强，正好保证下一步的 branch-value 集不含 0。非恒定来自 deg L>0；proper 曲线间非恒定映射有限，可用函数域有限扩张与 affine integral closure 证明，或复用现有有限性判据。

### 4.2 第一段的 RR／Serre 输入怎样从实际 Y 产生

已有 AG_FLT_ProvedTheoremsPromotionActual 能复用证明体，但它的 HasCanonicalDivisor、DCoordGenerates、ResidueTheorem、ConstantsAreBase 等不是自动实例。按以下顺序实例化：

1. **函数域与点。** F=Frac(A₀)。由 smooth dimension 1 得闭点局部环为 DVR。把闭点的 ord 映成 ported Place；反向用 properness 延拓 Spec F 的点到 valuation ring。由 separatedness 得唯一性，建立两套 divisor 的实际等价。
2. **微分坐标。** 用 A4 的 ω₀。每个 DVR 取 uniformizer u，把局部微分写 a(u)du，证明 Ω 在相应局部化上由 du 生成。这填 DCoordGenerates；ω₀ 的局部阶给 canonical divisor，与 A4 同一。
3. **局部 residue。** 在等特征零的完备局部域中取 Laurent 展开，定义 res(∑a_i u^i du)=a_{−1}，再施 residue-field trace。变量替换用形式求导和 Laurent 系数验证，与 uniformizer 无关。
4. **全局 residue theorem。** 沿 π 将微分 trace 到 ℚ(λ)，证明 local trace-residue 相容；ℙ¹ 上用 partial fractions，有限极点 residue 与 ∞ 的系数相消。把所有点按 π 的 fiber 分组，得到 Y 上的 residue 和为零。这个证明不使用高度或 ABC。
5. **constants 与 principal degree。** 几何整性、properness 及 Y 的有理点给常数域正是 ℚ。主除子 degree=0 可沿函数域 norm 归约到 ℙ¹ 的分子、分母次数计算。
6. **ported Čech 与真实截面。** 对每个 D，证明 LSpace(D) 正是满足所有 ord_P(f)+D(P)≥0 的函数，因 DVR 正则性识别为 H⁰(Y,O(D))。Čech differential 在两边均是重叠上的相减；给出 chain isomorphism，再运输 H¹ 与 Serre pairing。不能只有两个空间的 finrank 相等。
7. **若使用 genusReached 版本。** 在真实 plane model 上用
   0→O_{\mathbb P²}(m−n)→O_{\mathbb P²}(m)→i_*O_Y(m)→0。
   标准 affine cover 的 Laurent monomial Čech 计算给 m≥n−2 时 H¹(Y,O_Y(m))=0；同时给 Hilbert 函数差。将一个具体大 m 的 divisor 运输到 ported RiemannGenusReachedAt，而不是把该字段作为假设传下去。

这里 2–5 是实际数学实例，6 是两套 API 的对接。若直接用已构造的 Serre pairing bijectivity 得到所需 evaluation，便不必为了名字齐全先完成全部一般 RR API。优先证明 B2 所需的 evaluation 引理。

### 4.3 代数点到有理点：补的不是普通 Belyi existence

设 S₁=ψ(S)∪Branch(ψ)。由 B2，0∉S₁。问题成为：找实际 h:ℙ¹→ℙ¹，把 S₁ 和自身 branch values 送到 {0,1,∞}，同时 h(0) 避开这三点。

这里复用 Mzk1Consumer24AdapterUnconditionalActual.finiteBetaCorrectedBase_proved 的范围是：S₁ 已经有理，protected β 是有限有理值。它尚不承担一般代数 S₁ 的降阶。

一般部分按原文 Lemma 2.4 做，具体递归如下：

1. S₁ 取 Galois closure。以
   (最大 reduced degree，达到最大 degree 的点的 reduced-degree 总和)
   作 lexicographic 自然数度量。
2. 取最大次数 d₀ 的 α₀。选一个有理 Möbius pole 靠近当前 β、避开 S₁，再乘有理常数，使所有有限 α∈S₁ 满足 |α|≤1，而 |β| 足够大。有限集到 β 的正距离给这个选择的具体界。
3. 取 α₀ 的 monic minpoly f₀。其所有 conjugates 都在单位圆盘，系数由 elementary symmetric sums 估计；例如 |a_i|≤binomial(d₀,i) 已足够。
4. 导数根由 Cauchy root bound 有显式半径 R(d₀)；因此 f₀(S₁) 和 f₀(roots f₀') 的有限值均有只依赖 d₀ 的界 B(d₀)。把前一步 |β| 取得使 |f₀(β)|>B(d₀)。
5. 新禁集必须取 **critical values**：
   S₂=f₀(S₁)∪f₀(roots f₀')∪{∞}；最后一项覆盖 polynomial 在 ∞ 的分歧，且不改变最大非有理次数。不是只加入导数根。
   β₂=f₀(β) 不在 S₂。α₀ 的整个 orbit 映到 0；新 critical values 的 degree≤d₀−1。其他点 degree 不增，因此 lexicographic 度量严格下降。
6. 保留每一步实际有理函数及其 scheme morphism，证明 branch composition 公式。终止时用已有 rational finite-beta fold，然后反向复合。

这样原文的下降量有了每步 producer；已有 well-founded/measure 辅助定理继续复用。

### 4.4 从 rational function 到 scheme morphism 的固定实现

对 h=P/Q∈ℚ(t)，先约去 gcd。齐次化到同一 degree d，得 Pʰ(U,V)、Qʰ(U,V)。证明它们没有共同 projective 零点：有限图由 Bézout identity，∞ 图由最高次数及约分条件。于是两个 quotient functions 给实际 morphism ℙ¹→ℙ¹。

微分与分歧用 P'Q−PQ' 和 ∞ 图 t=1/z 的局部公式；有限可分 char 0 保证导数不恒零。链式法则证明 branch(h∘ψ)⊂branch(h)∪h(branch ψ)。

最后 φ=h∘ψ 满足 B1，且

\[
\phi^*O(1)\simeq L^{\otimes d},\qquad
\omega_Y(E_\phi)\simeq\phi^*\omega_{\mathbb P^1}(0+1+\infty),
\quad E_\phi=(\phi^{-1}\{0,1,\infty\})_{\rm red}.
\tag{B3}
\]

第二个等式由每一点的 dt/du 阶数计算；branch values 全在三点中，故边界以外没有 ramification 修正。这是后面高度相消的真正来源。

**本包出口：**B1–B3 的实际 scheme morphism、pullback 和 divisor 定理。已有 polynomial theorem 是其中一段供体，不再让它单独承担整个 G1 §13.2。


## 5. P6 的非循环主线：独立上界先行，最终 display 后用

### 5.1 首先把两个不同的“P6”拆开

用户指出的循环风险确实必须排除。以下是两个不同节点：

- **P6-pre：**实际 theta hull 的解析上界。只使用实际源作用、局部域格、different、单位对数体积、阿基米德容器、素数估计和加权平均。
- **P6-final：**把 hCor312 代入已证末端代数，推出最终 logQ/display 上界。

本路线的方向是：

\[
\begin{array}{ccccc}
\text{P5 实际下界}&\searrow&&&\\
&&hCor312&\longrightarrow&\text{P6-final}\\
\text{P6-pre 独立上界}&\nearrow&&&
\end{array}
\tag{C0}
\]

P6DisplayChainActual.p6Chain_display 明确接受 hCor312；HCor312SupplyFromP5Actual 明确接受 S2953 certificate。二者都不能拿来证明 P6-pre，也不能先用它们的结论再回填 hCor312。

已核对的上游供体：
LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean:814，
arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound。
其可见证明体按 endpoint inclusion → hull minimality → 正测度 → normalized-volume bound 推进，没有调用 hCor312 或最终 logQ bound。它接受的 e、ϖ、Φ、保格性、exceptional set 等必须在实际数据上构造。本轮未运行传递依赖的 kernel 检查，不把这次源码追踪报告成该项检查已完成。

### 5.2 独立上界怎样在 actual packet 上产生

以真实索引 a=(p,j,tuple,distinguished-slot) 组织 packet；p 不固定为一个全局素数。每个 packet 做以下工作：

1. **真正的 tensor 分解。** 分解的是实际 base completions 的有限 étale ℚ_p-algebra。通过 separable polynomial factorization 和 Chinese remainder 得各 field factor E_ν，再构造实际 AlgEquiv e。不要把 q-root extension product 冒充它的 field factors。
2. **ϖ 的来源。** 直接复用 Mzk1P6RootParameterWeightActual.rootParameterWeight_eq_ord_varpi。新增工作是给 DistinguishedScalarData 的实际实例：在源允许的 split Tate completion 中，用实际 E[2l]-点和 Tate uniformization 取 value-group 类为 1/(2l) 的代表 α；α^(2l)=q 先由商群关系得到相差 q 的整数幂，再调整代表得到。其 K_v-有理性由 Galois 对代表的差落在 q^ℤ、连续 cocycle 到离散 ℤ 必为零来证明。以 α^(j²) 绑定真实 ϖ，随后调用供体得到
   ord_p(ϖ)=j²/(2l)·ord_p(q_v)。
   用具体单位因子的赋值零消掉选择依赖；无需把根扩张与 base tensor 强行设为等价。
3. **作用族的来源。** 直接取已有 p6Phi，即所有保 unit-log lattice 的 ℚ_p-linear equivalences；phiActionSourceData 已给其非空性。这个较大的族足以作 upper 容器，不需要另证它恰等于源箭头族。真正要新增的是：从每个允许 source arrow 构造实际 linear realization，并由单位层交换图、log square 与格保存证明其属于 p6Phi。任意源箭头有覆盖代表，故没有漏掉 possible images。既不重做已有 A，也不以 {id} 代替 source coverage。
4. **实际源像入容器。** 对一个任意允许 source image 展开其 unit/log/Kummer 坐标。先进入 ϖ·O_hol，再施对应 φ，故落在 arithmeticTupleStepVPossibleImages；Ind3 如由包含表达，就证明包含而不索取不必要的等价。
5. **局部 upper。** 调用已证 donor，得到
   \[
   V_a\le
   \bigl(-\operatorname{ord}_p(\varpi)
       +\sum_i\operatorname{ord}_p(\delta_i)+1\bigr)\log p
   +\sum_{i\in I^*}(3+\log e_i).
   \tag{C1}
   \]
   exceptional set 直接定义为实际 e_i>p−2 的 indices，故 small_outside 是判定式推论；随后另行估计它的加权成本。
6. **运输和平均。** 按 StepVDistinguishedSlotAverage、StepVProcessionAverage、StepVDivisorAverage 的真实权重求和。place 次数、tensor dimension、distinguished 概率与 procession 归一化逐一列明。先证明 weights 非负且总和正确，再应用平均；不能为凑系数自由选择 weights。

这些步骤不需要最终 hCor312。C1 中的负 q 项来自实际 ϖ 的赋值；删掉这个负项会直接破坏后面的夹逼系数。

### 5.3 真正需要攻的桥：P5 读数与这个容器必须是同一对象的读数

现有 PaperKummerReading 的 qReading_log 读取
log(D.vol {qPilotInThetaCarrier T})。
这里 D.vol 不是自动等于局部域 Haar。正维局部域的 Haar 单点质量为零，不能直接把该 singleton 当成 Haar region。

本次推荐的精确出口是下面两个**从实际对象证明**的关系：

\[
q_{\rm P5}=-M,\qquad
\theta_{\rm P5}\le H_{\rm pkt}:=\sum_a w_a V_a,
\quad M=Q/(2l).
\tag{C2}
\]

theta 一侧有 ≤ 已足够，不必强求所有 carrier 的等价或体积等号。若已有真实同对象读数，则 C2 可加强为等号。q 一侧则必须核对根参数、global sum 与 degree normalization；原来的单 place C3 reading 不能无声明地改成 global sum。

对于这处尚需实际验证的运输，给出三条不同机制。它们的共同验收是 C2；不把 C2 作为新字段传给最终定理。

#### J1：直接实现为实际区域，再用包含和 Haar 单调性——首选

对每个 source pilot，使用它已经给定的实际局部 Kummer 元素构造主格或有限生成 integral span；source 中的“一个 pilot”实现为这整个区域，而不是实现为 Haar 单点。

- q 区域取实际 root-pilot 主格。对 Kummer relation r^{2l}=q，先在有限根扩张 L 中证明 normalized log-mass
  \[
  \frac{1}{[L:\mathbb Q_p]}\log
  \frac{\mu_L(rO_L)}{\mu_L(O_L)}
  =\log|r|_p=\frac1{2l}\log|q|_p .
  \]
  此处 |·|_p 是延拓自 |p|_p=p^{-1} 的绝对值。若 source 的 q 标记存的是 q_b 本体而非 r_b，先证明原文的 Kummer-root 区域是 {x:|x|_p^{2l}≤|q_b|_p}=r_b O_L；同一个 root-region 解释也必须用于 theta 端。不能只把 q 读数除以 2l 而保留另一端原定义。用 P4 的实际 divisor/weight 字典加权，得到 −M。它是各局部主格的体积恒等式，不要求存在一个人为 global field element q。
- theta 区域取实际 source images 的 integral span／holomorphic hull。源生成元在 hull 内，O-action 保持目标区域，因此从 source q membership 推出整个 q 主格包含于 theta 区域；单点包含本身还不够，O-saturation 这步要写出来。
- 对每个 theta 生成元，按 C1 前的来源计算进入对应 packet 容器，证明整个 theta 区域被实际 packet hull 控制。需要 product 结构时，从真实 field decomposition 的 integral closure 识别 O_hol，而不从任意 tensor norm 的 isometry 猜出来。
- 使用相对 log-volume
  log μ(S)−log μ(O_ref)。Haar 重标度在差中消去；若参考格不同，保留明确的 index/different correction，归入 C1 已有项。
- 证明这个实现与现有 q/theta reading 的定义相符。若现有 strict-volume 包装索取额外严格性，而本目标只需 ≤，直接从真实格包含证明非严格下界；保留已有 strict theorem 的适用范围，不制造严格体积差来填字段。

**最先可交付的数学对象：**一个真实 packet 上的 q 主格、theta 源生成元的 O-span，以及“source action→实际 linear action→区域包含”的交换图。先做符号恒等式，再推广索引；不先增加一个空的 GlobalSumAggregation 结构。

#### J2：改用 determinant line 和有限指数比较——绕开不同维 carrier 等价

这里比较的是实际格的 determinant norm，而不是整个 field algebra。

- 在各 p 上，给实际源格、tensor 格选真实 ℤ_p-bases。只为计算而选基，最终用 det 的基变换公式消去选择。
- 用源生成元的坐标写具体矩阵。方阵用 determinant，嵌入／商映射用 maximal minors 与有限 cokernel；指数由 Smith normal form 得到。
- 根扩张、base tensor 因子可分别进入有限 normal compositum 的各 embedding 分量；不能把一个 product algebra 嵌入单一 field。基扩张的次数变化通过 determinant-line norm 或 restriction of scalars 计算。
- 有理权重先清分母，在 determinant line 的 tensor powers 上比较，再除回公共倍数。复制的是确定的 weighted determinant 数据，不是宣称两个原 carrier 同型。
- 分别计算三类修正：scalar extension 的 degree；整基与 maximal order 的 different/index；q-root 的 1/(2l) 赋值。后两类必须与 C1 的 different 和负 q 项逐项对应。
- 由所得实际矩阵证明 θ-reading≤packet-reading+Δ。然后**计算 Δ**：若不同是参考格变化，配对消去；若是 trace-dual 的指数，纳入已存在的 different 预算；若是额外源作用，回到其 minors 估计，证明不超过已有余量。

这一路允许保留非零 det/degree 因子。若算出的 Δ 含未控制的正比例 Q 项，就继续证明该项的抵消／预算，不能把它叫常数。具体要算哪一个矩阵、哪些 minors 已在构造中明确，不以“存在保测同构”作终点。

#### J3：有限同余商计数——绕开先做完整 measure transport

先在实际 source 和 packet 两端各取紧开满格，及共同明确的上下格 C₋⊂Γ⊂C₊。寻找足够 N，使 p^N C₊⊂C₋。这个 N 由已有生成元／不同的赋值下界给出。

- 在 C₊/p^N C₊ 上把真实源作用降为有限模上的映射，证明 relation、Kummer 标记和 reduction 交换。
- 用真正的 kernel、image、cokernel 计数比较源区与容器；同余单位的 A/B 计数供体可以复用，但作用必须由实际箭头诱导。
- 对格 Γ，有
  \[
  \frac{\mu(\Gamma)}{\mu(C_+)}
    =\frac{\#(\Gamma/p^N C_+)}{\#(C_+/p^N C_+)}.
  \]
  对有限 coset union 同理。只要区域是此类紧开格／有限并，N 足够大后比值已经精确稳定，不必先攻一般极限测度理论。
- q 主格的 quotient 长度给 1/(2l) 的 normalized 赋值；theta→packet 的有限集合映射给大小不等式。逐 p 取 log，再清除权重分母并求和。
- 对需要闭包的区域，先证明它等于一个有限生成满格；若做不到，给出逐级一致上界和实际 cofinality，再用测度连续性。不能将任意一个有限集合的 card 定成目标数。

J1 的核心是几何区域包含，J2 是线丛／矩阵的 covolume，J3 是有限模的真实长度。这三路在最先要构造的对象、证明工具和失败信号上均不同，可避免一直卡在同一个 AlgEquiv 上。

### 5.4 精确夹逼：如何产生代码里的 hCor312

统一记号：

\[
Q=\text{实际未取根的全局 normalized q-divisor degree},\quad
M=\frac{Q}{2l},\quad
S_{\rm ar}=\log d_{F_{\rm tpd}}+\log f_{F_{\rm tpd}},
\]
\[
E_{\rm ar}=e^*l+\eta_{\rm prm},\quad
A=(1+12d_{\rm mod}/l)S_{\rm ar}+10E_{\rm ar},\quad
c_l=\frac16(1-12/l^2),\quad \kappa=\frac{l+1}{4}.
\]

原文 IV Thm 1.10 的 |log(q)| 是 M，不是 Q。P6-pre 要证明的上界是

\[
H_{\rm pkt}\le \kappa(A-c_lQ)-M.
\tag{C3}
\]

独立证明 C3 的具体来源：

1. C1 按真实权重求和，加入 Step (vi) 的例外素数部分和 Step (vii) 的 archimedean 容器；
2. 用实际 tower different 的 transitivity 与 Step (iii) 算术估计，把 d_i 项转成 S_ar；
3. 保留原文 Step (viii) 中间式
   \[
   H_{\rm pkt}\le\kappa\{(1+12d_{\rm mod}/l)S_{\rm ar}
       +2\log l+56-c_lQ
       +(20/3)l^*_{\rm mod}\log(s_{\le})\}-M;
   \]
4. 由实际 prime-count bound 得
   l*_{mod}log(s≤)≤(4/3)E_ar；
   由 e* 的真实定义及 l≥5 得 2log l+56≤(4/9)E_ar；
   两项合计≤(28/3)E_ar≤10E_ar，得到 C3。

**这一步不用新证 PNT。**交付前查重确认 Section2.lean 已有
iutIVProp16_primeCounting_le_four_thirds_eventually。其证明复用本文件
θ(x)≤(13/10)x+300 和 Mathlib 的 Abel 求和公式及积分余项小 o 估计，得到准确的 4/3 常数。选其阈值并增大到≥2，绑定本次全局 η_prm；这个选择在曲线之前固定。

令 x=e*l。x≥η_prm 时直接乘 log x>0；1≤x<η_prm 时，log x·π(x)≤log η_prm·π(η_prm)≤(4/3)η_prm。因此两分支给上述 (4/3)E_ar。新增工作仅是将实际 small-prime 集合的基数、log(s≤) 和 x 绑定到此已证计数定理。旧“显式 PNT 尚缺”的审计描述不能继续作为本包任务。

随后才用 P5：

\[
-M=q_{\rm P5}\le\theta_{\rm P5}\le H_{\rm pkt}
 \le\kappa(A-c_lQ)-M.
\]

加 M，除以 κ>0，得到 c_lQ≤A，即

\[
\boxed{Q/6\le A+(2/l^2)Q.}
\tag{C4}
\]

C4 正是 thm110Lhs≤thm110Mid+thm110Cor312Gap 的形状。到这里才填 hCor312，然后复用 S3171 的 slack 与最终 display。此前不使用任何以 C4 为前提的定理。

S2953 还要求 CThetaPaper=thetaLogVolume/M；upper bound 通常不足以证明这个等号。本路线不取这个额外要求。若要保留一个 certificate，字段应是实际 theta 值和已经证明的 upper，不是强制“上界恰好取到”；相关消费者必须一同按等强结论改接。

### 5.5 只为最终 ABC 时，可以先用较短的真实 Box 夹逼

若已经独立得到同一个 H 的真实 Step-V Box：

\[
-M\le H\le\frac{l+5}{4}D-\frac{l+1}{24}Q+S+(l+5)T,
\]

则立即有

\[
\frac{(l+4)(l-3)}{24l}Q
 \le\frac{l+5}{4}D+S+(l+5)T.
\]

因此 l≥7 时，

\[
\frac Q6\le
 \frac{l(l+5)}{(l+4)(l-3)}D+
 \frac{4l}{(l+4)(l-3)}S+
 \frac{4l(l+5)}{(l+4)(l-3)}T
 \le(1+7/l)D+(5/l)S+8T.
\tag{C5}
\]

这些系数可复用 Mzk1BoxConstantAuditActual。这个分支可先生产渐近高度不等式，避免为 ABC 先追求每个最优常数；它不冒充字面 C3。

注意 Mzk1P6IVActual.p6IVR 当前定义为 collectionBound 的平均，p6IVR_eq_paperBound 是这项表达式的恒等式。还要证明真实 H≤这个平均，才能代入上式。既有平均代数继续接受，不让这个表达式的名字承担未证明的 actual-hull 比较。


## 6. 从独立估计产生真正的局部高度 criterion

### 6.1 把 P8 中错误类型的紧性入口换成精确数学命题

对固定次数上界 d，以及在含 ∞、2 的有限 V 上远离 {0,1,∞} 的实际 compact domains K_V，证明

\[
\forall\eta>0\ \exists C_{d,K_V,\eta}\ \forall\lambda:
\quad [\mathbb Q(\lambda):\mathbb Q]\le d,\quad \lambda\in K_V
\Longrightarrow
h_{O(1)}(\lambda)
 \le(1+\eta)\{D(\mathbb Q(\lambda))+N_{\{0,1,\infty\}}(\lambda)\}+C_{d,K_V,\eta}.
\tag{D1}
\]

这里 D(K)=log|disc K|/[K:ℚ]，N 是 normalized truncated conductor；λ∈K_V 要对所有相关局部共轭成立。固定的高度／不同 convention 与原文逐项对齐。

D1 是这条路线要证明的中间定理，不是最终 theorem 的假设。它和 x²/(m+2) 的 uniform convergence 没有替代关系。

### 6.2 actual λ → actual Θ-data 的量词

从 λ 取真实 Legendre curve y²=x(x−1)(x−λ)。复用已经接受的 P7 initial-data 构造，但要把它实例化在这一条曲线上：

- moduli field、tripodal field、2·3·5 torsion field 与 √−1 extension 用实际 field compositum；
- q 参数是该曲线在实际乘法坏位的 Tate 参数；
- l 由实际 exclusion set 选择，不是输入一个满足最终不等式的 l；
- 大像／合法源数据使用已有 P7 的真实 producer；若某个导出仅对已给 T 叙述，λ→T 的这一次实例化不能省略。

保留两种 q-height：
h=Q_all 是全部 finite q-places 的 normalized degree；
Q 是进入当前 initial Θ-data 的选定位之和。先证明 Q≤h，再计算遗漏 h−Q，不能令 Q=h 来消掉问题。

原文 Cor 2.2 的素数选择可按已有路线的实际排除集合复用：排除小素数、整除指定局部整数赋值的素数、以及造成坏位冲突的素数。把 exclusion 的 log-prime 总量估计出来，复用 Section2.lean 中已有的 Chebyshev 下界及避素数供体，得到

\[
\sqrt h\le l\le C_d\sqrt h\log(2C_dh),
\qquad
0\le h-Q\le C_d\sqrt h\log(2C_dh)+C_{K_V}.
\tag{D2}
\]

C_d 只依赖固定 degree bound。有限／小 h 分支进入统一常数；不要求它也能产生同一大素数配置。已有 P7 的具体大像构造和例外高度界继续复用，不能把其例外点仅叫“有限”而不提供与 h 的界。

### 6.3 q-height 与通常高度的实际字典

在乘法坏位，Tate 展开给 −log|q_v|=log⁺|j_v|；potentially good 位 local j-height 为零。有限扩张后的局部 degree 权重按 Σef=[L:K] 运输，不能重复计算 extension degree。

在 K_V 的 archimedean 组件，j(λ) 是连续函数且分母不为零，故有固定上界。2-adic 处同理，自动满足原文 (*j-inv) 的有界条件。于是删去 2 与 arch contribution 造成的差有统一界，而非依赖当前 λ 的“常数”。

再用实际有理函数

\[
j(\lambda)=256\frac{(1-\lambda+\lambda^2)^3}{\lambda^2(1-\lambda)^2}.
\]

它在 ℙ¹ 上是 degree 6 的 morphism。齐次化后用 resultant/Bézout 控制局部共同小值：非阿基米德好位给精确 max 比较，有限坏位及复位给固定常数。求和得到 h(j)=6h(λ)+O(1)。因此

\[
h_{O(1)}(\lambda)=h/6+O_{K_V}(1).
\tag{D3}
\]

这里 O_{K_V}(1) 的见证从实际紧集和固定 rational map 产生。

### 6.4 独立 IV bound 到 D1 的误差吸收

把 §5 的上界用在上述 T。tripodal 字典必须给出原文 Cor 2.2 使用的关系：

- log-diff_X(λ)=log d_Ftpd；
- log f_Ftpd≤N_D(λ)；
- d_mod≤d，e* 被固定 degree 的函数控制。

这些关系由实际点域／tripodal field 识别和 conductor 的逐处定义证明；原文定义中的 finite field extension 不能只用同名字段作等式。

由 C4 后的 final display，或者 C5 的渐近分支，加上 D2，得到可操作的形式

\[
h/6\le(1+C_d/\sqrt h)\,
       \{D(\mathbb Q(\lambda))+N_D(\lambda)\}
       +C_d\sqrt h\log(2C_dh)+C_{K_V}.
\tag{D4}
\]

这里的 prime-count 常数直接用现有 Section2 供体。C_d 也可取更大的已证明上界；主系数仍趋于 1，不需要再优化这些绝对误差常数。

给定 η>0，先选 H₀，使 h≥H₀ 时 C_d/√h 足够小，且
C_d log(2C_dh)/√h≤η/[24(1+η)]。
这用 log x/x^{1/2}→0 的已知初等估计，可按幂比较给一个具体阈值。把 D4 中次线性误差移到左边，除以正系数，得到 D1。h<H₀ 时由 D3 直接 h(λ)≤H₀/6+C_K；加入同一个 C 即可，不需要先调用 Northcott 来穷举这些点。

**出口：**D1 的量词是 ∀d ∀K_V ∀η ∃C ∀λ；没有 hCor312、FreyHeightBound 或新的 arithmetic estimate 参数。D1 的证明依赖 §5 中尚待落地的实际上界运输，不把这里的代数吸收当作该运输已经完成。

## 7. G1-D：有限族映射与局部紧性，直接给统一常数

这一段可以比上一版“先取反例列，再为极限点选映射”更直接。它在同一条曲线 Y_n 上构造一个有限映射族，先把映射及常数固定，然后处理任意点。

### 7.1 只需 r+1 个彼此边界不交的 Belyi maps

固定 d=n²，固定 V={∞,2}；也可加入事先确定的 p|n。令 r=d·|V|。

递归构造 φ₁,…,φ_{r+1}:Y_n→ℙ¹，记
E_i=(φ_i⁻¹{0,1,∞})red。先任选 B1 给的一张图。构造下一张时，在 B1 中取 S=∅，T=∪_{k≤i}supp E_k。于是新 φ_{i+1} 在所有旧边界点避开 {0,1,∞}，所以

\[
E_i\cap E_j=\varnothing\quad(i\ne j).
\tag{E1}
\]

每个 T 都是有限 Galois-stable set，故所有 φ_i 可以在 ℚ 上构造。注意这里利用的是 Fermat cover 后的 **proper curve Y**；没有要求每张 φ_i 都把原来的同一个非空边界送入 {0,1,∞}，因此不存在“边界既固定又互不相交”的冲突。

### 7.2 把所有 bounded-degree 局部点放进固定局部域

对每个 p∈V_non，构造一个有限正规扩张 L_p/ℚ_p，包含所有 degree≤d 的 ℚ_p-extension 的嵌入像。所需的有限性可以这样内部证明：

1. 一个 degree≤d 扩张有 maximal unramified subextension，residue degree≤d；这些 unramified fields 由有限域及 Hensel lift 唯一构造。
2. 在该 unramified field 上，剩余全分歧扩张由 Eisenstein uniformizer 的 monic minimal polynomial产生。
3. different 由该多项式导数生成。导数各项的赋值按指数模 e 区分，得到 δ≤e−1+e·v_p(e)，因 e≤d 而统一有界。也可运输已有 LocalDifferentUpperBound 的实际有限扩张定理。
4. 导数是 conjugate differences 的乘积；所有差绝对值≤1，因此这个 bound 给 uniformizer 到其他 conjugates 的统一正分离下界。
5. 足够深的 coefficient congruence，经 Hensel 找到很近的根，再由 Krasner 的 conjugate separation 证明生成同一个 extension。证明 Krasner 所需的内容是：若一个嵌入固定近根却移动旧根，ultrametric triangle 与最近 conjugate 距离矛盾。
6. Eisenstein coefficients 模固定 p^N 只有有限多类，所以 extension types 有限。选代表并取它们的 normal closures 的 compositum，得到实际 L_p。

这里的 N 只依赖 p,d。没有把“存在所有点共享的局部域”留下作额外输入。∞ 处使用 ℂ。

### 7.3 正距离函数的最小值给统一受控区域

每个 Y_n(L_v) 紧致：用实际 plane model，ℙ²(L_v) 可由 normalized coordinate charts 的紧单位球覆盖，Y_n 是闭子集。定义

\[
\mathcal K=\prod_{v\in V}Y_n(L_v)^d.
\]

对于 ξ∈𝒦，给各位置取实际坐标点，定义

\[
\delta_i(\xi)=\min_{v,k}
 \operatorname{dist}_{\rm chordal}
       (\phi_i(\xi_{v,k}),\{0,1,\infty\}),\qquad
\delta(\xi)=\max_{1\le i\le r+1}\delta_i(\xi).
\]

实际 scheme morphism 的局部 rational formulas 保证这些函数连续。𝒦 的一个 tuple 至多有 r 个点；由 E1，每个点至多落入一个 E_i，所以至少一张 φ_i 避开全部点。于是 δ(ξ)>0。

紧性取最小值得到 **固定 δ₀>0**。对每个 v，令

\[
K_v=\{z\in\mathbb P^1(L_v):
       \operatorname{dist}_{\rm chordal}(z,\{0,1,\infty\})\ge\delta_0\}.
\tag{E2}
\]

K_v 紧且避开三点。任意 degree≤d 的点 y，其所有局部 conjugates 都可放入 𝒦，不足 d 个时补重复点。总有某个 i，使 φ_i(y) 的全部共轭落入这些固定 K_v。

如实际 moduli/tripodal 识别需要 Legendre 的六种重标记，取 K_v 在这六个固定 Möbius 变换下的有限并；仍紧且避开三点。j 的 2-adic 有界性保留。

**关键量词顺序：**Y、d、V、全部 φ_i、L_v、δ₀、K_V 先固定，然后才输入 y。映射选择 i 可以依赖 y；最终常数只取有限多个 i 的最大值。

不必再证明一个独立的反例序列版 §13.3。若旧消费者固定使用该形式，E2 直接施加于反例列，有限多 i 中有一个出现无穷次，再用下节统一估计矛盾即可。


## 8. G1-E：把局部高度估计运输成 P8 producer

### 8.1 对选中的 φ_i，先写出实际高度恒等式

由 B3，记 E_i=(φ_i⁻¹D)red，D={0,1,∞}，则

\[
h_{O(1)}(\phi_i(y))
   =h_{\omega_Y}(y)+h_{E_i}(y)+O_i(1).
\tag{F1}
\]

因为 ω_{\mathbb P¹}(D)≃O(1)，这是实际线丛同构的高度运输。

实施方式是：在 finite affine cover 上选线丛 frames，写出 B3 的 transition functions；在好 integral models 上局部 norm 恒等式成立，有限坏素数处由固定有理函数的分子分母／resultant 界控制，archimedean 处由紧致 normalized charts 控制。求和并用 product formula 消去 frame 选择，产生独立于 y 的 O_i(1) 见证。不将“同 degree”误当作高度有界差。

### 8.2 conductor 与 arithmetic different 的相消

令 L=ℚ(y)，K=ℚ(φ_i(y))。在固定坏模型素数以外，
φ_i(y) 在 D 上约化，当且仅当 y 在 E_i 上约化。对一个 K-place v，用 w|v 表示 L-places。归一化后，K 端 conductor 与 L 端 conductor 的差为

\[
\frac1{[L:\mathbb Q]}
 \sum_{w\mid v}(e_{w/v}-1)f_{w/v}\log Nv.
\]

不同指数满足 δ_{w/v}≥e_{w/v}−1，因此上述差由 relative different 控制。利用判别式 tower formula，得到

\[
D(K)+N_D(\phi_i(y))
 \le D(L)+N_{E_i}(y)+C_i.
\tag{F2}
\]

坏模型素数处只需控制 truncated conductor：每个固定有理素数的 normalized contribution≤log p，故其总和是固定常数。这里没有把随 y 变化的高阶 valuation 当常数。

此外，

\[
N_{E_i}(y)\le h_{E_i}(y)+C_i.
\tag{F3}
\]

在好位，截断的“是否相交”≤canonical section 的整数消失阶；archimedean 与坏模型处，固定连续 metric 给统一下界。这逐处证明 F3，而不是新加一个 regionVolume_le_normalizedWeight 卡片。

### 8.3 不需要一般 degree-height 渐近定理，也能吸收 h_E

为每个固定 E_i 构造一个实际 homogeneous polynomial P_i，degree r_i，满足：

- P_i 在 E_i 每个点消失；
- P_i 不在 Fermat 方程理想中。

具体做法：对每个几何点选经过该点而不包含 Y 的直线，取有限 Galois orbit 的乘积，再对 E_i 的各 orbit 相乘。系数下降到 ℚ，Y 不可约保证乘积不恒为零。于是

\[
\operatorname{div}(P_i|_Y)=E_i+F_i,\qquad F_i\ge0.
\]

固定 effective divisor 的高度在其 support 外有统一下界；support 本身是有限代数点，用非消失 frame 计算这些点的高度，把有限最小值也收入常数。因此

\[
h_{E_i}(y)\le r_i h_{O_Y(1)}(y)+C_i
 =\kappa_i h_{\omega_Y}(y)+C_i,
\qquad \kappa_i=\frac{r_i}{n-3}.
\tag{F4}
\]

最后等式来自实际 A4；不需要假设任意同次数线丛高度相差 O(1)。只需一个有限 κ_i，不追求最佳系数。

### 8.4 完成 proper curve 的统一高度上界

用 §7 选到的 φ_i，把 D1 施于 φ_i(y)，再用 F1–F3：

\[
h_{\omega_Y}(y)+h_{E_i}(y)
 \le(1+\eta)\{D(L)+N_{E_i}(y)\}+C
 \le(1+\eta)\{D(L)+h_{E_i}(y)\}+C.
\]

减去 h_E，代入 F4：

\[
(1-\eta\kappa_i)h_{\omega_Y}(y)
 \le(1+\eta)D(L)+C.
\tag{F5}
\]

所有 φ_i 早已固定。取 κ=max_i κ_i，给定 0<δ≤1，可明确选择

\[
\eta=\frac{\delta}{2(1+(1+\delta)\kappa)}.
\]

于是 1−ηκ>0，且 (1+η)/(1−ηκ)≤1+δ。对有限多个 i 的常数取最大值，得到

\[
\boxed{\forall y,\ [\mathbb Q(y):\mathbb Q]\le n^2:
\quad h_{\omega_Y}(y)\le(1+\delta)D(\mathbb Q(y))+C_{n,\delta}.}
\tag{F6}
\]

有限多个 boundary／特殊点若在某个旧局部接口之外，直接计入常数；§7 保证至少一张图的像满足 D1 的非边界条件。这个 C 在 y 之前确定。

### 8.5 Fermat lift 的 discriminant 为什么只按 radical 计

对 primitive a+b=c，取

\[
y=[(a/c)^{1/n}:(b/c)^{1/n}:1]\in Y_n(\overline{\mathbb Q}),
\qquad L=\mathbb Q((a/c)^{1/n},(b/c)^{1/n}).
\]

逐次 monic root extension 给 [L:ℚ]≤n²，π(y)=a/c。

- p∤nabc：两根均是单位，根多项式导数为单位，实际 integral extension étale，故无分歧。
- p|abc 且 p∤n：先在不分歧 extension 中加入 μ_n，Kummer extensions 的 ramification prime to p，故是 tame。δ=e−1；归一化对 w|p 求和后，贡献≤log p。
- p|n：不使用 v_p(a)、v_p(b)、v_p(c) 作上界。只用局部次数≤n² 与 LocalDifferentUpperBound；normalized different 被只依赖 p,n 的数控制。这些 p 是固定有限集。

由此得到实际判别式界

\[
\boxed{D(L)\le\log\operatorname{rad}(abc)+C_n.}
\tag{F7}
\]

这一步给出 radical 的系数 1。若用 polynomial discriminant 的粗界含入 v_p(abc)，将回到 log(abc)，那条估计不够，必须改用上述 tame different 计算。

### 8.6 固定 ε 后走到现有 ABC consumer

先给定 ε>0。取 δ=min(1,ε/3)，则 (1+δ)²≤1+ε；选整数 n≥4，使 n/(n−3)≤1+δ。之后才构造 Y_n、有限 map family、K_V、η 及全部常数。

Fermat 方程逐处给

\[
h(\pi(y))=n h_{O_Y(1)}(y)+O(1)
 =\frac n{n-3}h_{\omega_Y}(y)+O(1).
\tag{F8}
\]

第一式也可不走一般 height functoriality：在非阿基米德位，
|Y|^n=|Z^n-X^n|≤max(|X|^n,|Z|^n)；
archimedean 位多一个因子 2。求和得到显式 O(log 2)。

组合 F6–F8，使用 log rad≥0：

\[
\log c=h(a/c)
 \le \frac n{n-3}(1+\delta)\log\operatorname{rad}(abc)+C_\varepsilon
 \le(1+\varepsilon)\log\operatorname{rad}(abc)+C_\varepsilon.
\tag{F9}
\]

最后复用真实 Frey j-height 供体
h(j(E_{a,b}))≤6log c+log 256，取 B_ε=6C_ε+log256，得到开头的 (F)。

这才构造 P8UniformHeightBound 的 inhabitant，再调用现有
abcConjecture_iff_freyJProductHeightCriterion 的反向箭头。若为兼容旧接口保留 belyiCompactnessToFreyHeight，其证明应从已经完成的 F9 构造 FreyHeightBound；输入的 scalar uniform-convergence 命题可以不用，不能声称它承担了 F6 的高度证明。

## 9. 实施图、查重清单与交接出口

### 9.1 精简后的节点及两类依赖

下表每行是一个实际出口，非新增条件卡。statement dependencies 是写出准确命题需要的对象；proof dependencies 是证明该命题使用的结果。

| 节点 | 实际输出／消费者 | statement dependencies | proof dependencies |
|---|---|---|---|
| G-A | 两图粘合的 Y_n、π；供后续全部 G1 节点 | 两个 monic quotient rings、实际 ℙ¹ | 已有 affine Fermat、localization/gluing、finite⇒proper、局部 smooth |
| G-B | Ω≃O(n−3)、实际 ramification；供高度运输 | G-A 的真实微分／line bundle | 商环 Ω 呈现、A3 的 transition、local DVR |
| G-C | noncritical φ 与 B3；供有限 family | G-A/G-B、真实 divisor/section/branch 定义 | 实际 RR/Serre 实例、Lemma 2.4 降阶、已有 finite-beta fold |
| U-L | C1 及全 packet 加权 upper；供 C3 | 实际 source、tensor、Φ、ϖ、weights | 已有 local upper、H1/P7 对应实际来源、局部不同／arch 容器／素数估计；不依赖 hCor312 |
| U-R | C2 同源读数字典；供夹逼 | 原 reading、actual region 和 reference | J1 主线；需要时换 J2 或 J3，不要求错类型的 algebra equivalence |
| U-C | C4=hCor312；供 P6-final | Q、M、actual display terms | P5 下界、U-L、U-R；不调用 P6-final |
| L-H | D1 局部高度 criterion | λ、degree、actual K_V、D/N/height | U-C→P6-final 或 C5；实际 P7 实例、D2/D3、误差吸收 |
| G-K | 固定 φ_i 与 K_V；供 F6 | G-A/G-C、local fields 与 analytic points | disjoint E_i、局部 bounded-degree finiteness、紧致正最小值 |
| H-T | F1–F8 的 height/different 运输 | 实际 morphism、divisor、点域 | G-B/G-C、local metric/product formula、arithmetic different、Kummer tame 计算 |
| P8-P | (F) 的 producer | 原 ABCFreyJProductHeightCriterion | L-H、G-K、H-T、ε 选择；最后接已有 P8 consumer |

这个图没有“先假设目标成立，再用于构造某个前置”的边。数学研究风险集中在 U-R 的实际运输与 U-L 的 actual coverage；它们有三种具体构造机制和可检查的中间输出，不用最终高度界当作验证方法。

### 9.2 已有成果怎样复用，哪些任务不再重派

| 现有文件／供体 | 本路线复用的精确部分 | 本轮不把它扩张成的结论 |
|---|---|---|
| Mzk1G1FermatAffineSchemeActual | 一个真实 Spec(AdjoinRoot)、monic finiteness、导数 | 整条 projective smooth proper curve 已完成 |
| Mzk1G1FermatProjectiveSchemeActual | ambient Proj、闭子集、ambient proper | 闭子集已经带有目标 subscheme |
| Mzk1G1NoncriticalMapActual／GenEll16 | algebraic finite set 的 polynomial Belyification | 任意 protected set 的 actual morphism 已构造 |
| Mzk1Consumer24AdapterUnconditionalActual | rational set、finite rational β 的避让 | 一般代数点的 Lemma 2.4 induction 已完成 |
| AG_FLT_ProvedTheoremsPromotionActual | 既有 Serre／Weil／Čech 证明 | Fermat function field 的所有实际实例已填 |
| FinitePlaceStepVAssembly／Mzk1BoxReadoutLocalActual | 真 tensor hull 的条件明确的局部 upper | 任意 S1902 source reading 自动等于它 |
| StepV*Average／Mzk1BoxConstantAuditActual | 现有权重及系数代数 | 权重和所有 actual source 已连接 |
| Mzk1P6PhiActionFamilyActual／PhiActionSourceActual | 保格族、identity 成员、possible-images 入其 hull | 每个实际 source arrow 的 realization 已接入 |
| Mzk1P6RootParameterWeightActual | 幂关系到实际 ord 公式及 weighted sum 代数 | 真实 distinguished factor 内的根实例已自动给出 |
| Mzk1G1FermatChartRingActual2 | 两个单根扩张的 monic 和 power bases | 两张完整 projective charts 及 overlap 已构造 |
| IUTIV/Estimates/Section2.lean:409 | Prop 1.6 的 4/3 prime-count eventual bound、θ 双侧界 | 本次 actual prime set 的绑定可以省略 |
| S2715／S3171／P6DisplayChainActual | CTheta 代数、slack、final display | 可倒过来生产自己的 hCor312 |
| Mzk1G1AllCompactActual | 原有 scalar uniform-convergence 辅助定理 | 高度／different 的 compactness criterion |
| P8ProducerAttempt／Mzk1G1CriterionAllActual | 已有 producer→consumer 包装 | wrapper 已证明 FreyHeightBound |
| ABCEllipticHeightCriterion | actual Frey criterion ↔ ABC | 无输入的 criterion inhabitant 已在 |

核心结论：不要重写这些已有证明；新增的是其具体实例、对象识别和上游估计。原先接受节点的状态保持不变。

### 9.3 最有价值的下一包

**首先做 U-R 的一个实际 packet，连同 U-L 的源覆盖。**交付内容限定为：

1. 指明真实 source T、p、tuple、distinguished slot；
2. 给 q-root 主格、theta 源 span、reference 格的实际定义；
3. 写出一个任意合法 source arrow 的坐标作用，证明进入 Φ 并保格；
4. 证明 q-reading 的根／degree 公式和 theta-region 入 packet hull；
5. 把得到的含 degree/index 的公式代回 C1，核对负 q 项与权重；
6. 若直接 region 运输受 carrier 妨碍，当场换 J2 的实际矩阵或 J3 的实际有限商，不继续索求不成立的原 carrier AlgEquiv。

这个包最先回答的是“现有 lower 和独立 upper 是否真的约束同一量”，直接减少 hCor312 的前提。它不触碰 P6-final，不以其结论验证前置。

另一条不依赖该包的就绪工作是 G-A：从已有 affine donor 构造第二图、overlap isomorphism 和实际 π。随后 G-B 先给 Ω 的 transition，供 G-C 与高度运输共用。本轮按用户要求只给路线，不启动并行执行者。

### 9.4 文件、版本与验收

研究包：p7-g1-p6-p8-closure-route-20261116；owner：当前 chat；SHEAF 阶段：阶段 1 依赖分解及阶段 2 自然语言精确陈述。精确读取版本、来源哈希和两类边记录在同名 DAG JSON。

本包只新增本路线及 DAG 记录，并在旧路线、P7-GAP-ATTACK-PLAN、STATE、queue、AUDIT_LEDGER 追加指向本稿的更正。没有改任何 Lean 文件、既有目标定义或活动 owner。后续若需修改消费者，必须保留原目标语义并单独登记。

- statement_compiles：NOT_RUN；
- proof_body_checked：NOT_RUN；
- kernel_closed：NOT_RUN；
- target_accepted：NOT_RUN。

这些状态指本稿新增 producer 的形式验证；已接受节点仍按既有证据保留。本文交付的是具有完整依赖方向、实际构造步骤与最终量词的研究路线，未把尚未实施的 U-R/U-L、G-C、L-H、H-T 标成已证定理。

