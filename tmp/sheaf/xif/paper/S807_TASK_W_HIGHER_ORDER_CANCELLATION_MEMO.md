# S807 Task W：高阶相消 / 高阶估计工具专查 —— 能否给出 paper Cor 3.12 不等式或 least λO hull

日期：2026-10-30。
性质：研究 memo + 一个已编译的自足 no-go 文件（tmp/sheaf/xif/paper/S807CancellationNoGoActual.lean）。
范围：Task W。系统检索并评估六类“高阶相消/高阶估计”工具，判断它们能否给出 paper 的
-|log Θ| ≥ -|log q|（IUT III, Corollary 3.12）或 paper 的 least λO holomorphic hull
（IUT III, Remark 3.9.5, (i)）。不改目标、不引入 fake 对象、不把 estimate 伪装成恒等式。

## 0. 结论（TL;DR）

**六类工具全部明确拒绝。** 不是“还不够强”，而是**类型不对**：paper 的目标是
object-level 的集合包含 + 精确 Haar log 恒等式；六类工具给的是域元素之和 / 积分 /
秩 / 熵 / 基数的**估计**。三个彼此独立的拒绝理由：

1. **Typing（对象里没有“和”）**：paper 的 Θ-pilot possible image 是有限个单项式
   q[2u]^{j^2}（j ∈ F_l^×）及其在 (Ind1)-(Ind3) 下的像的并集；hull 是“包含该并集的
   最小 λO 区域”（Remark 3.9.5(i)，P1-P3）。全程没有对 j 的域元素求和；唯一的求和
   是 real-valued 的 procession 平均（权重 1/l⋆）。Gauss/Weil/decoupling/Gowers/
   polynomial method/entropy 全部作用于“和 / 积分 / 秩 / 基数”，在 paper 对象里没有
   可作用的参数。
2. **量化（p-adic 下根本没有相消）**：即使人为造一个 theta 和
   S = Σ_j q[2u]^{j^2}，因为 ‖q[2u]‖ < 1，j=1 项严格支配，S807 证明
   ‖S‖ = ‖q[2u]‖ **精确相等**（norm_thetaSum_Icc_eq）。Gauss/Weil 的 √l 是
   archimedean 模；l ≠ p 时 √l 是 p-adic 单位，对 valuation/log-volume 零信息。
3. **方向（hull 与高阶 label 无关）**：paper 不等式由 per-b 的
   q-pilot 区域 ⊆ Θ hull 蕴含（在 exact log 公式下等价；S800/S805），而 hull 已经等于 j=1 区域 F(c)O
   （S793 actual），与所有高阶 label j ≥ 2 **无关**（F(j^2 c)O ⊆ F(c)O）。所以任何
   关于高阶 label 分布 / 相消的陈述都不可能改变 least hull。相消若真能“缩小”hull，
   反而会改变 paper 对象（去掉 j=1 像），而 j=1 像正是 q-pilot 自身，不能去掉。

附带更正 S730 §4.1：paper hull 是“最小**包含**区域”，对嵌套球就是**最大**的球
F(c)O（j=1），不是 F((l⋆)^2 c)（那是各 label 区域的**交**，不含 j=1 像）。旧 hull
log ≈ 0 的真正原因是 **zero label**（θ_0 = q^0 = 1）把 hull 撑到 O_hol；S745/S779/
S793 去掉 zero label 后 hull = F(c)O，在 S801 的 scaling data 下 log = -c log p。
不是 hull 方向反了。S730 其余结论
（root 的 valuation 障碍、拒绝 Hodge/FF/tilt 作载体）不受影响。

## 1. paper 目标与当前 Lean 状态

### 1.1 paper 定义（source）

* IUT III, Remark 3.9.5, (i), lines 7787-7809：对 subsets αU（以及 AU、A,αU），
  holomorphic hull 定义为“the smallest subset of the form λ·O ... that contains αU”，
  其中 λ 的各分量非零；不 relatively compact 时 hull 取整个 IQ。
* IUT III, lines 7819-7827：该 hull 操作由三条性质唯一刻画：
  (P1) φ(H) = H；(P2) P ⊆ φ(P)；(P3) P1 ⊆ P2 ⇒ φ(P1) ⊆ φ(P2)。
  这正是“包含 P 的最小 λO 区域”（intersection of all candidates）。
* IUT III, Corollary 3.12, lines 1200-1229：-|log Θ| 是
  procession-normalized mono-analytic log-volume（对 j ∈ F_l^⋇ 取平均）of the
  holomorphic hull of the union of the possible images of a Θ-pilot object；
  -|log q| 是 q-pilot object 的像（**不** subject to (Ind1)-(Ind3)）的同一 log-volume；
  结论：-|log Θ| ≥ -|log q|（等价地 C_Θ ≥ -1）。
* IUT III, lines 1004-1013, 1071-1079：paper 自己的证明是“tautological”的：
  计算 Θ-pilot hull 的 log-volume “necessarily amounts to a computation of
  [an upper bound for] |log q|”。**paper 的证明里没有解析估计**，只有
  Θ×μ-LGP-link 的 gluing isomorphism 把 Θ-pilot 与 q-pilot 认同。

### 1.2 当前 Lean 对象（都是 object-level）

* literal hull：LiteralIQHolomorphicHullActual.literalIQHolomorphicHull
  （lines 92-97）= ⋂ H ∈ literalIQCandidateHulls P, H；containment
  literalIQImage_subset_holomorphicHull（lines 100-107）。
* qVFam block 上的 least hull：S793PaperLeastLambdaOHullActual.paperLeastLambdaOHull
  （lines 91-92）= ⋂ {H : H = F(λ)O 且 image ⊆ H 且 λ ≥ c}；候选条件实际迫使 λ = c。
  关键定理 paperLeastLambdaOHull_eq_minimal（lines 149-153）：
  paperLeastLambdaOHull = F(c)O。证明用 j=1 的像 forced 反向包含。
* q-pilot 包含：S800LeastLambdaOHullActual.qPilotPaperRegion_subset_leastLambdaOHull
  （lines 104-108）；S805NonzeroHullReplacementActual.qPilotPaperRegion
  （lines 46-48）及其 eq_rootThetaRegion_one（line 50）。
* log：S799LeastLambdaOPaperTargetActual.paperLeastLambdaOHullLog_eq_formula
  （lines 59-68）与 S801PaperHullLogActual.paperHullLog_eq_paperQPilotRegionLog
  （lines 54-58）、paperQPilotLogPaperOrder_le_paperHullLog_of_data（lines 85-90）。
  公式 -∑ c log p 来自
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
  （FinitePlaceNormalizedUnitScalingLogVolume.lean, lines 379-390）。
  唯一条件：ArithmeticTuplePureFractionalScalingData（一个 norm p^{-c} 的 generator，
  即 root / divisor-monoid exponent 的算术存在性）。
* 本任务重编译验证：S793、S800、S801 均 EXIT 0（paperLeastLambdaOHull_eq_minimal、
  qPilotPaperRegion_subset_leastLambdaOHull、paperQPilotLogPaperOrder_le_paperHullLog_of_data 等）。
  S799 因 Mathlib 构建缺 .olean.private（Data/List/DropRight）未能重编译；这是环境问题，
  不是证明失败。S805/S806 未重编译。
* 因此 per-b 不等式 = containment + exact Haar log；剩下的 exact inputs 只有：
  (i) fractional scaling data / root（S342、S730、S795 的 root 语义问题）；
  (ii) paper normalization / denomination（2l 归一化、l⋆ 平均、hull-first vs
  average-first：S764、S794、S797）；
  (iii) global assembly（nativeBadLocalWeight 的加权线性求和）。
  **没有一个是关于“和”的估计。**

### 1.3 关键结构事实：hull 与高阶 label 无关

对 j ∈ F_l^×，记 R_j = F(j^2 c) O_hol。因为 c ≥ 0、j^2 ≥ 1，有 j^2 c ≥ c，
而 fractional lattice 对 exponent 是 antitone 的
（arithmeticTupleFractionalLattice_mono，
FinitePlaceFractionalTensorLattice.lean, lines 113-120：“larger tuple of exponents
gives a smaller fractional tensor lattice”），所以

    F(j^2 c) ⊆ F(c)，  R_j ⊆ R_1，  ⋃_{j≠0} R_j = R_1.

因此“包含整个 union 的最小 λO 区域”就是 R_1 = F(c)O，**只由 j=1 决定**；所有
j ≥ 2 的 label 都是 hull-redundant。若把 zero label 也算进去，R_0 = F(0)O = O_hol
（因为 θ_0 = q^0 = 1），hull 被撑到 O_hol，log = 0——这正是旧 paperRootThetaHullLog
≈ 0 的来源（见 §5）。paper 的 label 是 j ∈ F_l^⋇，non-zero（S793 的
PaperNonzeroLabel；S745/S779 的 Nonzero 修正）。

结论：**任何只改变“高阶 label 的分布 / 相位 / 平均值”的工具，都不能改变 least
hull。** 能改变 hull 的只有两种操作：(a) 改变 P（去掉 j=1 像，或加入更大的像）；
(b) 改变 λO candidate 族本身。两者都是 object-level 的集合陈述，不是估计。

## 2. p-adic 相消不可能：已编译的 no-go

文件：tmp/sheaf/xif/paper/S807CancellationNoGoActual.lean
编译命令：

    lake env lean -j1 -R "D:\lean" tmp/sheaf/xif/paper/S807CancellationNoGoActual.lean

结果：EXIT 0。五个定理的 axioms 均恰为 [propext, Classical.choice, Quot.sound]；
无 sorry、无 axiom、无 True/PUnit、无 project import。

### 2.1 Mathlib 已有（不需要新证明）

* IsUltrametricDist.norm_add_le_max
  （Mathlib/Analysis/Normed/Group/Ultra.lean，norm_mul_le_max 的 additive 版）。
* IsNonarchimedean.add_eq_max_of_ne
  （Mathlib/Algebra/Order/Ring/IsNonarchimedean.lean:109）与 unbundled 版
  add_eq_max_of_ne'（:121）：f x ≠ f y ⇒ f (x+y) = max (f x) (f y)。
* IsNonarchimedean.apply_sum_le_sup（:134）：f (∑ i∈s, l i) ≤ s.sup' _ (f ∘ l)。
* Finset.Nonempty.norm_sum_le_sup'_norm（Group/Ultra.lean:207 的 additive 版）。

### 2.2 S807 新证明

* norm_add_eq_left_of_norm_lt：‖y‖ < ‖x‖ ⇒ ‖x + y‖ = ‖x‖。
* norm_sum_eq_of_unique_max：有限和若有唯一 strict maximum norm，则
  ‖∑ f‖ = ‖f i0‖（精确相等，不是 ≤）。
* norm_thetaSum_Icc_eq：r ≠ 0、‖r‖ < 1、1 ≤ n ⇒
  ‖∑_{j=1}^{n} r^{j^2}‖ = ‖r‖。
  **这是本 memo 的量化核心**：theta 标签和（如果真去造它）的 p-adic 范数精确等于
  j=1 项，没有相消；其 log 也精确等于顶层 theta value 的 log。paper 根本没有这个和，
  所以这个定理只是说明：即使造出最有利于“相消论证”的和，也得不到任何 gain。
* sum_mem_ball_not_image_subset：存在球 R（半径 ‖t‖ < 1），使
  1 + (-1) ∈ R 但 {1, -1} ⊄ R。
  **这是 typing 反例**：任何“和落在更深的球 ⇒ 像集落在更深的球 ⇒ hull 更小”的推理
  都是假的。Gauss/Weil/decoupling 即使给出再强的和估计，也不能推出 hull containment。
* mem_iInf_of_mem_closure：若每个 candidate 都含 P，则 P 的 additive closure 含于
  least hull（regions 是加法子群）。和不会**逃出** hull；配合上一条，和也不能**缩小**
  hull。和的控制与 hull 的确定是正交的。

### 2.3 一句话

p-adic 非阿基米德范数下 |sum| ≤ max 不仅成立，而且在 theta 的严格递减 valuation
情形下是**等号**。相消（cancellation）是 archimedean 模的现象；p-adic valuation /
Haar log-volume 看不见它。paper 要的是 lattice scale（valuation）与集合包含，不是
和的模。

## 3. 六类工具逐项审计

总表：

| 族 | 代表定理/论文 | 给什么 | 为什么 typecheck 不上 | Lean 可行性 | 判定 |
|---|---|---|---|---|---|
| (1) p-adic oscillatory integrals / stationary phase | Igusa; Denef–Loeser; Cluckers–Gordon–Halupczok | 积分值/临界点展开/conductor 界 | paper 无 phase function；积分是单点，不是 hull；unit phase 的积分是 p-adic unit，看不见 c > 0 | Mathlib 无 p-adic 积分 | REJECT |
| (2) finite field Gauss/Weyl/Weil/character sums | Gauss; Weil 1948/49; Deligne 1974; Katz 1988 | archimedean 模界；特殊情形精确值 | l ≠ p ⇒ 根单位是 p-adic unit，√l 是 unit；精确零也不缩小 hull（T5） | S684/S689 已有精确二次 Gauss；Weil/Deligne 无 | REJECT |
| (3) polynomial method / slice rank / Gowers / additive combinatorics | CLP 2017; Ellenberg–Gijswijt 2017; Tao slice rank; Gowers 2001 | 基数/秩界；additive uniformity | label set 固定为 F_l^×，无 F_p^n 未知子集；目标是 valuation 不是基数 | Mathlib 只有 Finset/ZMod | REJECT |
| (4) decoupling / Weil convolution for theta q^{j^2} | Bourgain–Demeter 2015; BDG 2016; Wooley | ℓ² decoupling / Vinogradov 界 | T4 精确支配；p-adic 对象无 archimedean 振荡；sup 就是 j=1，已知 | Mathlib 无 decoupling | REJECT |
| (5) higher-order Jensen/convexity/Brunn–Minkowski | Jensen; Brunn–Minkowski; Prékopa–Leindler; Alexandrov–Fenchel | 凸体体积不等式 | p-adic Haar log 对 c 线性精确；regions 是子模，BM 不等式反向；hull 是 max 不是平均 | Q memo 已证 Q_p 上无 PartialOrder/SMul Real/Module Real | REJECT |
| (6) tensor rank / entropy | Håstad 1990; slice rank; von Neumann entropy; Lieb–Ruskai; optimal transport | 秩/熵不等式、传输成本 | tensor block 是直积，log 精确可加；possible-image tensor 是 rank 1；全局是加权线性和 | 无 von Neumann entropy | REJECT |

### 3.1 (1) p-adic oscillatory integrals / stationary phase

具体定理/论文：

* Igusa, An Introduction to the Theory of Local Zeta Functions, AMS/IP Stud. Adv.
  Math. 14 (2000), Ch. 7：p-adic stationary phase formula。对 f : Z_p^n → Z_p、
  phase ψ，积分 ∫ ψ(f) |g| dx 可由 f 的临界点处的有限和（Gauss sum 权重）计算；
  其 valuation 由 conductor / Jacobian 控制。
* Denef–Loeser, Weights of exponential sums, intersection cohomology, and Newton
  polyhedra, Invent. Math. 106 (1991), 275-294：motivic/Newton polyhedron 版本。
* Cluckers–Gordon–Halupczok, Local integrability results in harmonic analysis on
  reductive groups in large positive characteristic, Ann. Sci. ENS 47 (2014)：
  p-adic stationary phase 的现代形式与 transfer principles。

给什么：积分值、临界点展开、conductor/Jacobian 的 valuation 界。stationary phase
的本质就是“用相位振荡相消来计算积分”。

为什么拒绝：

* (a) paper 对象里没有 phase function，也没有积分。possible image 是单项式
  q[2u]^{j^2}；hull 是 λO lattice 的交，不是 sublevel set / integral set。
* (b) 积分是一个**数**；它最多给出一个点的 containment，不能给出像集的 hull
  containment（§2.2 的 T5 正是这个反例）。
* (c) 对 unit phase，积分落在 Z_p[ζ] 里，p-adic norm ≤ 1；它看不见
  c = ord(q)/(2l) > 0 的 lattice scale。
* (d) stationary phase 的“相消”是 ψ 的 archimedean 振荡；ψ 的取值是根单位，
  在 Q̄_p 里是 unit，对 valuation 没有贡献。

Lean 可行性：Mathlib 没有 p-adic 积分理论、没有 Igusa local zeta、没有 stationary
phase；从零形式化是数月级项目，而且形式化完也 typecheck 不上 paper 的 hull 目标。
**REJECT**（只保留“p-adic unit integral 看不见 valuation”这一 no-go 引用）。

### 3.2 (2) finite field Gauss/Weyl sums, Weil bounds, character sums

具体定理/论文：

* Gauss：非平凡加法特征上 |G(a)| = √q。
* Weil, On some exponential sums, PNAS 34 (1948), 204-207；Numbers of solutions of
  equations in finite fields, Bull. AMS 55 (1949), 497-508：
  |∑_{x∈F_q} χ(f(x))| ≤ (deg f - 1)√q（χ 非平凡、f 的零点互异；加法特征情形类似）。
* Deligne, La conjecture de Weil I, Publ. Math. IHÉS 43 (1974), 273-307：
  |∑_{x∈F_q^n} ψ(f(x))| ≤ (deg f - 1)^n q^{n/2}（f 的齐次部分光滑等标准条件）。
* Katz, Gauss sums, Kloosterman sums, and monodromy groups, Ann. of Math. Studies
  116, Princeton (1988)；Burgess, On character sums and L-series II, Proc. LMS 13
  (1963), 524-536。

给什么：archimedean 模的界；特殊情形（二次 Gauss）的精确值。S684 已在 Lean 里
定义 quadraticGaussSum（ZMod N → ℂ）并证明 zero/even 对称；S689 的数值实验给出：
对 N = 2l，奇数 a 的 G = 0，偶数 a 的 |G|^2 = 4l；μ_{2l}-orbit 平均 A_j = 0。

为什么拒绝：

* (a) 对 label 群 F_l 上的 Gauss 和（取值 ζ_l）：l ≠ p ⇒ Q_p(ζ_l)/Q_p unramified
  ⇒ 所有 l-th 根单位都是 p-adic unit；Gauss sum 是 Q(ζ_l) 里的代数整数，p-adic
  norm ≤ 1（可能为 0）。archimedean 的 √l 满足 v_p(√l) = 0，是 p-adic unit。所以
  Weil 界在 p-adic 侧退化为**平凡界 1**，对 c = ord(q)/(2l) 零信息。
  注意：若换成 F_p 的加法特征 ζ_p，二次 Gauss 和 = √(±p) 在 p 处 valuation 1/2；
  但它不是 paper 的 label Gauss 结构，其 p-adic 大小也不进入 c 的计算；本 memo 的
  拒绝不依赖这个细节。
* (b) S689 的精确恒等式（orbit 平均 = 0）不是估计，而是 identity；而且它是
  **average-first 路线的负面结果**：μ_{2l}-平均把每个非零 theta label 都 annihilate，
  不能用来造 positive hull log。S797 已明确 S794 的 average-first 是 surrogate。
* (c) 即使和精确为零，也不缩小 summands 的 hull（T5）。
* (d) paper 的 label 值 q[2u]^{j^2} 的 valuation 已经精确知道（j^2 c），Gauss sum
  不增加任何关于这个 valuation 的信息。

Lean 可行性：S684 是 actual（仅 ℂ 上的有限 Gauss 组合恒等式）；S689 是数值实验。
Weil/Deligne/Katz 的完整形式化（étale cohomology、Weil conjectures）不存在，且与目标
无关。**REJECT**。

### 3.3 (3) polynomial method / slice rank / Gowers norms / additive combinatorics

具体定理/论文：

* Croot–Lev–Pach, Progression-free sets in Z_4^n are exponentially small,
  Ann. of Math. 185 (2017), 331-337。
* Ellenberg–Gijswijt, On large subsets of F_q^n with no three-term arithmetic
  progression, Ann. of Math. 185 (2017), 339-343。
* Tao, slice rank（2016 blog / symmetric formulation）；Gowers, A new proof of
  Szemerédi's theorem, GAFA 11 (2001), 465-588（Gowers norms）。
* Green–Tao 的 additive structure 理论。

给什么：F_p^n 子集的基数/秩上界；函数的 additive uniformity（Gowers norm）。

为什么拒绝：

* (a) paper 的 label set 是 F_l^×，基数固定为 l⋆；没有未知子集，没有 F_p^n 环境，
  没有 capset / progression-free 问题。
* (b) 目标是 valuation/log-volume，不是基数；polynomial method 的界是整数/实数基数界。
* (c) 唯一的有限组合输入是精确的二次映射 j ↦ j^2（Gauss/平方结构），已经是 identity。
* (d) Gowers norm 是 archimedean/complex-valued 的 additive uniformity，没有 p-adic
  lattice 意义。

Lean 可行性：Mathlib 有 Finset、ZMod、初等组合，但没有 capset/slice rank/Gowers
machinery；形式化它们对目标没有消费者。**REJECT**（没有 target）。

### 3.4 (4) decoupling / Weil convolution for theta q^{j^2}

具体定理/论文：

* Bourgain–Demeter, The proof of the l^2 decoupling conjecture, Ann. of Math. 182
  (2015), 351-389。
* Bourgain–Demeter–Guth, Proof of the main conjecture in Vinogradov's mean value
  theorem for degrees higher than three, Ann. of Math. 184 (2016), 633-682。
* Wooley, efficient congruencing / Vinogradov mean value（Adv. Math. 294 (2016),
  532-561 等）。
* Weil/Deligne 的 exponential sum 界（同上）。

给什么：parabola / moment curve 上 exponential sums 的 ℓ^p decoupling 与
Vinogradov mean value 界。

为什么拒绝：

* (a) T4：theta 和的 p-adic 范数精确等于 j=1 项；p-adic 对象里**没有** archimedean
  振荡可以 decouple。
* (b) paper 需要的是 label 的 sup（= j=1），而它由 ord(q) 精确给出；decoupling 最多
  重新推导这个平凡 sup。
* (c) decoupling 的 gain 是 archimedean L^p gain，不是 valuation/lattice gain。
* (d) paper 的不等式不需要 theta 和的任何界；它需要 hull containment，而 containment
  已由 j=1 label 给出（S800/S805）。

Lean 可行性：Mathlib 没有 decoupling / Vinogradov mean value；形式化成本高且无消费者。
**REJECT**。

### 3.5 (5) higher-order Jensen / convexity / Brunn–Minkowski

具体定理/论文：

* Jensen 不等式（凸函数）。
* Brunn–Minkowski 不等式；Alexandrov–Fenchel 不等式；
  Prékopa–Leindler（log-concave 函数的卷积）。
* 参考：Schneider, Convex Bodies: The Brunn–Minkowski Theory, 2nd ed., Cambridge
  (2014)。

给什么：凸体 / log-concave 函数的体积不等式。

为什么拒绝：

* (a) p-adic Haar log 对 exponent c 是**线性且精确**的
  （arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic：
  log = -∑ c_i log p）；没有 convexity gap 可利用。
* (b) regions 是 Z_p-子模；嵌套球的 Minkowski 和是较大的球：
  p^a O + p^b O = p^{min(a,b)} O。于是 Brunn–Minkowski 会读成
  μ(p^{min}O)^{1/d} ≥ μ(p^a O)^{1/d} + μ(p^b O)^{1/d}，右边多出一个正项，**假**。
  所以 archimedean BM 不等式在这个 p-adic lattice 设定里没有对应物。
* (c) paper 的 hull 是 label 的 **max**（最小包含区域），不是平均；S764 把 hull-min
  与 S694 label average 明确分开；Jensen 作用于平均，是另一个 functional。
* (d) Q_CONVEX_TOOLING_MEMO 已实测：Mathlib 无法在 Q_p 上合成 PartialOrder /
  SMul Real / Module Real，所以 Convex/Brunn–Minkowski 的 statement 都无法 elaborate。

Lean 可行性：实凸几何在 Mathlib 有，但 carrier 是 Q_p-向量空间，没有 real scalar
结构；Q memo 的 probe 已经给出证据。**REJECT**。

### 3.6 (6) tensor rank / entropy methods

具体定理/论文：

* tensor rank：Håstad, Tensor rank is NP-complete, J. Algorithms 11 (1990), 644-654；
  slice rank（Tao）。
* von Neumann entropy / strong subadditivity：Lieb–Ruskai, J. Math. Phys. 14 (1973),
  1938-1941。
* optimal transport / entropy（S741_OPTIMAL_TRANSPORT_ENTROPY_MEMO 已审）。

给什么：张量秩界、熵不等式（subadditivity/strong subadditivity）、传输成本。

为什么拒绝：

* (a) tensor block 是 local fields 的直积；normalized log 对 V 精确可加（现有定理是
  ∑ over V）；entropy 也精确可加，没有 subadditivity gap。
* (b) possible-image tensor 是 rank 1（local monomials 的纯张量积）；rank 方法没有
  可界定的对象。
* (c) global assembly 是 bad places 上的加权线性和（nativeBadLocalWeight），精确，
  不是熵/传输问题。
* (d) 熵/秩不等式是 real-valued 的；paper 要的是 p-adic lattice 的 Haar log。

Lean 可行性：Mathlib 没有 von Neumann entropy；tensor rank 只有线性代数层面；
形式化对目标无消费者。**REJECT**。

## 4. 唯一可接受的“相消”形态：exact identity / invariance

六类工具被拒绝，不等于 paper 里没有任何“相消/抵消”内容。paper 的抵消全部是
**object-level 的恒等式或不变性**，不是估计：

1. μ_{2l}-isometry：S730 的 root_norm_independent、root_pow_norm_independent；
   换 root 不改变 norm/hull（root 的 μ_{2l}-torsor 是 paper 自己的 indeterminacy）。
2. label 对称 j ↦ -j：j^2 相同，R_j = R_{-j}；不改变 hull。
3. zero-label exclusion：θ_0 = 1 会把 hull 撑到 O_hol（log 0）；paper 的 label 是
   j ∈ F_l^⋇，non-zero（S745/S779/S793）。
4. Kummer / log-Kummer identifications（Theorems A, (ii); 3.11, (ii)）：
   把 Θ-pilot 与 q-pilot 认同的 gluing isomorphism。

这些都是“P 的像集是什么 / 哪些 label 在 P 里”的集合陈述，已经由 paper 的
“tautological”论证给出。**如果未来某个论证真的需要 cancellation，它必须写成
P ⊆ 更小区域 或 H(P) = 更小区域，即改变 P 或 hull，而不是对某个和做估计。**
而 hull 与 j ≥ 2 无关，所以唯一能改变 hull 的方式是去掉 j=1 像——那正是 q-pilot
自身，不可能去掉。

## 5. 对 S730 §4.1 的更正（重要）

S730_HODGE_FF_PERFECTOID_CARRIER_MEMO.md §4.1 写道：current rootThetaHull 是
closure(union_j F(j^2 c)O_hol)，是 largest region；而“paper hull (intersection) is
instead the smallest region containing all labels, morally F((l⋆)^2 c)O_hol”，并称两者
是 opposite extremes。前半段（union = F(c)O）是对的；后半段把 paper 的
“smallest subset containing P” 误读成了“各 label 区域的交”。

正确陈述（对照 Remark 3.9.5(i) 原文）：

* paper hull = **包含 P 的最小 λO 区域**（P1-P3 的唯一刻画）。
* λO 区域是嵌套球；要包含 norm 最大的 j=1 像，λ 的每个分量必须取最大 norm
  （一因子时 λ = p^{-c}）。所以最小包含区域是**最大的球** F(c)O = R_1。
* F((l⋆)^2 c)O 是各 label 区域的**交**，它甚至不含 j=1 像，因此不是 candidate。
* 旧 rootThetaHull 的 log ≈ 0 不是因为 hull 方向反了，而是因为
  rootThetaImageSet（RootHullContainmentInequalityActual.lean, lines 74-75）
  对 **SignedLabel**（GaussianKernel.lean, lines 94-95：
  {j : Int // -(lStar l) ≤ j ≤ lStar l}，**包含 0**）取并；zero label 的
  θ_0 = q^0 = 1 使 R_0 = O_hol，union 变成 O_hol，hull log = 0。
* S745/S779/S793 去掉 zero label 后，hull = F(c)O；在 S801 的 scaling data 下
  log = -c log p。
* S793 已证 paperLeastLambdaOHull ⊆ 旧 union hull（paperLeastLambdaOHull_subset_
  old_unionHull, lines 156-166），并把“两者相等”定义为 OldUnionEqualsLeastLambdaOHull
  （lines 170-171）；相等 iff closure 不添加东西。S806 把 F(c)O 的 closedness 记为
  PaperRootHullNonzeroClosedGap：有 generator/scaling data 时 F(c)O 是 compact open，
  故 closed；无 generator 时它是 formal span，closedness 需单独处理。这个 closedness
  是集合论小缺口，与 cancellation 无关。

S730 的其余结论（root 的 valuation 障碍、拒绝 B_dR/FF/tilt 作 paper carrier、
μ_{2l}-torsor 的 isometric invariance）**仍然有效**，本 memo 不推翻。

## 6. 建议

1. **不要在 (1)-(6) 上投入**。它们不能给出 paper 不等式或 least hull；强行使用只会
   产生 surrogate（S794/S797 已拒绝 average-first surrogate）。
2. **least-hull 侧作为 object 已基本闭合**：S793（hull = F(c)O）、S800
   （q-pilot ⊆ hull）、S801（log 公式 conditional on scaling data）本任务已重编译
   EXIT 0；S799 因环境缺 .olean.private 未重编译，S805/S806 未重编译。建议 owner
   纳入 ledger；closedness（S806）与 scaling data（S801 的 PaperHullLogFormulaData）
   是两个明确的 exact 小缺口。
3. **剩余的真实缺口是算术/语义，不是分析**：(i) q[2u] 的 root 语义（S342/S730/S795：
   valuation 障碍；paper 放在 root-stack/log monoid）；(ii) paper 的 2l 归一化与
   l⋆ 平均 / hull-first 读法（S764/S794/S797）；(iii) global assembly 的权重。
   这些应分配给 source/normalization owner，而不是分析工具。
4. 如果未来某个地方真的需要估计，用 Mathlib 的 ultrametric sup bound
   （norm_add_le_max / add_eq_max_of_ne' / apply_sum_le_sup）加精确 Haar log；
   不要用相消。p-adic 侧“和 ≤ max”是恒等式级别的工具，不是估计工具。
5. 更新 ledger：记录 Task W 的六类 REJECT；更正 S730 §4.1；记录 zero-label 诊断；
   引用 S807 的编译结果。

## 7. Lean 可行性表

| 项目 | 现状 | 成本 | 对目标有用？ |
|---|---|---|---|
| Mathlib IsUltrametricDist.norm_add_le_max / IsNonarchimedean.add_eq_max_of_ne' | 已有 | 0 | 是（no-go 的 formal core） |
| Mathlib IsNonarchimedean.apply_sum_le_sup / Finset.Nonempty.norm_sum_le_sup'_norm | 已有 | 0 | 是 |
| S807 norm_add_eq_left_of_norm_lt / norm_sum_eq_of_unique_max / norm_thetaSum_Icc_eq | 本任务编译，EXIT 0 | 已完成 | 是（量化核心） |
| S807 sum_mem_ball_not_image_subset / mem_iInf_of_mem_closure | 本任务编译，EXIT 0 | 已完成 | 是（typing no-go） |
| S793 / S800（least hull / containment） | 本任务重编译，EXIT 0 | 已完成 | 是（object-level 主线） |
| S801（log 公式，conditional on scaling data） | 本任务重编译，EXIT 0 | 已完成 | 是（object-level 主线） |
| S799（least-hull 目标） | 未重编译：环境缺 .olean.private | 低（环境问题） | 是（S793 的薄包装） |
| S805 / S806（nonzero hull / closedness gap） | workspace 文件，未重编译 | 低 | 是（辅助） |
| S684（二次 Gauss，ℂ） | actual | 已完成 | 只作 label 记账，不作估计 |
| S689（μ_{2l}-orbit 平均实验） | 数值实验 | 已完成 | 负面结果；不作证明工具 |
| Igusa / Denef–Loeser p-adic stationary phase | Mathlib 无 | 数月 | 否 |
| Weil / Deligne / Katz exponential sums | Mathlib 无 | 数周-数月 | 否 |
| Bourgain–Demeter / BDG decoupling | Mathlib 无 | 数月 | 否 |
| polynomial method / slice rank / Gowers | Mathlib 只有 Finset/ZMod | 数周 | 否 |
| Brunn–Minkowski / Prékopa–Leindler（Q_p carrier） | Q memo 已证不可 elaborate | 不可行 | 否 |
| von Neumann entropy / tensor rank | Mathlib 无 | 数周 | 否 |

## 8. 参考文献

paper（本地 extract）：

* IUT III, Remark 3.9.5, (i), tmp/source-extract/iut3.txt lines 7787-7827。
* IUT III, Corollary 3.12, tmp/source-extract/iut3.txt lines 1200-1229。
* IUT III, “tautological” 论证, lines 1004-1013, 1071-1079。
* IUT II, p.2, lines 64-68（theta values = q[2u]^{j^2}）。
* IUT I, Definition 3.1(c), lines 3240-3248；Example 3.2(iv), lines 3774-3788。

Lean（workspace）：

* tmp/sheaf/xif/paper/S807CancellationNoGoActual.lean（本任务，EXIT 0）。
* tmp/sheaf/xif/paper/S793PaperLeastLambdaOHullActual.lean。
* tmp/sheaf/xif/paper/S799LeastLambdaOPaperTargetActual.lean。
* tmp/sheaf/xif/paper/S800LeastLambdaOHullActual.lean。
* tmp/sheaf/xif/paper/S801PaperHullLogActual.lean。
* tmp/sheaf/xif/paper/S805NonzeroHullReplacementActual.lean。
* tmp/sheaf/xif/paper/S806PaperRootHullNonzeroGapsActual.lean。
* tmp/sheaf/xif/paper/RootHullContainmentInequalityActual.lean。
* tmp/sheaf/xif/paper/LiteralIQHolomorphicHullActual.lean。
* tmp/sheaf/xif/paper/S730_HODGE_FF_PERFECTOID_CARRIER_MEMO.md。
* tmp/sheaf/xif/paper/S730PaperRootCarrierActual.lean。
* tmp/sheaf/xif/paper/S342QVFamilyRootImpossible.md。
* tmp/sheaf/xif/paper/S795OrderSemantics.md。
* tmp/sheaf/xif/paper/S764ThetaHullMinVsAverageActual.lean。
* tmp/sheaf/xif/paper/S797PaperHullFirstAuditActual.lean。
* tmp/sheaf/xif/paper/S684QuadraticGaussFiniteActual.lean。
* tmp/sheaf/xif/paper/S689_GAUSS_ORBIT_MEMO.md。
* tmp/sheaf/xif/paper/Q_CONVEX_TOOLING_MEMO.md。
* tmp/sheaf/xif/paper/S741_OPTIMAL_TRANSPORT_ENTROPY_MEMO.md。
* LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceFractionalTensorLattice.lean
  （arithmeticTupleFractionalLattice_mono, lines 113-120）。
* LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean
  （fractionalLattice_mul_holomorphic 公式, lines 379-390）。
* LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean（SignedLabel, lines 94-95）。

数学：

* Weil, On some exponential sums, PNAS 34 (1948), 204-207。
* Weil, Numbers of solutions of equations in finite fields, Bull. AMS 55 (1949),
  497-508。
* Deligne, La conjecture de Weil I, Publ. Math. IHÉS 43 (1974), 273-307。
* Katz, Gauss sums, Kloosterman sums, and monodromy groups, Ann. of Math. Studies
  116, Princeton (1988)。
* Igusa, An Introduction to the Theory of Local Zeta Functions, AMS/IP Stud. Adv.
  Math. 14 (2000), Ch. 7。
* Denef–Loeser, Weights of exponential sums, intersection cohomology, and Newton
  polyhedra, Invent. Math. 106 (1991), 275-294。
* Cluckers–Gordon–Halupczok, Local integrability results in harmonic analysis on
  reductive groups in large positive characteristic, Ann. Sci. ENS 47 (2014)。
* Croot–Lev–Pach, Ann. of Math. 185 (2017), 331-337。
* Ellenberg–Gijswijt, Ann. of Math. 185 (2017), 339-343。
* Gowers, A new proof of Szemerédi's theorem, GAFA 11 (2001), 465-588。
* Bourgain–Demeter, Ann. of Math. 182 (2015), 351-389。
* Bourgain–Demeter–Guth, Ann. of Math. 184 (2016), 633-682。
* Wooley, Adv. Math. 294 (2016), 532-561。
* Håstad, Tensor rank is NP-complete, J. Algorithms 11 (1990), 644-654。
* Lieb–Ruskai, J. Math. Phys. 14 (1973), 1938-1941。
* Schneider, Convex Bodies: The Brunn–Minkowski Theory, 2nd ed., Cambridge (2014)。

## 9. 诚实限制

* 六类工具的拒绝是数学/定理层面的分析，没有对 Igusa/Weil/decoupling/Gowers/
  Brunn–Minkowski/entropy 做 Lean 形式化；本 memo 不声称这些理论被形式化。
* S793、S800、S801 已在本任务重编译，EXIT 0。S799 未重编译：Lean 读取
  Mathlib/Data/List/DropRight.olean.private 失败（环境/构建问题，不是 S799 的证明错误）；
  S805/S806 按 workspace 现状引用，不声称已验证。S807 是本任务新编译的，EXIT 0，
  axioms 已核。
* paper 的 l⋆ 平均读法（hull-first vs average-first）是 paper-semantics 问题；
  本 memo 采用 S797 的 hull-first 读法，不裁决。两种读法下结论都成立，因为两者
  都是 exact log-volume 的 real-linear functional，不引入域元素的和。
* paper 的 possible images 还包含 (Ind1)-(Ind3) 的 indeterminacy 像；Lean 模型的 P
  目前是 label union。加入 indeterminacy 像只会把 hull 按 log-shell 的 O(1) 扩大，
  不会产生“和”，因此不改变本 memo 的结论；但这是模型与 paper 的一个已知差异，
  应由 paper-semantics owner 记录。
* 本 memo 没有改目标、没有改 ledger、没有改任何既有 Lean 对象；唯一新增是
  S807CancellationNoGoActual.lean。
