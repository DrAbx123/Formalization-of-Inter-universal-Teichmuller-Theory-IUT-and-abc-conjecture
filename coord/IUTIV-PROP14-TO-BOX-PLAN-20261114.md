# IUT IV 命题 1.4 的构造证明路线，以及接入真实 Box 的下一步

日期：2026-11-14。任务：iutiv-prop14-to-box-plan-20261114。负责人：当前 chat 的 root，单线程。

这份文件先处理命题 1.4，尤其是 (ii) 的精确公式；后半再处理用户列出的其余项目。它是自然语言证明与实施交接，不是本轮完成的 Lean 证明。未修改 Lean 源码，未运行新构建、传递公理检查或目标 comparator。

本轮只使用本地论文、相关源码和对应 DAG 记录；没有外部调研，没有全仓逐一定理审查。不能把“本轮没有找到”说成“全仓不存在”。来源版本哈希见同名 DAG 节点。

**主要判断：1.4(ii) 有一条具体、可完成的局部域证明路线。它的关键不再是重建对数分析，而是把已有对数同构、有限商、Haar 指数公式与 DVR 商环计数接起来。另一个重要发现是：原文 Step V 使用 1.4(iii) 的第二条上界，这条上界可以不经过 (ii) 的精确扭元计数。**

## 1. 锁定结论、对象与归一化

原文：[IUT IV 本地文本](../papers/motizuki_corpus/text/Inter-universal%20Teichmuller%20Theory%20IV.txt)，命题 1.4，文本约 L656–821，印刷页 13–14。用户所称“推论 1.4”在原文是 Proposition 1.4。

取一个真实的有限扩张 \(K/\mathbf Q_p\)，用延拓 \(\mathbf Q_p\) 标准范数的范数：

- \(O=\mathcal O_K=\{x:\|x\|\le1\}\)，\(\mathfrak m\) 为其极大理想。
- \(U=O^\times\)，\(\kappa=O/\mathfrak m\)，\(q=\#\kappa=p^f\)。
- \(e=v_K(p)\)，这里离散赋值满足 \(v_K(\pi)=1\)；\(d=[K:\mathbf Q_p]\)。
- \(T=\operatorname{tors}(U)\)，\(T_p\) 是它的实际 \(p\)-初级部分，\(\#T_p=p^m\)。
- \(L=\log_p(U)\subset K\)，是实际单位对数的像。

任取加法 Haar 测度 \(\mu\)。对正、有限测度的区域定义

\[
\ell_K(S)=\frac{\log\mu(S)-\log\mu(O)}d.
\]

这里的 log 对实际正实数测度取值。Lean 中先证明 ENNReal 测度非零、非无穷，再转 toReal。Haar 任意常数在相减时消掉，不添加“测度常数恰为 1”的输入。

目标是：

\[
\boxed{\ell_K(L)=-\frac{f+m}{ef}\log p
=-\left(\frac1e+\frac m{ef}\right)\log p.}
\tag{P14ii}
\]

有限局部扩张及其标准范数是原命题的合法对象条件。\(d=ef\)、商群阶、扭元阶、log 像质量都必须从这些对象证明，不能作为使用者另交的假设。

**这里特别容易混淆的两个集合：**

设
\[
s=\begin{cases}1,&p\ne2,\\2,&p=2,\end{cases}
\qquad a=p^s=p^*,\qquad \Lambda=a^{-1}L.
\]

仓库的 integralLogShell / integralLogShellLattice 是 \(\Lambda\)，论文 (ii) 中的是 \(L\)。因此
\[
\ell_K(L)=\ell_K(\Lambda)-s\log p.
\]
不能把现有非负的 integralLogShellDiscrepancy 直接当成论文负的 log-volume。

此外，\(L\) 一般只是 \(\mathbf Z_p\)-格，不能直接当成 \(O\)-理想；体积为 \(p^{-(f+m)}\) 不意味着 \(L=\pi^{(f+m)/f}O\)。

## 2. 已有供体：哪些工作不应再派一次

下表是当前源码检查结果。写“已有证明体”不等于本轮新编译通过；精确验收状态见 §10。

| 需要的内容 | 已有文件与声明 | 本轮判断 |
|---|---|---|
| 实际未缩放 log 像 | [UnscaledUnitLogLattice.lean](../LeanFormal/IUT/Foundations/LocalFields/UnscaledUnitLogLattice.lean)：coe_unitLogLattice_eq_range、coe_unitLogLattice_eq_scale_smul | 直接复用，不新造一个区域替代它 |
| 对数核就是扭元群 | [IntegralUnitLogarithmKernel.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithmKernel.lean)：unitLog_eq_zero_iff_isOfFinOrder、unitLogHom_ker_eq_torsion | 分析核心已有 |
| 深层同余单位对数同构 | [IntegralUnitLogarithmCongruenceEquiv.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithmCongruenceEquiv.lean)：logShellCongruenceLogEquiv | \(1+p^sO\) 经缩放 log 同构于 \(O\)，无需重证局部逆函数 |
| 扭元群有限 | [IntegralUnitLogarithmTorsionFinite.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithmTorsionFinite.lean)：finite_integralUnitTorsion | 已通过到深层同余商的单射证明 |
| 实际有限商 \(\Lambda/O\) | [IntegralLogShellIntegerQuotient.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellIntegerQuotient.lean)：finite_logShellIntegerQuotient、congruenceQuotientToLogShellIntegers、torsionIntegerQuotientKernelEquiv | 商、满射和核识别已有 |
| 精确基数乘法式 | [IntegralLogShellIndexArithmetic.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellIndexArithmetic.lean)：logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex | 不是接口假设；已有证明体 |
| Haar 质量等于有限指数 | [IntegralLogShellHaarIndex.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellHaarIndex.lean)：measure_integralLogShell_eq_index_mul、integralLogShellDiscrepancy_eq_log_congruence_sub_log_torsion | 最后的测度记账已存在 |
| 实际 \(O\) 是 DVR，\(e>0\) | [IntegralLogShellRamificationInertia.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellRamificationInertia.lean)：isDiscreteValuationRingIntegers、logShellRamificationExponent_pos | 不应继续说缺 DVR 结构 |
| 实际 residue 的特征与基数 | [IntegralLogShellSharpBounds.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellSharpBounds.lean)：logShellResidueField_charP、logShellResidueCard_eq_prime_pow、coprime_p_logShellResidueCard_sub_one | \(q=p^f\)、\(f\ge1\)、\((p,q-1)=1\) 已有 |
| 有限维 Haar 的 \(p\) 缩放 | [FinitePadicHaarScaling.lean](../LeanFormal/IUT/Foundations/LocalFields/FinitePadicHaarScaling.lean)：measure_prime_smul_finiteDimensional、log_measure_prime_smul_finiteDimensional | 不必另证 Jacobian 或重新构造 Haar |
| 整数环的 \(e\) 与 ramificationIdx 对应 | [LocalDifferentUpperBound.lean](../LeanFormal/IUT/Foundations/LocalFields/LocalDifferentUpperBound.lean)：logShellRamificationExponent_eq_ramificationIdx | 已有对应，不能重复登记为未知 |
| 现成条件公式 | [IntegralLogShellIndexResidueFormula.lean](../LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellIndexResidueFormula.lean)：LogShellQFECardinalityHypothesis 及其消费者 | **真正要做的是证明实际 constructor，不能把这个结构传给上层当答案** |

局部次数与 residue 的另一套规范化若来自 CommonPrimeCompletion，先复用 IndexArithmetic 中已有的 isometry/ringEquiv 指数运输；不要混用两种范数实例后直接写 rfl。

## 3. 1.4(ii) 的主路线：用现有精确序列完成有限计数

### 3.1 先把已有精确序列写成明确数学对象

令 \(U_s=1+p^sO\)。它就是现有 logShellCongruenceUnits：定义中的闭球条件
\[
\|u-1\|\le\|p^s\|
\]
等价于 \((u-1)/p^s\in O\)，因此等价于模 \(p^sO\) 为 1。

已有深层对数同构给出
\[
a^{-1}\log:U_s\xrightarrow{\sim}O.
\]
于是 \(O\subset\Lambda\)，且 \(T\cap U_s=\{1\}\)。

定义
\[
\Gamma=\Lambda/O,\qquad C=U/U_s.
\]
已有满射是
\[
C\longrightarrow\Gamma,\qquad [u]\longmapsto[a^{-1}\log u].
\]
核正是 \(T\) 在 \(C\) 中的像。说明这不是把核条件重新假设进去：若 \(a^{-1}\log u\in O\)，深层同构给 \(v\in U_s\) 满足 \(\log v=\log u\)，故 \(uv^{-1}\in T\)；反向显然。\(T\cap U_s=1\) 给单射。

因此有真正的有限群精确序列
\[
1\longrightarrow T\longrightarrow C\longrightarrow\Gamma\longrightarrow0,
\qquad \#C=\#T\cdot\#\Gamma.
\tag{1}
\]

**这一整步已有仓库实现。需要接入，不需要另开“证明 log 的核”或“构造有限商”任务。**

### 3.2 第一个新叶子：实际同余单位商的阶

由于 \(O\) 为 DVR，\((p^s)=\mathfrak m^{es}\)。令 \(n=es\ge1\)。

第一步构造群同构
\[
U/U_s\simeq (O/\mathfrak m^n)^\times.
\tag{2}
\]
模商映射的核就是 \(U_s\)。满射的证明也很具体：商环单位的任一提升不能落在 \(\mathfrak m\)，否则其剩余类非单位；局部环中不属于极大理想的元素就是单位。

第二步计数。已有 Mathlib 本地定理

**cardQuot_pow_of_prime**，文件 [.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean](../.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean)，约 L152，

给出
\[
\#(O/\mathfrak m^n)=q^n.
\]
它是根 namespace 下的定理，使用 Submodule.cardQuot；并非名为 Submodule.cardQuot_pow_of_prime 的声明。

非单位恰好是 \(\mathfrak m/\mathfrak m^n\)。由
\[
0\to\mathfrak m/\mathfrak m^n\to O/\mathfrak m^n\to O/\mathfrak m\to0
\]
计数得 \(\#(\mathfrak m/\mathfrak m^n)=q^{n-1}\)。也可用 uniformizer 乘法构造 \(O/\mathfrak m^{n-1}\simeq\mathfrak m/\mathfrak m^n\)；不必为此重建整个滤过理论。

所以
\[
\boxed{\#C=q^{es}-q^{es-1}=(q-1)q^{es-1}.}
\tag{3}
\]

建议输出两个具体定理：同余商与 quotient-units 的等价；实际 congruence quotient cardinality。然后由它们构造已有 LogShellQFECardinalityHypothesis 的实例。上层消费者不再接受自由 hqfe。

### 3.3 第二个新叶子：\(\Gamma\) 是有限 \(p\)-群

这是本轮建议的关键拼接，可避开重新形式化 Teichmüller 提升。

任取 \(z\in\Lambda\)。由于 \(\|p\|=p^{-1}<1\)，存在 \(N\) 使
\[
\|p^Nz\|\le1.
\]
所以 \(p^Nz\in O\)，即 \(\Gamma\) 中的 \([z]\) 被 \(p^N\) 杀死。加法商改用 Multiplicative 包装，正好满足 Mathlib 的 IsPGroup。

这里甚至不必先给整个 \(\Gamma\) 找统一 \(N\)；对每个代表元存在 \(N\) 已经足够。商有限已经由现有文件证明，因此由

[Mathlib/GroupTheory/PGroup.lean](../.lake/packages/mathlib/Mathlib/GroupTheory/PGroup.lean) 中 **IsPGroup.iff_card / IsPGroup.exists_card_eq**

得到
\[
\boxed{\#\Gamma=p^h\quad\text{for some }h\ge0.}
\tag{4}
\]

新证明的实质只是：取代表元；用 \(p^{-N}\|z\|\to0\) 进入整数环；改写商中 nsmul 为零。没有调用与 1.4 同等强度的体积公式。

### 3.4 用 (1)、(3)、(4) 算扭元阶，不必先分类所有根单位

令 \(t=f(es-1)\)。由上三式得
\[
\#T\cdot p^h=(q-1)p^t.
\tag{5}
\]
又因 \(p\nmid(q-1)\)，取整数的 \(p\)-进指数：
\[
v_p(\#T)+h=t.
\tag{6}
\]
定义 \(m=v_p(\#T)\)。这不是任意选来配平公式的参数：\(T\) 是有限交换群，其 \(p\)-初级部分就是唯一 Sylow \(p\)-子群，故阶恰为 \(p^{v_p(\#T)}\)。在 Lean 中用 CommGroup.primaryComponent 和 Sylow.card_eq_multiplicity，连接 Nat.factorization 与 padicValNat，确认它与论文的 \(m\) 相同。

于是
\[
\boxed{\#T=(q-1)p^m,\qquad h+m=f(es-1).}
\tag{7}
\]

这就内部推出了原文在 (ii) 前使用的扭元阶公式。既不假设“所有扭元都来自 residue”，也不假设 \(m=0\)，更不需要 residue degree 为 1。

实现时优先使用 Nat 基数的**乘法等式**再取对数/估值，不把 Nat.div 直接强转为实数除法。正性、整除性与有限性由上述构造交付。

### 3.5 \(d=ef\) 也可从同一套计数推出

可以复用一般 ramification–inertia 维数定理，但当前最省模型运输的路线是以下直接比较。

由 \((p)=\mathfrak m^e\)：
\[
\#(O/pO)=q^e.
\]
有限个平移陪集给
\[
\mu(O)=q^e\mu(pO).
\]
另一方面，已有 FinitePadicHaarScaling 给
\[
\mu(pO)=p^{-d}\mu(O).
\]
消去已证正、有限的 \(\mu(O)\)，得到
\[
p^d=q^e=p^{ef},\qquad\boxed{d=ef}.
\tag{8}
\]

这条证明使用的缩放定理按 \(\mathbf Q_p\)-向量空间维数证明，**不依赖 \(d=ef\)**，所以没有循环。也避免先把两套 completion/residue 模型逐个运到一起。

若已有实际消费者需要 Ideal.inertiaDeg 形式，另接 residue field 的 \(\mathbf F_p\) 维数与 \(q=p^f\) 的唯一性；不要在主证明中平白增加这个运输负担。

### 3.6 最后把质量算出来

已有 Haar 指数公式给
\[
\mu(\Lambda)=\#\Gamma\cdot\mu(O)=p^h\mu(O).
\]
而 \(L=p^s\Lambda\)，重复使用现有 \(p\) 缩放公式：
\[
\frac{\mu(L)}{\mu(O)}=p^{-sd}p^h.
\]
用 (7)、(8)：
\[
-sd+h=-sef+f(es-1)-m=-f-m.
\]
故
\[
\boxed{\frac{\mu(L)}{\mu(O)}=p^{-(f+m)}.}
\tag{9}
\]
取实对数、除以 \(d=ef>0\)，即得 (P14ii)。

也可以直接复用 integralLogShellDiscrepancy_eq_log_congruence_sub_log_torsion：
\[
\log\frac{\mu(L)}{\mu(O)}
=-sd\log p+\log((q-1)q^{es-1})-\log((q-1)p^m).
\]
\(\log(q-1)\) 抵消，结果相同。

**这条链的数学证明已经给全；尚未完成的是这些新叶子的 Lean 实现与当前版本验收。没有把所需基数、扭元阶或体积结论留作最终定理的新假设。**

### 3.7 必须核对的边界例子

| 实际局部域 | 参数 | 公式给出的结果 |
|---|---|---|
| \(K=\mathbf Q_p,\ p>2\) | \(e=f=1,m=0,s=1\) | \(\ell_K(L)=-\log p\)，对应 \(L=p\mathbf Z_p\) |
| \(K=\mathbf Q_2\) | \(e=f=1,m=1,s=2\) | \(\ell_K(L)=-2\log2\)，对应 \(L=4\mathbf Z_2\) |
| 奇素数处未分歧扩张，次数 \(f\) | \(e=1,m=0\) | 未归一化质量 \(p^{-f}\)，归一化后仍是 \(-\log p\) |

这三个是数学一致性检查，本轮没有另写 Lean 测试。\(p=2\) 的 \(-1\) 是扭元，不能误写 \(m=0\)；统一使用 \(s\) 后它会自然进入公式。

### 3.8 备选证明的使用位置

若 p-primary/Sylow 接口很费工，可先证明 \(\#\Gamma=p^h\) 及 \(h\le f(es-1)\)，立即得到
\[
\ell_K(L)\le-\frac1e\log p.
\]
这已经足够供给 1.4(iii) 第一条上界。精确 \(m\) 识别仍继续完成，不把弱结论改名成 (ii)。

另一条核验路线是原文的局部对数测度计算：\(U\) 的加法 Haar 质量为 \(1-q^{-1}\)，局部对数保持质量，再除以实际有限核 \(\#T\)。它给
\[
\frac{1-q^{-1}}{(q-1)p^m}=p^{-(f+m)}.
\]
但全局“除以有限核”需要局部图和有限覆盖证明；已有深层同余商路线已替我们完成这部分，因此不建议另外重写解析 Jacobian 框架。

## 4. 1.4(ii) 到 (iii)：第一条上界怎样接，不要求错误的载体等价

设 \(K_i/\mathbf Q_p\) 是论文中的实际局部域：
\[
A=\bigotimes_{\mathbf Q_p}K_i,\quad R_I=\bigotimes_{\mathbf Z_p}O_i
\subset\widetilde R_I,\quad L_I=\bigotimes_{\mathbf Z_p}L_i.
\]
\(\widetilde R_I\) 是**同一 \(A\)** 的整数闭包。其有限域乘积分解可以复用，但不将 \(A\) 与来自其他 q 根扩张的任意乘积强行做代数等价。

需要的体积恒等式是
\[
\ell_A(L_I)=\ell_A(R_I)+\sum_i\ell_{K_i}(L_i),
\qquad \ell_A(R_I)\le0.
\tag{10}
\]

具体证明：取每个 \(O_i,L_i\) 的 \(\mathbf Z_p\)-基，转换矩阵 \(M_i\)。若 \(d_i=[K_i:\mathbf Q_p]\)、\(D=\prod_i d_i\)，张量基的转换矩阵是 Kronecker 积，
\[
\det\Bigl(\bigotimes_iM_i\Bigr)=\prod_i(\det M_i)^{D/d_i}.
\]
用真实的 Haar/determinant 公式，除以 \(D\)，就是 (10)。Mathlib 的 Matrix.det_kronecker 已存在；局部格基可复用 FinitePadicIntegralLattice 与 UnscaledUnitLogLattice。

若项目中已有同一 carrier 的 determinant/Haar 公式，应直接适配；本轮未把“通用 determinant 公式仍缺”列为新结论。这里真正需要验的是 (10) 的**实际格实例和分母**。其中 \(\ell_A(R_I)\) 通常不能抹成零，非最大阶的指数贡献必须保留。

令论文 \(d_I\) 为 different orders 之和，\(a_I=\sum_i a_i\)，
\[
r=\lfloor\lambda-d_I-a_I\rfloor.
\]
由 (ii) 或 §3.8 的弱式：
\[
\ell_A(p^rL_I)
\le(-\lambda+d_I+a_I+1)\log p-\sum_i e_i^{-1}\log p.
\]
再用 SharpBounds 中已有
\[
a_i-e_i^{-1}\le4/p,
\qquad a_i-e_i^{-1}=0\quad(e_i\le p-2)
\]
得到
\[
\ell_A(p^rL_I)\le(-\lambda+d_I+1+4|I^*|/p)\log p.
\]

**这补完的是 1.4(iii) 第一条体积上界。到原文 Step V，有一条更短的直接入口，见下一节。**

## 5. 直接推进真实 Box：复用 (iii) 第二条上界

### 5.1 原文实际用了哪一条

原文 Step V，约 L1640–1741、印刷页 27–28，明确选择右侧最大阶容器，并使用
\[
\boxed{(-\lambda+d_I+1)\log p+
\sum_{i\in I^*}(3+\log e_i).}
\tag{11}
\]
因此“先证明 (ii) 才能推进任何 \(R\le\mathrm{Box}\) 工作”并非实际依赖。完整命题 1.4 当然仍要完成；Box 的这一入口可以先行。

### 5.2 已有第二条上界的供体及精确限制

[Iut/Concrete/LocalConstruct/Prop14Lattice.lean](../Iut/Concrete/LocalConstruct/Prop14Lattice.lean)：

- prop14iii_lattice 已有完整证明体：构造实际 \(a\in A^\times\)，使所有指定 \(\varphi\) 的像落入 \(a\widetilde R_I\)，并证明其 componentVol 满足 (11)。
- integral_eq_order_of_unramified 给未分歧时最大阶等于 tensor order。
- latticeAut_integral_subset 给相应稳定性。

**必须按当前类型看待它：**

1. 当前量词是 \(\varphi\in\mathrm{indAut}\)。[IndAut.lean](../Iut/Concrete/LocalConstruct/IndAut.lean) 明确写出 indAut_finite_eq：它等于 tensorAut，即逐因子保格自同构的张量；不是已经量化了全部 latticeAut。
2. 源码证明真正使用的只是 tensorAut_subset_latticeAut 后的线性和保格性质。在 prop14iii_lattice 约 L237、以及 (iv) 约 L307，改为直接解包 latticeAut 证书，可提取到**全部保格 \(\mathbf Q_p\)-线性自同构**的版本。保留旧定理作为推论，不改掉旧消费者的意义。
3. 现有域模型是数域完备化；对论文 Step V 这是合适的来源。若要涵盖任意有限 \(\mathbf Q_p\) 扩张的完整命题 1.4，需要把局部证明抽到一般有限扩张，不能把数域模型结论直接改标签。
4. 当前 prop14iii_lattice 有 \(\operatorname{ord}_p(x)\ge0\)。Step V 的 good 位取 \(x=1\)，bad 位取实际 q 根幂，均可从其定义证明非负。完整 (iii) 的任意 \(\lambda\) 可取 \(N\) 使 \(\operatorname{ord}_p(p^Nx)\ge0\)，套已有定理，再用线性性和体积缩放把容器乘 \(p^{-N}\)；\(-N\log p\) 与 \(+N\log p\) 抵消。
5. Iut 层 log-shell 使用 \((2p)^{-1}\log U\)，LeanFormal 此处用 \((p^*)^{-1}\log U\)。奇 \(p\) 时差一个 \(\mathbf Z_p\)-单位 2，\(p=2\) 时都为 4；利用格对单位乘法稳定证明同一格。与**未缩放** \(L\) 比较则仍必须保留 \(p^s\) 的体积平移。

本轮检查到默认 .lake 目录中的 Section2、DifferentDegreeUpperBound、IntegralLogShellHaarIndex 的旧 olean；没有在所查默认路径发现 Prop14Lattice.olean。后者在这里标作**待当前构建验收的源码供体**，不标成本轮 green。

### 5.3 若适配 Iut 成本较高，直接搬同一证明到现有真实 tensor

不必把两棵库的整体 LocalTheory 全搬过来。第二条上界只需要以下构造：

1. 每个 \(O_i\) 中选实际 different 生成元 \(\delta_i\)，其归一化赋值为论文 \(d_i\)。
2. 使用已有 trace-dual 包含得到
   \[
   \Delta\widetilde R_I\subset R_I,\qquad
   \Delta=\prod_i\iota_i(\delta_i).
   \]
   LeanFormal 的 IntegralTraceDualTensorInclusion 已有实际 different-generator 乘法包含，Iut 的 PacketDifferent/LocalDifferent 也有证明供体。
3. 从 SharpBounds 选实际 \(\alpha_i,\beta_i\)，满足
   \[
   \alpha_iO_i\subset L_i\subset\beta_iO_i,\quad
   \operatorname{ord}_p\alpha_i=a_i,\quad
   \operatorname{ord}_p\beta_i=-b_i.
   \]
   这些局部包含已有，不重证 p-adic log 级数估计。
4. 置 \(A_0=\prod_i\iota_i(\alpha_i)\)、\(B_0=\prod_i\iota_i(\beta_i)\)。于是
   \[
   A_0\Delta\widetilde R_I\subset L_I\subset B_0R_I\subset B_0\widetilde R_I.
   \]
5. 对实际 distinguished factor 中的 \(x\ne0\)，\(\lambda=\operatorname{ord}_p x\)，取
   \[
   r=\lfloor\lambda-d_I-a_I\rfloor,\qquad
   Z=\iota_j(x)p^{-r}(A_0\Delta)^{-1}.
   \]
   在同一 tensor 的每个实际域因子中，
   \[
   \operatorname{ord}_p Z=\lambda-r-d_I-a_I\ge0.
   \]
   因此 \(Z\in\widetilde R_I\)。这是整数闭包的分因子检验，不是把“Z 整”留作接口字段。
6. 若 \(\varphi\) 保持 \(L_I\)，由第 4 步和 \(\mathbf Q_p\)-线性性：
   \[
   \varphi(\iota_j(x)\widetilde R_I)
   \subset p^rL_I\subset p^rB_0\widetilde R_I.
   \]
7. 同一 tensor 上的实际标量质量公式给
   \[
   \ell_A(p^rB_0\widetilde R_I)=(-r+b_I)\log p
   \le(-\lambda+d_I+a_I+b_I+1)\log p.
   \]
   用已有 \((a_i+b_i)\log p\le3+\log e_i\)，及小分歧时 \(a_i+b_i=0\)，即得 (11)。

这条路线没有使用 (ii)，没有要求 tensor 与 q 根扩张乘积的错误等价，也没有把 determinant 因子设成 1。

### 5.4 Ind3 与 holomorphic hull：怎样补到原文容器，且不多付常数

不能看到包含 \(\varphi(x\widetilde R_I)\) 就跳过原文 Ind3。

令 \(N=|I|\)。原文还需要覆盖基准区域
\[
B_{\mathrm{base}}=p^{\lfloor\lambda\rfloor-N}2^{-N}L_I.
\]
利用 1.4(iii) 末尾的
\[
d_I+a_I\ge N\ (p>2),\qquad d_I+a_I\ge2N\ (p=2)
\]
可得
\[
r=\lfloor\lambda-d_I-a_I\rfloor
\le\lfloor\lambda\rfloor-N-Nv_p(2).
\]
所以
\[
B_{\mathrm{base}}\subset p^rL_I\subset p^rB_0\widetilde R_I.
\]
所需末尾下界来自 different 下界与 \(a_i\ge1/e_i\)，\(p=2\) 时 \(a_i=2\)；对应局部数值供体已有。

于是同一个容器同时覆盖受允许自同构作用的像和原文基准区域。容器是同一 \(A\) 的主分式理想，故对该模型的 holomorphic hull 已封闭；用 hull 最小性得到 hull 仍被它包含。Iut 的 [Hull.lean](../Iut/Concrete/LocalConstruct/Hull.lean) 有 exists_leastHull_finite，可复用其“任意包含容器都包含最小 hull”的结论。

**剩下必须实证的源接口**是：原文 actual possibleImage 经既定 Kummer/log-shell 读法确实落在上面覆盖的集合中。做法是按实际 image 生成操作逐项检查：源生成元的 \(x\) 赋值；每个允许作用的线性/保格性质；基准区域的缩放；组合与 hull 的闭包。不能用一个自由 PossibleImagesContained 假设交给最终消费者，也不能用单点 possibleImage 或 identity action 缩小原文范围。

这一源接口本轮没有完成。它和局部估计应单列；(ii) 的精确体积证明本身不依赖它。

另外，[ShellBound.lean](../Iut/Concrete/LocalConstruct/ShellBound.lean) 的 prop14iii_shell 针对 \(x\cdot\mathrm{tensorLogShell}\)，右端**额外多一个 distinguished-slot 的 \(3+\log e_j\) 项**。它不能直接填进原文 (11) 而删去该项。优先用本节的共同容器法，保持原文基准区域及常数；若改用 shell 版本，必须重新证明额外误差可由原文预算吸收，不能默认为零。

### 5.5 最终消费者必须接现有 distinguished-slot 平均

每个 tuple 先证明原文指定 slot 的实际上界：
\[
V_{j,\mathbf v}
\le\left(-\lambda_{j,v_j}+\sum_i d_{v_i}+1\right)\log p
\sum_{i\in I^*}(3+\log e_{v_i}).
\]
\(\lambda_{j,v_j}\log p\) 必须由实际 q 根及幂关系算成
\[
\frac{j^2}{2l}\log q_{v_j}.
\]
这是同一数据的赋值识别，不能凭一个 norm agreement 参数带过。

然后依次接：

1. StepVProcessionAverage.exceptionalSum_le_r4：从实际域/分歧上界证明 R4，再压住 exceptional sum。R4 不是新的自由输入。
2. StepVDistinguishedSlotAverage.weightedAverage_le_of_distinguishedBound：直接对指定 slot 的界平均。**不需要假设真实区域的体积在 slot 置换下不变，也不需要逐点小于 slot 平均。**
3. StepVDivisorAverage.eDegreeUnnormalized_eq_weightedAverage：正确把实际 degree weights 与 \(D,Q\) 识别。需使用其源码限定的纤维读数，不能丢掉整体系数。
4. StepVProcessionAverage.processionAverage_eq：得到精确式
   \[
   \frac1{l^\star}\sum_j\operatorname{Avg}_{\mathbf v}V_{j,\mathbf v}
   \le\frac{l+5}4D-\frac{l+1}{24}Q+S+(l+5)T.
   \]
   若再使用 processionAverage_le，则得到原文随后较松的改写式，而非把两种 RHS 混称同一个等式。
5. 加入非 distinguished 有限位的零贡献，以及阿基米德位贡献；沿原文 Step III/VIII 的 different/prime 预算得到 Thm 1.10 的整体上界。

真实 Box 保留负 \(Q\) 项，\(S,T\) 是实际算术量。既有 P7 #9 的 paperBox/A6 三平移方案只涉及项目 surrogate，不能替代以上任何一个实际接口。

## 6. 其余“未形式化”项目：查重后的推进建议

### 6.1 命题 1.1：已有真实 different 包含；优先接生成元路线

IntegralTraceDualTensorInclusion 已构造真实 tensor 整数格、整数闭包、trace dual，并有
arithmeticTensorDifferentGenerator_mul_mem_arithmeticTupleValuationIntegerLattice。

它末尾 arithmeticTensorPaperDifferentScale 仍接受 hdiff，不能拿这个条件推论宣称完全关闭。处理方式是 §5.3 的实际 \(\Delta\) 和逐因子赋值检验：对 \(p^{\lceil d_I\rceil}\Delta^{-1}\) 逐因子证明整，从而消除 hdiff，而不是要求调用者补证它。

文件头保留历史失败构建记录，不能只凭头注判定当前失败，也不能只凭后文有 proof body 判定当前通过；应由原 owner 做当前版本验证。

原文 1.1 的“排除一个 distinguished factor”的更尖锐 different 界可以后补。Step V 所需的 \(d_I\) 总和版本已有更直接供体，不应让无关的加强版阻塞这个消费者。

### 6.2 命题 1.2：局部夹逼已有，余下重点是 tensor 上的容器

IntegralLogShellSharpBounds 已有：

- padicFractionalLattice_paperA_le_unitLogLattice；
- unitLogLattice_le_padicFractionalLattice_neg_paperB；
- unitLog_range_eq_prime_smul_integers_of_odd_unramified；
- \(a_i,b_i\) 的数值界、小分歧抵消和实际标量。

所以应按 §5.3 做同一 tensor 的多线性张量化、different 整除与任意保格自同构作用，完成一般局部容器。不要再新开“从头构造 p-adic log、证明收敛/局部逆函数”的包。

### 6.3 命题 1.3：不仅 (i)，(ii) 也已经找到供体

除了 DifferentTowerEstimate / DifferentTameEquality：

- [DifferentDegreeUpperBound.lean](../LeanFormal/IUT/IUTIV/Estimates/DifferentDegreeUpperBound.lean) 的 iutIVProp13ii_normalizedDifferent_le 已有证明体。
- [LocalDifferentUpperBound.lean](../LeanFormal/IUT/Foundations/LocalFields/LocalDifferentUpperBound.lean) 的 localDifferentPaperOrder_le_degree_padicVal 已专门接到实际 norm-integers、实际域次数和 localDifferentPaperOrder。对应 DAG 记录标为 PROVED。

其内部方法值得直接复用：\(\operatorname{Tr}(1)=[L:K]\) 给 different 的迹整除障碍，从 DVR 幂理想阶得相对 different 上界，再用 different/ramification 的塔公式归一化。它给
\[
d_L\le d_K+v_p([L:K])+1/e_K,
\]
覆盖论文需要的 tame-intermediate/Galois 情形，甚至不需要这些额外条件。

**无需重走 Kummer p 次扩张与 \(\epsilon\)-放大证明。** 新工作是将 Thm 1.10 里确切的域塔、degrees、ramification 实例接上，并核对 Step III/R4 的数值预算；不是再次证明 1.3(ii)。

### 6.4 命题 1.5：复张量/度量也不是空白

已有 [ArchimedeanTensorMetric.lean](../LeanFormal/IUT/IUTIV/Estimates/ArchimedeanTensorMetric.lean)：
complexTensorToProd_bijective、complexTensorToProd_inner，以及 primitive automorphism 的度量结论。

已有 [ArchimedeanMultiTensorMetric.lean](../LeanFormal/IUT/IUTIV/Estimates/ArchimedeanMultiTensorMetric.lean)：
characterMap_bijective、characterMap_inner、card_characterIndex、
characterMap_tprod_norm、directSumInner_map_primitive、decomposition_unique。

实际剩余路线：

1. 把原文每个 archimedean log-shell 的实际范围送入既有 character coordinates；若元素只有范数 \(\le\pi\)，使用乘积范数估计写 \(\le\) 版本，不硬套“每个范数恰好等于 \(\pi\)”的现有定理。
2. 使用原文 product-of-disks 容器 \(B_I\)，证明全体允许 primitive actions 保持它。
3. 把 Haar 以实际 \(B_I\) 为参照、按实维数归一化，证明
   \(\ell(\pi^{j+1}B_I)=(j+1)\log\pi\)。
4. 接 procession 平均得 \((l+5)\log\pi/4\)。

不必重新计算球的 Gamma 体积；参照体积在比值中消去。也不要换成任意 Euclidean ball 而遗漏 \(2^{|I|-1}\) 的度量转换。

### 6.5 命题 1.6 / 2.1(ii)：当前源码已经有原文所需粗界

Section2 的旧文件头 machine-gap 被后续更新覆盖。源码实际包含：

- theta_sixfold_window_le；
- theta_le_thirteen_tenths_mul_add：对 \(x\ge0\)，\(\theta(x)\le1.3x+300\)；
- iutIVProp21ii_theta_le_four_thirds_eventually：上界阈值取 9000；
- iutIVProp21ii_theta_two_sided_eventually；
- iutIVProp21ii_exists_prime_notMem_le_two_mul；
- iutIVProp16_primeCounting_le_four_thirds_eventually；
- iutIVProp16_index_le_four_thirds_nthPrime。

内部证明使用六倍窗口
\[
\theta(6n)\le\theta(n)+9n\log2
\]
的递推，再用 Abel 求和取得 \(4/3\) 素数计数界；本轮已读到证明体。

论文此处需要“存在阈值”以及固定系数 \(4/3\)，不要求另一个 Explicit estimates 文献中的特定巨大数值阈值。不要混淆“系数明确”与“所有阈值都必须给出特定数值”。因此本轮建议直接接现有 \(\eta_{\rm prm}\)，并处理 \(x<\eta_{\rm prm}\) 的原文分支；不新开完整 PNT 项目。

### 6.6 推论 2.2：沿真实初始数据与高度接入，不再做 citation schema

大致顺序是：

1. 从实际 Legendre/椭圆曲线输入确定坏素数有限集和真实高度 \(h=\log q^\forall\)，保留原文 compactly bounded、degree 与 j-invariant 条件。
2. 复用 Section2 的避开有限素集选素数定理，构造实际 \(l\)；逐项证明 C1 的 \(\sqrt h\le l\) 与上界，并构造需要的 torsion/field 数据。
3. 将真实 Thm 1.10 上界与 Cor 3.12 的另一侧接到**同一** q/height 读数，然后证明 C2。不能只完成 \(R\le\mathrm{Box}\) 就宣布这一步已得。
4. 复用已有 ArithmeticDivisorDegree 与 GenEll 的实际高度定义；对每项 BD 等价给出有界差的证据，追踪常数仅依赖哪些原输入。
5. 用 \(\log h/\sqrt h\to0\) 及有限阈值估计处理 \(\epsilon_E\le\epsilon\)，小高度部分进入受控例外范围。

S3131IUTIVCor22Cor23InputActual 的 Cor22Statement/Cor23Statement 只是任意 Prop 的原样包装，不是构造供体，不再派一个同类文件。

### 6.7 推论 2.3：复用装配，但有界差方向必须先按字面检查

GenEll09IUTIVSection2ConsumerActual 已有**条件装配**。因此不能把“再写一次 II-to-I 蕴含”的封装当新进展；剩下是原有几何归约与实际 Cor2.2 输出的证明。

交接时建议直接锁定最终读数：
\[
\exists C,\ \forall x,\quad
h(x)\le(1+\epsilon)(\operatorname{logdiff}(x)+\operatorname{logcond}(x))+C.
\]

本轮查到一个具体方向问题：S3136BDClassChainToolActual 的 IsBDLe f g 定义为
\(\exists C,\ g-f\le C\)，而 IV Cor2.3 原文说目标 RHS 减 height **有下界**。该工具的传递性本身没问题，但按名字把 IsBDLe height RHS 直接交给目标会反向。复用时必须按实际定义交换参数，或者由原 owner 连同消费者一起修正定义；不能只看“BDLe”名字拼接。

本轮只登记这一接口意见，没有改动它或扩大到完整 GenEll 审查。

## 7. 建议的最小实施包与实际消费者

以下是建议，未派发；不覆盖现有 owner。文件名为候选落点，不表示已创建 Lean 文件。

| 包 | 精确交付 | 候选落点 | 消除哪项输入 |
|---|---|---|---|
| P14-CARD | \(U/U_s\simeq(O/\mathfrak m^{es})^\times\)，实际阶 \((q-1)q^{es-1}\)，以及实际 QFE constructor | Foundations/LocalFields/IntegralLogShellCongruenceCardinality.lean | 已有 QFE 条件公式的自由 cardinality 输入 |
| P14-PGROUP | 实际 \(\Lambda/O\) 是有限 p-group；\(\#T=(q-1)p^m\)，其中 m 绑定实际 primaryComponent | Foundations/LocalFields/IntegralLogShellPrimaryTorsionCount.lean | 扭元阶假设；无需新 Teichmüller 机器 |
| P14-EXACT | 以实际 Haar 缩放和商环计数证 \(d=ef\)，再证 (P14ii) | Foundations/LocalFields/UnitLogLatticeNormalizedVolume.lean | 1.4(ii) 精确 log-volume 缺口 |
| P14-BOX-LOCAL | 从现有证明提取全部 latticeAut 版本，保持 (11) 原常数；补基准区域及 hull 包含 | IUTIV/Estimates/NonarchimedeanLogVolume.lean 或原 owner 的现有文件 | Step V 的局部解析估计输入 |
| STEP-V-SOURCE | 同一源对象的 q 幂赋值、允许像包含、R4 和实际 degree/readout 识别 | IUTIV/Estimates/StepVLocalLogVolume.lean 或现有源消费者 | distinguished-bound 平均定理的实际 bound 参数 |

P14-CARD 最适合作为下一个小包：目标明确，已有 DVR、residue 与 log 商供体，输出立即消掉已有结构的一项真实条件。随后 P14-PGROUP 和 P14-EXACT 完成 (ii)。

用户若优先要推进 \(R\le\mathrm{Box}\)，则 P14-BOX-LOCAL 可以先接，不以 P14-EXACT 完工为启动条件；仍保持本 chat 单线程顺序执行。

这些包的验收都应查看**最终定理的实际类型**：不能出现自由 hqfe、hTorsionCard、hVolumeFormula、hBound、任意 R/Box 读数 identification，或把结论藏进 Required/Nonempty。中间探索可条件化，最终必须提供来自原输入的构造。

## 8. 依赖 DAG 的数学内容

陈述依赖：

    实际有限 K/Qp、整数环、unitLog、unscaled L
        → 1.4(ii) 的归一化体积陈述
    实际 tensor、整数闭包、允许线性作用、原文 possible images
        → 1.4(iii)/(iv) 与 Step V 局部陈述
    同一初始 Theta-data 的读数与权重
        → 真实 R ≤ Box 陈述

证明依赖：

    现有深层 log 同构、有限核、有限商、Haar 指数
       + DVR 同余商计数
       + log 商为 p-group
       + 现有 Haar p 缩放
        → 1.4(ii)
        → tensor 格体积恒等式
        → 1.4(iii) 第一条上界

    现有不同理想乘法包含 + 现有 a/b 夹逼
       + 同一 tensor 的标量/赋值/质量计算
        → 1.4(iii) 第二条上界
        → 原文基准区域与 hull 包含
        → 实际 distinguished-slot bound
        → 现有加权平均与 processionAverage_eq
        → 真实 Box

第二条边不经过 1.4(ii)；这是本轮确认的主要剪枝。两条边都没有通过 P7 surrogate 的 C0=0 吸收，也没有自动证明 Cor 3.12 的另一侧不等式。

## 9. 应更新的旧判断

1. “1.4(ii) 必须先补 Hodge 剧场机器”对该局部公式不准确；当前证法是有限局部域、对数同余商与 Haar。
2. “没有 1.4 的任何估计”不准确；Iut 有第二条上界与未分歧情形的源码供体，但量词/构建/源识别仍要验。
3. “1.3(ii) 还缺 Kummer tower proof”不准确；实际局部域的 trace-degree 上界供体已经存在。
4. “1.5 没有复张量机器”不准确；分解、度量、primitive action、纯张量范数已有。
5. “仓库未形式化原文 1.6/2.1(ii) 所需粗素数界”不符合 Section2 当前后半内容。
6. “完成 A6 即完成 IV 上箱”不成立；本次明确只追真实 Box 及原文对象。

这些修订保留历史来源，不覆盖原注释。本轮没有把相关源码改成新的状态标签。

## 10. 本轮交付与验收状态

- 实际结果：给出 1.4(ii) 完整的自然语言构造证明、明确新叶子、现有供体位置，以及保持原文常数的 Step V 接入路线；其余项目按查重结果缩减。
- statement_compiles：NOT_RUN；本轮未新增 Lean 陈述。
- proof_body_checked：NOT_RUN；人工读了上述相关证明体和原文，不等于对新证明做 Lean 检查。
- kernel_closed：NOT_RUN。
- target_accepted：NOT_RUN；没有宣称 1.4、Thm1.10、Cor3.12 或 ABC 在本轮已闭合。
- 只读旧 olean 的存在信息不能代替当前源码版本构建；对应 DAG 的 PROVED 也是旧记录证据。
- 未改 Lean、未派发任务、未重分配 owner；只新增报告及节点、追加本 chat 的协调记录。
- 一个可执行下一步：在真实 Integers K 上完成 P14-CARD 的 quotient-units 同构与 \((q-1)q^{es-1}\) 计数，直接构造已有 LogShellQFECardinalityHypothesis，而不是再写接受它为参数的推论。

**本轮最有用的新连接是：已有 log 精确序列的商自动是有限 p-group，于是 residue 单位的 \(q-1\) 因子必然落在实际扭元阶中；它使 1.4(ii) 的精确负体积公式可以从已有对象内部算出。对真实 Box，则应同时利用原文实际采用的第二条容器上界，避免把不必要的前置工作排进关键路径。**
