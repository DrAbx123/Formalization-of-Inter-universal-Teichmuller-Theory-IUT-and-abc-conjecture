# P7 三个显式缺口：实际证明、较弱构造与消费者接法

日期：2026-11-14。负责人：本 chat 的 root，单线程。任务节点：`p7-three-gaps-closure-20261114`。

目标仍是从原文合格初始数据得到原文结论。新增 `hscale`、`htransport`、`hbridge` 后的条件定理不能算完成。下面区分已经实际检查的证明与尚待实现的构造，不把路线的存在当成证明已经完成。

## 1. 建议采用的主线

三个名称对应的工作性质不同：

| 缺口 | 本次结论 | 应采取的动作 |
|---|---|---|
| `qhatHaarScaling` | 找到了已有的无条件供体，并已实际编译一个不带缩放假设的证明 | 接 S865；同时消掉局部 degree、正测度和有限测度等技术参数 |
| 一般 place 的 `Ind1ShellTransportForRequired` | 应构造原文真实作用在单位模挠部分上的连续映射，再由对数有理化得到保持格的线性作用 | 不要求先得到局部域的环同构；索引重标记与实际纤维作用分开构造 |
| S1902 carrier bridge | 最有希望的主线是逐 `p,j,tuple` 的有符号读数与一侧区域包含，直接消费已有实际 Step-V hull 估计 | 不再要求整个 S1902 全局乘积与某一个局部张量块等价；旧 `s1915A0` 保留原定义，另行证明真正的论文读数链 |

后两项还没有无条件 Lean 闭合证据。本文给的是具体待证构造、其证明办法和消费者，不保证尚未完成的原文源构造会自动成立。尤其不能把“有单位商的接口”写成“已有原始 procession 作用的实际单位商映射”。

这一轮仅查三个接口的相关源文件、供体、消费者及本地 IUT III/IV 原文，没有重做全仓审查，也没有外部调研。现有 owner 的源码均未覆盖。

## 2. `qhatHaarScaling`：可以实际消掉的假设

### 2.1 对象与精确结论

固定原有 `T : SourceNativeInitialThetaData.{0} l` 及坏位 `b`。记

\[
L_b=\mathrm{rootNormedExtension}(T,b),\quad
O_b=\mathrm{rootExtensionUnitBall}(T,b),\quad
d_b=[L_b:\mathbf Q_{p_b}],\quad
a_b=\mathrm{c0QHat}(T,b).
\]

实际定义给出 `c0QLattice T b = (fun y => a_b * y) '' O_b`。目标就是

\[
\mu_b(a_bO_b)=\|a_b\|^{d_b}\mu_b(O_b),
\]

其中乘数在 Lean 中是 `ENNReal.ofReal (‖a_b‖ ^ d_b)`。这里的 `d_b` 是根扩张的真实局部次数，不能换成 base completion 的次数，也不能在全局求和前擅自省略。

### 2.2 完整证明链

1. `c0Alpha_ne_zero` 与 `c0QHat = c0Alpha ^ (2*l.value)` 给出 `a_b ≠ 0`。
2. 令 `lam := Units.mk0 a_b ha`。其单位作用 `lam • O_b` 正是实际集合 `c0QLattice T b`。
3. 已有 `S865RootHaarFactorNormPowActual.rootHaarFactor_normPow_actual T b lam` 给出
   \[
   \mathrm{rootHaarFactor}(\lambda)=\operatorname{ofReal}(\|a_b\|^{d_b}).
   \]
   S865 的证明已经走过实际根域的赋值环、单位/素元分解及 Haar 模数；这里无需重新证明一般 determinant-Haar 定理。
4. 已有 `rootHaarFactor_eq_ratio` 给出
   \[
   \mathrm{rootHaarFactor}(\lambda)=\mu_b(\lambda O_b)/\mu_b(O_b).
   \]
5. 已有 `rootExtensionUnitBall_measure_pos` 和 `rootExtensionUnitBall_measure_lt_top` 允许用 `ENNReal.div_mul_cancel` 消分母，得到目标。

这条链只用了当前实际对象的既有定理，没有新增 Class-B 缩放输入，也不需要跨载体等价。

### 2.3 本次可交接代码

文件：[QhatHaarScalingReuse.lean](D:/lean/tmp/sheaf/three_gap_closure_20261114/QhatHaarScalingReuse.lean)。命名空间：`LeanFormal.IUT.ThreeGapClosure20261114`。

包含以下声明：

- `qhat_haar_scaling_actual`：上述逐 `b` 缩放等式。
- `local_degree_pos`：真实根域局部次数为正。
- `qhat_lattice_measure_pos`：实际 q 格具有正测度。
- `qhat_lattice_measure_lt_top`：实际 q 格测度有限。
- `qhat_signed_readout_eq_log_norm`：消掉上述技术条件后的局部有符号读数等式。

最后一条的结论是

\[
\frac{\log\mu_b(a_bO_b)-\log\mu_b(O_b)}{d_b}=\log\|a_b\|.
\]

证明先用缩放公式展开左侧，再用 `Real.log_mul`、`Real.log_pow` 以及 `d_b>0` 消去次数。正性和有限性都从实际单位球及非零 `a_b` 得到，不由调用者提供。

**查重更新：**在本次工作期间，现有 hull 线也已写出 `Mzk1P0QHatHaarScalingActual.qhatHaarScaling_unconditional`，同样使用 S865 与 ratio。不能再派一个从零证明 Haar 缩放的任务。本 chat 的文件是独立检查及技术条件消除的交接供体；正式集成沿用现有 owner 的命名即可。

### 2.4 消费者怎样收口

`Mzk1P0QThetaReadoutCorrespondenceActual.qhatHaarScaling T` 是 `∀ b, ...`，可直接用 `fun b => qhat_haar_scaling_actual T b` 填充。其 `qhatLogReadout` 展开后就是本文件最后一条定理的左侧。

全局 `c0ProductQ_normalizedLog_eq_sum_qhat` 的原有参数按以下方式供应：

| 原参数 | 实际供体 |
|---|---|
| `hd b` | `local_degree_pos T b` |
| `hscale b` | `qhat_haar_scaling_actual T b` |
| `hQ0 b` | `(qhat_lattice_measure_pos T b).ne'` |
| `hQtop b` | `(qhat_lattice_measure_lt_top T b).ne` |
| `hO0 b` | `(rootExtensionUnitBall_measure_pos T b).ne'` |
| `hOtop b` | `(rootExtensionUnitBall_measure_lt_top T b).ne` |

这样原全局公式的这些输入都能由 `T` 派生。再复用已有 `productNormalizedLog_pi`，无需新证乘积 Haar。

接入时还要区分两件事：本定理计算 `log ‖c0QHat‖`；它与 P2/native q 读数之间的范数实例及规范化一致性，是既有 A2 供体的职责。这里没有把两种绝对值未经核对地视为相等。

本次看到的 correspondence 快照仍残留 Class-B 分支，并有局部 `b` 的输入用于全局 `∀ b` 的量词问题。建议 owner 接入无条件供体时移除这条新增证明依赖；不要继续维护一个比实际需要更强、又没有 inhabitant 的一般缩放接口。该文件还在活动编辑中，本 chat 没有修改它。

## 3. 一般 Ind1：从单位商得到线性传输，而不先强求域同构

### 3.1 先把需要证明的量词写对

当前 `Ind1ShellTransportFor places e φ` 要求

```text
∀ i v,
  CommonPrimeCompletion (places i v)
    ≃ₗ[ℚ_[p]]
  CommonPrimeCompletion (places (e i) (φ i v)).
```

但论文 Ind1 的 `e,φ` 来自真实 procession 的自同构。应证明的是：

```text
对每个原始数据允许的 procession arrow a，
构造 Ind1ShellTransportFor places (labelAction a) (placeAction a)，
并证明它保持真实 log-lattice，且与复合、逆和 tensor packet 相容。
```

这不是给论文额外加“存在传输”假设，而是从原文已经允许的作用本身构造传输。反过来，把任意集合置换都当成原文允许作用，会要求本来无关的局部域具有同维数，偏离原始目标。

还要注意：现有结构只要求 `≃ₗ`，没有“保持 log-lattice”字段。单独填一个任意线性等价，仍然不能供应 `FinitePlaceStepVAssembly` 所需的 `hΦ`。因此，应当在构造该等价的同一包中证明格相容性，而不是先用基选择填满结构再另找理由。

### 3.2 把纯重标记先剥离

令 `X := Sigma Va`，`σ := capsulePositionEquiv e φ`，`P : X → FinitePlaceAtPrime K p` 是原 place family。构造目标族

\[
P'(x):=P(\sigma^{-1}x).
\]

于是 `P'(σ x)=P(x)`；源、目标 completion 的传输是沿这条真实等式作类型搬运。该操作支持任意重标记，不要求原族满足 `P(σ x)=P(x)`。

这一步得到的是**原 packet 到重标记 packet**的映射。不能把目标偷偷改回原 packet。后续真正的 procession arrow 再给出重标记后纤维与目标纤维之间的实际作用。

已有 `SourceProcessionCapsuleData.PolyIsoAction` 的 `PermutedTensorPacket`、`tensorMap_tprod` 和 `tensorMap_tprod_distributed` 已采用自然的重标记目标。依赖 place 版本应沿这个模式接 `Equiv.sigmaCongr`、逐纤维 `piCongr` 和 tensor reindex；不用重写分配律。

### 3.3 最有价值的较弱对象：实际单位群模挠部分

对实际局部域 `F/Qp`，设

\[
U_F=O_F^\times,\quad W_F=U_F/\operatorname{tors}(U_F),\quad
\Lambda_F=\log(U_F),\quad I_F=(p^*)^{-1}\Lambda_F.
\]

已有定理提供以下真实构造：

| 供体 | 已有内容 |
|---|---|
| `IntegralUnitLogarithmKernel` | `unitLogHom_ker_eq_torsion`、`unitLogTorsionQuotientEquivRange` |
| `IntegralUnitLogarithmQuotientTopology` | 原始商拓扑到对数像拓扑的 `unitLogTorsionQuotientHomeomorph` |
| `IntegralUnitLogarithmRationalization` | `UnitLogPerfection F` 是原始单位加法化后的整数局部化；`unitLogPerfectionEquiv` 给出它与 `F` 的实际 `ℚ`-线性等价 |
| `IntegralUnitPerfectionTopology` | 由单位与分母定义的拓扑；`unitLogPerfectionHomeomorph` |
| `UnitPerfectionFunctoriality` / `UnitPerfectionMapTopology` | 已有由实际等距环映射诱导的单位局部化映射、连续性和复合律；可复用其局部化证明方式 |
| `GaloisFixedUnitLogarithm` | 原始 Galois 不变单位的实际下降及其对数像，不把整个 perfection 的不变部分误当作紧的 pre-log-shell |

因此，下一个有实质意义的构造不是“直接猜一个 completion 等价”，而是从实际源作用 `a` 构造连续群同构

\[
\beta_a:W_F\longrightarrow W_{F'}.
\]

这是比环同构弱得多的对象；一般 mono-analytic 作用无需保持域乘法。

### 3.4 有了实际单位商作用后，后半段怎样完整证明

以下是中间引理的完整数学证明方案。`β_a` 必须按下一小节由原始作用派生，不能留作最终定理的自由参数。

**第一步：对数像上的映射。** 用已证明的商到像等价定义

\[
f_0=\overline{\log}_{F'}\circ\beta_a\circ\overline{\log}_F^{-1}:
\Lambda_F\longrightarrow\Lambda_{F'}.
\]

`f_0` 是连续加法同构。这里无需为每个 `log u` 任意选择一个单位代表；商模型已处理所有根单位歧义。

**第二步：有理化。** 每个 `x∈F` 都可写为 `n^{-1}log(u)`，其中 `n` 是非零整数；这正是已有 `exists_integer_smul_eq_unitLog`。定义

\[
f(n^{-1}\log u)=n^{-1}f_0(\log u).
\]

若两个分式相等，交叉乘分母后在 `Λ_F` 中相等；加法同态 `f_0` 保持该等式，所以定义良好。逆映射由 `β_a^{-1}` 同样构造。Lean 可用 `IsLocalizedModule.map` 与已有 `UnitLogPerfection` 证明套路，不需要另建一套 completion。

**第三步：连续性及 `ℚp` 线性。** 在每个整数分母层上，映射是“连续 `f_0` 加非零标量缩放”；已有最终拓扑/对数 homeomorphism 给出 `f` 与逆的连续性。先有 `ℚ` 线性，再对 `c∈ℚp` 取趋于 `c` 的有理数列，利用连续性得到 `f(cx)=c f(x)`。不能把仅有 `≃ₗ[ℚ]` 直接当作 `≃ₗ[ℚp]`。

**第四步：格保持。** 按定义 `f(Λ_F)=Λ_F'`，又因为同一个 `p` 下 `p*` 相同且 `f` 为 `ℚp` 线性，得到 `f(I_F)=I_F'`。这样同时供应现有 shell transport 与 Step-V 的单位对数格条件。

**第五步：组合与 tensor。** 商映射、局部化映射的复合律给出 `f_(ba)=f_b∘f_a`，逆和恒等也一样。逐纤维取直积线性等价，再取真正的 tensor map；纯张量上逐因子验证即可证明整个 tensor 格保持。用 `FiniteTensorProductDistribution.tensorProductLinearEquiv_tprod` 检查分配方块。

这些步骤没有使用完成域的环同构，也没有用任意选基代替真实作用。

### 3.5 真正还要补的源端：怎样得到 `β_a`

这一点不能掩盖。现在的 `DPrimeStrip` / `DPrimeStripEquiv` 只是群、投影及群同构的代数核心；其定义没有拓扑、实际整数单位、局部 reciprocity 或完整重构算法。不能只从这个抽象类型的字段推出上述连续单位商作用。

应沿已经存在的对象做如下工作：

1. 在实际 arithmetic realization 上，确认 source monoid 的单位确实对应实际 `O_F^×`，或直接对应 `W_F`。`sourceLocalLogShellDatum` 已给出具体 log-shell 校准；这里新增的是**作用与这份校准的交换方块**。
2. 对有实际 `FPrimeStrip` 箭头的部分，用其 `isoMon` 诱导 `Units.mapEquiv`，再用现有 `TimesMuQuotient.congr` 除去挠元。`SourceFTimesMuPrimeStripEquivalence.canonicalLift` 已有这个代数层步骤，不应重写。
3. 在实际拓扑上证明该映射连续，且保持原始单位层。若先在代数闭包的单位层构造，利用等变性和 `baseUnitsGaloisFixedEquiv`/`galoisFixedUnitLog_range` 下降到原始不变单位；不能把“有理化后所有不变量”直接当成原始单位群。
4. 对真正只以 `D⊢` 数据给出的 mono-analytic 箭头，落实 III Prop 1.2(vi) 的实际重构到这个单位商层，并保留其 Ism 轨道。目标可以限制为“实际单位商及紧子群的函子性”，无需先重构全域乘法。**这一步在本次检查的源文件中没有发现无条件 inhabitant，仍是要证明的算术节点。**
5. 验证全部论文允许的 procession 作用都在上述构造范围内。只完成域自同构诱导的作用，不能当成全体 Ind1 已覆盖。

旧 `SourceLogShellXMuChainSupply` 和 `SourceLogShellXMuChainActionCompatibility` 提供条件装配，文档也明确标出原算法与拓扑的缩减。它们可作为消费者规格；本身不能充当第 4 步的证明。

**具体第一包建议：**实现“实际单位商连续同构 → `ℚp`-线性、保持 `unitLogLattice` 的传输”的通用引理，同时在一个真实非恒等 source arrow 上构造 `β_a` 并验证方块。前半段能直接复用上述供体；后半段必须以源箭头的已有字段和实际构造为输入。最终原文定理不能仍带一个 `β_a` 或 `htransport` 参数。

### 3.6 为了 Box，可以进一步避免选一个 canonical 代表

Step-V 的估计对所有保持实际单位对数格的线性自同构统一成立。因此可在正确 packet 上构造

\[
\Phi_{\max}=\{g\in\operatorname{GL}_{\mathbf Q_p}(A):g(U_A)=U_A\}.
\]

恒等元证明它非空；所有实际 Ind1/Ind2 作用通过前述构造落入其中。扩大到这个作用族会扩大 possible-image hull，因而适合求**上界**。这避免了为了上界先选择唯一 canonical Ism 代表，也避免先证明实际作用族恰等于某个全自同构群。

但 `g(U_A)=U_A` 必须由真实作用证明，不能仅因定义 `Φmax` 就宣布所有源作用属于它。若作用改变 tuple，先作对应 packet/block 的传输及索引重排；不能未经证明把跨块作用写成单个固定块的自同构。

对域自同构诱导的子类还有较短实现：从 `w=σ(v)` 证明标准绝对值相容，延拓到 completion，随后复用 `IntegralUnitLogarithmFunctoriality.unitLog_map`。它适合首个非恒等测试实例，但不足以替代一般 mono-analytic 路线。

## 4. S1902：用带索引的读数与 hull 上界绕开过强 carrier 等价

### 4.1 实际供体比“局部估计尚缺”更前进了一步

`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean` 已有完整证明体：

- `arithmeticTuple_stepV_normalizedLogVolume_le_paperBound`：possible images 中任意正测度集合的上界。
- `arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound`：非空作用族的 possible-image **holomorphic hull** 上界。

第二条正是应优先消费的定理。它已经处理 hull 正测度、共同容器及最终上界，不能再派从零重证这些部分的任务。

在实际块 `A=⊗_i K_i` 上，它给出

\[
V_A(H)\le
\left(-\operatorname{ord}_p(\varpi)+\sum_i\operatorname{ord}_p(\delta_i)+1\right)\log p
+\sum_{i\in I^*}(3+\log e_i),
\]

其中 `H` 是 `Φ` 对 `ϖ·O_hol` 的 possible-image hull，`Φ` 保持实际 `arithmeticTupleUnitLogLattice`，`I*` 包含所有 `e_i>p−2` 的因子。`δ_i` 是已有实际 different 元素。

`Mzk1IutIVProp14iiiBoxFormalActual` 已经是前一条定理的包装。`BoxReadout`、`S1915BoxConsumer` 则仍把区域和读数识别作为字段；字段能声明不等于该识别已构造。

### 4.2 对接对象必须保留的三种信息

S1902 当前为

\[
X=\prod_{b\in Bad}L_b,\qquad
r_b=\max_j\|\alpha_b^{j^2}\|,
\]

而 S1915 已证明其旧读数形状为

\[
\mathrm{s1915A0}=\max\left(0,1+\sum_b d_b\log r_b\right).
\]

论文 IV Step (iv)–(v) 则先固定有理素数 `p`，再固定标签 `j`，再固定 `j+1` 个实际局部位置组成的 `tuple`。其 volume 是有符号、按维数归一化的局部 log-volume；随后作指定权重平均。

因此应保留：

1. **prime 分组**：不同 `p` 的局部块分开建，再按论文的全局读数相加；不要恢复 `NativeBadModuliFixedPrime`。
2. **标签 `j`**：负项来自 `j²/(2l)`。提前取 `max_j` 会丢掉后面平均所需的数据。
3. **signed volume 与维数**：不得先 `ENNReal.ofReal` 截断，再把结果当成可为负的局部量。

这不是要求修改旧 S1902 对象的定义。应保留它及其已证结论，利用底层仍保留的逐标签根值，构造适合原文消费者的细化数据。任何新读数与原文 `R` 的关系仍须证明；不能新定义一个容易估计的 `Rnew` 后把它叫作原来的 `R`。

### 4.3 推荐路线 A：实际 tensor 上直接构造允许区域

**A1. 固定正确的局部域族。** 对 `p,j,tuple`，按原文取 `K_i=K_{v_i}`，定义真实 `ArithmeticTensorTupleBlock`。本地原文 IV pp.27–28 明确使用 `K_{v_i}`，不是任意选一个 `F` 的 completion。现有 `qVFamTensorBlock` 是每个坏位的单因子 `F`-completion 模型，不自动等于完整的 `j+1` 因子块。

这里应直接复用 `SourceLogShellFamilyDependent` 和 `FiniteTensorProductDistribution` 的 actual packet 对齐。它们已经建立 tensor 与逐 tuple 分解；新增工作是原文该组 `K_{v_i}` 的源识别，而非另证一般分配律。

**A2. 构造实际 distinguished scalar。** 取 `i†=j`。好位取 `ϖ=1`；坏位使用该实际 `K_{v_j}` 中的 theta 值，并证明

\[
\operatorname{ord}_p(\varpi)
=\frac{j^2}{2l}\operatorname{ord}_p(q_{v_j}).
\]

根值的存在和上述等式必须沿实际 theta/pilot 评价、源局部域及其范数得到。已有 `rootNormedElement_pow` 与 S865 可供给根域侧计算；不能由“在另一个根扩张里存在”直接推出“在当前 tensor 因子中存在”。若原文合格数据含有相应 torsion/root 实现，应实例化并证明映射兼容，而不额外假设 `∃ϖ`。

**A3. 构造作用族。** 对实际源 Ind1/Ind2 使用第 3 节的对数格传输，或扩大到 `Φmax`。用恒等元给出非空性；逐生成元证明格保持。这里不需要它们都是代数自同构。

**A4. 证明实际允许像落入共同容器。** 对每个源 theta-pilot 生成元，写出它在正确 tensor packet 的值；Ind1/Ind2 通过 `Φ` 作用处理。Ind3 要按 Step (v) 的非正整数 `p` 次幂扩张及上半相容性接入。

必须分两种情况：若实际源像已落入 `Φ(ϖ O_hol)` 的并，直接使用 hull 版本；若还经过 Ind3 扩张，则复用该文件的 Step-V endpoint 包含与 `arithmeticTupleHolomorphicHull_subset_smul`，在同一个已计算容器上证明覆盖，再使用现有 volume 上界。不能把张量 log-region 的 `rfl` 包含当成全部 Ind3 已处理。

**A5. 汇总局部量。** 对每个块定义实际 signed readout

\[
V_{p,j,\tau}(S)
=\frac{\log\mu_{p,j,\tau}(S)-\log\mu_{p,j,\tau}(O_{hol})}
{\dim_{\mathbf Q_p} A_{p,j,\tau}}.
\]

使用论文指定的 block/地方次数权重。有限直积的基本计算为：令 `dτ=dim Aτ`，`D=Στ dτ`，则

\[
\frac1D\log\frac{\prod_\tau\mu_\tau(S_\tau)}{\prod_\tau\mu_\tau(O_\tau)}
=\sum_\tau\frac{d_\tau}{D}V_\tau(S_\tau).
\]

这条恒等式说明为何不能把一个未除总维数的 product log，直接当成某一块的 normalized log。具体论文权重是否就是这组 `dτ/D`，要通过实际地方次数/重复位置的计数证明，并复用已有权重供体。

**A6. 接已有平均链。** 使用 `StepVDistinguishedSlotAverage.weightedAverage_le_of_distinguishedBound`，只需要原本 distinguished slot 上的实际上界；不必新增“每一个 tuple 在所有 slot 上同时满足同一个界”的假设。再接 `StepVProcessionAverage.processionAverage_eq`，保留

\[
\operatorname{Box}=\frac{l+5}{4}D-\frac{l+1}{24}Q+S+(l+5)T.
\]

例如 `l=5`，标签为 `1,2`，`(j²/(2l))` 的平均是 `(1+4)/20=1/4=(l+1)/24`。这也是一个简单的语义检查：提前只留下最大半径时，不会自动恢复该平方平均。

**A7. 证明原文读数对应。** 最后要有一条从实际源 construction 得出的 `R` 等于上述加权读数，或 `R` 不超过该读数的定理。它的证明应展开真实评价、真实区域包含和归一化，不把此结论本身当成 `bridge` 字段输入。

这样 carrier 等价不再是必需证明依赖；取而代之的是更直接、能够消费实际估计的“生成元评价 → 区域包含 → signed readout → 平均”。A2/A3/A4/A7 仍需实现，本文不把它们登记为闭合。

### 4.4 S1902 已有数据怎样真正派上用场

不要只拿 `s1915A0` 一个数。逐 `b,j` 定义已有根元素的主格

\[
H_{b,j}=\alpha_b^{j^2}O_{L_b}.
\]

S865 对任意非零元素适用，因此有

\[
V_{L_b}(H_{b,j})=\log\|\alpha_b^{j^2}\|
=\frac{j^2}{2l}\log\|q_b\|.
\]

第二个等号由 `α_b^(2l)=q_b`、非零性、`log_norm_pow` 的计算及实际范数实例一致性得到。它不需要 `L_b ≃ F_b`，也不需要 root extension 和原 tensor block 具有相同 finrank。

这给出了**逐标签 scalar 读数字典**。随后应把同一 theta 值的实际 source 评价接到 A2，并把作用后的区域接到 A4。该等式本身尚不说明“根域上的所有允许像”与“原 tensor 中所有允许像”相同。

现有 `Mzk1A1DeltaExplicitActual` 的局部 q 格与最大半径比较、`Mzk1P0RouteC0GlobalReadoutActual` 的 `normalizedLog(Q)≤s1915ClosedForm−1` 继续保留为有效供体。但它们没有提供完整 `j`-procession 的平方权重，不能仅靠对已经取完最大值的数做代数整理补回。

### 4.5 推荐路线 B：相对格指标 / determinant 读数，进一步减少等价需求

若源 tensor 的实际线性传输已存在，而 holomorphic 参照格的精确像难对齐，可以只比较相对格指标。

设同一有限维 `ℚp` 空间中 `Λ,O` 为满秩紧开 `ℤp` 格，选择共同有限指数子格 `N⊆Λ∩O`。则

\[
\log\mu(\Lambda)-\log\mu(O)
=\log[\Lambda:N]-\log[O:N].
\]

这来自两个有限陪集分解，自动消去 Haar 的任意正比例常数。用实际 `ℤp` 基写成矩阵，则等于 `log |det M|p`。完整的相对指标不依赖所选共同子格或基。

然后利用两条结构公式：直积的 log 指标相加；张量线性变换满足 `det(f⊗id_W)=det(f)^(dim W)`。除以真实总维数后，得到正确逐因子归一化。这是处理 degree/determinant 因子的地方，不需要把 root product 和 tensor carrier 硬认成同一代数。

已有 `Mzk1P3HaarScaleFactorLogActual.logMass_eq_add_log_addHaarScalarFactor` 处理 Haar 比例；`FinitePlaceStepVAssembly` 已处理实际容器。需要新增的是实际源格/比较格、实际矩阵或有限指数、以及源允许像的包含证明。

这条路线可给一侧上界，而不要求区域完全相等。不过不能把任意 dimension 不同的两格的指标直接相等；它们之间必须来自实际乘积/张量/标量扩张计算，并记录所有次数和参照格项。

对根域下降到 base 的 ceil/floor 主格也一样：取整误差必须进入明确预算，不能宣称自动被 `S` 或 `T` 吸收。能用 A 路线的正确原文局部域和精确 theta scalar 时，应优先避免额外引入这项误差。

### 4.6 对当前 Box 消费者的具体修改建议

建议新增实际 packet 级消费者，其输入仅为原文合格数据和原文索引；局部 `μ`、`ϖ`、`Φ`、`H`、exceptional 集及权重都由构造给出。证明中调用现有 Step-V hull 定理及既有平均公式。

`BoxReadout` 可保留为通用辅助接口。`S1915BoxConsumer.a0_eq` 不能继续被视为一个只需填 `rfl` 的小缺口；它把一个全局、截断且含常数 1 的数，接成单个 prime/tuple 的 signed volume。应由上述实际读数链说明它在什么消费者中有用，而不围绕该字段强造一个集合来实现所需数值。

如果项目锁定的最终目标字面上包含旧 `s1915A0`，本建议本身并未授权改变它。必须另证旧目标与原文目标的关系，并重新通过目标 comparator 和语义审查。保留旧对象、增加正确的中间消费者，不等于旧目标已获证明。

## 5. 接下来可以交接的工作顺序

沿用已有 owner；下表是建议，没有在本 chat 派发新 agent 或覆盖别人的工作。

| 顺序 | 实际交付 | 直接复用 | 减少的缺口 |
|---|---|---|---|
| 1 | 接入无条件 qhat scaling、局部次数及测度技术条件 | 本包验证文件、S865、原 product log 公式 | 删除 correspondence 的 `hscale/hd/hQ/hO` 自由输入 |
| 2 | 一个真实非恒等 source arrow 的单位商映射及连续性；写出对数方块 | `TimesMuQuotient.congr`、实际 units/descent、商 homeomorphism | 开始构造 Ind1 实际 inhabitant，而非再包装 `Nonempty` |
| 3 | 单位商作用有理化、提升到 `ℚp`、证明格保持和 tensor 方块 | 原 unit perfection、source packet、tensor distribution | 同时供应 `Ind1ShellTransportFor` 与 Step-V 的 `hΦ` |
| 4 | 在原文 `K_vi` 的一个实际 `p,j,tuple` 中构造 distinguished theta scalar，核对其 `j²/(2l)` order | 根值幂等式、已有 P2 范数字典、实际 source evaluation | 删除局部 scalar 的存在假设，厘清 S1902 与原 tensor 的接点 |
| 5 | 对实际全部允许像证明共同容器包含；接 Ind3 扩张 | StepV endpoint、holomorphic hull minimality、已有 local bound | 得到真正原文对象的逐块上界 |
| 6 | 逐块 signed volume → 正确地方权重 → distinguished-slot 平均 → label 平均 | P3、StepVDivisorAverage、StepVDistinguishedSlotAverage、StepVProcessionAverage | 保留负 Q 项地得到真实 Box 消费链 |
| 7 | 冻结原目标类型，检查源覆盖、所有实际构造、传递公理及原文语义 | 项目既有 comparator/验收机制 | 才能标记原目标完成 |

第 2–3 项共同构成 Ind1 主线；第 4–6 项构成 carrier bridge 的替代主线。它们共享格保持方块，因此优先解决真正的单位商作用，比独立追逐一个全局 `blockEquiv` 更能同时推进两个缺口。

## 6. 验证与证据边界

本包 Lean 检查命令：

```powershell
python -X utf8 -B tools/lean_auto.py repair tmp/sheaf/three_gap_closure_20261114/QhatHaarScalingReuse.lean --runtime tmp/lean-automation/three-gap-closure-20261114 --timeout 180 --wait-timeout 30
```

初版单条 scaling 证明已返回 `green`、`cached=false`、`exit=0`，未发现 stale imports，`#print axioms` 为 `[propext, Classical.choice, Quot.sound]`。加入四个技术条件/读数声明后的最终验证结果在交付前补录到本节及 DAG。

本次没有运行全 Project、原目标 comparator 或独立原文审查。其余供体的状态依据本次读取的证明体及既有记录，不冒称全部重新构建。Ind1 与完整 S1902/原文读数桥均未标记为闭合；也没有宣称 `R≤Box`、Corollary 3.12 或 ABC 已完成。

本地原文定位：IUT III Prop 1.2(vi)，文本约 1898–1949 行；Thm 3.11(i)，文本约 9170–9305 行；IUT IV Thm 1.10 Step (iv)–(v)，印刷 pp.27–28，文本约 1590–1783 行。相关源文件、版本哈希与工具结果见本包 DAG 节点。
