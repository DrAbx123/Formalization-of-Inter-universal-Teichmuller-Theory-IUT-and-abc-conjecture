# P7 三个显式缺口：实际证明、较弱构造与消费者接法

日期：2026-11-14。负责人：本 chat 的 root，单线程。任务节点：`p7-three-gaps-closure-20261114`。

目标仍是从原文合格初始数据得到原文结论。新增 `hscale`、`htransport`、`hbridge` 后的条件定理不能算完成。下面区分已经实际检查的证明与尚待实现的构造，不把路线的存在当成证明已经完成。

**最新指令与进展修订：**用户已要求只提供重要思路、不再编译；本 chat 的后续编译进程已停止。用户随后提供的 Ind1 下游与 `Mzk1BoxReadoutLocalActual` 进展已纳入。不要按本文较早的数学分解重复派发这些已有后半段；当前重点是第 7 节的源端缩减，以及第 8 节从原文 torsion 数据推出根值落入 `K_v` 的具体证明。

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

**按用户最新状态修正：**`Mzk1Ind1LogLatticeActionActual`、`Mzk1Ind1UnitQuotientActual` 及 `ContinuousRationalPadicScalars` 已提供后半段的供体/装配，不再派发重做任务。第 3.4 节保留为数学说明。当前第一包应直接构造真实源箭头的 `β_a`，优先采用第 7 节的较弱目标；最终原文定理不能仍带一个 `β_a` 或 `htransport` 参数。

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

用户最新进展中的 `Mzk1BoxReadoutLocalActual` 已新增实际 packet 级消费者和 signed readout；不再建议重写这层包装。下一步应从原文合格数据及原文索引构造它的局部 `μ`、`ϖ`、`Φ`、`H`、exceptional 集及权重，并消费现有 Step-V hull 定理及既有平均公式。

`BoxReadout` 可保留为通用辅助接口。`S1915BoxConsumer.a0_eq` 不能继续被视为一个只需填 `rfl` 的小缺口；它把一个全局、截断且含常数 1 的数，接成单个 prime/tuple 的 signed volume。应由上述实际读数链说明它在什么消费者中有用，而不围绕该字段强造一个集合来实现所需数值。

如果项目锁定的最终目标字面上包含旧 `s1915A0`，本建议本身并未授权改变它。必须另证旧目标与原文目标的关系，并重新通过目标 comparator 和语义审查。保留旧对象、增加正确的中间消费者，不等于旧目标已获证明。

## 5. 接下来可以交接的工作顺序

沿用已有 owner；下表是建议，没有在本 chat 派发新 agent 或覆盖别人的工作。

| 顺序 | 实际交付 | 直接复用 | 减少的缺口 |
|---|---|---|---|
| 1 | 接入无条件 qhat scaling、局部次数及测度技术条件 | 本包验证文件、S865、原 product log 公式 | 删除 correspondence 的 `hscale/hd/hQ/hO` 自由输入 |
| 2 | 从真实源作用构造单位商的代数同构；连续性用第 7.1 节自动推出 | 实际单位对数格、既有下游；源端可选惯性阿贝尔化/有限 Kummer 路线 | 开始构造 Ind1 实际 inhabitant，而非再包装 `Nonempty` |
| 3 | 将已有 Ind1 下游实例化到上述真实作用，核对全部作用覆盖及 tensor 方块 | `Mzk1Ind1LogLatticeActionActual`、`Mzk1Ind1UnitQuotientActual`、source packet | 同时供应 `Ind1ShellTransportFor` 与 Step-V 的 `hΦ`；不重写一般理论 |
| 4 | 按第 8 节 torsion—Tate—固定域证明，在原文 `K_vi` 中得到 distinguished scalar 及 `j²/(2l)` order | `T.clauseB.q_comparison`、`T.clauseC` 的 torsion/kernel field、已有根值 | 删除局部 scalar 的存在假设，厘清 S1902 与原 tensor 的接点 |
| 5 | 对实际全部允许像证明共同容器包含；接 Ind3 扩张 | StepV endpoint、holomorphic hull minimality、已有 local bound | 得到真正原文对象的逐块上界 |
| 6 | 逐块 signed volume → 正确地方权重 → distinguished-slot 平均 → label 平均 | P3、StepVDivisorAverage、StepVDistinguishedSlotAverage、StepVProcessionAverage | 保留负 Q 项地得到真实 Box 消费链 |
| 7 | 冻结原目标类型，检查源覆盖、所有实际构造、传递公理及原文语义 | 项目既有 comparator/验收机制 | 才能标记原目标完成 |

第 2–3 项共同构成 Ind1 主线；第 4–6 项构成 carrier bridge 的替代主线。它们共享格保持方块，因此优先解决真正的单位商作用，比独立追逐一个全局 `blockEquiv` 更能同时推进两个缺口。

## 6. 验证与证据边界

本包 Lean 检查命令：

```powershell
python -X utf8 -B tools/lean_auto.py repair tmp/sheaf/three_gap_closure_20261114/QhatHaarScalingReuse.lean --runtime tmp/lean-automation/three-gap-closure-20261114 --timeout 180 --wait-timeout 30
```

初版单条 scaling 证明已返回 `green`、`cached=false`、`exit=0`，未发现 stale imports，`#print axioms` 为 `[propext, Classical.choice, Quot.sound]`。加入四个技术条件/读数声明的第二次检查在正测度证明的 `ENNReal` API 使用处失败；其后源码已作局部修正，但用户要求停止编译，因此最终整文件版本**未完成验证**。不能将当前五条声明一起标为 green。第 2 节的代码清单是交接源码，不代表五条都已完成本版本验收。

本次没有运行全 Project、原目标 comparator 或独立原文审查。其余供体的状态依据本次读取的证明体及既有记录，不冒称全部重新构建。Ind1 与完整 S1902/原文读数桥均未标记为闭合；也没有宣称 `R≤Box`、Corollary 3.12 或 ABC 已完成。

本地原文定位：IUT III Prop 1.2(vi)，文本约 1898–1949 行；Thm 3.11(i)，文本约 9170–9305 行；IUT IV Thm 1.10 Step (iv)–(v)，印刷 pp.27–28，文本约 1590–1783 行。相关源文件、版本哈希与工具结果见本包 DAG 节点。

## 7. 源端 `β_a` 的进一步缩减：不必先补齐整个 arithmetic monoid

这一节是在用户给出最新 A/B 状态之后补充的重点。它没有调用新的编译，也不把源端缺口改名后交回给调用者。

### 7.1 第一个重要缩减：实际单位商上的同构自动连续

固定有限扩张 `F/Qp`，令 `W_F=O_F^×/tors`。已有商对数 homeomorphism 将 `W_F` 识别为 `Λ_F=log(O_F^×)` 的加法群及其原始拓扑。`Λ_F` 是 `F` 中紧开加法格：紧性来自单位群；它包含一个非零的 `p` 幂乘整数环，由已有局部 log/exp 逆映射得到开放性。

因此

\[
W_F\supset pW_F\supset p^2W_F\supset\cdots
\]

是零点邻域基。这里 `p^nW_F` 是加法记号，即乘法商群中的 `p^n` 次幂像。

现在只给一个**抽象群同态** `β:W_F→W_F'`。它自动满足

\[
\beta(p^nW_F)\subseteq p^nW_{F'}.
\]

对目标任意零点邻域，取其中的某个 `p^nW_F'`，原像至少包含开邻域 `p^nW_F`。故 `β` 在零点连续，继而处处连续。若 `β` 是群同构，其逆也连续。甚至不需要先选基、先证两边次数相等。

随后由整数倍连续延拓，`β` 在对应格上自动为 `ℤp` 线性；有理化后就是 `ℚp` 线性。于是当前源端需求可实质缩小为：

> 从原文真实作用构造实际 `W_F` 之间的代数群同构。连续性、`ℤp` 线性及有理化后的 `ℚp` 线性不是三个额外独立的算术输入。

这个论证仅适用于**已经识别为实际单位模挠群**的对象，不适用于任意 `DPrimeStrip.G`。也不能凭它宣称任意抽象绝对 Galois 群同构连续；原文 Galois 箭头的 profinite 连续性仍应从原文允许的箭头类别来实化。

#### 7.1.1 针对 wild homomorphism 疑问的复核（2026-11-14）

**复核结论：保留上述数学结论，明确其范围和验证状态。** 对固定素数 `p`、有限自然数 `d,e`，标准 p-adic 拓扑下的任意加法群同态

\[
f:(\mathbf Z_p^d,+)\longrightarrow(\mathbf Z_p^e,+)
\]

都是连续的，进而是 `ℤp` 线性的。这里不存在以同样有限秩 p-adic 整数格为目标的不连续群同态。仅有数学证明；本 chat 没有将该引理写成并核验为 Lean 定理，原文 Ind1 的 `β_a` 也尚未由此构造。

**直接证明，不预设连续性或 `ℤp` 线性：**

1. 群同态保持整数倍，因此 `f(p^n x)=p^n f(x)`。
2. 若 `x−y∈p^nℤp^d`，取 `z∈ℤp^d` 使 `x−y=p^n z`。于是
   \[
   f(x)-f(y)=p^nf(z)\in p^n\mathbf Z_p^e.
   \]
3. `p^nℤp^d` 和 `p^nℤp^e` 分别构成零点邻域基。因此对目标邻域 `p^nℤp^e`，其原像包含源的开邻域 `p^nℤp^d`，这就是零点连续性；群同态随后处处连续。在标准坐标的 sup norm 下，实际还得到 `f` 为 1-Lipschitz。

还可完全不用极限交换，直接证明矩阵刻画。设 `A` 的第 `i` 列为 `f(e_i)∈ℤp^e`。对任意 `x∈ℤp^d` 和 `n`，选择整数向量 `r_n∈ℤ^d`，使 `x−r_n∈p^nℤp^d`。整数线性给 `f(r_n)=Ar_n`，所以

\[
f(x)-Ax
=\bigl(f(x)-f(r_n)\bigr)-A(x-r_n)
\in p^n\mathbf Z_p^e.
\]

对所有 `n` 成立，而 `⋂_n p^nℤp^e={0}`，故 `f(x)=Ax`。因此

\[
\operatorname{Hom}_{\mathbf Z}(\mathbf Z_p^d,\mathbf Z_p^e)
=M_{e\times d}(\mathbf Z_p).
\]

若 `f` 是群同构，其逆同样满足上述结论，两矩阵互逆；尤其 `d=e`，且矩阵属于 `GL_d(ℤp)`。这一证明没有把待证的连续性藏进定义。

**应用到实际 `W_F` 时的拓扑责任：**不能只拿一个抽象群等价 `W_F≅ℤp^d` 就随意指定拓扑。应使用已经存在的 `unitLogTorsionQuotientHomeomorph`，把原始商拓扑识别为 `Λ_F=log(O_F^×)` 的子空间拓扑。由于 `Λ_F` 紧且含有 `p* O_F`，它是紧开加法格。乘以非零的 `p^n` 是 `F` 的 homeomorphism，故 `p^nΛ_F` 开；紧性给出范数上界 `R`，而 `p^(−n)R→0`，所以这些子群构成邻域基。原第 7.1 节的论证由此适用于实际单位商，不必预先选择格的基。

**wild 同态在哪些对象上出现：**`ℚp` 作为 `ℚ` 向量空间确实有不连续的加法自同构。例如取 `a∈ℚp\ℚ`，将 `{1,a}` 扩充成 Hamel 基，定义一个 `ℚ`-线性自同构固定 `1` 和其他基向量、把 `a` 送到 `2a`。若它连续，由 `ℚ` 稠密且它在 `ℚ` 上是恒等映射，就必须在全部 `ℚp` 上恒等，矛盾。这个例子不能保持 `ℤp` 到自身：若保持，其限制由上述证明连续，再用 `ℚp=⋃_n p^(−n)ℤp` 及有理线性推出整个映射连续，仍矛盾。

因此，“一般抽象群同态不保证连续”正确；但不足以反驳当前**两端都是实际有限秩单位格、固定同一 p、使用原始 p-adic 拓扑**的具体命题。对无限直积、未识别拓扑的源群或有理化后的任意映射，不使用此自动连续性结论。

验收标记保持：自然语言证明经本 chat 自审；`statement_compiles=NOT_RUN`、`proof_body_checked=NOT_RUN`、`kernel_closed=NOT_RUN`、`target_accepted=NOT_RUN`。用户要求不编译，本次仅更新证明说明和研究记录。

### 7.2 首选源路线：用惯性在阿贝尔化中的像，绕开 `isoMon`

对实际局部域 `F`，在其真实绝对 Galois 群中定义

\[
G_F=\operatorname{Gal}(\overline F/F),\quad
I_F=\ker(G_F\to G_{k_F}),\quad
J_F=\operatorname{im}(I_F\to G_F^{ab}).
\]

这里必须使用 **`I_F` 在 `G_F^{ab}` 中的像**，而不是 `I_F^{ab}`；后者通常大得多。阿贝尔化也应是 profinite 阿贝尔化，即除以交换子群的闭包。

所需算术识别是实际局部 Artin 映射的单位限制

\[
\rho_F:O_F^\times\xrightarrow{\sim}J_F,
\qquad
\bar\rho_F:W_F\xrightarrow{\sim}J_F/\operatorname{tors}(J_F).
\]

一旦在仓库内部证明这条识别，而原文作用 `a:G_F≅G_F'` 保持实际惯性，就可以**定义**

\[
\boxed{\beta_a=\bar\rho_{F'}^{-1}\circ
  (a^{ab}|_{J}/\operatorname{tors})\circ\bar\rho_F.}
\]

这个构造用到 `a` 的真实群同构，不要求 `a` 来自域同构，也不要求将 `a` 提升成完整 `FPrimeStrip.isoMon`。所有群同构都保持挠子群，所以模挠这一步不增加条件。组合律由三个映射的复合直接得到。

这条路线把“大而杂的 monoid/拓扑/重构”拆成两个真正的算术定理：**惯性可由实际 Galois 群识别**，以及**实际单位群与惯性阿贝尔像的对应**。最终不能把这两条当自由字段输入；它们是新源节点中要在内部证明的叶子。

### 7.3 惯性保持不是随口增加的假设：一个可落实的群论证明

可以先在真实局部 Galois 群建立标准 tame 描述。记 `P_F` 为 wild inertia，`q=|k_F|`。其 tame 商具有形状

\[
G_F/P_F\simeq T\rtimes\widehat{\mathbf Z},
\qquad T=\prod_{\ell\ne p}\mathbf Z_\ell(1),
\]

Frobenius 对 `T` 的作用是乘以 `q`。下面的刻画不需要给定一条额外的“作用保持惯性”证书。

**第一步：`P_F` 是最大的闭正规 pro-p 子群。** 若 `N` 是闭正规 pro-p 子群，把它映到 tame 商。其与 `T` 的交是平凡的，因为一个群不能同时是非平凡 pro-p 与 pro-prime-to-p 群。正规性于是使 `[N,T]` 平凡。因此 `N` 的 Frobenius 投影在 `T` 上作用平凡。Frobenius 在全部 prime-to-p 根单位上的作用是忠实的，故该投影为零，`N` 在 tame 商中的像为零。于是 `N⊆P_F`。

**第二步：`T` 是 tame 商中最大的闭正规阿贝尔子群。** 设 `A` 为闭正规阿贝尔子群，`a∈A`，其 Frobenius 坐标为 `t`。对任意 `x∈T`，正规性给出 `[a,x]∈A∩T`；阿贝尔性又给出 `[a,[a,x]]=1`。在 `T` 的每个 `ℤℓ` 坐标上，这意味着

\[
(q^t-1)^2x=0\quad\text{对所有 }x.
\]

各 `ℤℓ` 没有零因子，所以 `q^t=1`。利用上述忠实性，得到 `t=0`，故 `A⊆T`。这样 `T` 是 characteristic 的，`I_F` 作为其原像也为 characteristic。

**第三步：把标准 tame 描述本身从实际局部对象证明。** 有限层可从 residue action、`m/m²` 及更高主单位过滤着手：wild 部分的 successive quotient 是 residue 加法群的子群，因而是 p-group；tame 部分来自 prime-to-p 素元根与非分歧扩张。取兼容逆极限得到上式。此处需要实际 Henselian/DVR 和有限 Galois 扩张理论，不能只在一个自定义半直积模型上证明前两步，就宣布实际 `G_F` 满足它。

这给出了明确的内部证明树。当前报告没有核实仓库已经具有该完整 tame realization，因此将其登记为待构造节点，而非伪装成现成定理。

### 7.4 单位—惯性对应怎样推进，怎样避免变成一个新空接口

不建议一开始就形式化全部局部类域论的外观。只实现上述 `ρ_F` 所需的范围：

1. 对每个实际有限阿贝尔扩张 `L/F`，构造单位的局部 reciprocity 到 inertia 的有限层映射，计算核为 `O_F^×∩N_(L/F)(L^×)`，并证明与扩张塔的 norm/restriction 相容。
2. 证明这些有限层映射满射到有限层惯性，并使核在单位群中给出正确拓扑；取逆极限得到实际 `O_F^×≃J_F`。
3. 用已经存在的有限 torsion、单位商和 log-image 理论除去挠元。连续性可按第 7.1 节处理，不再要求额外源拓扑字段。

第 1 步是有实质算术内容的局部 reciprocity，不能用定义 `ρ` 并把核/满射作为字段的方法宣称证明。这一轮未发现足以直接填满它的实际供体。若该工程过大，先考虑下一条以现有 Kummer 对象为起点的替代路线；不要把一个未证明的外部“标准结论”变成最终输入。

### 7.5 备选源路线：有限 Kummer 层 → 逆极限 → 模挠

如果实际源箭头已经带有可构造的 cyclotomic coefficient transport，则可绕开完整 monoid，也可能减少 reciprocity 的建设量。

对每个 `n`，从实际 Kummer 序列构造

\[
F^\times/(F^\times)^{p^n}\simeq H^1(G_F,\mu_{p^n}),
\]

并取 valuation 模 `p^n` 的核，这正是单位的 Kummer 部分 `U_F/U_F^{p^n}`。源群箭头与 coefficient transport 诱导上同调映射；证明它保持该单位子群，并与 `n+1→n` 相容。

令

\[
C_F=\varprojlim_n U_F/U_F^{p^n}.
\]

它是实际单位群的 pro-p 部分。prime-to-p torsion 在该极限中消失，p-primary torsion仍可能保留；再对整个极限群取 torsion quotient，就得到 `W_F`。这样不必在每个有限层另挑出“哪些扭元来自根单位”，因为有限层本来全是有限阶元，不能靠“有限阶”在单层区分它们。

源端真正要证明的内容缩成：cyclotomic coefficient transport、单位 valuation kernel 的保持，以及实际有限 Kummer 同构及其兼容性。一般 profinite 群同构下，这些性质不能凭空假定；必须从原文允许的源箭头或第 7.3 节的惯性识别推出。

仓库 `KummerGaloisClass.lean` 已有实际 finite-Galois Kummer ratio、根单位值和 kernel/injectivity 的供体，但文件明确只完成注入层；不能把它直接当成上面全部 `H¹` 同构及满射。`SourceH1H2Construction` 中的 H1/H2 是项目源构造编号，也不是 Galois 上同调 `H^1/H^2`，不能因名字相似误判供体齐全。

**建议取舍：**先尝试从现有原始 Kummer/cyclotomic 箭头取得第 7.5 节的有限层映射；若其单位部分仍无来源，则回到第 7.2–7.4 节的惯性阿贝尔化路线。两条路线都只求实际单位模挠群，不先追求域乘法重构。后者的证明树较清楚，但算术基础建设也较重，不能称为纯接口装配。

## 8. S1902 的一个更直接突破口：原文 `K_v` 中可能已经有全部所需根

### 8.1 这次核对到的原始输入

IUT I Definition 3.1 的本地原文明确有：`E[2·3]` 在 `F` 上有理；`K/F` 由 `E[l]` 的 Galois 表示的核确定。源码也实际记录了：

- `SourceClauseC.torsion23_rational`；
- `representation_eq_canonical`；
- `kernel_field_identification : A.K ≃ₐ[A.F] galoisLTorsionKernelField ...`；
- `SourceClauseB.q_comparison` 的 witness 中有同一个 q 参数的 `TateCurveComparison`；其 `points.pointEquiv` 与 `points.galois_naturality` 是实际点商等价和等变律。

因此，可以从**现有合格输入**证明 `E[2l]` 在 `K` 上有理，而不是再加一条 root-existence 假设。对 `P∈E[2l]`，`lP∈E[2]`、`2P∈E[l]`；取整数 `a,b` 满足 `al+2b=1`，有

\[
P=a(lP)+b(2P).
\]

两项都为 `K`-有理，故 `P` 亦然。随后把该有理性沿真实 completion/base-change 传到 `K_v`。这一步须使用实际 torsion 的 base-change/局部 Galois 限制，不只是把一个 `Fin 2 → ZMod l` 的向量空间基改类型。

### 8.2 核心引理：利用 torsion 的固定性把 q 的根降回 `K_v`

记 `M=K_v`，`n=2l`。在共同的局部代数闭包中取当前实际根 `α`，满足 `α^n=q`。设 `q` 与 Tate comparison 使用**同一次 witness**的参数，并且 `0<‖q‖<1`。

Tate 点商映射给出

\[
P_\alpha=\operatorname{Tate}([\alpha])\in E[n](\overline M),
\]

因为 `α^n=q`，其商类的 n 次方为单位元。由上一小节，`P_α` 被 `G_M` 固定。对任意 `σ∈G_M`：

1. Tate 映射的等变性给出 `Tate([σα])=σ(P_α)=P_α=Tate([α])`。
2. Tate 映射的单射性给出 `[σα]=[α]`，所以
   \[
   \sigma(\alpha)/\alpha=q^{m_\sigma},\quad m_\sigma\in\mathbf Z.
   \]
3. 另一方面，`σ` 固定 `q`，因此
   \[
   (\sigma(\alpha)/\alpha)^n=1.
   \]
4. 结合得到 `q^(n mσ)=1`。因 `0<‖q‖<1`，`q` 具有无限乘法阶，故 `mσ=0`，所以 `σα=α`。
5. 由实际局部 Galois 固定域性质，`α∈M=K_v`。

这个论证只需要 Tate 点商的**单射性、乘法性和 Galois 等变性**，不需要另证点商映射在 `K_v`-有理点上的满射，也不需要新做一个 `H¹(G_M,ℤ)=0` 的下降过程。

这正是能绕开旧“根不在 `F_v`”障碍的具体路线：根不在较小的 `F_v`，并不妨碍它在原文实际使用的 `K_v`。本次没有声称 `F_v≃K_v`，也没有声称现有 root extension 等于整个 `K_v`。

### 8.3 从根下降得到的是嵌入与 scalar 读数相等

把当前 `rootNormedExtension=F_v(α)` 放进与 `K_v` 相容的共同代数闭包，上一论证给出实际域嵌入

\[
\iota_b:F_v(\alpha_b)\hookrightarrow K_v.
\]

应在共同闭包中下降**当前选定的根**；不要只在 `K_v` 中任取另一根，再假装它必满足当前根的同一个最小多项式因子。

对标准 `ℚp` 延拓绝对值，该嵌入保持范数。令 `θ_(b,j)=ι_b(α_b)^(j²)`，则

\[
\operatorname{ord}_p\theta_{b,j}
=\frac{j^2}{2l}\operatorname{ord}_p q_b.
\]

现在它已经是正确 `K_v` 因子中的实际元素，可以作为 `PacketHullData.varpi`。根域的主格延拓为 `θ_(b,j)O_(K_v)`；尽管两域次数可以不同，分别按各自真实次数归一化后：

\[
\frac1{[F_v(\alpha):\mathbf Q_p]}
 \log\frac{\mu_L(\alpha^{j^2}O_L)}{\mu_L(O_L)}
=\log\|\alpha^{j^2}\|
=\frac1{[K_v:\mathbf Q_p]}
 \log\frac{\mu_M(\theta_{b,j}O_M)}{\mu_M(O_M)}.
\]

所以这里可以证明的是**principal-region 的 normalized scalar 读数相等**。不必有全载体等价；也不能声称嵌入把 `O_L` 满射到 `O_M`。前者利用局部 Haar 范数幂公式，后者一般不成立。

接下来将 `θ_(b,j)` 放到 tensor 的 distinguished slot，其余 slot 取 1，便得到既有 Step-V 上界所需的真正 `ϖ`。由于使用的是原文的 `K_v`，不会因额外人为扩域而引入一套尚未预算的 different 修正。

### 8.4 这条路线的实际证明责任与优先级

建议先做下面这条数学桥，优先于全局 carrier equivalence：

```text
现有 Θ-data 的 torsion23_rational + kernel_field_identification
  → E[2l] 在 K 及 K_v 上有理
  → 同源 Tate comparison 下 q^(1/(2l)) 被 G_(K_v) 固定
  → 当前 root extension 嵌入实际 K_v
  → 逐标签 scalar order 与 normalized log-volume 相等。
```

待落实的主要类型运输是：全局 torsion 到局部 torsion、同一个 q witness、局部代数闭包及 `F_v→K_v` 的兼容嵌入。若缺某个运输定理，应证明该定理；不能将整条链改成“假设根在 `K_v`”。

此外，`SourceClauseB.q_comparison` 对现有 `SourceNativeInitialThetaData` 是已经给出的合格输入。若另一个更上游目标要求从裸椭圆曲线构造这份 Θ-data，它仍须证明相应 Tate comparison；本路线没有替那个目标完成存在性，也不新增该目标的假设。

这一步完成后，B 中最容易被误认为“同维类型转换”的根值落点问题就获得了真实解决方法。剩余的实际作用覆盖、Ind3 容器、逐块权重链仍要做，但不再需要强求 `S1902Carrier ≃ₐ ArithmeticTensorTupleBlock`。

## 9. 最新工作判断

我建议现在将思路集中成两条主线：

1. **Ind1：先把源端目标缩成实际单位模挠群的代数同构。** 连续性自动补出；从惯性阿贝尔像或真实有限 Kummer 系统构造该同构。不要优先补齐全部 `isoMon` 外观，也不要重复已写好的 log/perfection 后半段。
2. **S1902：先用原文的 torsion 字段和实际 Tate 等变点商，把当前根降到原文 `K_v`。** 由真实嵌入取得逐标签 scalar 读数，再接已有 packet hull bound 和权重平均。不要先在全局 root product 与单个 tensor block 之间找等价。

第 7 节惯性/reciprocity 的完整源构造尚未核实存在；第 8 节给出了完整的数学推导，但尚未形式化上述全局—局部类型运输。这两处明确作为证明责任保留。当前交付是重要路线与证明细节，不是另一个接受 `β_a` 或 `s1902SignedReadoutGap` 假设的“完成版”。

<!-- ind1-dprime-realization-routes-20261114 -->
## 2026-11-14 后续更正：§7.2 的 local CFT 供体已找到

保留上面的历史调查。后续定向检查找到 `tmp/local-cft-port/Reciprocity/ArtinInertia.lean` 的实际 `PadicField.unitsInertiaEquiv`，以及 `GaloisStructure.galAbEquiv`、`ArtinTransfer.artin_transfer`、NormCompat、Conjugation 证明源码；S2027/S2098 已有项目接入。因此不要再安排从头构造局部互反律。尚缺的是 actual source 箭头保持惯性、carrier 对齐及全部箭头自然性。

新的详细消缺路线见 [IND1-DPRIME-REALIZATION-ROUTES-20261114.md](D:/lean/coord/IND1-DPRIME-REALIZATION-ROUTES-20261114.md)：§4 用 tame quotient 的内在子群刻画构造一般 beta；§5 通过标准 Frobenius 与 Artin 整数像构造全有限层乘法作用并粘合；§6 处理全部 procession 覆盖与 Ism 选择差。无 Lean 修改或编译；没有因此宣称一般 Ind1 已完成。
