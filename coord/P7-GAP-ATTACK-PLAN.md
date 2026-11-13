# P7 十 GAP 逐个击破计划（2026-11-13 R29 之后）

来源：coord/P7-GATE-REVIEW.md §13（Mzk1P7GapRegisterActual.gapRegister）。
用户指示：10 个 gap 是把一个大 gap 分解成 10 个，逐个击破。
状态：全部未 unconditional discharge；GAP-P7-CONTRACT 为 CONDITIONAL/INTERFACE。

## 编号 / 缺口 / 主攻 lane / 下一步（可执行）

| # | code | 当前状态 | owner | 下一步（具体） |
|---|---|---|---|---|
| 1 | GAP-P7-GENERAL-CMP | **PARTIAL（路线 A 完成，剩余为同源/标量识别）**；已 green：PadicBallCeil(A2 球质量，11:52:14Z)、BallMassFormula(12:03:46Z)、LowerBound(重写去 c/hprod，12:06:23Z)、S1915DegreeFinrank(rfl 语义等式，12:18:40Z)、C3S1902NormalizedLog(A5，12:38:53Z)。精确障碍（abc 已 file:line 定位）：`HullQDictionary` 的 q_eq_sum 需跨族同源（qVFamily ↔ C3 q，independent objects；另需 ∏qVFamNormRatio=1 与 place-求和恒等式）；theta_eq 需 C3↔S1902 hull 标量质量对齐（弱于 blockEquiv）。HullQDictionary = 唯一 named input（仅两标量）；(b) ∏qVFamNormRatio=1 经查不可由现有定义证（PaperSourceCorrectionFreeFields 源字段，两范数实例不同，BadPlaceSourceFieldsObstruction 明文；强行作定理即 fake） | abc | 优先证 (b) `∏_b qVFamNormRatio T b = 1`（可从 qVFamNormalizedGenerator_norm/qVFamDefaultNorm 乘积直接得）；其余两子障碍要源映射；margin 1 已有（S1915Comparison:113-125）但依赖 HullQDictionary inhabitant |
| 2 | GAP-P7-IQ-LITERAL | **DISCHARGED（definition-level）**；`Mzk1IQFiniteAdeleRestrictedActual` DONE 12:04:41Z（olean 41,096B）：`iqPlaceIndex=HeightOneSpectrum (𝓞K)`、`adicCompletion/adicCompletionIntegers` 真实载体，`iqCarrier_eq_mathlibFiniteAdeleRing`（rfl 到 Mathlib `IsDedekindDomain.FiniteAdeleRing`）+ `iqFiniteAdeleRingEquiv`（RingEquiv.refl）+ 结构运输 + 几乎处处整性；不依赖 FLT backport 链 | qpilot | **语义剩余**：paper-literal IQ 的 divisor/label/unit-group 结构未识别（definition-level ≠ paper-literal）；在 Mathlib carrier 上构造这些附加结构即下一阶段 |
| 3 | GAP-P7-OB33-SRC | **CONDITIONAL**；`Mzk1Ob33SourceIdentificationActual` GREEN（11:40:50Z）：实际 detDegree = actualUnitLineBundleData.detData.globalLogVolume，`ob33DetNormalizedLogVolume` 本地定义 + 显式 identification；B4.4 det line：mainline DetLineConstruction GREEN（11:47:36Z，log D(H,O)=logH−logO） | shehdd | B5 逐位：localizedLine DVR 生成元 + Haar scaling（mainline DetLinePlaceB5 的 named-input 口径）；arch metric；然后用 relativeDetLog 替换 Ob33 命名 identification |
| 4 | GAP-P7-MULTIRADIAL | PARTIAL；finite Q(i)-at-5 production green；general CarrierAlgorithmContract 无条件 green；RouteNormalForm named input；实际 production 缺失 | stepxi | 已完成：carrier 包 `Mzk1P7MultiradialCarrierActual`（finite model）、`Mzk1P7MultiradialGeneralBridgeActual`（general conditional）、精确缺口 `coord/P7-MULTIRADIAL-GAP.md`；下一步仅 actual n,oR_LGP/production 源 |
| 5 | GAP-P7-THETA-V | **DISCHARGED（general-k V 字典）**：L1 raw green、L2 normalized green、L3 actual scale=1/offset=1（`Mzk1ThetaVScaleOffsetIdentityActual` DONE 12:10:27Z）；general-k：`scaledThetaHull_normalizedLog_eq`（实际定理）+ **`Mzk1ThetaVGeneralUnconditionalActual` DONE 12:24:25Z（67s）**：rawV=scaledClosedFormR k、normV=normalizedLog(scaledThetaHull k)、scale=1/offset=1、qLogSum_nonneg、general-k C0=1 bound | hull | 无剩余 named closed-form 假设；若需 paper 的最终 V 形式再另行对齐（当前字典已实际构造） |
| 6 | GAP-P7-THETA-D | **DISCHARGED（S2717C3 实例）/PARTIAL（一般 S3137 C3）**；`Mzk1C3DKeyMapActual` + `Mzk1C3DDonorProjectionActual` DONE 12:05:14Z（actualDonorC3 展开到 D 字段，7 个 rfl 投影）；#6 对实际 donor C3 构造已识别 | hull | 一般 S3137 C3 桥另列精确缺口（不是 named dictionary） |
| 7 | GAP-P7-THETA-DEG | **PARTIAL（核心构造 DONE）**；`Mzk1C3BlockMeasureActual` GREEN 11:44:02Z；`Mzk1P7ThetaDegActual` GREEN 12:20:07Z（localCompletionDegree=finrank、block:Q_p=∏、block nonpos）；**`Mzk1P7ThetaDegC3Actual` GREEN 12:33:19Z**：`c3TensorBlockDimension_eq_sum_fieldProduct`（域分解 ⇒ C3 block:Q_p=Σ 实际 local degree）；B2 主体（packet 求和 calc）在编 | stage4 | B2 绿后合并更新 P7 §13 #7 为“域分解+求和 DONE”；剩余：degree 权重与 V 的最终归一化消去（精确 GAP） |
| 8 | GAP-P7-CONTRACT | **CONDITIONAL ASSEMBLY**（`Mzk1P7ContractMapActual` DONE 11:18:55Z，olean=True；AgreeFLT DONE 11:13:10Z） | mainline | 已完成：`recon12ToGap`/`missing7ToGap`/`gapCodesCovered`/`contract_fields_not_linked`/`p7_conditional_contract`；文档 `coord/P7-CONTRACT-MAP.md`。后续：等其它 GAP 关闭后把条件装配升级为 DISCHARGED |
| 9 | GAP-P7-HULL-UB | **CONDITIONAL（C0=1）**；paper V = s1915ClosedForm = 1+normalizedLog（a_i=d_b, β=1）；actual bound `V ≤ paperBox+1`；**C0=0 ⇔ slack:=paperBox−normalizedLog ≥ 1**，而现有 bound 只给 `slack ≤ 0` ⇒ C0=0 不能由现有数据推出（e-常数 1 精确障碍；disc≥2/cond≥1/l≥5 只给 paperBox≥1，不足） | hull | C0=1 已实际可达；C0=0 需新数据/新估计（slack≥1），已写 exact slack obstruction（C0Absorption/ObstacleRows/Discharge） |
| 10 | GAP-NORM-ARCH-C-K | **CONDITIONAL/PARTIAL（公式层 DONE）**；`Mzk1NormArchCKActual`(C_K/因子)、`Mzk1NormArchAbcHookActual`(接口+degree-one haarScale=1)、`Mzk1NormArchConsumerActual`(去 heightWeight 假设的 arch 加权和)、`Mzk1Ob33ArchMetricActual`(实际 Hermitian metric + compatibility PROVED)、B3 ratio on CommonPrimeCompletion(ProperSpace 障碍消除)、`CarrierEquivData`(单一 named input)、`NormArchC3HaarScaleFormula`(c3HaarScale=archCK·localUnitProduct，公式层 named data) 均 green | lattice | citizen 缺口清单：① C3S1902HaarScaleData.blockEquiv 实际构造；② unitMass 实际值；③ product of local normalized unit masses（需 localizedLine B3+prod）；CountLocalizationBridge 单独 GAP |

## 纪律
- 每项只允许：定理化（green）、条件接口（显式 named input，CONDITIONAL）、精确缺口文档（OPEN + 障碍说明）。
- 禁止：改对象/加 axiom/sorry/toy carrier；不得把条件接口写成 unconditional。
- 报告格式：gap code + 文件/定理 + watchdog DONE/olean + 状态变化（OPEN→CONDITIONAL→DISCHARGED）。
- 文档同步：P7-GATE-REVIEW §13 表、GapLedger、R29-STATUS。

## 优先级
1. GAP-P7-HULL-UB（#9，可能已有足够材料关闭）
2. GAP-P7-CONTRACT（#8，等 AgreeFLT）
3. GAP-P7-GENERAL-CMP（#1，C3S1902 链已就绪）
4. GAP-P7-THETA-V/D/DEG（#5/6/7，hull/stage4）
5. GAP-P7-IQ-LITERAL（#2，等 FLT Equiv）
6. GAP-P7-MULTIRADIAL（#4，可能真缺）
7. GAP-NORM-ARCH-C-K（#10）

## 用户指示（2026-11-13 晚）：条件本身也要尽量构造（condition realization）

不只“条件证明”，而是把 named input / 条件对象**实际塑造出来**（构造 inhabitant、实例、具体值）；只有确实做不到时才保留 named input + 精确障碍。

| gap | 条件/命名输入 | 构造目标（优先） |
|---|---|---|
| #1 | C3S1902TransportData（blockEquiv/region_eq/haarScale/haar_apply） | 用实际 C3 数据构造 inhabitant；haarScale 用实际 Haar 比给出具体值；haar_apply 用实测度等式 |
| #2 | FLT FiniteAdeleRing 实例/Equiv | Equiv 绿后直接构造 IQ↔FiniteAdeleRing 的 Equiv/instance |
| #3 | Ob33ArithmeticDegreeIdentification detDegree | 查 source arithmetic degree 实际定义；若能证 = ob33DetNormalizedLogVolume 则消去 named input |
| #4 | RouteNormalForm / general FiniteIndeterminacyDischarge | 尝试从 finite model + 实际 label/procession 数据构造 |
| #5 | ThetaVScaleOffset scale offset | 从 raw/normalized 定义直接构造 scale/offset（若 paper V 定义为 normalizedLog 则 1/0） |
| #6 | C3D dictionary D 侧 | 构造 D 侧 index/place/tuple 实际等式 |
| #7 | localCompletionDegree 识别 | 用 Module.finrank 实际实例构造 identification |
| #8 | 7 missing rows | 用已 green 的 C3/S3137 数据实例化每一行 |
| #9 | RawNormalizedDictionary | 从 normalizedLog 与 paper V 实际定义构造 scale/offset；若 identity 则直接关闭 |
| #10 | C3HaarScaleDocking | 查 C3S1902HaarScaleData 的 haarScale 来源；若 = 1/[K:Q]（如 [K:Q]=1）则构造 |

纪律：构造必须是实际对象/实例/定义值，不得把“要被识别的对象”定义成“识别结果”（循环）；若原文确实如此定义，须在文档说明这是定义级识别而非定理。


---

## 追加意见：以消除实际缺口为目标的三条构造路线（2026-11-13，单线程复核）

本节按用户要求追加：**最终目标是完整解决原问题；不能以新增假设输入或条件装配作为完成。** 原表和历史保留。以下给出具体构造、证明步骤及验收出口；不是再列一遍 OPEN。没有修改其他负责人的 Lean 文件，也没有启动子代理。

### 1. 可以立即改变执行方向的结论

**BALL-MASS/CEIL 有直接可复用的实际定理，不应继续把球质量公式作为待假设输入。**

本轮在当前源码找到：

- [S1915ThetaHullA0Actual.lean:201](D:/lean/tmp/sheaf/xif/paper/S1915ThetaHullA0Actual.lean:201)：s1915_local_measure，实际根扩域球的 Haar 质量公式；
- [同文件:251](D:/lean/tmp/sheaf/xif/paper/S1915ThetaHullA0Actual.lean:251)：s1915_hull_toReal，实际 hull 质量的乘积公式；
- [S709RootImageRadiusFormulaActual.lean:128](D:/lean/tmp/sheaf/xif/paper/S709RootImageRadiusFormulaActual.lean:128)：rootImageRadius_eq_rootNorm；第 145 行还有 rootImageRadius_eq_p_rpow；
- [S865RootHaarFactorNormPowActual.lean:35](D:/lean/tmp/sheaf/xif/paper/S865RootHaarFactorNormPowActual.lean:35)：rootHaarFactor_normPow_actual。

上述球质量定理的参数是原有 T、位置 b 和类型类，没有额外的 hball、hprod 或目标比较输入。这些文件当前有 olean。本轮核对声明、证明体及产物存在性，未重新构建或检验完整传递公理。

建议采用三条相连路线：

| 路线 | 实质工作 | 可消除的缺口 | 最终消费者 |
|---|---|---|---|
| A：精确球质量接线 | S1915 + S709 接入当前 C3S1902 | 球质量未知、ceil 假设、重复的范数下界搜索 | #1 的精确量化 |
| B：同源构造与相对行列式 | 从同一个输入构造索引、格、参照、读数 | 自由 dictionary、degree、Haar scale 中应由来源决定的字段 | #2/#3/#5/#6/#7/#9/#10 |
| C：真实生成元与整数系数 | 构造 q 格的 theta 生成表达，或较弱的行列式理想关系 | 最终 comparison/hle；只为比较而添加的冗余强桥 | #1，随后 #8 |

A 的局部质量步骤已有直接供体；B 是对象构造任务；C 是主比较需要的实质数学突破。这是研究路线，不声称完整 3.12 已经闭合。

### 2. “无额外假设”的完成标准

保留论文允许的合格初始数据；必须取消的是**为了证明目标新增、却没有从初始数据构造的困难输入**。最终交付应为：

~~~text
对每个原文合格输入 T：
  构造 actual 对象、运输及归一化；
  证明实际 hull 的有限性；
  证明实际 q/theta 比较；
  接入锁定目标并通过验收。
~~~

给定 comparison 再得到 Cor312Conclusion，给定 identification 再展开 identification，或给定足够大的 Haar 乘积再推出比较，均不算解决原问题。

严格说，条件定理本身未必循环；条件未构造意味着问题仍未解决，条件等价于目标意味着重述目标，构造条件又使用目标才是证明依赖循环。**对本项目的完成验收，这些情况都不得核销原缺口。** 公理检查干净也不能免除定理参数的构造责任。

### 3. 路线 A：复用实际最大 theta 值，直接算出球质量

#### 3.1 构造及完整数学推导

对实际位置 b，记

\[
L_b=\mathrm{rootNormedExtension}(T,b),\quad
d_b=[L_b:\mathbf Q_{p_b}],\quad O_b=\{x:\|x\|\le1\},
\]
\[
r_b=\mathrm{rootImageRadius}(T,b),\qquad B_b=\{x:\|x\|\le r_b\}.
\]

PaperRootExtensionFieldScalingActual 已从有限的真实 theta 值中构造达到最大范数的元素 \(\lambda_b\)，并证明

\[
r_b=\|\lambda_b\|,\quad \lambda_b\ne0,\quad B_b=\lambda_b O_b.
\tag{A1}
\]

集合等式不是新假设：若 \(x=\lambda_b y\)、\(\|y\|\le1\)，则 \(\|x\|\le\|\lambda_b\|\)；反向取 \(y=\lambda_b^{-1}x\)。

S865 的 Haar 缩放律给出 S1915 已有结论：

\[
\boxed{\mu_b(B_b)=r_b^{d_b}\mu_b(O_b).}
\tag{A2}
\]

有限乘积为

\[
\boxed{\mu(H_{\rm S1902})=
\left(\prod_b r_b^{d_b}\right)\mu(O_{\rm prod}).}
\tag{A3}
\]

正有限性直接使用同一个实际 hull/unit-ball 的已有定理。记
\(c_b=\mathrm{qVFamNormalizedCoefficient}(T,b)\)，S709 给出
\(r_b=p_b^{-c_b/(2l)}\)，故

\[
\log\mu_b(B_b)=\log\mu_b(O_b)
-\frac{d_bc_b}{2l}\log p_b,
\tag{A4}
\]

\[
\boxed{\mathrm{rootExtensionProductNormalizedLog}(T,H_{\rm S1902})
=-\sum_b\frac{d_bc_b}{2l}\log p_b.}
\tag{A5}
\]

式 (A5) 是相对单位区域的有符号实数 log。现有对象的半径已有精确式，不需要再把“theta 值范数下界”当成独立未知量。

**不能直接用 qOrder 替换 \(c_b\)**。现有 Mzk1RootImageRadiusFormulaActual 的 order 版本要求 normalization correction 为零；应保留并展开 correction，或从来源证明为零，不能添加 hcorr 后宣布完成。

#### 3.2 接入当前消费者的具体动作

当前 Mzk1C3S1902ComparisonActual 的右侧正是 \(\prod_b\mu_b(B_b)\)。下一包应：

1. 直接使用 s1915_local_measure 改写现有局部球；
2. 使用 s1915_hull_toReal 或同一乘积 Haar 定理合并；
3. 用 S709、Real.log_prod、Real.log_pow 得到 (A4)/(A5)；
4. 核对同一个球、测度、T、b 和 coefficient；
5. 从当前消费者的未证依赖中移除 BALL-MASS/CEIL，而不是新增一个同内容字段。

若实际运输由路线 B 构造，记其比例为 \(s>0\)，则当前原始 C3 比较精确化为

\[
\Delta=\log s+\sum_b\log\mu_b(O_b)
-\sum_b\frac{d_bc_b}{2l}\log p_b-\log\|q_P\|\ge0.
\tag{A6}
\]

继续的工作是从同源 q 对象求 \(\log\|q_P\|\)，从实际参照求
\(\log s+\sum_b\log\mu_b(O_b)\)，按真实权重合并，再对剩余项证明符号。仅获得 (A6) 的等价式不算 #1 完成，但球质量子缺口已有无新增数学输入的解决路径。

#### 3.3 当前 ceil 路线有一个应先修正的数学前提

Mzk1PadicBallCeilActual 的 p 幂 Haar 缩放引理可以保留。但是对任意分歧扩域，一般没有

\[
B(0,p^{-s})=p^{\lceil s\rceil}O_L.
\]

在 \(|p|=p^{-1}\)、分歧指数 e、剩余次数 f 的规范化下，应为

\[
B(0,p^{-s})=\pi^{\lceil es\rceil}O_L,\qquad
\frac{\mu(B)}{\mu(O_L)}=p^{-f\lceil es\rceil}.
\tag{A7}
\]

例如 \(L=\mathbf Q_3(\sqrt3)\)、\(s=1/2\)，实际球为
\(\sqrt3\,O_L\)，质量比 \(1/3\)；错误的 p 幂公式给出 \(1/9\)。
这检验的是拟议的一般球公式，不是原 IUT 定理的反例。

**当前半径已是实际元素范数，直接用 (A1)–(A5) 更短，连修正后的 ceil 理论也无需成为该消费者的前置。**

#### 3.4 避免接错 S1915 的另一个读数

S1915 还研究

\[
a_0=\max\left(0,1+\sum_b d_b\log r_b\right),
\]

并明确说明 ENNReal 截断。此处只复用局部质量、乘积质量和未截断的实数公式；不能用 \(a_0\ge0\) 证明 paper 的有符号比较。

另建议停止将 ConditionOne 的
\(1\le s\prod_b\mu_b(B_b)\) 作为主攻目标。它比实际需要的
\(\|q_P\|\le s\prod_b\mu_b(B_b)\) 更强：例如左侧 q 范数为 \(1/4\)、实际右侧为 \(1/2\)，原比较成立而 ConditionOne 不成立。保留这个条件工具，但主攻 (A6)。

#### 3.5 本路线的验收出口

交付实际 local ball mass 和 product signed relative log 的精确公式，接入当前消费者，且不含 hball、质量下界或新范数输入。只完成这一步时，记录为“球质量子缺口已消除、#1 运输及比较仍开放”；不能据此关闭整个 #1。


### 4. 路线 B：从同一个输入构造字典，用相对行列式消掉自由归一化

这一条主攻 #2/#3/#5/#6/#7/#9/#10。它的目标不是再证明“给定字典则可重写”，而是**让字典中每个数学字段都有来自原输入的构造和证明**。

#### 4.1 先重建同源索引，不用自由的右侧类型填字典

当前 Mzk1C3DKeyMapActual 把右侧 dIndex、dPlaces、dTuple 直接定义为所构造 C3 的字段，indexEquiv 为 refl。它确实构造了一份索引数据，但尚未独立识别 D 侧或原文侧的对象。

正确的下一步是：

1. 向下展开 S2717C3 和 actualSignedC3 的构造，只追它们实际读取的 donor 字段；
2. 将 D 的真实索引、位置、tuple 作为字典右端，而非再选一个任意类型；
3. 对从 D 到 C3 的每个投影证明等式；若是定义性投影，直接展开后 rfl；
4. 若存在依赖类型运输，使用同一来源等式的 transport，证明生成元、q、整数格一同被运输；
5. 只有当目标确实需要逆向重建时才证明相应逆律；不为方便强求整个 donor 可由其投影恢复。

本轮读到的 S2717C3 还固定使用 fiveLabel 和 FinitePrimePlace 2 7。它可作该实例的消费者，不能直接覆盖所有原文合格 l、位置和曲线。应回到一般构造，保留准确量词；不以实例成功关闭全称目标。

完成标志：原消费者不再要求独立填写 indexEquiv、fiberEquiv、place/q 对齐字段；这些项由同一个 T 的构造产生。

#### 4.2 避免把张量块误当成域的直积

源码中的 C3LogShellTensorBlock 是同一 p 上的算术张量块；S1902Carrier 是所有所选坏位置根扩域的有限直积。后者可能涉及不同有理素数。现有 C3S1902TransportData 只要求一个集合 Equiv，并额外输入 region_eq 和整套 Haar 等式；这没有证明两载体的算术对应。

应按真实 p、标签、tuple 先分块。对一个合法张量块，使用有限 étale 代数的域分解：

\[
E=\bigotimes_i K_i \simeq \prod_a E_a.
\]

构造映射的方式是：对每个实际域分量 a，用来自同一嵌入/共轭数据的映射 \(\iota_{i,a}\)，将纯张量送到

\[
x_1\otimes\cdots\otimes x_m
\longmapsto \prod_i\iota_{i,a}(x_i).
\tag{B1}
\]

证明所有分量合起来给出代数同构，保留分量重数，并核对

\[
\dim_{\mathbf Q_p}E
=\prod_i[K_i:\mathbf Q_p]
=\sum_a[E_a:\mathbf Q_p].
\tag{B2}
\]

现有 FinitePlaceArithmeticTensorBlockFields 是复用入口。**不是说任意两份当前 carrier 都满足 (B1)；必须证明它们分别是该实际分解的哪一部分。** 若整个 C3 与整个 S1902 并不对应，不再强攻错误的全局 Equiv，而是在共同实际分块上比较相应对象/行列式。中间接口可以等强修正，最终对象不改。

这也说明 #7 不应把一个完整张量块的 degree 强行识别成某一个局部域 degree。应先用正确的乘积与求和关系，再消去归一化中的维数。

#### 4.3 Haar scale 的构造来自参照格，不来自目标 hull

假设已构造实际连续加法同构 e，并将同一固定参照格 O 送到 O'。两套实际 Haar 测度的比例由参照决定：

\[
s=\frac{\mu(O)}{\nu(e(O))}.
\tag{B3}
\]

通过 Haar 唯一性和同一映射的测度运输证明

\[
\mu(S)=s\,\nu(e(S))
\]

在所需可测集合上成立。O 的选择由原对象规定，不依赖待证比较。

若处理的是相对读数，常数会消去：

\[
\log\frac{\mu(H)}{\mu(O)}
=\log\frac{\nu(e(H))}{\nu(e(O))}.
\tag{B4}
\]

因此不必先把绝对 Haar 比例猜成 1，或猜成某个全局次数倒数。若 e(O) 与另一端使用的 O' 不同，差值由两个真实参照格的指数给出；用已有 SNF/trace-dual/整数张量比较计算它。

这一构造可以实质消掉 haar_apply 和 haarScale 的自由输入。需要的是实际 e 和参照格关系；“定义 s 为两个目标 hull 质量的比，再用该 s 声称比较”没有完成源运输。

#### 4.4 用真实行列式证明 degree 字典，不把 degree 定义成目标数

对同一实际满格 H 及参照 O，构造

\[
\mathcal D(H)=\det(H)\otimes\det(O)^{-1}.
\]

取共同坐标基，H、O 的基矩阵为 B_H、B_O，则

\[
\log\frac{\mu(H)}{\mu(O)}
=\log|\det B_H|_p-\log|\det B_O|_p.
\tag{B5}
\]

右边同时是这份相对行列式的局部读数。换基时双方乘同一类单位/共同 determinant，故相对式不变。再按原文 degree、标签、procession 权重求和，加入实际无穷位度量；同一个全局有理基的变化用乘积公式消去。

具体证明顺序是：

1. 构造原来源 det(x)M 的实际 determinant line；
2. 给出它与上述相对 determinant 的同构，证明每个原来源态射在 determinant 上的作用；
3. 在每个有限位用 (B5) 计算；
4. 在无穷位用实际 determinant metric 计算；
5. 合并并证明原文 arithmetic degree = 实际规范化读数。

这样得出的 equality 是定理。当前 Ob33ArithmeticDegreeIdentification 接收任意 detDegree 实数；将这个实数直接设成 raw/blockDim 只构造了一个局部读数，尚未做第 1、2 步。这两步必须有实际对象和映射，不能再命名一个 identification 参数。

#### 4.5 paper V 接入必须包含真实的左端绑定

当前 HullUBDictionaryData 只把 dict.normV 绑定到实际 normalizedLog，没有字段或定理证明 dict.rawV 就是锁定的 paper V。即使 scale=1、offset=0，得到的也首先是字典中一个实数的上界。

路线 B 应先从实际读数推导：

\[
V_{\rm paper}=\sum_i a_i L_i+\beta,
\tag{B6}
\]

其中 \(L_i\) 是对应实际块的相对 log，\(a_i\) 来自实际维数和标签权重，\(\beta\) 来自参照差与无穷位项。只有当它确实能化成单一仿射式时，才使用 RawNormalizedDictionary。

若推导得到 \(a>0\) 且 \(V=aL+\beta\)，已有 \(L\le B\) 给出的是
\(V\le aB+\beta\)。应继续证明这个实际上界满足最终要求，不能为了复用旧 lemma 假设 a=1、beta=0。若真实符号不是正比例，先纠正中间接口及不等式方向。

当前 normalizedLog 上界的证明经过
“normalizedLog ≤ 0 ≤ 非负 main term”。这是一个有效上界，但它没有给出 q/theta 所需的下界，不能替代 #1。

#### 4.6 #10 应接真实的 height 权重，不应猜 Haar scale = C_K

最新 Mzk1NormArchAbcHookActual 新增了
C3HaarScaleDocking.haarScale_eq_archCK。不能仅因两者都是正实数系数，就把这个 equality 当作应当成立的来源字典。

两种操作不同：

\[
\log(c\mu(S))=\log\mu(S)+\log c,
\qquad
\frac1{[K:\mathbf Q]}\log\mu(S)
\]

后者是在 log 之后乘权重，前者是在 log 之前缩放测度。取
\(\mu(O)=1\)、\([K:\mathbf Q]>1\)，将测度除以次数会使单位区域 log 变成负的 log-degree；将其 log 读数除以次数仍为 0。

所以真正可执行的接法是：

- 复用 archCK_eq_heightWeight 和 hArc_eq_archCK_mul_sum；
- 在实际 ABC/degree 消费者的加权和中替换同一个 heightWeight；
- 核对实/复位置重数、toric 的 1/2、全局域的次数；
- 若换域，证明对应的范数与位置次数公式；
- 有限位 Haar 比例仍由 (B3) 独立计算。

不能把一个可能没有数学依据的新 equality 制造成第十个缺口的“最后输入”。已有常数定义可以直接构造相应输出结构；真正需接入的是原消费者的同一度量/高度表达。

#### 4.7 路线 B 的交付要求

交付一份从同一个 T 出发的构造，加上各来源投影、区域对应、degree/体积、参照修正和权重等式。接入后逐项列出哪些旧参数已经消失。

保留原输入的合法类型类；不能保留未构造的 transport、arithmetic-degree identification、paper-V identification 作为“最终假设”。本路线不保证每个现有字典原样可实例化：如果接口要求错误的对象相等，应修正中间接口并同步消费者，而不是添加假设使其可用。


### 5. 路线 C：用根关系构造 q 格，再用整数矩阵进入真实 theta hull

这一条直接攻击 #1。先给出一条有完整纸笔证明的根扩域比较，再说明如何进入原消费者；如果后一步不能成立，不把辅助比较冒充原文 3.12。

#### 5.1 第一种具体构造：根关系给出整数系数

固定同一个 T 和 b。取原有正标签 j=1 的实际 theta 根值 \(\alpha_b\)。令 \(\widehat q_b\) 是**先由原 q 数据得到**的规范化 q 元素在根扩域中的像。由原 root 构造证明

\[
\alpha_b^{\,2l}=\widehat q_b.
\tag{C1}
\]

这里不能根据想要的结论重新定义 q；应展开实际 root/theta 定义，在同一扩域中使用原来的根方程。

S709 已证明 j=1 达到最大范数，并且 \(0<\|\alpha_b\|<1\)。因此当前 S1902 的局部 hull 正是 \(\alpha_b O_b\)，且

\[
\widehat q_b O_b
=\alpha_b\bigl(\alpha_b^{2l-1}O_b\bigr)
\subseteq\alpha_b O_b.
\tag{C2}
\]

**为什么系数确实是整数：**\(\alpha_b\in O_b\)，\(2l-1\ge0\)，所以 \(\alpha_b^{2l-1}\in O_b\)。这给出了包含所需的实际系数，完全没有使用待证比较。

取实际有限乘积

\[
Q_{\rm root}=\prod_b\widehat q_b O_b,\qquad
H_{\rm root}=\prod_b\alpha_b O_b
\]

便得到

\[
Q_{\rm root}\subseteq H_{\rm root}.
\tag{C3}
\]

由同一 Haar 测度及正有限性：

\[
\log\frac{\mu(Q_{\rm root})}{\mu(O_{\rm prod})}
\le
\log\frac{\mu(H_{\rm root})}{\mu(O_{\rm prod})}.
\tag{C4}
\]

而且可以精确计算余量：

\[
\log\frac{\mu(H_{\rm root})}{\mu(Q_{\rm root})}
=(2l-1)\sum_b d_b(-\log r_b)\ge0.
\tag{C5}
\]

对每个块乘同一个正权重后求和，仍成立。这个辅助比较有显式对象、显式系数和完整证明，不需要 comparison、hprod、small-section 或额外强不等式。

#### 5.2 怎样让这个比较真正成为原问题的证明

必须接上三件事：

1. **q 来源：**证明 \(Q_{\rm root}\) 的相应行列式/权重读数就是原来的 q-pilot 读数；保留 qOrder 与 normalized coefficient 之间的真实 correction。
2. **theta 来源：**证明同一运输下 \(H_{\rm root}\) 进入原文允许像的实际 hull，或者给出足以比较体积的真实 determinant 关系。不能只给一个任意集合 Equiv。
3. **归一化：**由路线 B 证明维数、procession、参照及无穷位项的准确对应。若有修正项，代入 (C5) 计算它们是否由实际余量支付，不能假设修正项非负。

这三件事的输出必须是从 T 构造的对象和定理，不是输入给最终定理的新字段。

有一个必须先检验的来源问题：S1902 对正标签取最大范数，所以 j=1 给出半径；原文的 procession 可能保留各个标签块再平均。**先混合所有标签取 hull 与先逐块取 hull 再平均，一般不能交换。** 要证明原文允许的 Ind 作用确实提供所需像；不能把 j=1 随意放入每个独立标签块。

所以我建议将 (C1)–(C5) 作为“实际根侧 q 格比较”交付，然后立即针对真实标签/运输验证上述三件事。它是清晰的候选主链，不是已经证明两个 carrier 相同。

#### 5.3 第二种构造：在真实张量块上计算整数表达

若实际 target 不能直接接收 (C3)，不再强迫整个 S1902 carrier 与 C3 等价。直接在原目标的有限 étale \(\mathbf Q_p\)-块 E 中工作：

- 从原 q-pilot 得到满格 Q 的基 \(q_1,\ldots,q_d\)；
- 从**原文允许的实际像**中选有限个生成元 \(g_1,\ldots,g_r\)；
- 如 hull 是整数生成闭包，将整数环基乘这些元素一并列入；
- 记 G 为这些生成元的坐标矩阵，\(\Lambda_G\) 为其整数生成格，证明 \(\Lambda_G\subseteq H_\Theta\)。

接着构造具体整数矩阵 C，使

\[
Q_{\rm basis}=GC,\qquad C\in M_{r\times d}(\mathbf Z_p).
\tag{C6}
\]

式 (C6) 直接给出 \(Q\subseteq\Lambda_G\subseteq H_\Theta\)，于是得到所需 Haar 比较。

这不是建议新增一个“存在 C”的字段。系数可按以下两种实际算法产生。

**方法一：根的整数幂。** 对来自 (C1) 的坐标，直接使用
\(\alpha_b^{2l-1}\) 及其在整数基中的坐标。将 tensor 的纯张量展开与实际来源映射逐步应用到这些系数，验证每一步仍整。若某个标签导致负幂，则不能把它继续当作整数系数；应寻找真正允许的其他像，而不是删除这个标签。

**方法二：迹对偶或 Smith 标准形。** 从真实 G 选出一个满秩基
\(v_1,\ldots,v_d\)，令 \(v_i^\#\) 为迹配对的对偶基。则

\[
q_j=\sum_i \operatorname{Tr}_{E/\mathbf Q_p}(v_i^\#q_j)v_i.
\tag{C7}
\]

系数已经由原对象确定。下一步是把
\(\operatorname{Tr}(v_i^\#q_j)\) 的整性化为实际不同理想、根阶数和整数张量格的关系，用 IntegralTraceDualLattice、IntegralTraceDualTensorInclusion、PadicLatticeIndexFormula 等工具证明。

若选出的子基过小，改用整个 G 的 Smith 标准形，检查变换后的 q 列对初等因子的整除；不能靠重新定义对偶或给出整性假设跳过这一步。

本路线真正的新数学工作，就是用原输入关系证明这些**已明确写出的系数**整，而不是直接假设目标体积比较。

#### 5.4 如果格包含过强，改用行列式关系

体积比较不要求集合包含。若 (C6) 太强，可退到最大阶子式理想：

\[
I_d(G)=\bigl(\det G_J:\ |J|=d\bigr).
\]

构造一个来自实际源关系的整数线性组合

\[
\det Q_{\rm basis}=\sum_J a_J\det G_J,\qquad a_J\in\mathbf Z_p.
\tag{C8}
\]

则

\[
v_p(I_d(G))\le v_p(\det Q_{\rm basis}),
\tag{C9}
\]

由格指数/Haar determinant 公式得到

\[
\mu(\Lambda_G)\ge\mu(Q).
\tag{C10}
\]

若 (C6) 已有，(C8) 就是 Cauchy–Binet 公式，\(a_J\) 是 C 的对应子式；有时直接在 determinant 上构造 (C8) 比构造整个 C 更弱、更容易。

有分母时同时清分母并在 determinant 中补回相同的 p 幂。最后按原权重聚合；不强行要求每个位置独立满足一个比最终全局目标更强的不等式。

**不能把 (C8)/(C9) 作为新的未证输入。** 应明确列出实际子式、系数以及它们由哪条根/迹/源运输恒等式得到。本轮没有完成真实 C3 的这项计算，不把它标为已闭合。

#### 5.5 与 #4 MULTIRADIAL 的关系

为使用上述有限生成元，必须证明它们来自真实允许像。有限 Q(i)-at-5 模型的生产定理，或给定 RouteNormalForm 的一般 contract，不能自动提供这个事实。

建议把下一包源工作集中为：

~~~text
同一个原文合格输入；
一组具体的 theta/pilot 源元素；
每一步实际 Kummer、log、Ind 运输及其载体；
生成元进入目标 hull 的证明；
q 根关系/迹系数在这些运输下的对应。
~~~

这比“再全树搜索一次 multiradial”更接近直接消费者。只为该比较需要有限像时，不必先构造一个不被消费者使用的更大通用接口；但若完整 multiradial 输出是锁定目标的定义前提，该构造责任仍保留，不能用有限见证代替它。

### 6. 对十项 GAP 的具体改写建议

| GAP | 接下来应做的实际工作 | 不再计为核销的交付 |
|---|---|---|
| #1 GENERAL-CMP | A 接入精确质量；C 构造 q 格/行列式关系；B 计算全部归一化 | comparison ⇔ 某不等式；ConditionOne；新增 hle |
| #2 IQ-LITERAL | 从真实位置/纤维/整数参照构造受限积；证明坐标映射及整性“几乎处处”相容，继而拓扑/测度对应 | 任意 K/O 家族的 Πʳ 改名或 rfl |
| #3 OB33-SRC | B 构造来源 determinant line 及与实际格的同构，再算 degree | 任意 detDegree 与 raw/blockDim 的命名等式 |
| #4 MULTIRADIAL | C 所需实际源像、运输及关系；随后完成目标真正需要的 production | finite 模型改称 actual；RouteNormalForm 作为输入 |
| #5 THETA-V | B 推导逐块权重、维数、参照及 arch 修正，绑定实际 paper V | 四层状态表、自由 scale/offset |
| #6 THETA-D | B 展开实际 donor 构造，证明与独立源端字段对应 | 将字典右端再定义为 C3 自己 |
| #7 THETA-DEG | B 证明真实张量的 degree 乘积/域分解求和，并接到实际权重 | 把 finrank 改名 localDegree；只证非正 |
| #8 CONTRACT | 最后消费已经构造的比较及真实证据，不再留比较参数 | 计数表、映射表、conditional assembly |
| #9 HULL-UB | B 先绑定真实 V，再把 A 精确式或已有上界按实际系数运输 | 仅 scale=1/offset=0 条件；未绑定的 rawV 上界 |
| #10 ARCH-C-K | B 在真实 height/degree 加权和中消费已有系数 | 假设有限 Haar scale 等于全局归一化权重 |

这十项不是十个独立的大小估计：#3/#5/#6/#7/#9 共享来源与归一化，#8 是最终消费者，#1 才是核心比较。按十个编号各写一层接口，不会形成十份独立进展。

### 7. 建议的执行顺序与每包出口

**包 A0：先接现成球质量。** 精确消费者为 Mzk1C3S1902QuantityActual / ComparisonActual / LowerBoundActual；供体为 S1915、S709、S865。删除消费者侧对未知球质量的需求，输出 (A4)–(A6) 的实际版本。已有证明直接复用，不新增一批重复包装。

**包 B0：在同一个实际输入上固定 q 与 theta 的完整读数。** 输出“原输入 → 源索引/纤维 → 张量块 → 格 → 参照 → 权重 → paper 读数”的表及对应定理。每个等式都指向构造或来源引理。先做消费者必需的一个实际块，再按原量词推广。

**包 C0：构造根侧 q 格并证明 (C2)–(C5)。** 不输入 hcomparison。然后直接测试它是否通过 B0 的真实字典进入目标；如果不能，明确首次失配的源箭头，而不是新增一个同名 equality 参数。

**包 C1：在原 C3 块上算实际 G、q 基及迹/SNF 系数。** 交付 (C6) 或更弱的 (C8) 的显式证明；若系数不整，保留具体障碍，改变合法像的选择或证明方法。不能用模型的可满足性代替这项实际计算。

**包 F：完整聚合与最终验收。** 合并全部原文允许像的统一有界性、实际比较、归一化和源证据，再接最终 contract。核对原文量词，不能只在 fiveLabel 或某个固定位置模型上通过。

不要求等待所有包完全证明后才写上层准确陈述；但所有未闭合依赖都保留为未闭合，不能把依赖移入结构字段后报告“消失”。

### 8. 完成报告必须回答的四个问题

每包报告：

1. 哪一个原未证输入已由哪个实际构造/定理消除？
2. 最终消费者的参数清单减少了什么？剩余参数是原文合法输入还是仍欠构造？
3. 同一个 T 的对象、标签、载体、权重和符号是否保持？
4. 对应版本的 statement_compiles、proof_body_checked、kernel_closed、target_accepted 分别是什么？

尤其不能用“#print axioms 只有三公理”代替第二问。当前 S3137 assembly 把 comparison 直接填入 target_le_theta，并在一个形式 contract 中使用 True 的 IPL/SHE/APT 字段；它是给定比较后的标量装配，不是这些源证据的构造。最终应消费真正构造的来源事实，或者只使用经语义核对确实足以证明原目标的最小结论。

### 9. 本轮核对范围、版本及状态

本次是当前聊天 root 的单线程研究与文档追加。读了本计划、相关 P7/R29 记录、上述直接源文件及项目入口；没有重新全仓审计、没有外部调研、没有修改 Lean 源码或当前各 lane 的文件归属。

直接消费者是原有 P7 比较及其字典接口。数学验收目标保持“从原文合格输入构造并证明”，没有把任意更弱数据当作原输入，也没有添加目标等强假设。

本节来源有并行改动；下面指纹用于界定实际核对版本，不代表后来版本已审查。olean 存在仅作现状参考，不能替代对应版本的构建、公理和语义验收。


| 源文件快照 | 字节 | SHA-256 | olean 存在性 |
|---|---:|---|---|
| [S1915ThetaHullA0Actual.lean](D:/lean/tmp/sheaf/xif/paper/S1915ThetaHullA0Actual.lean) | 19348 | 1e38330f641cecfa3afe7c7cd5ae157b4e95113f36fc58e8f47a74c38ffa1aca | 存在 |
| [S709RootImageRadiusFormulaActual.lean](D:/lean/tmp/sheaf/xif/paper/S709RootImageRadiusFormulaActual.lean) | 6857 | b531b905883cb5fc2abfaf70cab1ec9024d6443f4dbe49f35f65a49f367c34f8 | 存在 |
| [S865RootHaarFactorNormPowActual.lean](D:/lean/tmp/sheaf/xif/paper/S865RootHaarFactorNormPowActual.lean) | 4192 | adaa6510c6ac8eeb145cd4bdd95000d49f44d87574654f0c93c94fd068b176a0 | 存在 |
| [Mzk1C3S1902BridgeActual.lean](D:/lean/tmp/sheaf/xif/paper/Mzk1C3S1902BridgeActual.lean) | 4940 | 70e99131136602e530805fc7762bb59b78e1fa717905cd32d023cbdeb653cefe | 存在 |
| [Mzk1HullUBDictionaryActual.lean](D:/lean/tmp/sheaf/xif/paper/Mzk1HullUBDictionaryActual.lean) | 3300 | faeb42e37624bb3fb89dfd62aa04659e74eb130bcba60aa861fcc848dc42351f | 未见 |
| [Mzk1C3DKeyMapActual.lean](D:/lean/tmp/sheaf/xif/paper/Mzk1C3DKeyMapActual.lean) | 2906 | f118709a093978a45b9356bc03ded519d3c1c48a03bd2ea3d4bce3d80d22b538 | 存在 |
| [Mzk1Ob33SourceIdentificationActual.lean](D:/lean/tmp/sheaf/xif/paper/Mzk1Ob33SourceIdentificationActual.lean) | 3925 | 81c4063c58a8584affd7c426d7a6197050c81ce4383445545c8a0bb5dc15a690 | 未见 |
| [Mzk1NormArchAbcHookActual.lean](D:/lean/tmp/sheaf/xif/paper/Mzk1NormArchAbcHookActual.lean) | 2143 | 56f2fe8f6617837ed72d5d5e67cec1d4761f4bc1e09cb83d7b0d86e891f4ac4d | 存在 |
| [Mzk1PadicBallCeilActual.lean](D:/lean/tmp/sheaf/xif/paper/Mzk1PadicBallCeilActual.lean) | 4289 | 852815181d347c1a335cd866b9ad6243074a8e02b313253b6107b6eae9c1477f | 未见 |
| [Mzk1P7ContractMapActual.lean](D:/lean/tmp/sheaf/xif/paper/Mzk1P7ContractMapActual.lean) | 5296 | 1b642356af25425331b29eff26b0b13470bb8f284503550a461f723f74d0c20e | 存在 |

本轮状态：statement_compiles = NOT_RUN；proof_body_checked = NOT_RUN；kernel_closed = NOT_RUN；target_accepted = NOT_RUN；独立审查 = NOT_RUN（同一助手自查）。没有把候选路线或旧 olean 的存在性写成新的数学验收。

本轮可交接的新增内容是：S1915 精确质量公式到现有 P7 消费者的复用链；从根关系产生整数系数的 q 格比较；同源字典/相对行列式的构造步骤；以及一般分歧球的 ceil 公式、Haar 比例与 degree 权重之间的具体修正。**最终仍以消除所有非原文输入、完整证明原目标为准。**

**并行更新说明。** 追加期间，原表另将 #9 标为“DISCHARGED（paper V at k=0）”，并给 #10 增加次数为 1 的实例。本轮未重新验收这些更新对应的全部源码及原文语义；本节对先前接口的判断以上表指纹为界，不覆盖新增记录。若 k=0 的来源识别已通过验收，应直接复用并从 B0 中扣除这一已完成部分；一般 k、一般原输入范围及一般 K 的归一化仍须按实际目标逐项处理，不能由特例自动推广。下一包仍建议先完成 A0 的具体接线。

<!-- END P7-NO-EXTRA-INPUT-ROUTES-20261113 -->

<!-- EXECUTION-STATUS-20261113-EVENING -->
## 执行状态（按本文件追加的 A/B/C 路线，Lead 分派）

- 路线 A（球质量精确接线）→ abc：S1915 s1915_local_measure/:251 s1915_hull_toReal + S709 :128/:145 + S865 :35 接入 C3S1902；删除 hball/hprod；放弃错误 ceil 假设（改 (A7) 或直接用 (A1)-(A5)）。
- 路线 B0/B #2 → qpilot：真实位置/纤维/整数参照构造受限积与 Equiv；不再用任意 K/O 家族改名。
- 路线 B #3/#8 → mainline（+shehdd 支援）：构造 det(x)M determinant line、相对 determinant 同构、(B5) 逐位/无穷位计算；#8 消费已构造比较而非参数装配。
- 路线 B #5/#9 → hull：绑定 rawV 到实际 paper V（(B6) V=ΣaL+β），不假设 a=1/β=0。
- 路线 B #6/#7 → hull/stage4：#6 展开 S2717C3 实际 donor 与 D 侧独立对应；#7 真实张量块域分解 (B1)/(B2) 后再算 degree 权重。
- 路线 B #10 → lattice：接真实 heightWeight 加权和，不假设 Haar scale=C_K。
- 路线 C0/C1 → stepxi：构造根侧 q 格 (C1)-(C5)，然后检验 5.2 三件事并报首次失配源箭头。
- 路线 C1 的实际 C3 系数（迹/SNF）待 C0 完成后由 stepxi/hull 接力。

完成验收按本文件 §2：取消为了证明目标新增而未能从初始数据构造的输入；条件等价、计数表、conditional assembly 不计核销。

<!-- BEGIN P7-REUSE-CORRECTION-20261113 -->
## 查重补充：已有供体与建议任务的缩减（2026-11-13，当前 chat 单线程）

用户追问是否已逐一检查全仓定理，以免安排重复证明。**准确回答：没有逐一定理检查全仓；上一轮是目标附近的有界核对，不能据此保证建议完全没有重复。** 本轮针对 A0/B0/C0/C1，补查主库 `LeanFormal`、`Iut`、`PadicLogVolume` 和 `tmp/sheaf` 中的相关声明，再阅读命中文件的实际陈述、定义与证明段。关键词检索只负责找候选，不等于全库语义查重。

本轮的实际消费者是上文执行计划，目标是缩减“需要新证”的范围。阶段为研究/复用核对；未改 Lean、未运行编译、未调度 agent、未修改已有 owner。版本指纹记录于 `dag/nodes/p7-no-extra-input-routes-20261113.json` 的 `reuse_review`。旧调查与执行记录保留，以下是对本 chat 建议的修订。

### 1. 明确应复用的部分

| 原建议中的步骤 | 本轮核对到的已有声明 | 调整后的工作范围 |
|---|---|---|
| A0：实际球质量 | S1915 的 `s1915_local_measure` 上一轮已列为供体；当前 [Mzk1PadicBallCeilActual](D:/lean/tmp/sheaf/xif/paper/Mzk1PadicBallCeilActual.lean) 另已有 `rootExtension_ballMass_eq_radius_pow` 和 `rootExtension_ballMass_eq_p_rpow` | 不重证球质量，不另造同义包装。继续处理消费者的具体代入及实际 transport；本轮快照未见该文件 olean，已有源码由原 owner 验证 |
| A0：把半径对数化为加权系数和 | 较早的 [Mzk1S1915ComparisonActual:69](D:/lean/tmp/sheaf/xif/paper/Mzk1S1915ComparisonActual.lean:69) 已有 `s1915ClosedForm_eq_one_sub_sum` | 不重做这段求和代数。注意该量是 `1 + normalizedLog`；转成实际相对 log 时需减去 1，不能偷换归一化 |
| B0/#7：实际张量的域乘积分解 | 主库 [FinitePlaceArithmeticTensorBlockFields:25](D:/lean/LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlockFields.lean:25) 的 `exists_arithmeticTensorTuple_fieldProduct`，第 39 行还有整包版本 | 已从真实 `places/tuple` 构造分解，并提供各域有限维、完备及双向连续性。**不再安排从头证明有限 étale 分解或连续性**；实例化到实际 C3，接入维数与源权重 |
| B0/#7：域分解后的维数求和 | 当前 [Mzk1P7ThetaDegB2Actual:18](D:/lean/tmp/sheaf/xif/paper/Mzk1P7ThetaDegB2Actual.lean:18) 已有 `finrank_arithmeticTensorTupleBlock_eq_sum_fieldProduct` | 这个定理仍输入 `e`；上一行的主库存在定理可供应该参数。剩余是实例接入与对应版本验证，不是另设一个分解假设 |
| C：q 区域到根侧 theta hull 的包含和 log 单调性 | 较早的 [RootHullContainmentInequalityActual:81](D:/lean/tmp/sheaf/xif/paper/RootHullContainmentInequalityActual.lean:81) 有 `qPilotClassicalRegion_subset_rootHull`，第 123 行有 log 比较；[RootQPilotContainmentActual:88](D:/lean/tmp/sheaf/xif/paper/RootQPilotContainmentActual.lean:88) 有根系数模型的包含 | 不重写这些一般包含/单调性证明。前者仍需实际系数次序、缩放数据、正质量及有限性；后者的根侧区域也未自动等于当前 P7 的两份区域 |
| C0：显式根幂系数产生的局部及乘积包含 | 当前 [Mzk1RouteC0RootQLatticeActual:104](D:/lean/tmp/sheaf/xif/paper/Mzk1RouteC0RootQLatticeActual.lean:104) 已有 `c0QLattice_subset_alpha`，第 127/131 行有乘积包含和 Haar 单调性 | 不另建第二份 C0。保留原 owner 的实现并验证；继续处理实际目标对应。`c0Remainder_nonneg` 已有证明体，但当前文件还没有把该表达式证明为两份实际 log 质量之差，不能把整条 (C5) 算完 |
| C1：迹对偶、不同理想清分母、SNF/行列式指数 | [IntegralTraceDualTensorInclusion:993](D:/lean/LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualTensorInclusion.lean:993) 已有实际张量上的不同理想乘法包含；[IntegralTraceDualLattice:226](D:/lean/LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualLattice.lean:226) 已有商群基数与行列式赋值公式；`PadicLatticeIndexFormula` 已有有限自由情形的 SNF 公式 | 上一轮已把这些库列为工具，本轮明确到声明。不要重建一般理论；新证明只针对原目标的生成元、系数整性和精确损失能否被已有根阶数吸收 |
| B0/#5/#9：S1915 读数的常数项 | 当前 [Mzk1HullUBPaperVRawBindingActual:25](D:/lean/tmp/sheaf/xif/paper/Mzk1HullUBPaperVRawBindingActual.lean:25) 已有 `closedForm_eq_one_add_normalizedLog`，第 43 行给出系数和 | 直接复用 `+1` 的真实公式，不再尝试任意取 offset=0。仍须核对这份读数如何对应独立给定的论文 V |

其中有此前即存在的供体，也有上一轮之后版本发生变化的当前实现。`Mzk1PadicBallCeilActual` 已不同于上一节记录的 SHA；不能把所有新增源码都说成上一轮遗漏。另一方面，较早的域分解、包含及系数和公式，应当在交接里明确列出，上一版对此不够完整。

### 2. 一个可以直接消去现有参数的复用连接

`Mzk1P7ThetaDegB2Actual` 中的 `e` 不必一直作为外加输入保留。已有主库供体给出以下步骤：

1. 用实际 C3 的 `places`、`tuple` 调用 `exists_arithmeticTensorTuple_fieldProduct`。
2. 从存在见证取得 `J/E`、域与代数实例、`e`；将逐因子的 `FiniteDimensional` 证明安装为局部实例。
3. 调用现有 B2 的维数定理，输出“实际 C3 存在这样的分解及维数等式”，或在消费者内直接消去存在量词。
4. 若需要整个 packet，复用 `exists_arithmeticTensorBlock_fieldProducts` 与 `arithmeticBlockFieldAlgEquiv`；无需逐块再证明分类。

这是基于已读声明的具体接入步骤，本轮未编译。它能消去“存在某个有限域分解”这一输入，**不能自动证明这些域因子就是另一个独立源端预先指定的因子，也不能自动给出论文的全部 degree 权重**；后两件事要使用相应的源映射证明。

### 3. 查重后仍然需要推进的工作

- **A0 收窄为消费者代入与 transport。** 当前 `Mzk1C3S1902QuantityActual` 仍停在球质量乘积，`ComparisonActual` 仍接受 `C3S1902TransportData`。`LowerBoundActual` 头部“未找到显式球质量公式”的文字已被供体证据推翻，应由原 owner 修正；不据此新开球质量研究任务。
- **B0 收窄为同源识别。** 已有域分解、维数求和、相对 log 与常数项的代数不能重复建设。真正要补的是同一个原始输入到 C3、根侧对象及原文加权读数的箭头。
- **C0 收窄为原目标对应及尚未接上的精确质量差。** 现有局部包含值得复用；仍要证明它比较的两份区域、归一化和标签确实是原目标需要的那些对象。标签并集的包含不自动给出逐标签平均的结论。
- **C1 仅计算实际系数。** 先复用迹对偶/不同理想/SNF 定理，再核算实际 q 基在实际 theta 生成元中的系数。一般工具已经存在；目标相关的系数整性仍不能假设。

已有 `coord/ROUTE-A-REUSE.md` 与 `coord/REUSE-AUDIT-HULL.md` 还记录了源 q 读数、HDD 高秩行列式等供体和对象差异。它们应作为后续查找入口，本轮没有把其中未逐项重核的记录升级成当前版本的证明验收。

### 4. 对“是否重复安排”的最终说明

**存在需要缩减的任务描述；不能回答“已经全查过，保证无重复”。** 本节已把确认有供体的基础步骤改为复用或接入。上方 Lead 的任务归属保持，旧记录不删除；本 chat 没有向其他 chat 发出新任务。

后续从本建议提取具体证明任务时，记录“精确消费者目标—现有供体声明—对象/假设差异—最小剩余证明”。若供体完整覆盖目标，任务就是调用和验证；检索未找到则记录“本轮未找到”，不声称全仓不存在。仍以无额外困难假设地完成原目标为验收标准。

本轮 `statement_compiles` / `proof_body_checked` / `kernel_closed` / `target_accepted` 均为 NOT_RUN；源码阅读及 olean 存在性不替代构建和语义验收。

### 5. 用户补充的全仓索引：D:/lean/iut-audit-20261113

已按用户补充查阅 [PROGRESS-AUDIT.md](D:/lean/iut-audit-20261113/PROGRESS-AUDIT.md)、[R29-HANDOFF-EXECUTION.md](D:/lean/iut-audit-20261113/R29-HANDOFF-EXECUTION.md)，并定向检索 sections 的文件/声明清单。该目录确有帮助：它覆盖的文件范围比上一轮直接源核对更广。其自述方法是“文件清单 + 首部声明 + olean 存在性 + 文档引文”的静态登记，不能把读过该索引说成已逐一定理检查完整证明。

索引再次确认上面的旧供体，并进一步定位到下列内容；本轮已回到当前源码核对：

- `sections/07-iut-modules.md` 登记了实际张量域分解和迹对偶主库；`sections/06b-mzk1-keyfiles.tsv` 已登记 `Mzk1S1915ComparisonActual`。这些应进入具体任务的复用清单。
- `sections/07b-tmp-sheaf-inventory.txt` 定位到 [RootNormalizedContainmentActual.lean](D:/lean/tmp/sheaf/xif/paper/RootNormalizedContainmentActual.lean)：不仅有一般包含，还已有 `rootHalfCoefficient_le_norm`、`rootNormScalingData`、`qPilotNormRegion_subset_rootNormHull` 及 `qPilotNormLog_eq`。因此对这个 **c_norm/(2l) 的 qVFam 块模型**，系数次序与 normalized scaling data 也不应重新安排构造。余下 log 比较仍带正质量/有限性；它是否对应原文系数与当前 S3137 目标要另证。
- 同一索引中的 `BadPlacePaperRootThetaHullActual` 使用 `order(q)/(2l)` 的另一份系数，并保留 `PaperRootHullFormulaGap.data/hull_eq`。不能因前一个 normalized 模型有证明，就把这两个字段算作已提供。
- `tmp/sheaf/n8/closure/EtaPAdicDetHaarScalingActual.lean` 虽有对应产物记录，其主结论仍输入 `MissingPAdicLatticeIndexDetBridge`；`EtaBasisChangeDetIndexActual` 的行列式等式仍输入实际矩阵关系和单位行列式证明。它们能复用代数步骤，不能据文件名或 olean 把一般 det/Haar 桥从剩余任务中删除。

`R29-HANDOFF-EXECUTION.md` §10 已区分 S3137/Paper312Statement 的当前比较与旧的含零标签 hull；这一现成版本说明应直接继承，避免重复完成旧模型再当成目标进展。本轮没有重做其历史调查，也未把其历史构建记录当作当前构建。

检索说明：03 分片的部分 Markdown/TSV 含 NUL，普通 `rg` 会提示停止按文本搜索；本轮相关查找已用 `rg -a` 补查。因此对索引中未命中的名字，不作“仓库没有”的结论。
<!-- END P7-REUSE-CORRECTION-20261113 -->
