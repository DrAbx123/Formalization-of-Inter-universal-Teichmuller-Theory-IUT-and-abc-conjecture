# 一般 D⊢ / DPrimeStrip 箭头：实际 realization 与全部箭头覆盖路线

日期：2026-11-14。负责人：当前 chat / root，单线程。

交付范围：自然语言数学证明、现有供体查重、源语义及消费者连接建议。遵用户要求，不修改 Lean，不编译，不启动其他线程，不重新全仓审查。本文中的新引理名称均为建议名称，不表示已有同名 Lean 定理。

实际目标：对原文允许的每一个非阿基米德 procession 箭头，构造它在实际局部整数单位模挠群、log 像、log-shell 上的作用，证明它来自该箭头，并覆盖原文 Ind1 的量词。最终消去 `Ind1ShellTransportForRequired` 的额外输入；必要时构造乘法层 `isoMon`，而不是只制造一个同维线性同构。

证据版本与读写范围见 `dag/nodes/ind1-dprime-realization-routes-20261114.json`。四项验收 `statement_compiles / proof_body_checked / kernel_closed / target_accepted` 均为 **NOT_RUN**。自然语言证明不等于机器闭合。

## 0. 建议采用的主线

**先复用已有 F→D 的 transition lifts，把一般箭头分解为基点自同构；对基点自同构，通过“惯性 → 拓扑阿贝尔化 → 已有 Artin 单位等价”构造单位作用。需要完整乘法层时，再恢复标准 Frobenius，用 transfer 把所有有限扩张上的作用粘起来。最后按原文 Ism-orbit 消化 realization 的选择。**

这是三个可先后验收的层次，而不是三个互不相干的大工程：

1. **单位层短路线**：消去局部 `β_a` 的来源缺口。新核心是惯性的群论可识别性；局部互反律供体已经存在。
2. **完整乘法层路线**：在第一层上增加 Frobenius 保持性与有限层自然性，构造一般箭头的 `isoMon`。无需证明箭头来自域同构，也无需恢复域的加法。
3. **procession / Ism 覆盖路线**：把前两层应用于每个真实 component，证明覆盖全部原文箭头；选择不同 realization 的差用现有 Ism 定理处理。

这里的“无条件”指：仅用原文合格初始数据与原文箭头，不增加 `hβ`、`hasLift`、`inertiaPreserved` 或最终 log-square 假设。中间待证引理必须由实际算术对象证明，不能变成最终调用者要提供的新字段。

## 1. 查重结果：什么已经有了，什么才是真正的新工作

| 内容 | 已读到的实际供体 | 本次判断 |
|---|---|---|
| 已选 theater links 的 F-level 运输 | `SourceH1H2Construction.fLinkAt`、`dLinkAt`；`SourceDThetaConstruction.fPrimeStripVerticalCore` | 已有构造；不要重做 |
| F/D core 及其箭头严格对齐 | `fdPrimeStripVerticalCore_core_toD / member_toD / vertical_link_toD / core_link_toD` | 已有对齐；仅覆盖指定 links |
| 单位到阿贝尔惯性 | `tmp/local-cft-port/Reciprocity/ArtinInertia.lean` 的 `PadicField.unitsInertiaEquiv`，L246；`artin_injective`，L133 | 有实际定义及证明体；不是新增局部互反律任务 |
| 整个阿贝尔 Galois 群的结构 | `Reciprocity/GaloisStructure.lean` 的 `galAbEquiv`，L268；`galAbEquiv_artin'`、`galAbEquiv_snd` | 已有 `G_F^ab ≃ₜ* O_F^× × Zhat`，可直接用于 Artin 像识别 |
| 无分歧商及标准 Frobenius | `PadicField/UnramifiedZHat.lean` 的 `galMaxUnramifiedEquiv`、`galMaxUnramifiedEquiv_frobUr`；`Reciprocity/Artin.lean` 的 `mk_eq_arithFrob_of_artin` | 已有实际算术模型；尚须证一般 Galois 箭头保持它 |
| 域包含对应 transfer | `tmp/local-cft-port/Brauer/ArtinTransfer.lean` 的 `PadicField.artin_transfer`，L246 | 已有核心兼容公式；仍需接入任意 open-subgroup 的重索引图 |
| norm / restriction 兼容 | `Reciprocity/NormCompat.lean` 的 `artin_baseChange`，L416 | 已有供体；注意它与 transfer 的方向不同 |
| 共轭自然性 | `Reciprocity/Conjugation.lean` 的 `abRec_conj`，L410 | 有有限层公式；无限层通过限制到有限商证明 |
| 项目对 local CFT 的接入 | `S2027LocalArtinActual.galoisGroupMaximalAbelian`；`S2098M2aCoreActual.unitProfiniteCompletionEquivGal` | 项目已经在用这批对象，不是孤立外部材料 |
| 固定域模挠像、Ism 与比较的选择差 | `TimesMuKummer.invariantImage`、`Isomorphism.sourceDifference`、`Isomorphism.orbitOf_eq` | 已有；应复用 |
| 任意 Galois 箭头保持惯性 / 标准 Frobenius | 本次定向搜索没有定位到可直接消费的无条件定理 | 新数学节点，下面给证明 |
| 原文全部 procession 箭头的实际 realization、所选局部域与 capsule 运输 | 现有 chosen links / permutation 构造不足以单独给出 | 真实 source 覆盖节点 |

以上是源码层面的证据，不是本轮重编译结果。尤其不能把 local CFT 目录的旧说明、旧构建记录，或“未搜到 sorry”，写成本轮传递公理验收通过。

历史更正：此前 `IND1-UNIT-QUOTIENT-GAP.md` §E 及相关调查把惯性路线描述为“未找到局部互反律供体”。现在应收窄为：**actual `unitsInertiaEquiv` 已有；缺的是源箭头上的惯性识别、carrier 对齐与自然性。** 不再安排从头证明 local CFT。

## 2. 先锁定正确的箭头域，避免证明错命题

### 2.1 原文所需的不是任意弱结构的自同构

`PrimeStripCore.lean` 的 `DPrimeStrip` 只有 `Pi / G / proj / proj_surjective`；`DPrimeStripEquiv` 只有群同构及投影交换。这个弱类型本身不包含拓扑、局部域、整数单位或实际 Galois realization。

IUT III Prop. 1.2(vi) 的对象是 `D⊢_v = B(G_v)^0`，要求从这个 Galois 范畴函子性构造 log 模块及 log-shell。Thm. 3.11(i) 的 Ind1 是 **D⊢ procession 的自同构**。因此正确量词是：原文合格对象及其全部原文箭头；不是任意抽象群拼成的 `DPrimeStrip`。

对实际对象，必须从它的构造证明一次：

\[
r_v:G_v\simeq_{\rm top}G_{F_v},\qquad
G_{F_v}=\operatorname{Gal}(\overline F_v/F_v).
\]

给实际箭头 `a` 后取

\[
\alpha_{a,v}=r'_{a(v)}\circ a_v\circ r_v^{-1}.
\]

若原文从有限 étale 对象的范畴给箭头，可选 fiber functor 得到此连续群同构，选择差为内自同构；需要在 source adapter 中证明这一点。若实际 constructor 已存储连续群箭头，直接保留该数据即可。不要先擦除拓扑，再把“所有抽象群同构连续”当免费步骤。

这是保留原文箭头语义，不是人为缩成“那些碰巧有 lift 的箭头”。相反，把原文允许箭头定义为已有 F-lift 的像，再用定义证明覆盖，才会把真正缺口藏掉。

### 2.2 实际有限域层必须有自己的 open subgroup

`LocalPrimeStrip.localFPrimeStrip` 的 `Mon` 是 `(AlgebraicClosure Q_p)^×`，`G` 是实际 `G_{Q_p}`。如果消费者要的是某个 `K_v/Q_p`，必须使用它对应的 open subgroup `H_v`；对整个 `G_{Q_p}` 取固定点只会得到 `Q_p`。

可复用 `S2027LocalArtinActual` 已有的 `localField p U`、`localGaloisGroup p U` 及拓扑阿贝尔化字典。对实际 completion 先选 `K_v → AlgebraicClosure Q_p`，证明其像是对应固定域，再运输单位和 log-shell。该选择只在对象层做一次，不能为每个箭头另找域同构。

箭头必须把所选 `H_v` 运输到目标对应 subgroup；若它运输到另一个 capsule/域层，目标应随之运输，不能强迫它仍落在原固定 slice。

### 2.3 p 的范围

下文固定同一原文非阿基米德 `p`-packet，允许任意有限 `F/Q_p`，包括野分歧扩张及 `p=2`。使用 tame quotient 不等于额外假设 `F/Q_p` tame。跨不同 residue characteristic 的箭头，必须另从原文 place 数据证明 p 的对应；本文不以任意 place permutation 偷换该条件。阿基米德部分也不由下述 p-adic 构造覆盖。

## 3. 第一项实质缩减：全部箭头 = 已有运输 + 基点自同构

在一个实际连通分量内选基点 `D_*`。对每个成员 `D_i`，复用已有 transition

\[
t_i:D_*\longrightarrow D_i
\]

及其已有 F-lift `\widetilde t_i`。一般 procession 箭头包含位置置换 `σ` 与 component `a_i:D_i→D_{σ(i)}`。定义

\[
s_i=t_{\sigma(i)}^{-1}\circ a_i\circ t_i\in\operatorname{Aut}(D_*).
\]

则严格有

\[
a_i=t_{\sigma(i)}\circ s_i\circ t_i^{-1}.
\]

因此，只要对 **每个** 基点自同构 `s` 构造单位作用 `β_s`，一般 component 的作用就是

\[
\beta_{a_i}=\beta_{t_{\sigma(i)}}\circ\beta_{s_i}\circ\beta_{t_i}^{-1}.
\]

后两侧的 transition 运输已有来源。这不是声称所有自同构由现有 links 生成；剩余的 `s_i` 正是尚须处理的全部 stabilizer。

若 procession 的定义还要求 component 与 transition 图交换，则可用自然性推出相应 `s_i` 一致；没有该条件时必须保留整族 `s_i`。不同连通分量分别选基点。

`MultiradialProcessionActual.PrcAutomorphism.component` 当前已经是 `FPrimeStripEquiv`，`ofPerm` 用的是 `PrcTransition`。这适合消费已构造的 lifts，但不能反过来作为“一切原文 D⊢ 箭头都可提升”的证明。

## 4. 单位层主路线：从惯性的内在刻画构造 β

### 4.1 要证明的局部命题

对任意有限 `F,F'/Q_p` 和连续群同构

\[
\alpha:G_F\xrightarrow\sim G_{F'},
\]

从 `α` 构造

\[
\widetilde\beta_\alpha:O_F^\times\xrightarrow\sim O_{F'}^\times,
\qquad
\beta_\alpha:W_F\xrightarrow\sim W_{F'},\quad
W_F=O_F^\times/\mu(F).
\]

证明单位、复合、逆及实际 log-square。没有额外 `inertiaPreserved` 参数；它是下一个要证的引理。

### 4.2 惯性可识别性的完整群论部分

记 `P_F` 为 wild inertia，`I_F` 为 inertia，`q=|k_F|`。从实际 tame extension tower 得到

\[
H_F:=G_F/P_F\cong T_F\rtimes\widehat{\mathbb Z},\qquad
T_F=I_F/P_F\cong\prod_{\ell\ne p}\mathbb Z_\ell(1),
\]

其中标准 arithmetic Frobenius 通过乘 q 作用于 `T_F`。可以选择 splitting 进行证明；最终对子群的刻画不依赖 splitting。

**第一步：Frobenius 的 `Zhat` 作用忠实。**

对每个整数 `n≥2`，令 `m=q^n−1`，则 `m` 与 p 互素，q 在 `(Z/m)^×` 中的阶恰为 n：`q^n≡1`；若 `0<k<n`，则 `0<q^k−1<q^n−1`，不可能被 m 整除。如果 `t∈Zhat` 在所有 prime-to-p roots 上作用恒等，则在这些 m 层上 `t≡0 mod n`。对所有 n 成立，故 `t=0`。

**第二步：`P_F` 是 `G_F` 的最大闭正规 pro-p 子群。**

先证明 `H_F` 无非平凡闭正规 pro-p 子群 N。由于 `T_F` 是 pro-prime-to-p 群，`N∩T_F=1`。正规性给出 `[N,T_F]⊆N∩T_F`，故 N 中每个元素都中心化 `T_F`。第一步的忠实性迫使 N 到 `Zhat` 的投影为零；所以 `N⊆T_F`，进而 `N=1`。

实际 `P_F` 本身为闭正规 pro-p 群。任何其他闭正规 pro-p 子群映到 `H_F` 后必平凡，因此包含于 `P_F`。这个刻画只依赖拓扑群和 p，故

\[
\alpha(P_F)=P_{F'}.
\]

**第三步：`T_F` 是 `H_F` 的最大闭正规阿贝尔子群。**

设 A 为任意闭正规阿贝尔子群，`a∈A` 在 `Zhat` 中的像为 t。把 `T_F` 写成加法群。对任意 `x∈T_F`，正规性给

\[
[a,x]=(q^t-1)x\in A\cap T_F.
\]

A 阿贝尔，所以 a 与这个交换子也交换，得到

\[
(q^t-1)^2x=0\qquad(\forall x\in T_F).
\]

逐个 `Z_ell(1)` 分量来看，标量环 `Z_ell` 无非零幂零元，故 `q^t−1=0`。由第一步 `t=0`，从而 `A⊆T_F`。而 `T_F` 自己就是闭正规阿贝尔子群，所以它被所有连续群同构保持。

**第四步：恢复 inertia。**

`I_F` 正是 `G_F→H_F` 下 `T_F` 的逆像。因此

\[
\boxed{\alpha(I_F)=I_{F'}.}
\]

这四步没有用局部域加法重构、IUT 3.12、不等式或待构造的 β；不存在上述对象之间的循环依赖。

### 4.3 tame presentation 自身怎么做，不能当输入略过

本次定向搜索没有定位到完整可用的 `G_F/P_F = T_F ⋊ Zhat` 供体。应登记一个实际算术证明节点，按以下有限层路线构造：

1. 复用 port 的 `Unramified / MaxUnramified / UnramifiedZHat`，得到 `F^ur`、全部有限 unramified layers 与 arithmetic Frobenius。
2. 对 `(n,p)=1`，在 `F^ur` 中用 Hensel 证明单位 n 次幂可解；其剩余域为代数闭包，且 n 在整数环中可逆。
3. 选择实际 uniformizer `π`，在代数闭包中取兼容 `π^(1/n)`。证明有限 tame totally ramified extension 在无分歧基变换后由这种根生成：先把 uniformizer 的幂关系写成单位乘 π，再利用第二步消掉单位。
4. 因而 `F^t = ⋃_(n,p)=1 F^ur(π^(1/n))`。由根的作用得到 `Gal(F^t/F^ur)=lim μ_n = ∏_(ell≠p) Z_ell(1)`。
5. Frobenius 对 `μ_n` 的作用为 q 次幂；作用于根的公式给出 tame inertia 的共轭关系。统一根选择不是最终对象的数据：证明得到的是全部 tame 扩张的复合域即可去除选择依赖。
6. 通过有限 Galois 扩张的 ramification filtration 证明 kernel `P_F` 为 pro-p：`G_1` 是 p 群，`G_0/G_1` 的阶与 p 互素；再取逆极限。

第 3、6 步是需要写实的局部估值论内容，不能用“tame 是标准事实”冒充项目已有证明。但它们是有限层可核查的数学命题，且不依赖新 β，也不依赖 IUT 的目标不等式。这里不需要先形式化整个 ramification 理论的所有结论。

现有 `S2447WildTameInertiaAPI` 的命名不能直接当该供体：它把 `PadicAbsoluteGaloisInertia` 作为 wild inertia；后者在 `S2442InertiaAPI` 中定义为对 prime-to-p roots of unity 作用的 kernel，按实际算术语义对应 ordinary inertia。应以 `Gal(Fbar/F^t)` 与 `Gal(Fbar/F^ur)` 区分 P、I，核实后再接旧 API，不沿错标签继续推进。

### 4.4 现在直接消费已有 Artin 单位等价

用**拓扑阿贝尔化**

\[
G_F^{ab}=G_F/\overline{[G_F,G_F]},\qquad
J_F=\operatorname{im}(I_F\to G_F^{ab}).
\]

惯性闭且紧，其像也是闭的。通过实际 Galois correspondence，`J_F` 等于 `Gal(F^ab/F^ur)`，即 port 的 `abInertia`。`S2027LocalArtinActual.galoisGroupMaximalAbelian` 已提供核心 carrier 字典。不要把没有闭包的抽象 `Abelianization` 偷换进来。

`PadicField.unitsInertiaEquiv` 给出

\[
\rho_F:O_F^\times\xrightarrow\sim J_F.
\]

其源码 `unitGroup p F` 是 `F^×` 中 norm=1 的子群。与 `(Integers F)^×` 的桥由“u 与 u⁻¹ 都整 ⇔ |u|=1”构造，不是新假设。

由惯性保持性得到 `α^ab|J_F:J_F≃J_F'`，定义

\[
\boxed{\widetilde\beta_\alpha
=\rho_{F'}^{-1}\circ(\alpha^{ab}|_{J_F})\circ\rho_F.}
\]

群同构自动保持有限阶元素，所以它下降为 `β_α:W_F≃W_F'`。身份、复合、逆由上述公式消去中间 `ρ` 直接得到。这一步是实际构造，不是接受 `Nonempty β`。

连续性有两条已知落地方式：由 `continuous_artin` 加 compact→Hausdorff 双射得到单位 Artin 同胚；或在模挠后用实际 `W_F≅Z_p^[F:Q_p]` 与 p^n 邻域基。无需另向用户索取连续性。

### 4.5 log-square 与线性化

复用实际局部对数的 kernel=μ(F)、单位模挠到 log 像的等价。令 `λ_F:W_F≃log(O_F^×)`，定义

\[
B_\alpha=\lambda_{F'}\circ\beta_\alpha\circ\lambda_F^{-1}.
\]

于是

\[
B_\alpha(\log u)=\log(\widetilde\beta_\alpha(u)).
\]

这不是声称 β 是域同构、因而可与对数级数逐项交换。`B_α` 是由单位商上的真实作用运输得到，交换式来自构造及 log 的 kernel 定理。

`B_α` 是实际 Z_p 格之间的同构；由连续性与整数的稠密性得到 Z_p 线性，再延伸到 Q_p-span。复用 `Mzk1Ind1UnitQuotientActual`、现有 rational/continuous scalar 链即可。

若实际 shell 是某个标量倍的 log 格，仍须检查原文的标量及其 p/e/f 依赖被保持，不能把 shell 默认为 `log(O_F^×)`。下面 §5 的 q、degree、e 恢复正好提供这些校准量。等价保持原格给出 lattice transport；log-volume 的原归一化还须明确引用该格/degree 字典。

## 5. 进一步构造真正的 isoMon：Frobenius + Artin 像 + transfer

如果下游只需 β，§4 已是优先路线。若 source provenance 或已有 `FPrimeStripEquiv` 消费者要求完整乘法层，应沿同一构造继续，而不是转去寻找域同构。

### 5.1 先恢复 q，再恢复标准 Frobenius

`J_F≃O_F^×` 的 prime-to-p torsion 恰为 Teichmüller 部分 `μ_(q−1)`，阶 q−1。证明用剩余域单位群及 Hensel lift：prime-to-p roots 的 reduction 单射、每个剩余域非零元有唯一 Teichmüller lift。因此 α 诱导的 `J_F≃J_F'` 给出

\[
q_F=q_{F'}.
\]

这是复用实际单位结构的有限计数，不需要预设两域同构。

现在看 tame quotients。`α` 已保持 `T_F`，在无分歧商 `Zhat` 上作用为乘某个 `u∈Zhat^×`。选择 `T_F≃∏ Z_ell(1)` 与目标的坐标。连续群同构逐个 pro-ell 分量为 Z_ell 线性，因此与整数标量 q 交换。Frobenius 共轭公式迫使

\[
q_F=q_{F'}^{\,u}
\quad\text{作为 }\prod_{\ell\ne p}Z_\ell^\times\text{ 中的作用标量。}
\]

由 q 相同和 §4.2 的忠实性，`u=1`。故 α 在两侧标准 Frobenius 坐标下诱导恒等的 `Zhat` 映射。

**注意：这里只恢复 quotient 中的 arithmetic Frobenius，不选择也不要求保持 G_F 中某个 Frobenius lift。** 后者相差惯性，本来就不应加入不必要约束。

### 5.2 从 completion 中识别实际 F^×，不是只得到 profinite completion

记

\[
\nu_F:G_F^{ab}\longrightarrow\widehat{\mathbb Z}
\]

为标准无分歧商，`rec_F:F^×→G_F^ab` 为已有 Artin 映射。需证

\[
\boxed{\operatorname{im}(rec_F)
=\nu_F^{-1}(\operatorname{im}(\mathbb Z\to\widehat{\mathbb Z})).}
\]

这个等式已有很短的证明：`rec_F(π)` 投影为 1，单位投影为 0；反之若 `ν_F(g)=n∈Z`，则 `g rec_F(π)^(−n)∈J_F`，由 `unitsInertiaEquiv` 它等于某个 `rec_F(u)`，故 `g=rec_F(uπ^n)`。

也可直接消费 `galAbEquiv_artin' / galAbEquiv_snd`：在已有 `O_F^××Zhat` 坐标中，Artin 像正是 `O_F^××Z`。uniformizer 用于证明等式，定义像子群无需选择 uniformizer。

现在 §5.1 保证 `α^ab` 保持右边的“整数 valuation”子群，而 `artin_injective` 保证逆像唯一。因此定义

\[
\psi_{\alpha,F}:F^\times\xrightarrow\sim F'^\times,
\qquad
rec_{F'}(\psi_{\alpha,F}(x))=\alpha^{ab}(rec_F(x)).
\]

这就是从一般连续 Galois 箭头构造实际乘法群同构。它在单位上的限制等于 §4 的 `\widetildeβ_α`，且保持标准化离散 valuation。仅有 `artinCompletionEquiv` 而没有 Artin 像保持性时，尚不能得出这一步。

### 5.3 为什么所有有限扩张层可以粘起来

对每个 open subgroup `H≤G_F`，设 `L=Fbar^H`，`H'=α(H)`，`L'=Fbar'^H'`。将上述构造用于 `α|_H:H→H'`，得到 `ψ_H:L^×≃L'^×`。

对 `H_2≤H_1`，对应 `L_1⊆L_2`。需要的方块是

\[
\psi_{H_2}|_{L_1^\times}=\psi_{H_1}.
\]

证明：域包含 `L_1^×→L_2^×` 在 Artin 下对应群 transfer `H_1^ab→H_2^ab`，已有 `PadicField.artin_transfer`。transfer 与群同构天然交换：用有限 coset representatives 的乘积公式，α 把 coset representatives 逐个送过去即可。两条路的 Artin 像相同，再用目标 `artin_injective` 得到元素相同。

这里必须分清：

- **域包含 → transfer**：用于直接极限的粘合。
- **域 norm → Galois restriction / abelianized inclusion**：由 `artin_baseChange` 提供另一类自然性。

有限扩张不必 Galois；open subgroup transfer 已包含此情形。若某条现有 Lean 供体采用固定域或 common algebraic closure 的特定表达，需通过现有 carrier equivalences 运输，不另塞一个兼容性输入。

### 5.4 构造代数闭包乘法层，并检查 Galois equivariance

每个 `x∈Fbar^×` 都属于某个有限 L。定义

\[
\Psi_\alpha(x)=\psi_H(x),\qquad L=\overline F^H.
\]

独立于有限层的选择：两个有限层嵌入共同有限复合域，应用 §5.3。逆映射由 `α⁻¹` 构造，故 `Ψ_α:Fbar^×≃Fbar'^×`。

共轭自然性给

\[
\Psi_\alpha(gx)=\alpha(g)\Psi_\alpha(x).
\]

具体从现有有限 `abRec_conj` 推到各有限 abelian quotient，再用 inverse-limit 分量相等；对任意有限 L 可先嵌入有限 Galois closure。不能只写“自然”而不指明这一共轭方块。

由构造还得到对**每个** open H：

\[
\Psi_\alpha((\overline F^\times)^H)
=(\overline F'^\times)^{\alpha H}.
\]

这条全 open-subgroup 性质是接 `TimesMuKummer.Ism` 所需的强 provenance，远强于任意选一个同秩单位格同构。

### 5.5 degree / norm 条件怎么证明

`FPrimeStripEquiv` 还要 `compatDegree`，不能只给乘法群和 action。

对每个有限 L，§4 的单位模挠同构保持 Z_p-rank，由 `rank_Zp W_L=[L:Q_p]` 得到绝对 degree 相同。§5.1 保持 q，故 residue degree f 相同；再由 `[L:Q_p]=e_L f_L` 得到 e 相同。

这个 rank 结论可由足够深的 principal units 上 log/exp 互逆证明：其 log 像是 L 的一个开 Z_p 格，秩为 `[L:Q_p]`；深层单位在整个单位群中有限指数，模掉有限 torsion 不改变秩。这里只需要定性的有限指数，不依赖尚在推进的 #C 精确截断单位计数，也不依赖最终 log-volume 不等式。对应 rank 供体若尚未落地，应登记这一短证明节点，不能把数值 degree equality 重新设成输入。

§5.2 保持整数标准化 valuation，所以

\[
|\psi_H(x)|_p=p^{-v_L(x)/e_L}=|x|_p.
\]

经直接极限得到 `Ψ_α` 保持代数闭包上的实际 p-adic norm，因而保持 `localUnitNormDegreeFor` 使用的 norm-log degree。这里用的是实际离散 valuation 与绝对 ramification index，不把它们误当同一个归一化。

在实际 F-strip 的 action 通过 `proj:Pi→G` 分解时，§5.4 的 G-equivariance 与已有 `DPrimeStripEquiv.compatProj` 合成 `compatAction`。于是 `isoPi / isoG` 保持原 source 箭头，`isoMon=Ψ_α`，另外两项由上述证明填写。

这给出具体 arithmetic realization 上的完整 lift 路线。对于任意抽象 `FPrimeStrip`，其 `Mon / action / degree` 可能完全不同；必须先由实际对象 constructor 证明与上述模型的对齐，不能把此结论无差别推广到弱类型的全部 inhabitants。

## 6. 覆盖全部原文 Ind1：怎样防止只完成一小族例子

### 6.1 最终应证明什么

建立独立于 lift 的实际原文箭头类型，保留 label、place、procession level 与其相容条件。然后证明如下内容：

> 对每个该类型中的箭头 a，构造上述局部动作、逐 factor 运输及 tensor / direct-sum 运输；在 D⊢ 层忘却后回到 a，或在原文要求的 Ism-orbit 层与 a 的动作一致。

在 full D 箭头层，lift 的 `isoPi / isoG` 必须就是原 a；在只给 D⊢ 的层，目标仅锁定它的 G / Galois-category 动作，不人为要求恢复额外的几何 Π 信息。

§3 的分解给出执行办法：现有 transitions 负责对象之间的运输，§4–5 对每个 residual stabilizer 适用，所以覆盖的量词是全部 a，而非 `ofPerm`、identity 或 K-automorphism 的像。

### 6.2 label 与 capsule 运输也属于覆盖证明

现有 `S1311PaperInd1PermutationLiftActual` 已有一般 family permutation 不保固定 capsule slice 的例子，不要重做反例。实际修复是把箭头视为

\[
\mathrm{Capsule}(A)\longrightarrow\mathrm{Capsule}(aA),
\]

并运输相应的 place/field/subgroup 数据。只有确实稳定该 slice 的 endomorphism 才作用在原 capsule 自身。不能只保留 stabilizer 然后称已覆盖原文所有 arrows。

同理 `Ind1ShellTransportFor places e φ` 的任意参数 φ 未必来自实际源箭头。应从 a 推导允许的 `(e_a,φ_a)`，由 β 得到其局部线性同构，再证明原文每个 a 都进入这个消费者。不要对任意置换不同 local degree 的 φ 硬找线性同构。

### 6.3 Ism 处理的是选择，不是替代缺失的构造

原文 Prop. 1.2(vi) 从 F⊢×μ 给出的是到 mono-analytic log 模型的 **Ism-orbit**；Thm. 3.11(i) 的 Ind2 对每个 direct summand、每个 tensor factor 允许独立 Ism。应使用这一真实的不确定性，减少不必要的 canonical-choice 证明。

已有 `TimesMuIsm.lean` 中，Ism 要求：

1. 与 G-action 交换；
2. 对每个 open H，保持 `invariantImage rho H`，它是“先取固定点，再映到 torsion quotient”的像。

§5.4 给第二项所需的真实全有限层性质；群同构保持 torsion，故可下降。对 `α:G→G'` 先把目标 action 沿 α 拉回，再用同一 G 的 `Isomorphism` API。对两个合法 realization comparison，已有 `sourceDifference` 给 Ism 元素，`orbitOf_eq` 给相同轨道。

不能把 Ism 换成整个 `GL_d(Z_p)`；后者并不自动保持所有 finite fixed-field images。也不能只有单位层 β，便直接宣称已得到整个 `Fbar^×/μ` 上的 Ism 比较：这需要 §5 的 valuation 部分及全有限层粘合。若下游只消费 unit/log 子层，应把该子层的 orbit 比较单独证明并与原文语义对齐。

对 inner ambiguity：基域单位的 β 不受 inner conjugation 影响，因为阿贝尔化上内自同构平凡；全 open-subgroup 图中，inner conjugation 会运输 H，必须带着这个运输使用 §5.4 的 equivariance，不能宣称每个有标签有限层都逐点不变。

## 7. 对当前 fixed-points / infinitely-divisible 候选的具体修正

`Mzk1Ind1GaloisFixedRouteActual.lean` 当前的 `candidateIntegralLayer` 在

`TimesMuQuotient ((F.Mon v)^×)`

这个**整个环境群**内取无限 r 可除子群。在实际 `F.Mon=Fbar^×` 模型中，环境模挠群是可除群，结果就是整个环境群；它不能识别 `O_F^×/μ(F)`。

当前 `containsFixedUnits : actionFixedUnitsInTorsion ≤ integralLayer` 的方向，也不是所需的“积分单位层在固定域乘法群中”的关系：固定域乘法群还包含 uniformizer，不能全部塞进积分单位层。

可修复，不必放弃这一条旧路线。准确构造是：对实际 selected open H，先取

\[
A_H=\operatorname{im}\big((\overline F^\times)^H
\longrightarrow\overline F^\times/\mu_\infty\big)
\cong L^\times/\mu(L).
\]

现有 `TimesMuKummer.invariantImage` 已经是这个定义。选择整数 `r≥2` 且 `(r,p)=1`，在 **A_H 内部** 取

\[
D_r(A_H)=\bigcap_{n\ge0}r^n A_H.
\]

因为 `L^×/μ(L)≅Z⊕Z_p^[L:Q_p]`，r 在 Z_p 上可逆，而 `⋂r^n Z=0`，故

\[
D_r(A_H)=O_L^\times/\mu(L).
\]

然后才把该子群映回 ambient。Lean 形状应是

```text
(infinitelyDivisibleSubgroup (G := A_H) r).map A_H.subtype
```

而不是先在 ambient 取该操作。最终要证的是 `integralLayer ≤ A_H` 与它等于实际单位像，不是旧的反向包含。

这条修正适合复用已经有 `isoMon` 的 arrows。一般 D-only 箭头仍先走 §4–5 构造作用；不能把修正后的 extraction 当作凭空产生该作用的办法。本文仅提出修改建议，没有覆盖该活动 owner 的源码。

## 8. 可执行的证明顺序与依赖图

### 8.1 陈述依赖

- `D0`：原文 D⊢ procession 箭头域、实际 p/place/open subgroup；与现有 weak Lean records 的 adapter。
- `D1`：实际 `G_F / I_F / P_F / TopologicalAbelianization / abInertia`；不混淆 P 与 I。
- `D2`：actual unit group、torsion、log lattice、其 Q_p-span、degree 与原 shell normalization。
- `D3`：全 open-subgroup 的 `invariantImage` 及原文 Ism-orbit。

### 8.2 证明依赖与消费者

```text
实际无分歧塔 + Hensel + 有限 tame / wild 分解
  → tame quotient 的 T ⋊ Zhat 描述
  → P = 最大闭正规 pro-p；T = 最大闭正规阿贝尔
  → 每个 actual α 保持 I
  → 拓扑阿贝尔化 + 已有 unitsInertiaEquiv
  → β_α / log-square / 线性格运输
  → 局部 Ind1ShellTransportFor 的实际 inhabitant

同一条 I 保持性 + prime-to-p torsion 计数
  → q 保持 → 标准 Frobenius 保持
  → Artin 像 = 整数 valuation 的逆像
  → ψ_H : L_H^× ≃ L'_{αH}^×
  → 已有 transfer / conjugation → 所有 H 的相容系统
  → Ψ_α : Fbar^× ≃ Fbar'^×，action / degree 相容
  → full multiplicative lift、全 invariantImage 运输

已有 F→D transition lifts + 上述全部 stabilizer 构造
  → 全部真实 procession 箭头覆盖
  → 已有 Ism sourceDifference / orbitOf_eq
  → 原文 source provenance 与消费者接入
```

### 8.3 建议的最小交接包

| 包 | 必须产出 | 已有供体 | 新叶子 / 接入 |
|---|---|---|---|
| R0 对象和箭头 adapter | 原文每个 actual a 对应连续 `α`，实际 H/places 随之运输 | actual source constructors、S2027 fixed-field 模型 | 范畴/拓扑及标签语义对齐；不能定义为 lift 的像 |
| R1 惯性重构 | `α(I_F)=I_F'` | unramified tower | tame finite layer + §4.2 群论证明 |
| R2 β 与 log | 从 a 构造 β、log-square、复合律、实际格同构 | unitsInertiaEquiv、现有 unit quotient/log 后半段 | carrier 字典与 original shell 标量 |
| R3 完整乘法层 | Frobenius 保持、Artin 像保持、所有有限层 ψ、Ψ | galAbEquiv、Artin transfer/norm/conjugation | §5 的短群论/自然性连接 |
| R4 全覆盖与选择 | 每个真实 procession arrow 的作用；Ism 轨道独立性 | existing transitions、TimesMuIsm | 原文 component/level/capsule 的覆盖语义 |

这些是对现有 source owner 的数学交接，不是本 chat 新派工。R2 可先交付局部消费者；R3 用于需要完整 `isoMon` / 全有限层 provenance 的部分；R4 无论如何都不能省略。

## 9. 本次判断与完成边界

我优先推荐 **R1→R2**，因为它把最硬的“源端 β 从何而来”压缩成一个明确的局部 Galois 子群重构问题，随后立即消费已有实际单位 Artin 等价。需要完整箭头时，**R3** 给出从 `F^×` 到 `Fbar^×` 的具体粘合办法，而不是新增 `hasLift` 条件。

数学论证最需要写实的新增算术部分是 tame tower 的有限层描述；最需要语义核实的是 R0/R4 的原文箭头域和 selected local fields。二者都不能用“工程接线”概括。另一方面，局部互反律、单位模挠后的对数线性化、既有 transition lifts、Ism 选择差不应再整体重做。

当前没有宣称一般 Ind1 已闭合，也没有宣称 IUT 3.12 已完成。本文交付的是有具体证明步骤、现有供体与消费者的消缺路线。下一步最值得动手的数学命题是：**在 actual finite local-field 模型上证明 §4.2 的惯性保持性，并把 `unitsInertiaEquiv` 实例化为同一个 actual source 的 β，而不是再增加一个接受 β 的 wrapper。**

原文依据：本地 `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`，Prop. 1.2(vi)，L1898–1949；Thm. 3.11(i)，L9258 附近。本文没有新增外部调研或引用外部结论作为证明输入。
