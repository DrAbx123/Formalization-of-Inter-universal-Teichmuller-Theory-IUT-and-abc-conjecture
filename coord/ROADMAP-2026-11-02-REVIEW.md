# xi-f / 3.12 路线图单线程核查意见

**2026-11-03 定向复核。** 本次对照的[路线图](ROADMAP-2026-11-02.md)工作树版本为 SHA-256 `0D4ACE06CBCA6C75A2EA32D09F0B1DC28BF705FC83C759B08B10AC5C4C7227F9`。以下两节给出今天对 3.12 的建议，11 月 2 日的判断保留在附录。

## 一、从 3.12 倒推，第一项工作选什么

**如果只做一包，我选定理 3.11 的任意一份合格输入 `C`，追踪它的 q 标记在最终求值中去了哪里。** 对这同一份输入，记 q 的有符号读数为 `Q_C`，Θ-pilot 所有允许像的 holomorphic hull 的归一化读数为 `H_C`。推论 3.12 要给出 `H_C` 有限以及 `Q_C ≤ H_C`。有限性已有候选引理 `ambient_hull_logVolume_lt_top`，要把它用在由 `C` 实际构造的 hull 上。五项阻塞分属不同构造路线，即使各自解决，也仍须交付这个源对象识别和读数比较。[IUT III，推论 3.12，第 173–174 页](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf#page=173) · [已有有限性引理](../tmp/sheaf/xif/PaperSignedHull.lean#L85)

我会复用已有的 `U₂K₂` 运输，集中检查它的**下一支箭头**。运输得到的 q 标记仍在 prime-strip 一侧。要指出哪个原文求值操作把它送进该 `C` 的允许输出族 `P_C`，并在同一张量幂、原 `O(−)` 参考对象和同一组位点权重下，给出 `D ∈ P_C`、`ν_C(D) = Q_C`。再把针对同一族的上界 `ν_C(D) ≤ H_C` 接上即可。若只有逼近可用，对每个 `ε > 0` 给出 `Dε ∈ P_C` 且 `Q_C − ε ≤ ν_C(Dε)` 也够。已有追踪分别确定了 `U₂K₂` 的终点和 sQ3 的定义域，两者之间仍缺一支实际箭头。若找不到新源引理或实际构造，我会把这里保留为 3.12 的显式缺口。把 (xi-f) 作为前提只会得到条件推导。[IUT III，步骤 (xi-e)–(xi-f)，第 184 页](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf#page=184) · [已有追踪及定义域更正](../tmp/sheaf/n8/closure/C9-U2K2-SQ3-MARKED-TRACE-20261026.md#L194) · [两种充分条件](../tmp/sheaf/n8/closure/C9-C1-HANDOFF-SUMMARY-20261026.md#L14)

## 二、五个硬阻塞

### 1. S2135 的全称命题目前不可判定

固定 `l`，S2324 用经典排中得到如下析取。或者每份完整 `T` 的每个坏位点均满足 `p_b = qVFamTensorP T b ≤ 7`，或者存在一份完整 `T,b` 满足 `p_b > 7`。当前证据未选定任何一支。「不可判定」指这一全称问题的项目状态，对给定数值 `p_b` 检查上界是可判定的。S2331 的具体模型使用 3、5、7。单给一个更大的素数仍欠完整的合格输入。`Nonempty (S2321OUnitsChain T b)` 与 S2135 等价。S2040 layer (1) 的**对齐 split 包**也依赖 S2135，并另需剩余次数 `f=1` 和分歧指数 `e=1`。[S2324 二分](../tmp/sheaf/xif/paper/S2324S2135DecideActual.lean#L58) · [具体模型](../tmp/sheaf/xif/paper/S2331S2135ModelsActual.lean#L50) · [S2321 等价](../tmp/sheaf/xif/paper/S2321OUnitsChainFinalActual.lean#L58) · [完整 split 包的充要条件](../tmp/sheaf/xif/paper/S2232Layer1PrimeAlignmentActual.lean#L265)

**我的取舍是先试实际素数 `p_b` 上的接口。** S2268 已经在 `sectionKPlace T b` 下方的实际素数上给出单位及单位商等价，S2280 已识别它等于 `qVFamTensorP T b`。先看 3.12 的 Kummer 箭头能否直接消费这个位点上的单位商，并保留其 Galois 作用、位点权重及与原 prime-strip 的相容性。若可以，就绕过 `p_b ≤ 7` 这项模型义务。若消费者确实取 `v : FinitePrimePlace 2 7`，这个接口仍然是条件性的。为保留论文对合格输入的原量词，应把 7 的上界留在该模型的专用结论中。只有在必须判断该固定 strip 对所有输入是否适用时，我才会投入完整反例的构造。[S2268 的实际素数与单位商](../tmp/sheaf/xif/paper/S2268LocalBridgeActual.lean#L104) · [S2280 的素数识别](../tmp/sheaf/xif/paper/S2280PaperVPrimeMatchActual.lean#L39)

### 2. D6 的 uniform strict-cone / graph-compat 路线已反驳

`S2291NotStrictConeIso` 和 `S2291NotGraphCompatAll` 已否定 `S2185StrictConeIso` 与 `S2269GraphCompatAll`。本次核查期间又出现了更强的 S2350 记录（源码 SHA-256 前缀 `604DBF96F11D`，已有构建及 import 检查）。在同一反例上，旧 apex 的两条腿落入余积的不同分支，严格纤维积没有点，而见证会迫使其投影有截面。`S2350IsEmpty` 由此证明 `S2130ConcreteTwoPullback` 本身为空。「existence 仍 open」现仅适用于一般几何 D6(c)。在同一个反例上，`S2350PresentationAtDatum` 给出了另一个 `EtaleStackBaseChangePresentation` 的具体见证。[S2291 的两个否定](../tmp/sheaf/xif/paper/S2291UniformGraphCompatActual.lean#L513) · [S2350 的空性与几何见证](../tmp/sheaf/xif/paper/S2350D6AfterRefuteActual.lean#L224) · [对应构建与公理记录](../AUDIT_LEDGER.md#L3865)

**我会从 D6 的候选证明里剪去这三个全称中间命题。** 若 3.12 的具体覆盖需要 D6，先查其来源是否给出 `StrongCover`，可以直接复用该范围内的有限 étale presentation。若一般几何目标确需任意弱覆盖，就从几何对象的真实 2-拉回选取另一个 apex，证明其两个投影、比较 2-cell 和泛性质，再接回原来的有限 étale 消费者。新 apex 必须在 S2291 的同一例子上给出正确的几何 presentation。尤其要避开 `∀ B C, S2240ConeEssSurjAt B C` 这一全称形式。S2357 的 `S2357CorrectedD6FirstMissing` 在核读版本中正是这个定义，取 `B=C=S1850DoubledCover` 即与 `S2269NotConeEssSurjAt_doubled` 冲突。这条判断来自展开声明和特化已有否定定理，本次未编译新的组合。[强覆盖上的构造](../tmp/sheaf/xif/paper/S2240StrictConeIsoActual.lean#L793) · [S2357 的定义](../tmp/sheaf/xif/paper/S2357CorrectedD6ApexActual.lean) · [doubled cover 的否定](../tmp/sheaf/xif/paper/S2269GraphCompatActual.lean#L474)

### 3. D9 的 NatIso 卡在限制映射的符号

S2332 已给出逐点子类型预层 `Psub`，其限制映射保留符号 `g`。缺的是 `S2152Q.presheafHom M N ≅ S2332Psub S M N` 的自然性。**我会先证明一个只在 `SignGroup` 中比较的等式。** 令 `s_T(x)` 为作用群胚态射 `x` 的底层符号。对 `p : T₁ ⟶ T₂`，所需引理是 `s_T₂(QHom.map p x) = s_T₁(x)`。`S1971PrecompFunctor_map_val` 已证明普通预合成保持这个值。剩下的是把实际 `presheafHom.map` 的伪函子比较和 `eqToIso` 运到符号投影下，并核对它们的作用。两侧符号相等后可用 `Subtype.ext` 收尾，再由逐点同构组装 NatIso。先前日志记录了整张方形上的 `rfl` 失败。验证符号投影能把失败定位到一个具体的 cast。这项工作优先服务于确实需要该商栈 Hom 层的消费者，有效下降与商的泛性质仍分别验收。[S2332 预层](../tmp/sheaf/xif/paper/S2332PsubCorrectActual.lean#L28) · [预合成保持符号](../tmp/sheaf/xif/paper/S1971ActionStackificationActual.lean#L242) · [cast 的剩余等式](reports/S2332-d9-psub-correct.md#L30)

### 4. corrected Dedekind–Frobenius 可拆成三次比较

S2217 用 `f = X` 反驳了 S2167 的字面全称命题。一个线性因子贡献次数 1，`Perm.cycleType` 却省略不动点。修正版可用包含不动点的轨道大小多重集，或在因子次数一侧过滤 1。S2345 已给出整数环根集与域中根集的等价，S2339 已给出相应可分分裂条件下每个不可约剩余因子根上的 Frobenius 传递性。[S2217 修正版与反例](../tmp/sheaf/xif/paper/S2217DedekindFrobTheoremActual.lean#L592) · [S2345 根集等价](../tmp/sheaf/xif/paper/S2345RootSetEquivActual.lean#L61) · [剩余根传递性](../tmp/sheaf/xif/paper/S2339FbarFactorsActual.lean#L51)

如果需要这条桥，我会按以下顺序处理。**先证 Galois 等变**，把两个根都嵌入 `L`，用 `algebraMap_galRestrict_apply` 比较值，显式识别整数环上的作用与 `galRestrict`，再由根子类型的外延性返回。**再证 Frobenius 约化**，对同一个 `σ,P` 使用 `IsArithFrobAt` 在剩余域中给出的同余（可在相应 `AlgHom` 上用 `AlgHom.IsArithFrobAt.mk_apply`），得到 `red(σ·x) = Frob_q(red x)`。**最后比较多重集**，按每个根所属的首一不可约因子分纤维，用可分性及已知传递性把每条轨道的大小识别为该因子的次数。对 D5 的具体 `ℓ=5` 模型，只有把置换送到实际表示的像里才交付了循环型。在定理 3.11 已给合格输入的 3.12 主线，大像条件是原文允许的输入。只有实际消费者需要另造该模型时，我才上调 D5。[原文初始 Θ 数据 I.3.1(c)，第 62 页](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf#page=62) · [S2352 的作用问题](reports/S2352-galois-action.md#L14) · [S2342 的约化与计数](reports/S2342-dedekind-final.md#L27)

### 5. H¹ 优先走 Kummer 幂商，再接实际塔的 lim¹

S2225 已证明给定有限 `Q_n` 时其 H¹ 有限。现缺实际的 `G_v ↠ Q_n` 和逐层 `H¹(G_v, μ_{n!}) ≃ H¹(Q_n, μ_{n!})`。系数作用能通过有限商分解，尚不足以产生这项上同调比较。S2214 已有实际 `h1Proj` 同态，每层满射与实际塔的 `lim¹ H¹ = 0` 都还欠证明。[有限商比较的字段](../tmp/sheaf/xif/paper/S2225H1FiniteQuotientActual.lean#L52) · [实际 H¹ 转移](../tmp/sheaf/xif/paper/S2214H1MonoidActual.lean#L16)

**这是五项中我最看好的一条算术路线。** 先比较 S2204 的连续一余循环及其余边界与已移植的 Kummer 模型，并核对逐层转移。对 `K = ℚ_p` 和 `m = n!`，Kummer 给出 `H¹(G_K, μ_m) ≃ Kˣ/(Kˣ)^m`。现有 `PadicField.index_range_pow` 给出幂子群的有限指数。两层商之间由同一个代表元 `a` 诱导的投影自然满射，`kummerEquiv_quotTransition` 正可用于识别这张方块。若消费者确实需要有限商本身，可从有限多个幂类代表 `a_i` 取 `K(μ_m, a_i^(1/m))` 的有限 Galois 群作为 `Q_n` 的候选。候选商应承载每个代表的 Kummer 余循环。若 inflation 后某个余循环成为余边界，可用商映射的满射性检查同一个零上链在商上也给出该余边界。这给出了验证 S2225 所需等价的两个方向。[实际 H¹ 模型](../tmp/sheaf/xif/paper/S2204ActualH1InstanceActual.lean#L12) · [Kummer 等价](../tmp/local-cft-port/continuous-kummer-theory/ContinuousKummerTheory/Kummer/Equiv.lean#L94) · [幂指数公式](../tmp/local-cft-port/PadicField/PowIndexPadic.lean#L113) · [转移相容](../tmp/local-cft-port/continuous-kummer-theory/ContinuousKummerTheory/Kummer/Limit.lean#L117)

有了**实际转移**的满射，可在这条可数阿贝尔群塔上递归选原像，证明乘积上的差分映射 `(xₙ) ↦ (xₙ · h1Projₙ(xₙ₊₁)⁻¹)` 满射，从而处理其余核所计算的 `lim¹`。还要将这项消失结果接到实际 H² 比较所需的 `CoboundaryLift`。H² 的满射一侧可用 `S2114CompatibleRepresentativeLift` 单独验证。这样得到的结果具体服务于 `PsiCnsH2LimitComparison`。只有当这一归一化确实供给主线所需的 Kummer 求值时，我才给它独立的优先资源。[可数阿贝尔群塔的差分公式](https://stacks.math.columbia.edu/tag/07KV) · [抽象 ML 的范围](../tmp/sheaf/xif/paper/S2138H1MLActual.lean#L30) · [H² 单射的条件](../tmp/sheaf/xif/paper/S2112ContH2LimitActual.lean#L737) · [H² 满射的消费者](../tmp/sheaf/xif/paper/S2114H2SurjectivityGapActual.lean#L26)

**11 月 3 日只读 Lean 核验结果。** 在已构建依赖上通过标准输入检查了四个具体推论。`S2324DecisionRequired` 由 `s2324_dichotomy l` 分情况直接得到，全称分支使用 `s2324_chain_universal_of_universal`，反例分支原样返回。`¬ S2357CorrectedD6FirstMissing` 由 `fun h => S2269NotConeEssSurjAt_doubled (h _ _)` 得到。对 D5，当前实例下 `algebraMap O_L L (σ • a) = σ (algebraMap O_L L a)` 的证明为 `rfl`。设 `e = s2345RootSetEquiv f hm`，还验证了 `(e.symm (rootPerm K L f hs σ (e a))).val = σ • a.val`：对等式使用 `RingOfIntegers.coe_injective`，再用 `e.apply_symm_apply`，两端即按定义相等。这给出了具体的整数根 Galois 传输公式。四个声明的 `#print axioms` 均仅含允许的三项。含探索项的探针整体退出码为 1，D9 的 `pullHom` 符号等式及 H¹ 的有限性探针未通过。没有生成新的 Lean 文件或 `.olean`，未运行全 Project 构建或 comparator。3.12 的固定输入读数见证仍缺，`target_accepted` 未达到。

## 附录 · 2026-11-02 首审及当时的排期意见

2026-11-02。核查对象为[当天的路线图](ROADMAP-2026-11-02.md)，工作树基线为 `9399e9fab4d6`。路线图原稿的 SHA-256 为 `7F8AD793E70D82574B8AB4ED5ACAC64B379CECF5DC52304885A8C53DFE1C2E73`。

**paper-level 3.12 仍未验收，这一点与路线图一致。** 排期上，建议把 S2040 的单位商和原文 hull 的有限性放在 D6(c) 前面。这两项直接决定验收时比较的是哪两个对象。D6 的两个分量方程即使通过，也只消去给定 twist 之后的局部义务。

### 一、直接影响 paper-level 验收的三处差异

**1. 区分有限单位根子群与单位商。** 第 1.2 节把 S2040 的 `O^×μ attachment` 列为 `[ACTUAL]`。沿 `s2040PaperOtriAttachmentActual` 展开，`paperOUnitsMu` 是整数单位中的 `rootsOfUnity (2 * l.value)`，附件证明每个元素的 `2l` 次幂为一。这正好描述两个候选根之比的歧义。IUT II 的 `O^×μ` 则是单位群除以全部挠元所得的商。建议把前者记为已证的根歧义引理，把后者在实际 prime-strip 上的商映射、核及作用相容性单列。项目已有 `TimesMuQuotient` 和 `SourceFTimesMuPrimeStrip.canonical` 可复用。S2040 的另一个 ambient 构造确实选了商群载体，但其 `quotient_compatible` 槽里放的是该群非平凡的命题，尚不足以给出这张交换图。[IUT II，第 7 页](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf#page=7) · [S2092 的子群](../tmp/sheaf/xif/paper/S2092PaperOtriActual.lean#L179) · [S2040 的附件](../tmp/sheaf/xif/paper/S2040PaperOtriFromS2092Actual.lean#L35) · [ambient 构造](../tmp/sheaf/xif/paper/S2040PaperOUnitsMuAmbientActual.lean#L111) · [prime-strip 的单位商](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L236)

**2. 第 6 节应写出原文的有限性结论。** 在定理 3.11 的情形下，令 `H = −|log Θ|`，`Q = −|log q|`。原文的 `H` 起初可取 `+∞`，取的是 Θ 侧在 Ind1–Ind3 下所有可能像的并之 holomorphic hull 的 procession 归一化对数体积。`Q` 取自不施加这些不定性的 q-pilot。推论同时给出 `H ∈ ℝ` 与 `Q ≤ H`。仓库的 `PaperSignedHull.ambient_hull_logVolume_lt_top` 已对给定 `P` 提供有限性。建议要求同一份合格输入上的对象识别，将这条引理和不等式同时接到原文的 hull。单看 `.toReal` 的返回类型无法验收有限性。S2030 左端用固定的 `S1487Cand.q`，保留作标量校验是合适的。[IUT III，推论 3.12，第 173–174 页](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf#page=173) · [PaperSignedHull 的读数与有限性](../tmp/sheaf/xif/PaperSignedHull.lean#L80) · [S2030 的量词和两端](../tmp/sheaf/xif/paper/S2030Direct312Actual.lean#L363)

**3. Batch 4 应按实际消费者安排工作。** 旧接口的 `logVolumeComparison` 字段直接要求目标不等式。较新的 `s2040_paper312_of_firstMissing` 已能从 `S2040FirstMissing O Opaper P` 推出它。后者列出四项 q-pilot 识别、`O.qPilotLogVolume = log Opaper.q`，并要求存在同一个 displacement `D`，使 `P.signedHullLogVolume = log D.rootStackTheta`。其中四项识别也是 `Opaper.paperO_identifications` 的内容，工作量在于从合格输入构造这样的 `Opaper`。按 `rootStackTheta_eq` 和 `s2040Theta_log`，这个末项指定了精确值 `log(Opaper.q)/(2l)`，强于原文下界。建议把它标为这条证明路线的充分条件，注明支持该等式的原文步骤或保留缺口。以旧字段本身为输入的推导只能记作条件结果。[旧接口](../tmp/sheaf/xif/paper/S2040ActualThetaLinkActual.lean#L57) · [S2040FirstMissing 及消费者](../tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean#L445) · [标量对数公式](../tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean#L126)

Batch 4 的两个局部对象也应分开。Layer (1) 比较 `Completion (qVPlace T b)` 与有理素点的完备化。`S2040QVPlaceSplitDataOfPackage` 只是从含 `f=e=1` 和保范数环同构的包中取出所需数据。单凭 `b` 是坏位点，没有在这个构造中得到分裂。若沿此路，应标出对原范围内每个 `T,b` 的分裂依据，并核对完整组装还接收同一 `S.v` 上的积分单位比较 `U`。`qv_root_attachment` 登记的 `paperOtriRootMissing T b` 要求根落在所选 **K 侧完备域**。要使用已构造的代数闭包中的根，仍需证明它下降至该完备域。[split 包及其投影](../tmp/sheaf/xif/paper/S2040QVPlaceSplitActual.lean#L60) · [完整组装的参数](../tmp/sheaf/xif/paper/S2040S2060Actual.lean#L74) · [S2092 的两个根目标](../tmp/sheaf/xif/paper/S2092PaperOtriActual.lean#L287)

### 二、其余批次的实际依赖

**Batch 1 · D6(c)。** S2127 主文件已写出 `S2127Legs` 和 `S2127ToAWitness`，二者都收 `h : S2121ComparisonTwist f g T ptA Pg`。本次找到该版源码（SHA-256 前缀 `9EC37F98A156`）及小型 probe，在所查记录中未见主文件的匹配成功构建和公理输出。建议把「等 legs」改读为「核对这项条件定理的版本证据」。真正的组装入口 `S2086FirstMissing` 同时需要两项数据。先给 `hg : S2086CospanGMapFiniteEtale`，再对每个 cospan、`T`、`ptA` 给出 **该 `hg` 所选** base-change presentation 的见证。值得尝试的 twist 只须覆盖这些选定的 `Pg`。S2125 的命题则量化 strong presentations，经 `toWeak` 使用，与任意 weak `Pg` 的局部 `h` 范围不同。若走 S2110 的现成强分支，其签名还列有 `hRC`、`hBig` 和强 `hg`。建议以能否填到 `S2086FirstMissing` 为停止点。[S2127 签名](../tmp/sheaf/xif/paper/S2127ToYLegsActual.lean#L328) · [S2086 的选定范围](../tmp/sheaf/xif/paper/S2086ToAAssemblyActual.lean#L198) · [S2125 的量词](../tmp/sheaf/xif/paper/S2125PresentationCoherentActual.lean#L315) · [S2110 强分支](../tmp/sheaf/xif/paper/S2110StrongTwoFullInputsActual.lean#L289)

**Batch 2 · M2b。** S2119 已为 (B) 给出 `verCarrierComparison`。要构造 `LocalReciprocityData p`，S2113 的 `localReciprocityData_of_canonical` 直接收 **`∀ U : Index p, canonicalTorsionComparison p U`（M2c）和 `TransferBridge`**。`hcanon` 只出现在还要兼容 S2098 的 `(hc U).some` 的入口。建议把 M2c 与 (A) 列作规范构造的两项前提，只在确有旧接口消费者时另列 (C)。S2117 把一条 M2c 路线约到 `G_ℚp` 的拓扑有限生成与 Nikolov–Segal 换位子宽度，两项仍是该定理的参数。[S2119 的 (B)](../tmp/sheaf/xif/paper/S2119VerCarrierActual.lean#L175) · [规范入口](../tmp/sheaf/xif/paper/S2113M2bTransferActual.lean#L417) · [S2098 兼容入口](../tmp/sheaf/xif/paper/S2113M2bTransferActual.lean#L476) · [M2c 约化](../tmp/sheaf/xif/paper/S2117TopFGActual.lean#L318)

**Batch 3 · S2036 的 H²。** 第 1.2 节和 Batch 3 都漏列了满射。S2112 给出 `Z²` 交换，并证明 `Injective h2Comparison ↔ CoboundaryLift`。得到双射的定理另收 `Surjective h2Comparison`，即每个相容的层级上同调类族可由同一个极限类表示。建议把 G3 的 `lim¹ H¹ = 0` 记作通往 `CoboundaryLift` 的一条待证路线，单列满射所需的代表元提升。已有 `kummerEquiv_quotTransition` 把 H¹ 转移对应到 `Kˣ/(Kˣ)ⁿ` 的自然投影，可先检查这能否在实际塔上给出 Mittag–Leffler 条件。[S2112 的单射刻画](../tmp/sheaf/xif/paper/S2112ContH2LimitActual.lean#L737) · [双射的两个前提](../tmp/sheaf/xif/paper/S2112ContH2LimitActual.lean#L807) · [Kummer 转移](../tmp/local-cft-port/continuous-kummer-theory/ContinuousKummerTheory/Kummer/Limit.lean#L117)

接到 S2091 时还要核对两次识别。S2112 用 `n+1 → n` 的塔，`Brauer.H2ZHatOne` 按正整数的整除关系取极限，需给出共尾塔及逐层映射的相容性，或直接在原指标上比较。G1 的 `S2046G1TopologicalModuleData` 目前只列群作用、乘法等价和等变方程，定义中没有连续性字段。要运输连续上链，需在实际系数拓扑上证明作用连续、比较为双向连续的等变同构。交付出口是 S2091 的 `PsiCnsH2LimitComparison p`。M4 的 `PsiCnsKummerNormalization p` 仍须另给。[S2112 系数塔](../tmp/sheaf/xif/paper/S2112ContH2LimitActual.lean#L160) · [端口的极限](../tmp/local-cft-port/Brauer/H2ZHat.lean#L40) · [G1 的字段](../tmp/sheaf/xif/paper/S2046G1CyclotomeActual.lean#L37) · [M3 的消费者](../tmp/sheaf/xif/paper/S2091H2ZhatActual.lean#L162)

**Batch 5 · D5 与 D9**

- **D5。** S2126 给出指定十次多项式 `f` 的不可约性。完整模 29 分解还要求整数模型、二次因子、次数与乘积识别。`S2057FrobMod29CycleTypeBridge` 中 Frobenius 与置换是分列的字段，`cycleType_eq` 只约束置换。建议以实际扭点表示像中的 `HasCycleType102` 为出口，给出 Frobenius 在十二对点上诱导该置换的证明，并分别追踪 `PairTransitive` 与行列式满射。[十次因子](../tmp/sheaf/xif/paper/S2126Mod29IntegrationActual.lean#L1585) · [分解、Frobenius 与最终三个前提](../tmp/sheaf/xif/paper/S2057DedekindFrobBridgeActual.lean#L75)
- **D9。** `SlicePushNaturality` 给出态射下降，再加对象的有效下降才得到 `IsStack`。`S2093LargeCFFirstMissingExact_iff` 的另一合取项仍是 `Nonempty (S1964HonestCFQuotient l A)`，其中须有实际符号商及其泛性质。建议分别登记栈性质与商见证的来源。[态射下降消费者](../tmp/sheaf/xif/paper/S2103D9PrestackActual.lean#L247) · [完整 D9 数据的分解](../tmp/sheaf/xif/paper/S2093D9StackActual.lean#L355)

### 三、排期和验收建议

- 若只选一项，先核对 S2040 在实际坏位点及两个 theater 上使用的单位商映射与诱导作用。它能直接判定第 1.2 节的哪一项资产可以交给 Θ-link。第 4 节的百分比可作暂定预算。第 6 节的前置应限于目标的实际依赖，保留论文允许的初始数据。若 D5 或 D9 用于构造特定实例，应另指出主定理使用该构造的位置。
- 第 7 节的「不再对 M3/CardV 投入」宜限定为 **S2106 的曲线纤维函子 M3 / CardV**，以免误停 S2036 的 H²。S2106 给了任意域表述的数学反例，并形式化了从反例数据推出否定的引理，具体反例覆盖尚未在该文件构造。D6 的 `¬ S2094GPresentationConeEssSurj` 则有直接的 Lean 否定定理。两处可保留 `REFUTED`，同时注明证据层次。`MISSING` 宜解释为当前证据中尚无构造，只有给出否定证明时才断言不存在。[S2106 的证据边界](../tmp/sheaf/xif/paper/S2106CurveM3Actual.lean#L508) · [S2100 的否定定理](../tmp/sheaf/xif/paper/S2100GPresentationConeEssSurjActual.lean#L116)
- Batch 6 应把局部条件定理的构建与最终目标验收分开。对实际证明批次按约定做集成构建，最终验收还需同版本锁定类型的 comparator、目标闭包的传递公理检查，以及对同一组定义的原文语义审查。现有 xi-f 节点登记为条件组装，`locked` 为 `false`。[SHEAF 验收标准](../SHEAF.md#L157) · [xi-f 节点](../dag/nodes/xif-source-construction.json#L67)

### 四、如果由我安排下一批

我会先保留两项主线工作。一项给出实际局部单位商上的比较映射，另一项固定同一份合格输入，写清全局 q 读数和 Θ-hull 读数各自来自哪里。前一项揭示 Θ-link 可以传递哪些数据，后一项决定传递这些数据能否得到 3.12。两项交付之后，我才会按暴露出来的缺口调整第 4 节的预算。

#### 1. 用两个具体等式核对 S2040 的单位商

固定一个实际坏位点，令 `π` 为其整数单位群到全挠商的投影。若 `r₁,r₂` 是同一个 `q_v` 在所选完备域中的两个 `2l` 次根，记 `h₁,h₂` 为相应的根方程，第一项检验应是 `π(paperRootRatio T b h₁ h₂) = 1`。S2092 已把这个比值构造成整数单位并证明它属于 `μ₂ₗ`，而 `quotientMap_ker` 已识别 `π` 的核。这个检验能说明商映射确实消除了根的选择歧义，根在完备域中的存在性仍单列。若两侧单位群之间已有来自实际 link 的映射 `e`，第二项检验是对每个单位 `u` 验证 `ē(π₁(u)) = π₂(e(u))`，再核对所用 Galois 作用。仓库已有由单位群等价诱导商等价的计算引理。如果原文在这一步只给商上的 poly-isomorphism，就按其允许的代表和歧义核对，要求一个规范的全单位群提升会额外增加证明责任。[根比值](../tmp/sheaf/xif/paper/S2092PaperOtriActual.lean#L266) · [商映射的核及诱导作用](../LeanFormal/IUT/IUTII/Kummer/TimesMuQuotient.lean#L40) · [商等价在代表元上的公式](../LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean#L133)

这一项也能决定 Local CFT 的优先级。S2038 的 `PaperOActual` 包含从群构造的 `OUnitsMuActor` 和 `OperationKummerEvaluation`。S2040 本地名为 `S2038PaperOActual` 的结构却列出 q、两个 strip 和四项识别。两份声明的参数和字段不同。建议以一条实在的应用为依据提高 CFT 的优先级，例如说明哪一个算术等变比较产生所需的 Kummer 映射，以及这张映射如何进入同一输入的 displacement。[S2038 的作用与 Kummer 数据](../tmp/sheaf/xif/paper/S2038PaperOActual.lean#L439) · [S2040 所用结构](../tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean#L176)

#### 2. 用多坏位点情形检验 q 的归一化

现有定义让这项核对十分具体。`O.qPilotLogVolume` 绑定到 `−∑ b, |log(q_b)|`，`Opaper.q` 绑定到 `I.oneColumnQAtZero`。要使用 `S2040QPilotLogIdentification`，就要解释**同一个输入**的单列 packet 为何满足 `log(I.oneColumnQAtZero) = −∑ b, |log(q_b)|`，以及这个和与论文的 procession 归一化如何对应。我会优先看各坏位点怎样进入 packet，局部次数和权重在哪一步处理。S1487 已给出一个现成的区分案例，其旧接口上的单坏位点等式成立，双坏位点时全族读数多计了一份。这个案例适用于该旧接口的具体输入，足以检验一条拟议的复用是否遗漏求和下标。[坏位点和的定义](../tmp/sheaf/xif/PaperQPilotObject.lean#L66) · [单列 packet 的 q](../tmp/sheaf/xif/paper/ThetaLinkLogKummerActual.lean#L54) · [S1487 两种结果](../tmp/sheaf/xif/paper/S1487OQPilotScalarEqualityActual.lean#L615)

我也会据此决定是否投入 layer (1)。如果下游算式只读剩余域范数，已有 `log N(v) = f · log N(v₀)` 保留实际剩余次数 `f`，值得先检查全局权重能否吸收这个因子。如果下游确实要沿保范数的环同构运输元素，再回到 split 包。另一方面，K 侧根满足 `l ∣ eSource` 是筛查候选根的必要条件。这里的 `eSource` 和 layer (1) 相对 `ℚ` 的分歧指数分属不同扩张，应在算式中写出基域。[剩余次数公式](../tmp/sheaf/xif/paper/BadPlaceRationalDegreeActual.lean#L68) · [所选 K 位点的分歧指数](../tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.lean#L116) · [根的必要条件](../tmp/sheaf/xif/paper/S2092PaperOtriActual.lean#L359)

#### 3. 对 hull，先检查不等号方向，再决定是否追精确等式

`PaperSignedHull.signedHullLogVolume_le_neg_image_toReal` 给出了容易读反的方向。在有关体积有限时，取负号以后，像集包含于 hull 给出 **`H ≤ −vol(image).toReal`**，其中 `vol` 指此接口的非负 `logVolume`。3.12 需要的是 **`Q ≤ H`**。单有像集包含，即使有限性已经解决，也不能填这一端。另一个值得利用的分支是，原文中一旦证明 `H` 有限，`H ≥ 0` 的情形由 `Q < 0` 直接结束。现有 `PaperSignedHull` 的读数恒非正，若用它表示所有源输入，应说明这个范围如何覆盖，或在源对象上先处理非负分支。[取负后的包含方向](../tmp/sheaf/xif/PaperSignedHull.lean#L125) · [模型的符号范围](../tmp/sheaf/xif/PaperSignedHull.lean#L98) · [原文推论与证明首段，第 174 页](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf#page=174)

在需要实质比较的分支，我更看好已有的固定输入路线。对同一份合格数据 `C`，若 `P_C` 的每个允许输出都满足 `ν_C(D) ≤ H_C`，从实际求值操作取得一个 `D ∈ P_C` 且 `ν_C(D) = Q_C` 就够了。交接中还给了较弱的充分条件，即对每个 `ε > 0` 取得同一族里的 `Dε`，使 `Q_C − ε ≤ ν_C(Dε)`。我的选择标准是能否指出产生这个输出的实际操作，以及读数如何落到 S2040 所用的同一 `P`。若可指出，就没有必要先证明所有 hull 都等于 `log(q)/(2l)`。若只能引用 (xi-f) 的读数结论，则只能登记为对该原文步骤的条件应用。[固定输入的两种充分条件](../tmp/sheaf/n8/closure/C9-C1-HANDOFF-SUMMARY-20261026.md#L14) · [IUT III，步骤 (xi-e)–(xi-f)，第 184 页](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf#page=184)

### 五、哪些支线值得缩短，什么证据会让我上调它们

**D5 最值得先试一条更短的群论路线。** 前文列出的三个前提属于 S2057 的全像组装。固定实际基 `S1982Basis`，令 `H` 为该模 5 表示的像。D5 的目标 `S1725ImageTail` 只要求 `SL₂(𝔽₅)` 的像包含于 `H`。若 `(10,2)` 元素已落在这个 `H`，则 `ten_dvd_natCard_of_mem_cycleType102` 给出 `10 ∣ |H|`。于是 `5 ∣ |H|`，再给出实际十二对点上的 `PairTransitive H`，即可应用 `sl_le_of_five_dvd`。它的左端是两个标准初等矩阵生成的子群，`closure_trv_eq_map` 和 `closure_sl_eq_top` 将其识别为目标中的 `SL₂` 像。我会先核对这条条件链在实际基上的接合，把 Weil pairing／行列式满射的投入留给确实需要 `H = GL₂(𝔽₅)` 或行列式的消费者。算术上仍缺该表示像内的循环型和传递性，这次没有编译这项组合。[固定基上的 D5](../tmp/sheaf/xif/paper/S1987D5LargeImageFiveActual.lean#L183) · [目标子群](../tmp/sheaf/xif/paper/S1725SourceTorsionFPrimeActual.lean#L411) · [循环型给出整除](../tmp/sheaf/xif/paper/S2009DicksonActual.lean#L406) · [传递作用给出子群包含](../tmp/sheaf/xif/paper/S2020DicksonActionActual.lean#L17) · [生成元与 SL₂](../tmp/sheaf/xif/paper/S2020DicksonTransvectionActual.lean#L304)

**M2c 值得先读到 torsion 上。** 对每个开子群 `U`，S2113 用的是规范映射在挠元上的双射。按 S2109 的充要条件，可以分别查核内的每个有限阶元是否为一，以及目标中的每个有限阶元能否提升为有限阶元。我会先查现有局部 Artin 比较对哪一问给出了新信息，再决定是否值得移植完整换位子宽度定理。如果只能得到抽象群满射，应保留第二问，因为一个提升的阶仍可能无限。[S2109 的充要条件](../tmp/sheaf/xif/paper/S2109M2cCarrierActual.lean#L201) · [构造规范映射的具体条件](../tmp/sheaf/xif/paper/S2109M2cCarrierActual.lean#L291)

**H² 若获排期，我会先试逐层修正代表元。** 先在实际 `μₙ` 的共尾离散塔上检查系数投影的满射性。若成立，一上链可用集合截面逐值提升，离散系数保证这种提升连续。相邻二余循环代表的投影若只差一个余边界，就尝试用抬升的一上链修正高层代表，递归得到严格相容的代表族，再交给 `twoCocycleExchange`。这一路线有清楚的交付物，即 `Surjective h2Comparison`。`CoboundaryLift` 仍是单射一侧的责任，接回算术端口还须核对塔和等变性。[微分与投影的交换式](../tmp/sheaf/xif/paper/S2112ContH2LimitActual.lean#L610) · [相容二余循环的组装](../tmp/sheaf/xif/paper/S2112ContH2LimitActual.lean#L534) · [端口的投影与作用](../tmp/local-cft-port/continuous-kummer-theory/ContinuousKummerTheory/Kummer/Limit.lean#L193)

**D6 与 D9 按几何见证调高优先级。** 对 D6，S2125 已表明，在记录的 lift 上改变所输入的两腿比较同构，strong field 给出的结论保持相同。我会在有人指出 `hg` 所选 presentation 上实际的 cone morphism、并能比对它的两个投影时上调 D6。对 D9，若先做下降，S2093 已把栈问题约到实际 étale 覆盖族，可从这里限制工作量。若预期交付的是 `C_F`，则我更重视构造具有双范畴泛性质的符号商见证，因为它直接供给 `S1964HonestCFQuotient` 所需的商结构。只有下降部分有新结果时，就按栈性质这一项计进展。[D6 在记录 lift 上的限制](../tmp/sheaf/xif/paper/S2125PresentationCoherentActual.lean#L514) · [D9 的覆盖族约化](../tmp/sheaf/xif/paper/S2093D9StackActual.lean#L308) · [D9 的商见证消费者](../tmp/sheaf/xif/paper/S2043D9FullActual.lean#L73)

本次为单人文档核查，原文对照限于上引段落。`statement_compiles`、`proof_body_checked`、`kernel_closed` 本次均未复验。paper-level 3.12 的 `target_accepted` 未达到。本次未运行 Lean、全 Project 构建、comparator 或独立语义审查。
