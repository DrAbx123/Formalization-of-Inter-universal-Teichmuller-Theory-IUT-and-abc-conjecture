# N8 group4 · Stage 1 — Thm 3.11 多径向输出：见证保持构造与 Ind1–Ind3

- 任务：N8 / distilled-04，读本 [`logs/coordination/n8-distilled-04-multiradial-construction-20261018.md`](../../../logs/coordination/n8-distilled-04-multiradial-construction-20261018.md)
- 节点：`n8-group4-theorem311-multiradial-output`
- 阶段：**stage 1 only**。本包不写生产代码、不做证明尝试、不改任何定义。
- 证据版本：Lean `leanprover/lean4:v4.32.2`，Mathlib `v4.32.2`（manifest rev `905b95818eb32af7874a58b427f50c1711a5e96c`）。阅读日期 2026-10-22。
- 结论（一句话）：**见证保持（witness preservation）在通用核里已经由"所有律共用同一个索引 `c`"结构性成立**，所以 distilled-04 §A 的"见证互不相容"风险在当前 `Profile` / `ProcessionPacketProfile` 形状下不会发生；真正缺的是把 `possibleImage` 从"自由律字段"变成"实际构造的像"，以及全族并集控制与真实归一化。Ind1/Ind2（商后才相等／实际可逆）、Ind3（单向包含 + 单向数值）在 `Core` / `Profile` / `VerticalSiteData` 里已分层，但有一处与原文措辞冲突待裁（§2.5）。

---

## 1. 原文对象与量词（逐项）

**证据文件**（本地原文提取，非权威公式转录）：
`papers/motizuki_corpus/text/source_audit/IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt`
文件头记录：源 PDF `Inter-universal Teichmuller Theory III.pdf`，`SOURCE_SHA256 = 9A7EE3C77B1C7717210C0613EB39B6844649D0040DC3D9E1BE7D544F8F91A0B9`，物理页 153–159（Theorem 3.11）、173–186（Corollary 3.12），`EXTRACTION_MODE: pypdf plain`，并自带 `NOTE: Machine extraction is an index, not an authoritative formula transcription`。因此下列对象按"页 + 语段"引用，字形级公式未逐项核对。

仓库内既有的 corpus 行号锚（用于交叉核对，见 `LeanFormal/IUT/IUTIII/Theorem311/SourceMultiradialTwoActionEquivalence.lean:110-117`）：(i) :9324；(a) :9336；(b) :9352；(c) :9383；(Ind1) :9419；(Ind2) :9422；functoriality :9434-9436；permutation :9437-9456；(ii) :9458；(iii) :9613；Remark 3.11.1 于 :9786 / 9803 / 9817-9827 / 9843 / 9923；Remark 3.10.2 :9225；Cor 3.12 Step (xi-b) :10950。

### 1.1 全局量词

固定一组 initial Θ-data `(F/F, X_{F,l}, C_K, V, V^bad_mod, ε)`（[IUTchI] Def 3.1）；给定一簇**互不相同的** Θ±ellNF-Hodge theater `{_{n,m}HT^{Θ±ellNF}}_{n,m∈Z}`（视为来自 LGP-Gaussian log-theta-lattice，Def 3.8(iii)）。对每个 `n∈Z`，`_{n,∘}HT^{D-Θ±ellNF}` 是这些 theater 在 Theorem 1.5(i) 的 vertical coricity 下**在同构意义下**确定的 D-Θ±ellNF-Hodge theater。所以 `n`、`m` 是 `Z` 上的量词，不是有限集；`m` 只通过 `n` 固定的 log-link 列进入。

### 1.2 (i) Multiradial Representation — 对象

1. `Prc(_{n,∘}D^{⊢}_{T})`：由 [IUTchI] Prop 6.9(ii) 的自然函子作用于 `_{n,∘}HT^{D-Θ±ellNF}` 的 D-Θ±-bridge 得到，是一条递增 procession `{_{n,∘}D^{⊢}_{0}} ↪ {…, _{n,∘}D^{⊢}_{0}, _{n,∘}D^{⊢}_{1}} ↪ … ↪ {…, _{n,∘}D^{⊢}_{0},…, _{n,∘}D^{⊢}_{l^⋇}}`。
2. 数据 (a)：`∀ v∈V, v|v_Q∈V_Q, j∈|F_l|`，拓扑模与 mono-analytic integral structure `I(S^±_{j+1}; _{n,∘}D^{⊢}_{v_Q}) ⊆ IQ(…; _{n,∘}D^{⊢}_{v_Q})`、`I(S^±_{j+1,j}; …_{v}) ⊆ IQ(…)`（Prop 3.2(ii)），并带 **procession-normalized mono-analytic log-volumes**（Prop 3.9(ii)）。
3. 数据 (b)：`∀ v∈V^bad`，splitting monoid `Ψ^⊥_{LGP}(_{n,∘}HT^{D-Θ±ellNF})_v`（Prop 3.5(ii)(c)），经自然 poly-isomorphism 视为 `∏_{j∈F^⋇_l} IQ(S^±_{j+1,j}; _{n,∘}D^{⊢}_{v})` 的子集，并带其上的（乘性）**作用**。
4. 数据 (c)：`∀ j∈F^⋇_l`，数域 `M^{⊛}_{MOD}(…)_j = M^{⊛}_{mod}(…)_j ⊆ IQ(S^±_{j+1}; _{n,∘}D^{⊢}_{V_Q}) := ∏_{v_Q∈V_Q} IQ(…)`，连同 global non-realified/realified Frobenioid 的自然同构（Prop 3.10(i)），其 global degree 用 (a) 的 log-volume 计算（Prop 3.9(iii)）。
5. `_{n,∘}R^{LGP}`：数据 (a),(b),(c) 的汇总，**只在两类 indeterminacy 下取**：
   - **(Ind1)** 由 procession `Prc(_{n,∘}D^{⊢}_T)` 的**自同构**诱导的不确定性；
   - **(Ind2)** 对**每个** `v_Q∈V^non_Q`（相应地 `v_Q∈V^arc_Q`），由 `Ism` 的**独立副本**（相应地 Prop 1.2(vii) 中 order-2 自同构轨道的副本）作用在**每个 direct summand** 上诱导的不确定性，direct summand 位于定义 `IQ(S^±_{j+1}; _{n,∘}D^{⊢}_{v_Q})` 所用 tensor product 的 `j+1` 个 factor 中；**direct summand 的基数 = 落在 `v_Q` 上的 `v∈V` 的基数**。
6. 算法：`_{n,∘}R^{LGP}` 可经 procession 中的算法构造，且**对 processions of D^⊢-prime-strips 的同构函子性**。
7. `∀ n,n′∈Z`：étale-picture 的置换对称性诱导相容 poly-isomorphism `Prc(_{n,∘}D^{⊢}_T) ~> Prc(_{n′,∘}D^{⊢}_T)`、`_{n,∘}R^{LGP} ~> _{n′,∘}R^{LGP}`，并与 bi-coricity 诱导的 `_{n,∘}D^{⊢}_0 ~> _{n′,∘}D^{⊢}_0` 相容。

### 1.3 (ii) log-Kummer correspondence 与 (Ind3)

`∀ n,m∈Z`，labeled data 的 Kummer 同构（[IUTchII] Cor 4.6(iii)、4.8(i)(ii)）在 (i) 的 **尚未施加 (Ind1)/(Ind2)** 的 vertical coric 数据 (a)(b)(c) 与**每个** theater `_{n,m}HT^{Θ±ellNF}` 的对应数据之间给出同构；`t ∈ LabCusp^±(_{n,∘}D^≻)`。

- `m` 变化时，(b) 与 (c) 第一行第一 display 的同构彼此相容，"只相差 log-link 定义域中的 unit root（即经 log-link 的 addition by zero，无不确定性）"。
- 该相容性蕴含 (c) 第一 display 第二、三行中**下标为 `MOD` 的同构**之间的相容（但**不**含 `mod`，见 Prop 3.10(iii)、Remark 3.10.1）。
- **(Ind3)** `m` 变化时，(a) 的同构相对于 `n`-列的 log-link 是 **upper semi-compatible**，"involves certain natural inclusions `⊆` at `v_Q∈V^non_Q` and certain natural surjections `↠` at `v_Q∈V^arc_Q`"（Prop 3.5(ii)(a)(b)）。
- (ii) 末句：`m` 变化时，(a) 的同构 "are **[precisely!]** compatible … with the respective **log-volumes**"（Prop 3.9(iv)）。

### 1.4 (iii) Θ×μ-LGP-link compatibility

(a)(b)(c)(d) 四段：Kummer 同构与 `F^⋊±_l`-对称性、`F^⊢×μ`-prime-strip 的 full poly-isomorphism、`F^⊩`-prime-strip / `F^⊢×μ_env` 的自然同构、`_{n,∘}R ~> _{n+1,∘}R` 的置换对称性，全部要 **stabilized/equivariant/functorial w.r.t. arbitrary automorphisms of the domain and codomain of the horizontal arrows**，"up to the indeterminacies (Ind1), (Ind2), (Ind3) described in (i), (ii)"。

### 1.5 distilled-04 的六个要求对应原文哪里

| distilled-04 | 原文位置 | 原文真正断言的量词形状 |
|---|---|---|
| §A 带见证输出 `r(x,c)`，`U(x)={y \| ∃c∈C(x), r(x,c)=y}` | (i) 全段 | `_{n,∘}R^{LGP}` 是 (a)(b)(c) 的**汇总**；indeterminacy 在**汇总之后**取商，不是逐项各取存在量词 |
| §B `C(x)` 是带约束族 | (Ind1)+(Ind2)+(i) 的 `v_Q`/`j`/`v` 索引关系 | `C(x)` = procession 自同构 × 逐 `v_Q` 的 `Ism` 副本作用；两者由 `j+1` 个 factor 的 direct-summand 基数与 `v_Q` 绑定 |
| §C 每步不变量 `P_k`（源、相容、可控制区） | (i) 算法函子性 + (ii) 相互相容 + (iii) 水平相容 | 原文"算法"= 对 procession 同构函子的构造，不是任意递推 |
| §D Ind1–3 分开处理 | (Ind1)(Ind2)(Ind3) 三处 | Ind1/Ind2 是可逆自同构；Ind3 是 `⊆`/`↠` 的单向 + 体积的 "precisely" |
| §E–F 单自同构保体积 ≠ 并集有界；需共同格／紧参数／显式算子范数 | (i) 的 `V_Q` 有限性 + (ii) `m∈Z` 变化 | 原文的紧性是 `1,∘U_{j,v_Q}` 的紧性（Cor 3.12 证明），**不是** Ind 参数空间的紧性 |
| §G–H 标签置换加权平均、归一化随真实索引 | (a) procession-normalized log-volumes（Prop 3.9(ii)）、(b) 的 `∏_j`、(c) 的 `∏_{v_Q∈V_Q}` | 权重来自**真实**索引：`j∈F^⋇_l`、`v_Q∈V_Q`、`j+1` 个 tensor factor |
| §I 忘掉隐藏结构 | (i) 取 (Ind1)(Ind2) 商 | 商的合法性要求构造在每根纤维上恒定；原文以 "regarded up to indeterminacies" 表达 |

---

## 2. 当前 Lean 接口（读到的确切形状）

### 2.1 通用核（与具体模型无关）

- `MultiradialKernel.Core`（`MultiradialOutputKernel.lean:12`）：`base : Choice`，`level : Choice → Nat`，`ind1/ind2 : Label → Choice → Choice`，`ind3 : Nat → Choice → Choice`，群律 `ind1_zero/add/inverse`、`ind2_zero/add/inverse`、`ind3_zero/add`（`ind3_add : ind3 (m+n) c = ind3 n (ind3 m c)`，单向幺半群），三者两两交换，以及 `ind1_level`、`ind2_level`（等号）、`ind3_level : level c ≤ level (ind3 n c)`（**单向**）。
- `Core.GeneratedEqualityRelation`（`:99`）= 由 `Ind1Step`/`Ind2Step` 生成的等价关系（含 refl/symm/trans），**不含** `Ind3Step`；`generatedSetoid`（`:132`）、`GeneratedQuotient`、`generatedQuotientMap`。
- `Profile`（`MultiradialProfileKernel.lean:13`）：`logVolume : Choice → Real`、`possibleImage : Choice → Set Real`，加 7 条律：`ind1_invariant`、`ind2_invariant`（logVolume **等号**）、`ind3_upper : logVolume c ≤ logVolume (ind3 n c)`、`possibleImage_nonempty`、`possibleImage_ind1`、`possibleImage_ind2`（集合**等号**）、`possibleImage_ind3 : z∈img c → ∃w∈img (ind3 n c), z≤w`。
- `Profile.possibleImage_respects_generated`（`:75`）、`quotientPossibleImage`（`:90`，`Quotient.liftOn'`）——Ind1/Ind2 的商下降已证。
- `RouteStep`（`:121`）、`applyRoute`（`:134`）、`horizontal`（`:232`）、`Output`（`:326`，字段 `source : Choice`、`route : List (RouteStep Label)`、`source_image_nonempty : (possibleImage source).Nonempty`），`Output.target`（`:338`）= `applyRoute core route source`。
- `Output` 的结论：`target_level_ge`、`source_logVolume_le_target`、`horizontal_target_logVolume_eq`、`horizontal_target_image_eq`、`target_image_upper`（`:362`）。

### 2.2 source 边界（论文 (i)(ii)(iii) 的仓库形状）

- `Theorem311Source.DPrimeStripProcession`（`SourceFaithfulBoundary.lean:58`）= `Core` 的逐字段展开（另立名字，避免把 kernel 当原文）。
- `ProcessionPacketProfile`（`:125`）= `Profile` 的逐字段展开；**`possibleImage` 与其三条律全是记录字段**。
- `DerivedPrerequisiteInput`（`:278`，`abbrev Input := DerivedPrerequisiteInput`）：把 (a)(b)(c) 装成字段——`packet : ProcessionPacketProfile prime`、`localPacket : LocalTensorPacket prime`、`packet_profile_volume`、`vertical : UpperSemiCorrespondence Nat Real`、`verticalSite : VerticalSiteData Choice`、`verticalSite_{nonarchimedean,archimedean}_profile`、`labelledCount`、`evaluation`、`labelledKummer`、`family`、`horizontal`、三条水平相容。
- `VerticalSiteData`（`:256`）：`nonarchimedean_inclusion : z∈S → z∈nonarchimedeanImage m S`；`archimedean_surjection : z∈archimedeanImage m S → ∃y∈S, z≤y`。**这正是原文 (Ind3) 的 `⊆` at `V^non` 与 `↠` at `V^arc` 的分层**，两侧不混。
- `IndeterminacyQuotient`（`:624`）、`quotientMap`（`:627`）、`quotientLevel/quotientVolume/quotientImage`（`:674/:678/:683`）：Ind1/Ind2 商上的 well-defined 层。
- `PartI`（`:714`）：字段 `quotient`、`source`、`source_map`、`source_image_nonempty`、`level_bound`、`volume_bound`、`ind1_invariant`、`ind2_invariant`（后两条在**商上**陈述，形式已对）。
- `Theorem311Output`（`:1584`）：`part_i`、`part_ii`、`part_iii`、`source`、`source_eq`、`quotient`、`quotient_eq`、`labelled_bijective`、`ind1_quotient`、`ind2_quotient`、**`ind3_upper`**（`∀ n c z, z∈possibleImage c → ∃w∈possibleImage (ind3 n c), z≤w`）、`horizontal_square`、`horizontal_evaluation`。构造子 `theorem311Output`（`:1604`）逐字段投影已有证明。

### 2.3 参数化载体（Step-XI 消费者实际用的形状）

- `ParametricTheorem311.Carrier`（`ParametricCarrier.lean:25`）：`core`、`profile`、`connector : Choice → Choice → List (RouteStep Label)`（+ 水平性 + 同层可达）、**`ind3_level_eq : level (ind3 n c) = level c + n`**（`:33`）。
- `Ind1Certificate`（`:232`）／`Ind2Certificate`（`:272`）／`Ind3Certificate`（`:312`）：每种一步的**带见证证书**——`target : Choice`、`target_eq : target = …`、`level_eq`、`profile_eq`（Ind3 为 `profile_le`）、`image_eq`（Ind3 为 `image_upper`）。`IndependenceBundle`（`:353`）把三者与三条交换律放进**同一个** bundle。
- `AlgorithmInput`（`:403`）、`AlgorithmOutput`（`:419`）：`target`、`target_eq`、`level_monotone`、`profile_monotone`、`target_image_upper`；`runAlgorithm`（`:429`）全字段构造。

### 2.4 具体 Q(i)-at-5 模型

- `ConcreteFiniteTheorem311.ProcessionChoice`（`ConcreteFiniteModel.lean:98`）= `{processionLabel : Fl l.value, tensorLabel : Fl l.value, upperSemiLevel : Nat}`，`Fl l = ZMod l`（`Foundations/Arithmetic/FiniteLabels.lean:26`）。
- `ind1Act`（`:121`）= 加法平移 `processionLabel`；`ind2Act`（`:124`）= 加法平移 `tensorLabel`；`ind3Lift`（`:127`）= `upperSemiLevel + n`。
- `normalizedLogVolume l c = thetaLogVolume l + (c.upperSemiLevel : Real)`（`:329`）；`possibleImage l c = {normalizedLogVolume l c}`（`:379`，单点集）。
- `SourceFiniteMultiradial.core l`（`SourceFiniteMultiradial.lean:20`）、`profile l`（`:95`）逐字段用上面的 model 律装入 `Core`/`Profile`。
- `SourceFiniteMultiradial.routeOutput`（`:197`）、`sameLevel_quotient_eq`（`:282`）、`quotient_image_ind3_upper`（`:319`）、`profile_possibleImage`（`:125`）。

### 2.5 一处与原文措辞冲突（必须登记，本包不改定义）

distilled-04 §D 写 "Ind3 对体积出现单向比较"，并要求"若只得 `V(TX)≤V(X)`，写成 `=` 会抹掉关键方向"。但原文 (ii) 末句是 "the isomorphisms of (a) are **[precisely!]** compatible … with the respective **log-volumes**"——字面上体积是**精确兼容**，单向性属于集合像的 `⊆`/`↠`。当前 Lean 把体积做成单向：`Profile.ind3_upper : logVolume c ≤ logVolume (ind3 n c)`（`MultiradialProfileKernel.lean:21`）、`FiniteOutput.ind3_upper`（`ConcreteFiniteModel.lean:440`）。

- 若"precisely"指 log-volume 在 (Ind1)(Ind2) 商上被精确确定，则现在的 `≤` 是**弱化**，`Theorem311Output.ind3_upper` 也就弱于 (ii)。
- 若"precisely"只是"与 Prop 3.9(iv) 的 log-volume 相容"，则 `≤` 仍不足以覆盖该句。
- 两种读法下都不能声称覆盖该句。裁定需要 Prop 3.9(iv) 与 Cor 3.12 证明 Step (x)/(xi) 的原文；**不授权**本包改 `Profile` 或 `VerticalSiteData`。这是 `statement_disputed` 型缺口（SHEAF §5 第 1 优先级）。

---

## 3. 实际消费者（唯一具名）

**主消费者链（Theorem 3.11 → Cor 3.12 Step XI）**

1. `SourceProcessionBoundary.Input`（`SourceProcessionBoundary.lean:33`）：`theater`、`history`、`carrier : Carrier Label Choice`、`baseChoice`、`baseChoice_eq`、`packetVolume`、`packetVolume_eq_profile`、`base_packetVolume_eq_theta`、`target_q`、`route_normal_form`。
2. `ParametricStepXI.StepXIWallCertificate`（`ParametricStepXI.lean:183`）：字段 `theorem311 : AlgorithmOutput carrier input`（`:185`）、`ind1_route/ind2_route/ind3_route`、`commutation12/13/23`、`output_is_run`。构造子 `stepXIWallCertificate`（`:194`）**全部由已有定理填满**。
3. `SourceProcessionStepXI.Wall`（`SourceProcessionStepXI.lean:32`）与 `sourceStepXIBoundaryV2`（`:512`）。

**消费者实际需要什么、不需要什么（关键剪枝）**

- 它只需要 `AlgorithmOutput`（`ParametricCarrier.lean:419`）的四个字段：`target`、`level_monotone`、`profile_monotone`、`target_image_upper`——即 **每个 `c` 上的逐点单向性**，**没有任何全族并集界、没有 sup/log-volume 数值比较**。
- `StepXIInput`（`ParametricStepXI.lean:27`）的三个数值 `qSigned/targetSigned/thetaSigned` 与 `q_le_target`、`target_le_theta`（`:41-42`）是**自由字段**：Cor 3.12 的两个 ε 比较**不是**从 Theorem 3.11 的输出推出来的。
- 因此：**Ind1–Ind3 的"全族统一控制"当前没有 Lean 消费者**。任何声称"3.11 输出已供第 6 章体积界使用"的说法都不成立。

**次消费者（真正需要体积，但对象不同）**

- `SourceImageHullVolume.lean`：`SourceCompactBound`（`:264`）、`sourceSetVolume_possibleImage_lt_top_of_compactBound`（`:273`）、`sourceHullVolume_lt_top_of_hullBound`；负结果 `not_exists_sourceHullLogDegreeBound_of_degreeFaithful`（`:414`）、`sourceHullVolume_eq_top_of_degreeFaithful`（`:428`）。
- 其对象是 `possibleThetaPilotImageSet`（`Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean:231`），索引是 `ThetaPilotCarrier l = Fin (lStar l.value + 1)`（`:64`）——**不是** `ProcessionChoice`。在 `IUTIII/Corollary312/StepXI/HolomorphicHull/` 目录里 `ProcessionChoice` 出现 **0 次**（已 grep 全目录）。
- 结论：kernel 的 `profile.possibleImage : Choice → Set Real`（Ind1–3 见证索引）与 Cor 3.12 的 `sourceSetVolume (possibleThetaPilotImageSet v R n)`（值幺半群 + 有限 `n` 索引）是**两条形式互不相连的分支**。连接二者是一个**新节点**，不是本节点能顺带补的字段。

---

## 4. 已有 Lean 供体（file:line)

### 4.1 核与见证（可直接复用，已证）

| 供体 | 位置 | 内容 |
|---|---|---|
| `MultiradialKernel.Core` | `Theorem311/MultiradialOutputKernel.lean:12` | Ind1/2 群作用 + Ind3 幺半作用 + 交换律 + level 律 |
| `Core.GeneratedEqualityRelation` | 同上 `:99` | 只由 Ind1/Ind2 生成的等价关系（Ind3 不入商） |
| `Core.generatedSetoid` / `GeneratedQuotient` | 同上 `:132` | Ind1/2 商 |
| `Profile` | `Theorem311/MultiradialProfileKernel.lean:13` | log-volume + possibleImage 的 7 条律（同一 `c` 索引） |
| `Profile.possibleImage_respects_generated` | 同上 `:75` | 商下降的合法性 |
| `Profile.quotientPossibleImage` | 同上 `:90` | 商上的像 |
| `RouteStep` / `applyRoute` / `horizontal` | 同上 `:121/:134/:232` | 算法路径语言 |
| `Output` / `Output.target` | 同上 `:326/:338` | 带 source+route 的输出 |
| `Output.target_image_upper` | 同上 `:362` | 沿整条 route 的单向像控制 |
| `DPrimeStripProcession` | `Theorem311/SourceFaithfulBoundary.lean:58` | source 名下的同一批律 |
| `ProcessionPacketProfile` | 同上 `:125` | source 名下 `Profile` 的逐字段副本（`possibleImage` 是字段） |
| `VerticalSiteData` | 同上 `:256` | (Ind3) 的 `⊆` at `V^non` / `↠` at `V^arc` 分层 |
| `IndeterminacyQuotient` 及 `quotientLevel/Volume/Image` | 同上 `:624/:674/:678/:683` | 商上的 well-defined 量 |
| `PartI` | 同上 `:714` | (i) 的源侧形状（商上陈述 Ind1/Ind2） |
| `Theorem311Output` / `theorem311Output` | 同上 `:1584/:1604` | (i)(ii)(iii) 的 field-level 汇总 |
| `Carrier` | `Theorem311/ParametricCarrier.lean:25` | 参数化载体（含 `ind3_level_eq`） |
| `Ind1Certificate` / `Ind2Certificate` / `Ind3Certificate` | 同上 `:232/:272/:312` | 每步带见证证书 |
| `IndependenceBundle` | 同上 `:353` | 三种证书 + 三条交换律的共同 bundle |
| `AlgorithmOutput` / `runAlgorithm` | 同上 `:419/:429` | 逐点不变量全部由 route 推出 |
| `CarrierAlgorithmContract` | `Theorem311/Output/MultiradialAlgorithmReduction.lean:265` | 任意 carrier 的算法契约（已证） |
| `SourceOutputLawBundle` / `sourceMultiradialOutputDischarge` | 同上 `:461/:536` | `Input` ⟹ 输出 + 律 bundle（条件性） |

### 4.2 具体模型与 Ind 专项

| 供体 | 位置 | 内容 |
|---|---|---|
| `ProcessionChoice` | `Theorem311/ConcreteFiniteModel.lean:98` | `Fl × Fl × Nat` 的自由积选择族 |
| `ind1Act/ind2Act/ind3Lift` | 同上 `:121/:124/:127` | 两个平移 + 一个 Nat 递增 |
| `normalizedLogVolume` | 同上 `:329` | `θ + level` |
| `possibleImage` | 同上 `:379` | 单点集 `{θ + level}` |
| `possibleImage_ind3` | 同上 `:396` | 单向 `∃w, z≤w` |
| `FiniteOutput` / `finiteOutput` | 同上 `:427/:451` | 把上面装成 §2.2 的字段形状 |
| `SourceFiniteMultiradial.core` / `profile` | `Theorem311/SourceFiniteMultiradial.lean:20/:95` | 具体实例的 `Core`/`Profile` |
| `sameLevel_quotient_eq` | 同上 `:282` | 同层 ⟹ 同商类 |
| `quotient_image_ind3_upper` | 同上 `:319` | 商上的 Ind3 单向 |
| `quotientClass_eq_iff_level_eq` | `Theorem311/Indeterminacy/Ind1QuotientTransport.lean:68` | 商类 = level 完全不变量的半边（iff） |
| `normalizedLogVolumeOnQuotient` (+ `_mk/_unique/_injective`) | 同上 `:80/:86/:92/:104` | 商上体积：存在、唯一、**单射** |
| `ConstructedOutputQuotientCompatibility` | 同上 `:127` | (Ind1) 的冻结 consumer 形状（已实例化） |
| `outputImageFamily` / `constructedOutputUpperSemi` | `Theorem311/Indeterminacy/Ind3UpperSemiConstruction.lean:47/:138` | Ind3 的阶族与对应 |
| `outputImageFamily_not_le_of_lt` | 同上 `:121` | **严格单向**：后阶不支配前阶 |
| `UpperSemiCorrespondence` | `Theorem311/Indeterminacy/UpperSemi.lean:18` | 集合值 upper-semi 核 |

### 4.3 紧性/区域控制（distilled-04 §E–F 的仓库对应物）

| 供体 | 位置 | 内容 |
|---|---|---|
| `OneCircUGeometry` | `Theorem311/SourceOneCircUGeometry.lean:113` | 有限 `|F_l| × V_Q` 索引 + 每像紧 + 单位区凸 + 缩放区闭有界 |
| `oneCircU_isCompact` | 同上 `:164` | 有限并紧 |
| `hull_subset_scaledUnitRegion` | 同上 `:185` | `hull ⊆ λ·O`（= §F 的"共同区域/共同格"方法） |
| `hull_bounded` | 同上 `:198` | `Bornology.IsBounded hull` |
| `modelLogVolume` | 同上 `:208` | 与 `sourceSetVolume` 同形状的 `iSup` |
| `SourceCompactBound` | `Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean:264` | 原文紧性作为**具名假设**（不是字段） |
| `sourceSetVolume_possibleImage_lt_top_of_compactBound` | 同上 `:273` | 有紧界 ⟹ 像的 log-volume 有限 |

### 4.4 加权/归一化（distilled-04 §G–H）

| 供体 | 位置 | 内容 |
|---|---|---|
| `WeightedDeterminantPacket` | `Corollary312/StepXI/HolomorphicHull/WeightedNormalization.lean:25` | `hullLogDegree`、`denominator : label → ℕ+` |
| `commonTensorDegree` | 同上 `:38` | `∏ i, denominator i`（**由真实索引算出**） |
| `summandTensorExponent` | 同上 `:43` | `∏_{j≠i} denominator j` |
| `weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume` | 同上 `:97` | 一般加权恒等式（任意 packet） |
| `sourceNormalizationPacket` | `IUTII/Theta/ConcreteSourceHistoryLinkBridge.lean:434` | **具体实例**：`hullLogDegree ≡ 0`、`structureSheafLogDegree = 0`、索引 `Fin 2`、`denominator = 2,4` |
| `sourceNormalizationPacket_common_degree` | 同上 `:447` | 推出 `commonTensorDegree = 8` |
| `sourceNormalizationPacket_weighted_identity` | 同上 `:453` | 该实例的恒等式 |
| `EWeightedLogVolumeData` | `Theorem311/SourceEWeightedLogVolumeData.lean:99` | Remark 3.1.1(iv) 的 (V,E,M) 骨架 |
| `kappa_log_eWeightedVolume_eq_weightedSum` | 同上 `:203` | (iv) 的 display（Q1） |
| `shift_pvQ_add_log` | 同上 `:256` | `p_{v_Q}` 平移律（Q2） |
| `labelWeight` / `weightedDiagonalHom` | `Theorem311/SourceLabelWeightedDiagonal.lean:33/:80` | `j²` 权重与加权对角 |
| `sourceLabelWeightedDiagonal` | 同上 `:335` | 该文件的 Audit 卡 |

---

## 5. 精确缺口（G4-A … G4-J）

### G4-A（核心）`possibleImage` 是自由律字段，不是构造出的像

`ProcessionPacketProfile`（`SourceFaithfulBoundary.lean:125`）与 `FiniteOutput`（`ConcreteFiniteModel.lean:427`）都把 `possibleImage : Choice → Set Real` 连同三条律写成**记录字段**。`Theorem311Output`（`:1584`）与 `SourceOutputLawBundle`（`MultiradialAlgorithmReduction.lean:461`）只是把这些字段投影出去。于是：

- 见证保持（distilled-04 §A）在**索引层面**成立：所有律共用同一个 `c`，不会出现"三个存在量词各有不相容见证"。
- 但**没有任何东西强制 `possibleImage c` 是某个 `r(x,c)` 的像**。这一点可以**证明**（见 §6 的 S2-W）：存在一个 admissible profile，与预期 profile 的 `logVolume` 在**每个** `c` 上完全相同，却在同一个 `c` 上给出不同的 `possibleImage`。

### G4-B 没有"输出值"，也没有 (a)(b)(c) 的构造

- `MultiradialKernel.Output`（`:326`）只有 `source`、`route`、`source_image_nonempty`；`target = applyRoute route source`。它是**路径**，不是数据 (a)(b)(c)。
- source 侧的 Card MP/MA（`SourceMultiradialTwoActionEquivalence.lean:149/:199`）把输出数据写成**自由类型参数** `Output : Type uOut`，且自带 `nonempty_iff : Nonempty (SourceTheorem311MultiradialPresentation G I n Output) ↔ Nonempty Output`（`:180`）与 `nonempty_iff : Nonempty (SourceTheorem311MultiradialAlgorithm …) ↔ Nonempty Output`（`:258`）——即该记录在数学上**等价于"输出类型非空"**：任取一个 inhabitant + 平凡作用即可满足。
- `SourceMultiradialPresentationWiring.sourcePresentationOfCarrier`（`:191`）把 `Output` 实例化为 `Choice` 本身，`output := runAlgorithm … .target`。所以该 wiring 的"输出"是**procedure 的终点索引**，不是数据 (a)(b)(c)。这与该文件 header `:40-64` 的 R1–R4 与 W.3 "not expressible" 自述一致。

### G4-C 无全族并集控制，也无"无穷体积分支"标记

- `IUTIII/Theorem311` 目录内 `BddAbove` 出现 **0 次**。
- 具体模型：`possibleImage l c = {θ + level c}`，`level` 取遍 `Nat`（`c = base` 配 `ind3Lift n`），故 `⋃ c, possibleImage l c = {θ + n | n : Nat}` —— **上无界**。这正是 distilled-04 §E 的 `diag(p^n, p^{-n})` 现象在加法坐标下的同型：每步保体积（`ind1/ind2` 等号、`ind3` 只有 `≤`），但族并集无界。
- 而 `Nat` 参数不紧；`Fl l = ZMod l` 有限因此紧。所以 §F 的"紧参数法"只能覆盖 Ind1/Ind2（平凡地），**Ind3 恰好在失去紧控制的位置**。
- 分支对照：Branch B（`SourceImageHullVolume.lean:428`）已**如实保留无穷体积分支**（`sourceHullVolume = ⊤`，`:414` 证明整 hull 界不可满足）；Branch A 没有对应声明。

### G4-D 选择族是无约束自由积，且不紧

`ProcessionChoice = Fl l × Fl l × Nat`（`:98`），没有 (Ind1)/(Ind2) 之间的任何兼容关系，也没有"多个位来自同一全局对象／同一整体作用"的约束。distilled-04 §B 要求的受约束子族在 Branch A 里**不存在**；模型里它恰好无害（像是单点），但它使"`C(x)` 是什么"不可从 Lean 读出。

### G4-E `Carrier.ind3_level_eq` 是强于原文的接口假设

`ParametricCarrier.lean:33`：`ind3_level_eq : level (ind3 n c) = level c + n`，而 `Core.ind3_level : level c ≤ level (ind3 n c)`（`MultiradialOutputKernel.lean:31`）是单向。模型里 `rfl` 成立（`ConcreteFiniteModel.lean:162`）。这是**对载体的额外假设**，不是原文 (Ind3) 事实；所有用到 `Carrier` 的结论（含 StepXI）都继承它。必须登记为 model-strengthening。

### G4-F Ind1/Ind2 在 raw choice 上取等，比原文的"商上相等"更强

`Profile.ind1_invariant`（`:17`）与 `ind2_invariant`（`:19`）是 raw 等号。原文 (i) 只说 "regarded up to indeterminacies"，即商上相等。更强的形式使商下降（`possibleImage_respects_generated`、`Ind1QuotientTransport.lean:80`）变成**平凡**一步，也让 `Ind1QuotientTransport` 的"唯一性／单射性"结论在模型中不承担证明量。这不算错，但会让"商转换已证"被高估。

### G4-G 标签加权平均在 Branch A 完全缺失，且在模型里已脱钩

- `finiteLabel l = Fl l.value = ZMod l.value`（`ConcreteFiniteModel.lean:32`），而 theta 权重的下标是 `SignedLabel l.value`（区间 `[-l*, l*]`）。
- `ind1Act` 平移 `ZMod l`，**不**作用于 `SignedLabel`；`thetaLogVolume` 是对 `SignedLabel` 求 `log thetaScale` 的和。
- 因此 distilled-04 §G 的 `Σ_i w_i a_{σ(i)} = Σ_j w_{σ^{-1}(j)} a_j` 在当前模型里**即使证出来也是空转**：Ind 群根本不动标签集。这是模型边界，不是待证引理。
- 仓库有真实供体可用于将来的加权重索引：`WeightedNormalization.lean:38/:43/:97`、`SourceEWeightedLogVolumeData.lean:99/:203/:256`、`SourceLabelWeightedDiagonal.lean:33/:80`。

### G4-H 定理 3.11 输出里的"归一化"实例是空等式

`sourceNormalizationPacket`（`ConcreteSourceHistoryLinkBridge.lean:434`）取 `hullLogDegree := fun _ => 0`、`structureSheafLogDegree := 0`、索引 `Fin 2`、`denominator := 2,4`。于是 `weightedLogVolume = Σ_i exponent_i · 0 = 0`、`normalizedLogVolume = Σ_i 0/d_i = 0`，恒等式 `weightedLogVolume = commonTensorDegree * normalizedLogVolume` 化为 **`0 = 8 · 0`**。该等式被 `SourceFiniteOutput.output_normalization_identity`（`:130`）与 `SourceFiniteMultiradial.source_output_normalization`（`:415`）当作 3.11 输出的归一化事实转发。**一般**恒等式（`WeightedNormalization.lean:97`）是真的且对任意 packet 成立；但 3.11 的实例没有数值内容，不能充当 distilled-04 §H 的"随真实索引计算归一化"。`Fin 2` 也不等于论文的 tensor 秩／局部域次数／packet 权重／全局次数中的任何一个。

### G4-I `possibleImage` 对 `level` 的因子化／下降没写

模型里 `possibleImage l c` 只依赖 `c.upperSemiLevel`，所以它**沿 `level : ProcessionChoice l → Nat` 因子化**（可以证），即 distilled-04 §I 的"`A` 在 `π` 纤维上恒定 ⟹ 单值下降"有**正例**可写；但既然 `Nat` 无界，这个单值下降恰好把无界性暴露出来（`n ↦ θ+n`）。当前代码既没有这个因子化定理，也没有"下降后仍无界 ⟹ 保留集合值／无界分支"的标记。

### G4-J 分支不相连（结构性缺口，需新节点）

`profile.possibleImage : Choice → Set Real`（Branch A）与 `sourceSetVolume (possibleThetaPilotImageSet v R n)`（Branch B）之间**没有任何 Lean 桥**（§3 的 grep 证据）。没有桥，Branch A 的 Ind3 结果无法进入 Cor 3.12 的 hull/volume 消费者；反过来 Branch B 的紧界也不能回答"3.11 的多径向像是否被控制"。这是"`IUT-III.source-APT-transport-supply`／`IUT-III.IPL.algorithmic-provenance` 一类具名卡"之外的**另一个**新节点，本包只登记。

---

## 6. 最小阶段 2 陈述（精确类型）

### 6.1 S2-W（**最小**，先做）：kernel 不决定 `possibleImage`

放在 `tmp/sheaf/n8/group4/Statements.lean`，独立 namespace，只 import 现有生产模块。

```lean
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import Mathlib.Tactic

namespace LeanFormal.IUT.MultiradialKernel

universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- 冻结的 kernel 律不能确定 possibleImage：对任意 core 与任意基准体积，
存在 admissible Profile，其 possibleImage 处处是 univ、logVolume 恒等于基准值。
即 (Ind1)(Ind2) 的像等号、(Ind3) 的单向支配、非空、体积律全部满足，
而"像"可以是任意全空间。 -/
theorem exists_profile_univ_image
    (core : Core Label Choice) (baseVolume : Real) :
    ∃ Q : Profile core,
      (∀ c : Choice, Q.possibleImage c = Set.univ) ∧
        Q.logVolume = (fun _ : Choice => baseVolume) := by
  refine ⟨{ logVolume := fun _ => baseVolume
            possibleImage := fun _ => Set.univ
            ind1_invariant := fun _ _ => rfl
            ind2_invariant := fun _ _ => rfl
            ind3_upper := fun _ _ => le_rfl
            possibleImage_nonempty := fun _ => Set.univ_nonempty
            possibleImage_ind1 := fun _ _ => rfl
            possibleImage_ind2 := fun _ _ => rfl
            possibleImage_ind3 := fun _ _ _ _ =>
              ⟨_, Set.mem_univ _, le_rfl⟩ }, rfl, rfl⟩

end LeanFormal.IUT.MultiradialKernel
```

**精确类型（写进节点用）**：

```text
exists_profile_univ_image :
  ∀ {Label : Type u} {Choice : Type v} [AddGroup Label],
    MultiradialKernel.Core Label Choice → Real →
      ∃ Q : MultiradialKernel.Profile core,
        (∀ c : Choice, Q.possibleImage c = Set.univ) ∧
          Q.logVolume = (fun _ : Choice => baseVolume)
```

**尖锐形式（推荐最终 S2-W，约 20 行、无 `sorry`）**：

```lean
namespace LeanFormal.IUT

open ConcreteFiniteTheorem311

/-- 具体 Q(i)-at-5 载体：存在与 Constructed 输出**逐点体积完全相同**、
但像处处不同（univ）的 admissible Profile。 -/
theorem concrete_profile_image_not_determined (l : PrimeGeFive) :
    ∃ Q : MultiradialKernel.Profile (SourceFiniteMultiradial.core l),
      Q.logVolume = (SourceFiniteMultiradial.profile l).logVolume ∧
        Q.possibleImage ≠ (SourceFiniteMultiradial.profile l).possibleImage := by
  refine ⟨{ (SourceFiniteMultiradial.profile l) with
            possibleImage := fun _ => Set.univ
            possibleImage_nonempty := fun _ => Set.univ_nonempty
            possibleImage_ind1 := fun _ _ => rfl
            possibleImage_ind2 := fun _ _ => rfl
            possibleImage_ind3 := fun _ _ _ _ =>
              ⟨_, Set.mem_univ _, le_rfl⟩ }, rfl, ?_⟩
  intro h
  have h0 : (0 : Real) ∈ (SourceFiniteMultiradial.profile l).possibleImage
      (ProcessionChoice.base : ProcessionChoice l) := by
    rw [← h]; exact Set.mem_univ 0
  have h1 : (1 : Real) ∈ (SourceFiniteMultiradial.profile l).possibleImage
      (ProcessionChoice.base : ProcessionChoice l) := by
    rw [← h]; exact Set.mem_univ 1
  rw [SourceFiniteMultiradial.profile_possibleImage, possibleImage,
    normalizedLogVolume] at h0 h1
  simp only [ProcessionChoice.base_upperSemiLevel, Nat.cast_zero,
    Set.mem_singleton_iff] at h0 h1
  linarith

end LeanFormal.IUT
```

注意：`{ profile l with possibleImage := … }` 会同时保留 `logVolume` 与三条体积律，只换像与三条像律——这正是"同一个见证、同一个体积、不同像"的精确形式。`h0`/`h1` 用 `rw [← h]` 把目标里的 `(profile l).possibleImage` 换成常值 `univ`（`h` 的方向是 `Q.possibleImage = profile l 的像`，故必须反向重写）；stage 2 落地时若 `simp` 集合不同，只改 `simp` 列表，不改陈述。

**S2-W 的价值**：它把 G4-A 从"担心"变成"定理"，并给出**改动许可**——若要让 `Theorem311Output` 成为 (i) 的忠实形式化，`possibleImage` 必须由构造给出（S2-W′），不能继续作自由字段。其消费者是 `IUT-III.theorem-3.11-output`（`Obligations.lean:5`，状态 `pending`）与 `SourceOutputLawBundle`（`MultiradialAlgorithmReduction.lean:461`）的忠实性主张：它证明后者当前不足以声称 (i)。

### 6.2 S2-W′（S2-W 之后，同节点）：见证保持的 profile

```lean
structure WitnessedProcessionProfile
    (P : Theorem311Source.DPrimeStripProcession Label Choice) where
  /-- 每个 choice 内部仍允许的选择（Kummer 选择、标签、局部表达等） -/
  inner : Choice → Type v
  /-- 构造在该 choice、该内部选择上真正给出的输出值 -/
  value : ∀ c : Choice, inner c → Real
  /-- (Ind1)：内部选择沿群作用被重索引，值不变 -/
  ind1_reindex : ∀ (g : Label) (c : Choice), inner (P.ind1 g c) ≃ inner c
  ind1_value : ∀ (g : Label) (c : Choice) (i : inner c),
    value (P.ind1 g c) (ind1_reindex g c i) = value c i
  /-- (Ind2)：同上 -/
  ind2_reindex : ∀ (g : Label) (c : Choice), inner (P.ind2 g c) ≃ inner c
  ind2_value : ∀ (g : Label) (c : Choice) (i : inner c),
    value (P.ind2 g c) (ind2_reindex g c i) = value c i
  /-- (Ind3)：只要求单向支配（不要求逆、不要求等号） -/
  ind3_dominate : ∀ (n : Nat) (c : Choice) (i : inner c),
    ∃ i′ : inner (P.ind3 n c), value c i ≤ value (P.ind3 n c) i′
```

**这里有一个必须承认的设计问题**：`Profile.logVolume : Choice → Real` 是**单值**的，而见证保持的构造天然是 `(c, i) ↦ value c i`。若 `inner c` 多于一个元素，就无法从 `value` 得到单值 `logVolume`；唯一诚实的做法是把 index 换成 `Σ c, inner c`（新的 `Core`/`Profile` 变体），或要求 `value c` 在 `inner c` 上恒定（那时见证保持就退化）。S2-W′ 的实质是**定夺这一点**，不是写一个 wrapper。**不要在 stage 1 假装它已解决。**

暂定目标类型（待上面定夺后敲定）：

```text
WitnessedProcessionProfile.toProfile :
  ∀ {Label : Type u} {Choice : Type v} [AddGroup Label]
    (P : Theorem311Source.DPrimeStripProcession Label Choice),
    WitnessedProcessionProfile P → Theorem311Source.ProcessionPacketProfile P
```

具体实例 `witnessedConcreteProfile l : WitnessedProcessionProfile (core of l)` 取 `inner c := PUnit`、`value c _ := normalizedLogVolume l c`，可与现 `SourceFiniteMultiradial.profile l` 交叉核对——但注意 `PUnit` 情形下 `inner` 不承载任何信息，所以它只验证接口一致性，**不证明源实例**。

### 6.3 不选为最小项的两个候选（记录理由）

- **全族并集界**（G4-C）：没有消费者（§3），且反例已成立（并集无界）。若要做，正确形状是"逐 level 控制 + 无界分支"两条，而不是伪造一个 `BddAbove`。
- **`Ind3` 体积等号**（§2.5）：属 `statement_disputed`，需要原文 Prop 3.9(iv) / Cor 3.12 Step (x)(xi) 才能裁定；在裁定前写 `=` 或 `≤` 都是替原文做决定。

---

## 7. 剪枝决定（本节点不再做）

1. 不重证 Ind1/Ind2 商下降（`MultiradialProfileKernel.lean:75/:90`、`Ind1QuotientTransport.lean:80`）。已 `proof_body_checked`。
2. 不重证 Ind3 阶族与严格单向（`Ind3UpperSemiConstruction.lean:47/:121/:138`）。
3. 不再包装 Card MP/MA/TA 的 `nonempty_iff`（`:180/:258`）——它已经是"该记录无内容"的证明，任何新 wrapper 只会加深同义反复。
4. 不在本节点做 `1,∘U` 的紧性／`hull ⊆ λ·O`（`SourceOneCircUGeometry.lean:164/:185/:198`）——那是 Cor 3.12 的已有供体，且属 Branch B。
5. 不做 `Nat` 上的紧化或把 `ind3Lift` 改成有界算子——那会改对象。
6. 不把 `EWeightedLogVolumeData` 的一般恒等式硬塞进 `sourceNormalizationPacket` 的零实例来"修好" G4-H；正确做法是给 3.11 输出一个**真实索引**的归一化实例（新节点），先定索引再定数值。

---

## 8. 运行／未运行

- 本包**未编译任何 Lean**（stage 1 only，按任务要求不做证明尝试）。因此 `statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 对 S2-W / S2-W′ 全部**未运行 / 未取得**。
- 已执行的机械检查：全目录 `grep`（`BddAbove` = 0；`ProcessionChoice` 在 `HolomorphicHull/` = 0；`possibleThetaPilotImageSet` 的引用清单）；声明行号核对（`glob`／`grep`／`read`）。
- stage 2 一旦写文件，用：`pwsh -NoProfile -File tools/build_guard.ps1 -Command 'lake env lean tmp/sheaf/n8/group4/Statements.lean' -WorkDir 'D:/lean' -WaitTimeoutSec 60`；只记 `statement_compiles`；含具名 `sorry` 时不得改写 `lean_auto` 的 proof-policy 结果。
- 未运行 comparator；未做独立语义审查；`locked_targets` 仍为空。

## 9. 证据版本

| 项 | 值 |
|---|---|
| Lean | `leanprover/lean4:v4.32.2` |
| Mathlib | `v4.32.2`，manifest rev `905b95818eb32af7874a58b427f50c1711a5e96c` |
| 读取的源文件版本 | 工作树当前（行号以本次读取为准） |
| 原文 | `papers/motizuki_corpus/text/source_audit/IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt`，PDF SHA256 `9A7EE3C7…A0B9`，物理页 153–159 |

---

## 10. 下一步（一个动作）

**写 `tmp/sheaf/n8/group4/Statements.lean`，只含 §6.1 的 `exists_profile_univ_image`（约 12 行、无 `sorry`）与尖锐形式 `concrete_profile_image_not_determined`（约 20 行、无 `sorry`），编译并记录 `statement_compiles` / `proof_body_checked`。**

理由：它是当前唯一**既能立即闭合、又能改变下游决策**的陈述——把 G4-A 从"接口担忧"变成已证事实，从而授权（并强制）stage 2 用一个见证保持结构替换自由字段 `possibleImage`；在此之前，任何对 `Theorem311Output` 的"source-faithful (i)"报告都应被拒绝。

## 原文核对补充（2026-10-22 root）

对 §2.5 的 Ind3 体积方向冲突，直接读 IUT III 原文：

- p.183 (xi-d)-(xi-f) 明确写 `R≤−|log(Θ)|` 与 `−|log(q)| ∈ R≤−|log(Θ)|`，结论是 **upper bound**，不是等号。
- p.20-21 第1150行 “precisely! compatible ... with the respective log-volumes [cf. Proposition 3.9, (iv)]” 是对 **log-link 与 log-volume 的相容性** 的措辞；同页第227-229行明确说这种相容性最终导致 Cor 3.12 的 **upper bounds — i.e., as opposed to 'precise equalities'**。

因此：

- Lean 中 `Profile.ind3_upper : logVolume c ≤ logVolume (ind3 n c)` 与 Cor 3.12 的最终单向上界一致，**不应**为了 “precisely” 改成等号。
- 但 “precisely compatible” 仍要求记录每个 Kummer 同构与其 log-volume 的相容关系；当前的 `≤` 不足以单独覆盖该句，应另立 child node，保留为 open，而不是把现有字段改成 `=`。
- 原先的 “semantic conflict” 降级为：最终不等式方向已由原文确认；log-link 相容性的精确形式仍需 child 节点。
