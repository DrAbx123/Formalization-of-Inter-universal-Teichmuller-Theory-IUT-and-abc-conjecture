# N8 group5 — IPL / SHE / APT 跨列运送（stage 1）

- Node: `n8-group5-ipl-she-apt`（队列行 `coord/queue.md:91`）
- Stage: **1 only**（本文件即全部交付）。未编辑任何生产文件；本 session **未编译 Lean**。
  `statement_compiles`、`proof_body_checked`、`kernel_closed`、`target_accepted` 四项全部**未运行**。
- 版本锚点: git HEAD `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee`；Lean `v4.32.2`，Mathlib `v4.32.2`（SETUP.md）。
  本包引用的多数 StepXI/Theorem311 文件相对 HEAD 是未跟踪（`??`）或已修改（`M`），
  所以版本锚点取 **working-tree SHA-256**（§6），不取 git 对象。
- 读入（本 session）: `logs/coordination/n8-distilled-05-ipl-she-apt-20261018.md`（219 行，
  SHA-256 `53664EBB…83F3`，全文）；`AGENTS.md`/`SHEAF.md`/`GOAL.md`/`SETUP.md`、
  `coord/STATE.md`/`coord/queue.md`/`coord/FRACTAL-STAGES.md`；
  `logs/coordination/n8-proof-handoff-index-20261018.md`、`n8-route-distilled-20261018.md` §5。
  未做全仓审查；未读文件在 §3 明确标为“未读”。
- 方法：SHEAF 节点局部阶段，consumer first。本文件只固定原文对象/量词、消费者、供体、缺口和一个最小 stage-2 陈述。

## 0. 结论摘要（接手者先读这一节）

1. 三张卡都在，并且各自接进 `StepXIContract` 的 (IPL)/(SHE)/(APT) 槽；但它们住在**三个不同的层**：
   kernel `Core Label Choice`（IPL，`SourcePolyIsoTransportLaws.lean`）、
   `FPrimeStrip`（SHE，`SourceSHETransportLaws.lean`）、
   抽象 `Output`（APT，`APT.lean`）。树里**没有 strip ↔ `Output`/`Choice` 的字典**；
   两个互不引用的模块各自把它记为 root gap（`SourceMultiradialIplLinkWiring.lean:41-47` 与 `:217-224`；
   `SourceColumnCarrierIdentification.lean:84-88` 与 `:701-707`）。因此“同一个运送同时服务 IPL/SHE/APT”
   在现有类型上无法陈述，更无法证明。
2. 三个槽命题在各自的 canonical 点上都可**无条件** inhabit（§4.5 给出三行推导/引用）：IPL 用 `trivialSupply`，
   SHE 的 landing 谓词等价于 `Nonempty Output`，APT 的 reflexive 陈述由算法自身的 `output` 字段给出。
   所以**再写一个 wiring、再补一个 canonical instance、再把卡重命名，都不是数学进展**（SHEAF §4、§6；§4.5）。
3. 原文这一章真正缺的是**内容型**对象：算法在其两个算术全纯结构上的实际执行、许可族的覆盖量词、以及 strip 层与
   `Output` 层的实现映射。本记录不伪造它们；§5 只给出今天就能写、且不影响既有消费者的最小陈述（IPL 族的量词修复）。
4. 一个可执行下一步：§7。

## 1. 原文对象与量词（逐项固定）

论文定位沿用仓库自己的引用（IUT III；plain-text 行号由仓库给出，本 pass 未重读 PDF 原文）：
Remark 3.11.1 (iii) `:9843-9907`（IPL `:9850-9865`、`:9869-9878`；SHE `:9890-9907`），
(iv) `:9923-9946`（APT `:9931-9938`；HIS `:9947-9958`），(v) `:9982-10000`；
Cor 3.12 Step (xi-b) 聚焦抽取 `:1007-1044`（三性质清单 `:1032-1034`），(xi-c) `:1045-1066`。
依据：`APT.lean:19-47`、`APT.lean:131-139`、`SourcePolyIsoTransportLaws.lean:34-66`、
`SourceSHETransportLaws.lean:40-57`。

### 1.1 三个条款的对象与结论

| 条款 | 原文对象 | 结论（不得替换） | 仓库里对应物 |
|---|---|---|---|
| (IPL) (iii) | 输出数据（`n,∘RLGP` 的约化）；输入数据 prime-strip，即 coric/fixed q-pilot prime-strip；算法每步的 F-prime-strip 箭头；每个中间 prime-strip（可同时充当算法输入与 Kummer 输入） | 输出**经算法操作诱导的 full poly-isomorphisms** 与输入 prime-strip 相连；连接同构是“前两个 lower horizontal 的逆 → 第一个 vertical（Kummer）→ upper horizontal（evaluation）”的复合 | `LinkSpan`+`polyIsoRel`（kernel 层，`SourcePolyIsoTransportLaws.lean:190-207,334-336`）；`ReducedIplLink`（`SourceMultiradialIplLinkWiring.lean:95-114`）；`SourceFTimesMuPrimeStripPolyIsomorphism.lean` 的 `iplLink`（未读，仅由 `SourceMultiradialIplLinkWiring.lean:177-182` 转述） |
| (SHE) (iii) | 域侧算术全纯结构（产生 Theta-pilot 的那一个）与余域侧算术全纯结构（产生输入 prime-strip 的那一个）；输出数据的**构造过程本身**与输出数据 | 构造与输出数据“**同时**相对于两个结构 valid/executable/well-defined”；不是“每个输出各挑一个方便表达” | `SourceSimultaneousHolomorphicExpression`（strip 层，`SourceSHETransportLaws.lean:275-288`）；`SourceLocalizationExpression`（1,∘ 层，`SourceArithmeticHolomorphicLanding.lean:243-257`） |
| (APT) (iv) | Theta-link 域/余域的算术全纯结构；构造**算法**及其操作 | 运送“不是把某个集合论区域经某个集合论函数搬过去”，而是“**同时**对两侧结构 valid/executable/well-defined 的构造算法”；(HIS)：theta 函数/值只是隐藏内部结构 | `SourceAlgorithmicParallelTransport`（抽象 `Output` 层，`APT.lean:163-172`）；`SourceProcessionIsomorphism`（`SourceAdjacentColumnProcessionIsomorphism.lean:160-172`） |

### 1.2 量词（哪些全称、哪些存在，不得擅自替换）

1. **许可族，不是选定的一个同构**（chapter C，distilled-05:37-56）。
   设 `P ⊆ Iso(A,B)`，对元素 `x` 的可能像是 `P·x = {φ(x) | φ ∈ P}`。
   结论若要对所有许可像成立，就必须 `∀ φ ∈ P`；若只需某个像，必须保留“是哪个 φ、它如何与其他步骤相容”。
   两个族 `P:A→B`、`Q:B→C` 的复合族 `QP={ψ∘φ}`；**`QP ⊆ R` 不推出 `R = QP`**；
   反向把 `P` 扩成所有同构会扩大可能像并破坏数值估计。
2. **SHE 的“同时”是 `∀` 两个结构**（chapter D，:58-75）。对每个被用到的操作都要问：它需要乘法群、积分幺半群、环加法还是模结构？
   另一列是否真的提供同种结构？跨列比较由哪条已证对应给出？比较是严格相等、同一轨道还是单向包含？
3. **APT 量化在算法步骤上，不在集合映射上**（chapter E/F，:77-111）：代表方形 `T_out(r₀(x,c)) = r₁(T_in x, τ(c))`
   给出 `T_out(U₀(x)) ⊆ U₁(T_in x)`；反向包含需要 `τ` 在所需意义下满射；`T_out` 是同构也不能省掉选择族的覆盖性。
   复合沿代表逐段归纳；若两段用了不相容的中间识别，必须先解决，不能因类型相同默认同一实现。
4. **同一 `T_out` 必须同时服务两种作用**（chapter G，:113-128）。分别选 `T_a`、`T_b` 令两图交换，
   再把二者都叫 transport，是不能复合的。这正是本组 consumer 侧同时需要 D-equivalence、F-times-mu 运送、
   H2 阶段/包含、K1/K2 识别和算法相容性的原因（distilled-05:123-128）。
5. **readback 不是格式转换**（chapter H，:130-146）：`ρ` 定义在 `range(ι)` 上当且仅当 `ι` 单射；
   若 `ι` 已合并代表，只能在商上谈逆。仓库已记录 `RoundtripRealizationSpec` 与 readback 等强（chapter H:145-146；
   文件 `StepXI/SourceRoundtripRealizationSpec.lean`，本 pass 未逐行读，不作依赖）。
6. **数值层不可由抽象字段推出**（chapter K，:180-198）：只保存集合同构/共同载体/交换方形，可以把两个数值分别标成 −1 与 −2。
   因此接入 Step (xi-f) 时必须展示 q-pilot 源值如何读出、输出可能值如何在**同一 degree/log-volume 归一化**下读出、
   构造/逼近为何使该 q 进入允许范围。最后一项是 `SourceXifSignedComparison` 的实际核心，不在本组。

### 1.3 本章给出的、可直接形式化的普通数学（供 stage 2/3 复用）

- 代表→集合的投影与复合（chapter E/F/I）：一组 `Set.image` 级的包含/等式引理。
  **注意**：这些引理是通用集合论内容；只有接上实际 `r₀/r₁/T_in/τ` 才有项目意义（见 §4.6、§5.2）。
- hull 交换（chapter I，:148-165）：`T(hull₀(S)) = hull₁(T(S))` 需 T 双向保持真实 holomorphic 区域族；
  只有单向条件时只得一个方向。该对象属 group6 的 hull consumer，本组不抢。
- 本章**没有**给出实际 SHE/APT 与最后源比较的证明（:213-218）。本记录不把“分解已写出”当作证明。

## 2. 实际消费者（file:line）

### 2.1 三槽合同（最终消费者）

`StepXIContract`（`Corollary312/StepXI/Contract.lean:32-44`）：

| 槽 | 字段 | 位置 | 证据字段 |
|---|---|---|---|
| (IPL) | `ipl : Prop` | `Contract.lean:37` | `ipl_evidence : ipl` @ `:40` |
| (SHE) | `she : Prop` | `Contract.lean:38` | `she_evidence : she` @ `:41` |
| (APT) | `apt : Prop` | `Contract.lean:39` | `apt_evidence : apt` @ `:42` |

数值面 `q_le_target` @ `:43`、`target_le_theta` @ `:44` 是**独立假设**；结论
`Cor312Conclusion` 只经 `le_trans`（`cor312_of_constructed_stepXI` @ `:49-51`）。
即：三张卡不提供这两个数值面（chapter K 的仓库侧落点）。合同义务 `IUT-III.StepXI.contract-construction`
（`:61-78`）在 `:74-76` 列出 `IUT-III.IPL/SHE/APT`。

### 2.2 有限证书链路（真正把卡接进去的消费者）

| 消费者 | 位置 | 现状 |
|---|---|---|
| `FiniteStepXILinkEvidence` 三槽 | `StepXI/FiniteCertificateBridge.lean:17-25`（`ipl/she/apt` @ `:20-22`；证据 @ `:23-25`） | 结构本身只带裸 `Prop` + 证据 |
| `linkEvidenceOfQCMP` | `StepXI/FiniteCertificateLinkEvidenceWiring.lean:61-79` | 三槽全部是**裸端口** `ipl she apt` |
| `linkEvidenceOfQCMPWithIPL` | 同文件 `:169-185` | **唯一接地的槽是 (IPL)**：`ipl := CardIPLExchangeShape L E`，证据 `cardIPLExchangeShape L E`；`she/apt` 仍是裸端口（文件头 `:33-35` 明说） |
| `cor312Conclusion_of_QCMPWithIPL` | 同文件 `:188-205` | 该链路的终点（经 `cor312_of_finite_certificate`） |
| `SourceAPTSlotAssembly.ofHullTargetLink` | `StepXI/APT.lean:368-377` | 收 `ipl she : Prop` 及其证据 + `transport : SourceAPTStatement S A A'` |
| `SourceAPTSlotAssembly.ofAbsoluteDegreeNormalizedSignedLog` | `StepXI/APT.lean:384-403` | 同上（`ipl_evidence`/`she_evidence`/`transport`） |
| `SourceSHELandingSlotAssembly` | `Theorem311/SourceArithmeticHolomorphicLanding.lean:340-347`；证据 `sheSlot_evidence` @ `:355-359` | 把 `she` 定义为 `SourceLocalizationExpressible S Output` |
| `StepXIInput.ipl/she/apt` | `StepXI/ParametricStepXI.lean:35-37`；证据 `:38-40` | 参数化载体，同三槽形状 |

结论：**(SHE)/(APT) 在真实消费者上仍是自由端口**；只有 (IPL) 有一个接地实现，而该实现的输入是 pending 的 supply。§4.5 说明这三个槽为何不能靠 wiring 变得有内容。

### 2.3 待填 supply 卡（实际缺口的登记处）

| 卡 id | 位置 | 内容 |
|---|---|---|
| `IUT-III.source-APT-transport-supply` | `StepXI/APT.lean:456-496` | 实际 `SourceAPTStatement S A A'` 的 inhabitant；路线 (a)(b)(c) 已试并 blocked（`:481-491`） |
| `IUT-III.source-adjacent-column-procession-isomorphism` | `StepXI/SourceAdjacentColumnProcessionIsomorphism.lean:318-355` | 实际相邻列 procession 同构；最小规格 (D)(C)(S)(T)(F) 在 `:326-339` |
| `IUT-III.IPL.algorithmic-provenance` | `Theorem311/Output/SourceMultiradialIplLinkWiring.lean:190-248` | 图示箭头的算法来源与到源分解的桥；三条路线 (a)(b)(c) 在 `:217-237` |
| `IUT-III.source-SHE-landing-evidence` | `Theorem311/SourceArithmeticHolomorphicLanding.lean:556-576` | 实际的 1,∘ 局部化表达证据 |
| `IUT-II.vertical-log-kummer` | `Corollary312/Obligations.lean:19-24`；repo 对应 `SourceK1K2Construction.lean:666-689`（未读，按 `APT.lean:93-95` 转述） | K1/K2 边界 |

## 3. 现有 Lean 供体（file:line）

以下全部为本 session 实际读到的声明（除标注“未读”者）。

### 3.1 IPL 侧

| 对象 | 声明 | 位置 |
|---|---|---|
| kernel core | `Core Label Choice`（`ind1/ind2/ind3`、`ind1_inverse`、`*_level`） | `Theorem311/MultiradialOutputKernel.lean:12-31` |
| 链接壳 | `LinkSpan`（carrier `mid`、`left/right`、`act1/act2`、`left_act1` 等） | `Theorem311/SourcePolyIsoTransportLaws.lean:190-207` |
| 壳关系 | `LinkSpan.Rel`；`rel_ind1_iff`；`rel_ind2_iff`；`LinkSpan.refl` | `:215-216`；`:220-230`；`:233-243`；`:246-263` |
| 核消去 | `ind1_inv_cancel`；`ind2_inv_cancel` | `:166-171`；`:174-180` |
| 路线 | `routeApply`（`List Label` 的 `act1` fold，仅 (Ind1) 步） | `:272-274` |
| O4 因子化 | `KummerEvaluationFactor`（`lower/upper/kummer` + 两条因子化律） | `:283-289` |
| supply | `CardIPLTransportSupply`：O1 `XMu/xmuGroup/xmuAct`（`:315-319`）、O2 `polyIso`+两作用律（`:320-322`）、O3 `provenance`+等式（`:323-324`）、O4 `kummerEval`（`:325`） | `:313-325` |
| 运送关系 | `polyIsoRel`；`routeRel`；`polyIsoRel_eq_routeRel` | `:334-336`；`:341-343`；`:347-354` |
| 交换律 | `polyIsoRel_act1/act2`；`polyIsoRel_ind1_iff`；`polyIsoRel_ind2_iff`；`polyIsoRel_eq_rel_of_polyIso_refl` | `:358-374`；`:380-393`；`:397-410`；`:416-425` |
| 消费者形状 | `CardIPLExchangeShape`（6 个字段）；`cardIPLExchangeShape` | `:448-468`；`:475-483` |
| 路线代数 | `LinkSpan.act1_inv_cancel`；`routeApply_eq_act1_sum`；`routeApply_append`；`routeApply_eq_iff_act1_sum`；`routeRel_iff_act1_sum` | `SourcePolyIsoTransportDischarge.lean:82-86,99-113,117-122,140-147,151-155` |
| canonical supply | `trivialSupply`；`trivialSupply_polyIsoRel_eq_rel`；`trivialSupply_exchangeShape` | `:166-183`；`:196-199`；`:209-212` |
| 算法来源片段 | `ReducedIplLink`（`target_eq`/`intermediate_compose`/`automorphism_compatible`）；`reducedIplLink_holds` | `Theorem311/Output/SourceMultiradialIplLinkWiring.lean:95-114`；`:118-129` |

### 3.2 SHE 侧

| 对象 | 声明 | 位置 |
|---|---|---|
| strip | `FPrimeStrip V`（`Pi/G/Mon/proj/action/degree`）；`FPrimeStripEquiv` | `IUTI/HodgeTheater/PrimeStripCore.lean:117-121`；`:166-177` |
| strip 自同构群胚 | `FPrimeStripEquiv.refl/symm/trans` | `PrimeStripCore.lean:188-194,196-217,219-240` |
| strip 链接 | `FPrimeStripLink`（`index/mapPi/mapG/mapMon` + 三条相容律）；`trans` | `IUTII/Frobenioid/PrimeStripsConstruction.lean:46-58`；`:75-113` |
| 共轭引擎 | `FPrimeStripLink.conjugate`；`conjugate_index`/`_mapPi/_mapG/_mapMon`；`conjugate_trans_mapPi/G/Mon_apply` | `StepXI/SourceSHETransportLaws.lean:137-186,188-208,214-257` |
| SHE 方形 | `SourceSimultaneousHolomorphicExpression`（`domainExpression`/`codomainExpression`/`simultaneous`） | `:275-288` |
| 构造/交换/运送 | `ofCommutingLegs`；`swap`；`transport`（沿四个 `FPrimeStripEquiv` 共轭） | `:299-303`；`:313-317`；`:327-336` |
| 分量 | `simultaneous_index`；`simultaneous_mapPi/G/Mon_apply` | `:339-342`；`:347-377` |
| 槽谓词 | `sheStatement`；`sheSlot_evidence` | `:383-389`；`:399-403` |
| 等价的 link 影子 | `FPrimeStripEquiv.toLink` + 4 条点态律 | `StepXI/SourceSHETransportObligations.lean:98-105,107-120` |
| 逐腿升级 | `SourceEvaluationLegUpgrade`；`SourceKummerLegUpgrade`；`SourceReverseKummerLegUpgrade`；`SourceSHESquareSupply` | `:130-135,140-145,151-156,165-181` |
| toLink 共轭 | `toLink_conjugate`；`toLink_conjugate_symm` | `StepXI/SourceSHETransportConjugation.lean:71-78,79-86` |
| 1,∘ 结构 | `SourceOneColumnArithmeticHolomorphicStructure`；`SourceArithmeticVectorBundle`；`SourceLocalizationExpression` | `Theorem311/SourceArithmeticHolomorphicLanding.lean:155-167,210-215,243-257` |
| landing 谓词 | `SourceLocalizationExpressible`；`sourceLocalizationExpressible_iff`；`sourceLocalizationExpressible_of_equiv` | `:292-294`；`:297-300`；`:305-316` |

### 3.3 APT 侧

| 对象 | 声明 | 位置 |
|---|---|---|
| 约化展示 | `SourceTheorem311MultiradialPresentation`（`output`、`processionAction`） | `Theorem311/SourceMultiradialTwoActionEquivalence.lean:149-156` |
| 约化算法 | `SourceTheorem311MultiradialAlgorithm`（`presentation`、`ind2Action`、`ind1_ind2_commute`） | `:199-211` |
| 两作用商 | `twoActionRel`；`TwoActionGeneratedRel`；`twoActionSetoid`；`twoActionQuotient` | `:281-283,286-293,297-300,304-306` |
| 两作用等价 | `SourceTheorem311TwoActionEquivalence`（`ind1GroupEquiv`/`outputEquiv`/`preserves_ind1`/`preserves_ind2`）；`quotientEquiv` | `:318-331`；`:412-422` |
| APT 记录 | `SourceAlgorithmicParallelTransport`（`comparison`、`landing`） | `StepXI/APT.lean:163-172` |
| 门 | `quotientEquiv`；`twoActionGeneratedRel_iff`；`nonempty_iff`；`reflexive`；`nonempty_iff_self` | `:183-192`；`:197-205`；`:210-215`；`:219-223`；`:229-233` |
| 复合 | `SourceAlgorithmicParallelTransport.trans` | `:261-288` |
| 槽命题 | `SourceAPTStatement`；`SourceAPTSlotAssembly`；`aptSlot_evidence` | `:308-311`；`:332-341`；`:353-355` |
| procession | `SourceProcessionIsomorphism`（`levelEquiv`/`component`/`link_naturality`）；`refl`/`comp`；route-1 构造 | `StepXI/SourceAdjacentColumnProcessionIsomorphism.lean:160-172`；`:190-236`；`:243-255` |
| 列索引 | `OriginalInput`；`fPrimeStripAt`；`fLinkAt`；`fLinkAt_trans` | `Theorem311/SourceOriginalInput.lean:41-46`；`SourceH1H2Construction.lean:52,165,232` |
| 合同/义务 | `StepXIContract`；`IUT-III.IPL/SHE/APT` | `StepXI/Contract.lean:32-44`；`Corollary312/Obligations.lean:5-24` |

未读（本 pass）：`SourceFTimesMuPrimeStripPolyIsomorphism.lean`、`SourceRoundtripRealizationSpec.lean`、
`SourceK1K2Construction.lean` 的 `:666-689` 段、`SourceSHETransportConjugation.lean` 的 `:88-466`
（只读了文件头与 `toLink_conjugate*`）。它们不作为本包已核依赖。

## 4. 精确缺口

### 4.1 G0（root）：strip 层与 `Output`/`Choice` 层之间没有字典

证据（两处独立记录，且互不引用）：

- `SourceMultiradialIplLinkWiring.lean:41-47`：“the reduced interface has no prime-strip object attached to the algorithm output
  (no correspondence between the carrier choice type and `FPrimeStrip V` is modeled anywhere in the tree — the same reason W.3 is unexpressible)”；
  同一文件 `:217-224` 的路线 (b)：经 F-prime-strip 层（`FPrimeStripEquiv`）也被 blocked，理由同上。
- `SourceColumnCarrierIdentification.lean:84-88`：“the strip-level Kummer/evaluation roundtrip interfaces are not type-composable with it
  (no strip-to-`Choice` dictionary; that is the forwarded FPrimeStrip wiring request)”；`:701-707` 重复同一诊断。

后果：IPL 的 kernel 关系、SHE 的 strip 方形、APT 的输出载运三者**无法类型复合**；chapter G 的“同一 `T_out` 服务两种作用”
在现有类型上无法陈述。这不是量词细节，是本组的第一缺口。

### 4.2 G1：IPL 卡把“许可族”塌缩成一个选定同构，且 O4 没有关系层定律

- `CardIPLTransportSupply.polyIso : L.mid ≃ L.mid`（`SourcePolyIsoTransportLaws.lean:320`）是**单个**等价；
  `polyIsoRel`（`:334-336`）用它读第二腿。这正是 chapter C（distilled-05:37-56）点名的错误形态：
  结论若要对所有许可像成立就必须 `∀ φ ∈ P`；`QP ⊆ R` 也不等于 `R = QP`。
  该模块自己称 O2 为“full poly-isomorphism **proxy**”（`:301-303`）。
- O3 的路线被限制为纯 (Ind1) 步 `routeApply`（`:272-274`，文件自述“lite stand-in restricted to (Ind1)-steps”），
  且 `routeApply_eq_act1_sum`（`SourcePolyIsoTransportDischarge.lean:99-113`）证明整条路线就是**一次** `act1 sum` 平移。
- 模块自述缺口：`:126-127`“No relation-level transport law for the O4 Kummer step is stated … adding one would strengthen
  the obligation list (left to a future card)”；O1 的 times-mu 载体没有源对象（`:296-303`）。
- `ReducedIplLink`（`SourceMultiradialIplLinkWiring.lean:95-114`）只覆盖“输出是路线的像 + 中间 strip 双向角色 +
  与 procession 自同构相容”这三条，且**明确不含** poly-isomorphism 面（`:92-94`）。

### 4.3 G2：SHE 的两套槽谓词互不相连，且 landing 谓词可证地弱

- 两套候选 (SHE) 槽命题：`sheStatement E := E.domainExpression = E.codomainExpression`
  （`SourceSHETransportLaws.lean:383-385`）与 `SourceLocalizationExpressible S Output`
  （`SourceArithmeticHolomorphicLanding.lean:292-294`）。模块自述**没有** cross-wiring（`SourceSHETransportLaws.lean:94-99`、
  `:396-398`：“no cross-wiring lemma from this square to that predicate is provided”）。
- landing 谓词弱：`sourceLocalizationExpressible_iff : SourceLocalizationExpressible S Output ↔ Nonempty Output`
  （`SourceArithmeticHolomorphicLanding.lean:297-300`，由 `SourceLocalizationExpression.nonempty_iff` `:275-279`）。
  即“能在 1,∘ 局部化中表达”被约化成“输出类型非空”。
- SHE 方形的两条表达式是**自由字段**（R2，`SourceSHETransportLaws.lean:65-68`），内部操作不建模；
  Kummer 腿是不透明链接（R3 `:70`）；未绑定 1,circ 列（R4 `:71-73`）。
- 尚缺（模块自述 `:85-99`）：实际源 Kummer 箭头及其 weight/local-unit（S2）、1,circ 绑定（S3）、hull 表达（S4）、
  times-mu/full-poly 升级（G1）；这些由 `SourceSHETransportObligations.lean:130-181` 的逐腿升级记录**要求**而不是推出。

### 4.4 G3：APT 记录没有列、没有算法，且自证“只等于两个字段”

- **列索引是幻影**：`SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output`（`SourceMultiradialTwoActionEquivalence.lean:199-211`）
  的字段只用到 `G₁`/`G₂`/`Output`；`I` 与 `n` 仅出现在类型下标里，
  其展示结构 `SourceTheorem311MultiradialPresentation`（`:149-156`）也只有 `output` 与 `processionAction`。
  即：记录的字段数据不依赖 `I`/`n`，同一份字段可原样重建在列 `n+1`；
  取 `outputEquiv := Equiv.refl` 与同一组作用，两作用等价与 APT 运送都自动成立。跨列陈述因此**不含算术内容**。
- **记录不自带内容**：`nonempty_iff`（`StepXI/APT.lean:210-215`）证明
  `Nonempty (SourceAlgorithmicParallelTransport S A A') ↔ Nonempty (TwoActionEquivalence A A') ∧ SourceLocalizationExpressible S Output₂`；
  记录“adds no further field”。
- **无相邻列**：R8（`APT.lean:83-86`）明确“adjacency is not enforced as a field, and no adjacent-column procession isomorphism is constructed”；
  `SourceAdjacentColumnProcessionIsomorphism.lean:65-70` 同样只冻结了 level equivalence + 组件，未建模自动同构作用与算法函子性。
- **无算法实现**：R2/R3（`APT.lean:56-65`）说明“simultaneously valid/executable/well-defined”被约化成“一个记录 + 两作用等价”，
  操作的 scheme-theoretic 语义不建模。
- supply 卡 `sourceAPTTransportSupply`（`:456-496`）自述三条路线 (a)(b)(c) 全部 blocked，PARKED。

### 4.5 三槽在 canonical 点都可无条件 inhabit（因此 wiring 不是进展）

1. **(IPL)**：对任意壳 `L`，`trivialSupply L`（`SourcePolyIsoTransportDischarge.lean:166-183`）
   给出 `CardIPLExchangeShape L (trivialSupply L)`（`trivialSupply_exchangeShape` @ `:209-212`）。
   于是 `linkEvidenceOfQCMPWithIPL` 的 (IPL) 证据可取 `E := trivialSupply L`。
2. **(SHE)**：`SourceLocalizationExpressible S Output` 由 `Nonempty Output` 给出（`:297-300`）；
   消费者自选 `Output`（例如 `Unit`）即免费。若改用 `sheStatement`，则方形自身的 `simultaneous` 字段
   直接就是证据（`SourceSHETransportObligations.lean:191-193`）。
3. **(APT)**：对任意 `S`、`A`，`SourceAPTStatement S A A` 可证：
   `A.presentation.output : Output₁` ⟹ `Nonempty Output₁` ⟹ `SourceLocalizationExpressible S Output₁`
   （`:297-300`）⟹ `Nonempty (SourceAlgorithmicParallelTransport S A A)`（`APT.lean:229-233`）
   ⟹ `SourceAPTStatement S A A`（`:308-311`）。**注意**：这是“同一实例到自身”；不同实例（不同 `Output`）仍需
   输出等价，而该等价不是免费的。本推导由所引已证定理逐步给出，本 pass 未编译。

结论：**三个槽的 Prop 都可在 canonical/gate 点被 inhabit**；任何 wiring 重构、canonical 实例或槽谓词改名都不减少缺口。
SHEAF §4/§6 的“不得把可 inhabit 当成源忠实性”在这里有精确落点。

### 4.6 G4：需求侧（chapter E 的代表方形）在树里没有对象

`T_out(r₀(x,c)) = r₁(T_in x, τ(c))`（distilled-05:79-94）需要四个对象：输入运送 `T_in`、输出运送 `T_out`、
代表映射 `r₀/r₁`、选择运送 `τ`。树里**一个都没有**：`SourceAlgorithmicParallelTransport` 只有
`comparison` 与 `landing`（`APT.lean:163-172`）；`SourceTheorem311MultiradialAlgorithm` 只有作用（`:199-211`）；
没有 `r`/`U`/`τ`。把它写成“带四个自由字段的 supply”正是 chapter E 明令禁止的形式（:94），
且没有真实消费者。

### 4.7 G5：消费侧只接了 IPL

见 §2.2：`linkEvidenceOfQCMPWithIPL`（`FiniteCertificateLinkEvidenceWiring.lean:169-185`）只把 (IPL) 接地；
(SHE)/(APT) 是裸端口（文件头 `:33-35` 明说）。`SourceSHESquareSupply` / `SourceAPTStatement` / landing 装配记录
都存在，但**没有任何真实消费者**把它们接进 `FiniteStepXILinkEvidence` 或 `StepXIContract` 三者同时。
这一项可以补（代价一个 def），但它不产生内容（§4.5），因此不作为本组的 stage-2 主陈述。

## 5. 最小 stage-2 陈述（精确类型）

### 5.1 推荐陈述：IPL 许可族的关系层换向律

**为什么是它**：chapter C 是本组唯一能在现有类型上写成**非平凡定理**的原文内容（IPL 的量词结构），
且它是当前 (IPL) 槽唯一接地实现的直接上游；其余缺口（G0/G2/G3/G4）都需要新的源对象或新消费者，
不能在一个 stage-2 文件里诚实完成。

**精确类型**（建议文件 `tmp/sheaf/n8/Group5Statements.lean`，独立 namespace，SHEAF §4）：

```lean
import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportLaws

namespace LeanFormal.IUT.Tmp.N8Group5

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.Theorem311Source.PolyIsoTransport

universe u v w

/-- (IPL) 关系的许可族形态：`P` 是算法操作诱导的 full poly-isomorphism 族
（Remark 3.11.1 (iii) 的 “via full poly-isomorphisms”）在 kernel 壳上的约化影子。
与 `polyIsoRel` 的差别只在量词：`∃ φ ∈ P`，不是选定的一个 `E.polyIso`。 -/
def familyRel {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid)) (a b : Choice) : Prop :=
  ∃ m : L.mid, L.left m = a ∧ ∃ φ ∈ P, L.right (φ m) = b

/-- **stage-2 主陈述**：族关系对 (Ind1) 的换向律。
`hP` 是 chapter C 的覆盖条件：族中每个成员都与 (Ind1) 作用交换
（“induced by operations in the algorithm”在作用层的约化形式）。
它不是 `polyIsoRel_ind1_iff` 的推论：单个代表不满足 `hP` 时，换向律不成立。 -/
theorem familyRel_ind1_iff {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid))
    (hP : ∀ φ ∈ P, ∀ (g : Label) (m : L.mid), φ (L.act1 g m) = L.act1 g (φ m))
    (a b : Choice) (g : Label) :
    familyRel L P (core1.ind1 g a) b ↔ familyRel L P a (core2.ind1 (-g) b)

/-- (Ind2) 版本；假设只要求与 `act2` 交换。 -/
theorem familyRel_ind2_iff {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid))
    (hP : ∀ φ ∈ P, ∀ (g : Label) (m : L.mid), φ (L.act2 g m) = L.act2 g (φ m))
    (a b : Choice) (g : Label) :
    familyRel L P (core1.ind2 g a) b ↔ familyRel L P a (core2.ind2 (-g) b)

/-- 与既有卡的一致性：任一 supply 的 `polyIso` 属于族 `P` 时，
`polyIsoRel` 蕴含 `familyRel`（chapter C 的单向 `QP ⊆ R` 形式；
**不**断言 `R = QP`）。既有消费者因此不受影响。 -/
theorem polyIsoRel_le_familyRel {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (E : CardIPLTransportSupply L) (P : Set (L.mid ≃ L.mid))
    (h : E.polyIso ∈ P) (a b : Choice) :
    polyIsoRel L E a b → familyRel L P a b

end LeanFormal.IUT.Tmp.N8Group5
```

**证明路线**（预计 35–45 行，两条交换律同构）：
正向取见证 `(m, φ)`，用 `L.act1 (-g) m` 作新见证：`L.left_act1`（`SourcePolyIsoTransportLaws.lean:201`）+
`core1.ind1_inverse`（`MultiradialOutputKernel.lean:20`）给左腿，`hP` + `L.right_act1`（`:202`）给右腿；
反向取 `L.act1 g m`，用 `ind1_inv_cancel`（`:166-171`）。与 `polyIsoRel_ind1_iff`（`:380-393`）逐行平行，
只多一次 `hP` 重写。(Ind2) 版本把 `act1` 换成 `act2`、`ind1` 换成 `ind2`。

**它减少什么缺口**：(IPL) 关系层恢复 chapter C 的量词（`∃ φ ∈ P`），并把“单个选定代表”降为特例
（`P = {E.polyIso}`）；同时给出 chapter C 明确要求的方向性（仅 `QP ⊆ R`）。
**它不减少什么**：G0（strip↔Output 字典）、G3（列幻影）、G4（代表方形）、G5（SHE/APT 未接地）都不动；
也不能把 (IPL) 槽变成“有内容”（§4.5 依旧成立）。

**验收顺序**：(1) 只编译陈述，记录 `statement_compiles`（SETUP.md 的 `build_guard.ps1` 命令，具名 `sorry` 允许）；
(2) 证明体 `proof_body_checked`；(3) 再谈公理探针。不要在 stage-2 文件里导入 `Project`。

### 5.2 被拒绝的替代（避免接手者重复）

1. **加一个 `linkEvidenceOfQCMPWithSHEAPT`**：把三槽都接地的纯 wiring。可做、便宜，但按 §4.5 不产生内容，
   且不是本组 stage-2 的数学陈述。若维护者需要“三槽统一接地”，它应作为独立集成小包，不与本陈述混在一起。
2. **新 record 带 `T_in/T_out/r₀/r₁/τ` 自由字段**：chapter E 明令禁止把未知 τ/满射性/交换式放成待填字段再宣称 APT 已证
   （distilled-05:94）；且无真实消费者。
3. **新 slot 谓词并把三卡合取**：合取包装（SHEAF §4、GOAL.md “不作为主线进度”）。
4. **把 `SourceAPTStatement` 直接改弱/改强**：改对象或缩量词，需用户指令与消费者重审。

### 5.3 紧随其后的陈述（不在本包）

1. chapter C 的复合覆盖：`familyRel L (QP) ⊆ familyRel` 与“decomposition of every `R` arrow”作为**假设**而非字段；
2. `FPrimeStripEquiv.toLink` 的函子性（`toLink_trans`/`toLink_refl`，树里**不存在**：
   `SourceSHETransportObligations.lean:98-105` 只有 `toLink` 与点态律，`SourceSHETransportConjugation.lean:71-86` 只有共轭律）——
   它是 chapter F 的“两个方形复合”在 strip 层的必要引理；
3. G5 的三槽接地（若维护者要）。

## 6. 版本与证据（working-tree SHA-256，2026-10-22）

| 文件 | 行数 | SHA-256 |
|---|---|---|
| `logs/coordination/n8-distilled-05-ipl-she-apt-20261018.md` | 219 | `53664EBBDA97E112C59373FCD78A336C4AB0278D324759E6238FEB6CAEC783F3` |
| `StepXI/APT.lean` | 501 | `EDD0AE7EC596275796092AE127A79D284A57B7E5407B51F2E8D40FBBC123D1E5` |
| `StepXI/SourceSHETransportLaws.lean` | 447 | `7032FD6A893DBF822337EA9F4D3FA2224FA12B87BEABC34F062499B1AE970622` |
| `Theorem311/SourcePolyIsoTransportLaws.lean` | 521 | `E064E76534E9542A6F66D0E077D01B0C7ADCB3F2ECFBDA8D1726FC9035EAEE53` |
| `Theorem311/SourcePolyIsoTransportDischarge.lean` | 248 | `3492E1CF68C959DCB8151C8AE61425A7E05B762EFE8CCAD99FDC6A8912D8AFFF` |
| `Theorem311/SourceMultiradialTwoActionEquivalence.lean` | 613 | `DE0B8E1C466690BFE15981949D815AA8E1A6938A9BA5C44B315AD59AFB040553` |
| `Theorem311/SourceArithmeticHolomorphicLanding.lean` | 582 | `01F055B25DDE3EA142684A4B43CFEE21F649003C99E452AE76D037876C1E1244` |
| `Theorem311/MultiradialOutputKernel.lean` | 177 | `5538016EDCAB4714165076E586BFF348C2E769B7A14D9763F6B49BEE5062D9AC` |
| `Theorem311/Output/SourceMultiradialIplLinkWiring.lean` | 251 | `CC7D5775EE072B9C0CDE34D7CB0FF43B760E729AD17738FD4B5F24CF70959560` |
| `StepXI/SourceAdjacentColumnProcessionIsomorphism.lean` | 360 | `D694A6FEA45524A06EA1BC6EC2AA7CEB5C7D4F4ADC379D8AAD3C976CAA72604F` |
| `StepXI/SourceSHETransportObligations.lean` | 411 | `D7C21E86EDB6D87395CD392B8A7FCC4EF796E48D189465F6C57D7590CD021D82` |
| `StepXI/SourceSHETransportConjugation.lean` | 466 | `4ADD6AC92E0BD52162A1F3C619FD52964D9D6593A32FC7CAC70768E040195723` |
| `StepXI/SourceColumnCarrierIdentification.lean` | 880 | `A738DF902E516B39983C31775FB5CBDEEFD699762D7273EB800E1EEAF2A93196` |
| `StepXI/FiniteCertificateBridge.lean` | 78 | `4C28F1AEC0AC4034FF8464248DDA1CC343803398867AAB2FDADA3AB8B1A805C3` |
| `StepXI/FiniteCertificateLinkEvidenceWiring.lean` | 598 | `B51EE88C9E383756FCAD431FFA044234094B051D4073CFC97797744FFAF8E435` |
| `StepXI/ParametricStepXI.lean` | 382 | `36CFD74924915ED6CB737ACE80068F67CE12698D03CDB30D2DE90C5C69925D98` |
| `StepXI/Contract.lean` | 81 | `1E59E3B72396CE9CF11E6263AA29DD434F949E64B15B77C5B52A8E16CEE40070` |
| `Corollary312/Obligations.lean` | 27 | `CA1D7F8352432B27CD9C7275EC2146EA1DAC015F4B6122B2E65FE1EB3309613F` |
| `StepXI/IPL.lean` | 4 | `B785E00F3FA38EC3B778A34BEE5D10903B3D7F1C26CD8135B9BD235DDFF3BBF5`（只有 `import Obligations`，无 IPL 内容） |
| `StepXI/SHE.lean` | 4 | `CB65F66A1A29C0F649A266AFA129764EA5096D13C8DBFF87164C73C86C088606`（同上，无 SHE 内容） |
| `IUTI/HodgeTheater/PrimeStripCore.lean` | 264 | `B67C2ABFC38C6317377B89F484B6F772631E99D73026A23D8AE2C8E6E14D58DA` |
| `IUTII/Frobenioid/PrimeStripsConstruction.lean` | 414 | `25BE0A67DC9C39C17A69A2C557CE842D96C3A00FB5D1A7AD4C7C49060A97E2C7` |
| `Theorem311/SourceOriginalInput.lean` | 1664 | `11C288D385682760B56890B24C57F1738A771DC6A75E2543EFFD67D9FFAFA795` |

未运行：Lean 编译、`lean_auto.py`、`build_guard.ps1`、comparator、公理探针、全 Project 构建。
`IPL.lean` 与 `SHE.lean` 是空壳（各自 4 行，只 import `Obligations`），
所以“当前 IPL/SHE 界面”实际在这些模块之外（`SourcePolyIsoTransportLaws.lean` /
`SourceSHETransport{Laws,Obligations,Conjugation}.lean`）。

## 7. 一个下一步

写 `tmp/sheaf/n8/Group5Statements.lean`（§5.1 的三个声明，独立 namespace，具名 `sorry` 仅用于两条交换律的
证明体），用 SETUP.md 的 `build_guard.ps1` 命令记录 `statement_compiles`；然后优先补
`FPrimeStripEquiv.toLink_trans`（§5.3 第 2 条，chapter F 的复合前提，树里不存在）。若维护者选择先做 (§4.7) 的三槽接地，
应另开集成小包，不与本陈述共用文件。
