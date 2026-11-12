# A490 NumericalWall 逐字段映射与缺口（只读审计）

来源: 已移植 LANA 树 `tmp/sheaf/lana/iut/Iut/...`（源仓库对照 `tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut/...`，内容相同、imports 已改写）。
状态 caveat: Wall 与 WallEquiv 共 19 个 .lean 文件全部在 watchdog 队列（queued=19, olean=0），即下述 file:decl 目前是**源码级**引用，尚未在 4.32.2 上编译验证；LANA 原仓库为 4.32.0。本文件只读，未改任何文件/队列/watchdog。

## 1. 目标公式（精确形式）

- `Wall.NumericalWall D`（`tmp/sheaf/lana/iut/Iut/Wall/Checks.lean:56`）:
  `exists U : Region D, IsAdelic D U  and  InHullOfImage D U  and  (qVal D.bpsDegrees).eta (logVol D U) = etaQ D`
- `Wall.numericalWall_iff`（Checks.lean:61）: `NumericalWall D <-> Corollary312Variant (concreteVariantData D)`
- `Wall.numericalWall_iff_rss`（Checks.lean:69）: `NumericalWall D <-> exists (U : Region D) (hU : IsAdelic D U), InHullOfImage D U and Rss.mk D U hU = (rssEquiv D).symm (concreteVariantData D).qPilot.lhs`
- `Wall.Wall D A`（`Iut/Wall/EtaAlg.lean:173`）: 对每个 Theta-link，存在 choice iota 与 Ind3 的 S，使 etaAnab iota S = etaQ D。`Wall` 是假设，不证明。
- `Corollary312Variant X`（`Iut/Cor312/Statement.lean:89`）= `X.qPilot.lhs <= X.rhsData.rhs`；`corollary312Variant_iff`（Statement.lean:95）= Iff.rfl。即 `-|log(q)| <= -|log(Theta)|`（docstring L80 明确）。
- `concreteVariantData`（`Iut/Concrete/ThetaRegion.lean:359`）= `{data := D, qPilot := D.qPilot, rhsData := D.rhsData}`；`qPilot`（ThetaRegion:348，权重 f_w/[F:Q]）；`rhsData`（ThetaRegion:335，源自 `rhsDataOn` 316-336）；`lhs_eq_neg_degNorm_qDivisor`（`Iut/Arakelov/QPilot.lean:110`）。

## 2. RHS 逐字段映射（字段 -> 定义/构造 -> 现有引理清单 file:decl）

### 2.1 字段 U : Region D（容器区域）

| 角色 | file:decl | 说明 |
|---|---|---|
| 类型/容器 | Iut/Wall/Rss.lean:311 VC := LocalTheory.container D.placeSect (nC D) | concrete large volume container；`nC D = (ell-1)/2`（Rss:303），`nC_pos`（Rss:305） |
| 区域类型 | Iut/Wall/Rss.lean:314 Region := forall i : Fin (VC D).proc.length, (VC D).AdmissibleRegion i | capsule-indexed admissible regions |
| 基本构造 | Iut/Wall/Rss.lean:469 integralRegion；Iut/Wall/Rss.lean:390 archScale；Iut/Wall/Rss.lean:186 archRegion；Iut/Wall/Rss.lean:328 hullOf；Iut/Wall/Rss.lean:333 thetaImage | integral structure / archimedean rescaling / hull / theta-pilot image region |
| q-pilot 区域 | Iut/Wall/QPilotRegion.lean:314 qRegion；:95 powRegion；:113 powAt；:136 pow；:316 isAdelic_qRegion；:321 logVol_qRegion；:331 qRegion_first | q-region {q_v O_v} 构造，log-vol = qPilot.lhs |
| LGP 区域 | Iut/Wall/IdentifiedCopies.lean:169 lgp；:146 lgpRegion；:152 lgpAt；:183 isAdelic_lgp；:281 logVol_lgp；:444 logVol_lgp_integral | identified-copies 模型 LGP·S，log-vol(LGP·O) = -s·|log q| |
| log-shell 容器 | Iut/Wall/Ind3.lean:123 vcI；:125 isAdelic_vcI；:129 isAdelic_hullOf_vcI；:133 vcI_le_hullOf | VC(I) 与 hull(VC(I)) |
| 容器/包层 | Iut/Cor312/Container.lean: LargeVolumeContainerData/AdmissibleRegion/integralAdmissible；Iut/Cor312/ContainerHull.lean: IsAdmissible/hullAdmissible/hullFamily；Iut/Cor312/HolomorphicHull.lean: HullSystem/hull_mem_hullRegions/subset_hull/le_hullAdmissible/hullFamily；Iut/Cor312/PacketPresentation.lean: DirectSumPresentation/integralRegion/productRegion；Iut/Cor312/LogVolume.lean: LogVolumeData/packetVol/globalVol/processionVol | 底层容器/包/全纯 hull/log-volume 数据 |
| **存在性引理（关键）** | Iut/Wall/Rss.lean:403 exists_adelic_iff；Iut/Wall/EtaAlg.lean:189 exists_out_of_wall | exists_adelic_iff x : (exists U, IsAdelic and InHullOfImage and logVol = x) <-> x <= rhs；exists_out_of_wall : Wall D A -> exists U (IsAdelic and InHullOfImage and logVol = qPilot.lhs) |

### 2.2 字段 hU : IsAdelic D U

| 角色 | file:decl | 说明 |
|---|---|---|
| 定义 | Iut/Wall/Rss.lean:319 IsAdelic U := forall i, (LocalTheory.hull D.placeSect (nC D)).IsAdmissible (U i) | 每个 capsule 区域是 hull-admissible：乘积 of 非空/相对紧/可测/正有限 Haar |
| 保持性引理 | Rss.lean:346 thetaImage_isAdmissible；:365 isAdmissible_hullOf；:393 isAdelic_archScale；:471 isAdelic_integralRegion；:91 smul_mem_admissible_infinite | hull/archScale/integral/arch smul 均保持 adelic |
| 其它区域实例 | Iut/Wall/Ind3.lean:125 isAdelic_vcI；:129 isAdelic_hullOf_vcI；Iut/Wall/QPilotRegion.lean:155 isAdelic_pow；:316 isAdelic_qRegion；Iut/Wall/IdentifiedCopies.lean:183 isAdelic_lgp；Iut/Wall/Scaling.lean:251 isAdelic_act；:270 isAdelic_act_iff | q/theta/LGP/act 实例 |
| hull 层引理 | Iut/Cor312/ContainerHull.lean: IsAdmissible/hullAdmissible/hullAdmissible_mono/hullAdmissible_idem；Iut/Cor312/HolomorphicHull.lean: IsLeastHullRegion/IsLeastHullRegion.unique/hull_le/hull_eq_self/hull_iIdem/hull_mono/subset_hull | 底层 hull 封闭性/单调性 |
| 来源 | Iut/Wall/EtaAlg.lean:96 EtaAlg.realisation (T3) | 每个 EtaAlg 输出自动 IsAdelic 且 InHullOfImage —— 一旦有算法，hU/hI 由 T3 给出 |

### 2.3 字段 InHullOfImage D U

| 角色 | file:decl | 说明 |
|---|---|---|
| 定义 | Rss.lean:338 InHullOfImage U := exists l : forall i, Lab (nC D) i, forall i, U i <= hullOf (thetaImage D l) i | U 落在单个 (Ind1)-image 的 hull 内 |
| 单 image 版本 | Rss.lean:343 InImage U := exists l, forall i, U i <= thetaImage D l i；:350 InImage.inHullOfImage | image ⊆ hull 的单侧弱化 |
| hull 包含 | Rss.lean:346 thetaImage_isAdmissible；:360 rhs_eq_logVol_image；Concrete/Ind1Invariance.lean:700 rhsDataOn_singleton | theta-image hull 的 admissibility 与 log-vol = rhs（Ind1 不变性） |
| LGP image 引理 | Iut/Wall/IdentifiedCopies.lean:204 lgp_le_thetaImage；:222 inImage_lgp；:229 inHullOfImage_lgp | LGP·S ⊆ theta image，从而 LGP·S 在 hull 内 |
| T3 来源 | EtaAlg.lean:123-125 realisation : IsAdelic (out i S) and InHullOfImage (out i S) | 接口字段；给定算法即得 hU/hI |
| **存在性引理（关键）** | Rss.lean:403 exists_adelic_iff | 给定 x <= rhs，直接产出 U 同时满足 IsAdelic、InHullOfImage 且 logVol = x |

### 2.4 字段 Rss 等式 `Rss.mk D U hU = (rssEquiv D).symm (qPilot.lhs)`

| 角色 | file:decl | 说明 |
|---|---|---|
| R_ss 定义 | Rss.lean:446 Rss := Quotient (logVol 等值 Setoid)；:453 Rss.logVol；:450 Rss.mk | adelic 区域模相等 log-volume |
| 类运算 | Rss.lean:456 Rss.logVol_mk；:460 Rss.mk_eq_mk_iff；:464 Rss.logVol_injective | mk 相等 <-> logVol 相等；logVol 单射 |
| 实线同构 | Rss.lean:486 rssEquiv : Rss D =~ Real（logVol 双射）；:478 logVol_surjective；:469 integralRegion；:474 logVol_integralRegion；:397 logVol_archScale | R_ss = Real 的 bijection 与 rescaling 调整 |
| etaQ | Rss.lean:501 etaQ；:505 logVol_etaQ_pilot；QPilotRegion.lean:343 etaQReg；:347 etaQReg_eq_etaQ；:353 etaQ_pilot_eq_mk；:362 logVol_etaQ_pilot_eq_qRegion | eta_q pilot -> class of q-region，log-vol = qPilot.lhs |
| **等式化简** | 由 rssEquiv 定义: `Rss.mk D U hU = (rssEquiv D).symm x` <-> `logVol D U = x`（用 Equiv.eq_symm_apply + Rss.logVol_mk / mk_eq_mk_iff）；`numericalWall_iff_rss` 的证明正是 `simp only [ValBPS.eta_eq_eta_iff, Equiv.eq_symm_apply]` | 字段内容 = logVol U = lhs；由 exists_adelic_iff 直接给出 |

## 3. 关键归约（审计核心结论）

1. `NumericalWall D` 的四个字段 **全部已有现成引理**：
   - U 的构造: `integralRegion`/`archScale`（Rss.lean:469/390）或 `qRegion`（QPilotRegion:314）或 `lgp (hullOf (vcI))`（IdentifiedCopies:169 + Ind3:123）；
   - IsAdelic: 上述构造各自的 isAdelic_* 引理；
   - InHullOfImage: `InImage.inHullOfImage`（Rss:350）/ `inHullOfImage_lgp`（IdentifiedCopies:229）；
   - Rss 等式: `rssEquiv` + `Rss.mk_eq_mk_iff`（Rss:486/460）；
   - 最重要的是 `exists_adelic_iff`（Rss.lean:403）**一次性打包** U + IsAdelic + InHullOfImage + logVol = x（对任意 x <= rhs），其证明内部已用 hull/archScale/rhsDataOn_singleton 等完成全部组装。
2. 因此 `NumericalWall D` 的证明等价于 **纯数值不等式**：
   `numericalWall_iff`（Checks:61）+ `corollary312Variant_iff`（Statement:95）+ `exists_adelic_iff`（Rss:403）给出:
   `NumericalWall D <-> (concreteVariantData D).qPilot.lhs <= (concreteVariantData D).rhsData.rhs`，即 `-|log q| <= -|log Theta|`。
   （等价于 `Corollary312Variant (concreteVariantData D)`；LANA 把后者定义为**假设**，见 Statement.lean:85-91 与 EtaAlg.lean:169-175。）
3. **接线部分不是缺口**：`Rss.lean`/`QPilotRegion.lean`/`Scaling.lean`/`IdentifiedCopies.lean`/`Ind3.lean` 已经把 U/adelic/hull/Rss 的组装全部证完；缺口是最后的不等式（等价于 Cor 3.12 variant 本身），**不是**把现成引理接起来就能消除的——除非接受 `lhs <= rhs` 或等价输入。
4. **LANA 自身的非可导出性结果**: `Iut/WallEquiv/NonDerivable.lean:556 nonDerivability`（以及 `not_forall_xi` 543、`counterexample` 484）证明 Step (xi) 独立于 Thm311Package 字段；`Iut/Wall/Checks.lean` 文档也说明 numerical wall 作为存在式等价于 variant（循环）。故 "证明 NumericalWall" 若不引入新输入（或具体算法 provenance，见下）不可能由已有 LANA 引理完成。

## 4. 更可操作的备选目标（已有更强结构，仍 open）

| 目标 | 定义/定理 (file:decl) | 与 NumericalWall 关系 | 状态 |
|---|---|---|---|
| SSIneq (Scholze–Stix) | Iut/Wall/MultiContainer.lean:88 SSIneq D := (sFactor (nC D) - 1) * absLogQ <= logVol (hullOf (vcI D)) | `Wall D (idAlg D) <-> SSIneq D`（IdentifiedCopies:488 wall_idAlg_iff）；`SSIneq -> variant`（WallEquiv/Gap.lean:543 variant_of_ss_gap，用 gap >= 0） | open（LANA 未证；NonDerivable 暗示需 ABC 强度输入） |
| gap=0 | WallEquiv/Gap.lean:505 gap D := rhs - logVol (lgp (hullOf (vcI D))); :514 gap_nonneg; :531 ss_iff_le_rhs_sub_gap; :548 ss_iff_variant_of_gap_eq_zero; :554 variant_and_not_ss_iff | gap=0 时 SSIneq 与 variant 等价；SSIneq 单独已足够推出 variant | open |
| LGP 律算法的 wall | Iut/Wall/Checks.lean:93 EtaAlg.LGPLaw；:112 wall_iff_of_lgpLaw；Iut/Wall/IdentifiedCopies.lean:468 idAlg；:479 idAlg_lgpLaw；:483 idAlg_not_isTrivial；:488 wall_idAlg_iff；:504 idAlg_wall_imp；Iut/Wall/Constraints.lean:201 wall_iff_ss_of_thetaShift | 任意满足 LGP shift 的算法，其 wall 等价于 SSIneq；idAlg 给出具体模型 | open（等价于 SSIneq） |
| variant 的等价形式 | Iut/WallEquiv/Basic.lean:95 lana91_iff_wall；:111 lana91_iff_ss；:131 wall_iff_ss_of_thetaShift；:172 variant_iff；Iut/WallEquiv/Forms.lean:47 ss_iff_lgp_vcI；Iut/WallEquiv/VcI.lean（68 decls）；Iut/WallEquiv/Gap.lean:537 variant_iff_le_rhs | 多套等价刻画（LANA §9.1/§9.2/§9.3, VC-I） | 等价形式已有证明；被等价的目标仍 open |
| 主链出口 | Iut/Wall/EtaAlg.lean:212 cor312VariantHolds_of_wall；:223 classicalABC_of_wall；Iut/MainTheorem.lean classicalABC_of_variant | 若对某个算法族证 Wall（即 SSIneq/variant），即得 ClassicalABC | 出口已证，入口 open |

## 5. 缺口清单（G0–G3）与"非缺口"清单

### 缺口
- **G0（唯一数学核心）**: `Corollary312Variant (concreteVariantData D)`，即 `qPilot.lhs <= rhsData.rhs`（`-|log q| <= -|log Theta|`）。由 numericalWall_iff 与 corollary312Variant_iff，它与 `NumericalWall D` 等价；LANA 明确无证明（Statement.lean:85-91）。
- **G1（更可操作充分条件）**: `SSIneq D`（MultiContainer:88）或 gap=0。SSIneq 直接给 variant（Gap.variant_of_ss_gap），并且对 idAlg/LGP-law 算法与 wall 等价（wall_idAlg_iff / wall_iff_ss_of_thetaShift）。它不含 U/adelic 存在量词，是纯 log-volume 不等式：`(sFactor(nC) - 1) * |log q| <= logVol(hull(VC(I)))`。
- **G2（provenance/非循环性）**: `etaAnab` 的行程来源（T1)-(T3) 太弱（Checks 文档、NonDerivable.counterexample/nonDerivability 证明 Step(xi) 独立于 package）；要非循环，需要一个具体算法（如 identified-copies idAlg）及其 LGP 律，进而 wall 等价 SSIneq（已证），所以真正的数学内容仍是 G1。
- **G3（源侧常数/对象）**: 若坚持 ExpEst 显式常数路线（q/Theta 的 log-vol 具体数值、C_Theta 常数层），需要 Iut4Sec1/Implication 的 log-volume 常数层（见 coord/EXPLICIT-ESTIMATES-MAP.md §9），当前 LANA 也未把 Cor 5.2 的 delta/kappa_log/h_d 显式常数形式化。

### 非缺口（已齐，可直接复用）
- U 的构造与存在性: Rss.lean:469/390/333/403; QPilotRegion.lean:314; IdentifiedCopies.lean:169; Ind3.lean:123。
- IsAdelic 保持与 hull 结构: Rss.lean:319/346/365/393/471；ContainerHull/HolomorphicHull 的 hull 系统。
- InHullOfImage: Rss.lean:338/343/350/360；IdentifiedCopies.lean:204/222/229；Concrete/Ind1Invariance.lean:700。
- Rss/R_ss 实线: Rss.lean:446–490（Rss/mk/logVol/mk_eq_mk_iff/rssEquiv/logVol_surjective/logVol_archScale）；QPilotRegion.lean:343–364（etaQReg/etaQ_pilot_eq_mk/logVol_etaQ_pilot_eq_qRegion）。
- 体积计算: Rss.lean:63/75/91/106/125/133/143/158/172/186/194/203/213/228/233/262/283/397（componentVol/packetVol/globalVol/processionVol/archScale 全套）；QPilotRegion.lean:176–306（pow 体积）；IdentifiedCopies.lean:67/82/248/281/295/344/407/444（LGP 体积）；Ind3.lean:138/151/226/244/248/253/270（vcI/hull/Ind3 体积范围）。
- 约束接口: Constraints.lean:97 IPL（且 ipl:103 对任意 EtaAlg 已证）、:110 SHESides（sheSides_iff:116）、:132 SHEq（sheq_iff_wall:137）、:151 Multiradial、:174 ValDependent（not_valDependent:180）、:191 SetTransport/:196 APT、:222 WallDistinct（wallDistinct_of_wall:227）；MultiConstraints.lean / MultiContainer.lean 的 multiradial/SSIneq 组合引理。

## 6. 建议装配链（如 mainline/stepxi 要写文件；此审计不写代码）

目标 A：`numericalWall_of_le_rhs : qPilot.lhs <= rhs -> NumericalWall D`（已可由现成引理 10 行内完成）:
  1) `obtain ⟨U, hU, hI, hvol⟩ := (Wall.exists_adelic_iff D _).mpr h`（Rss.lean:403）；
  2) 目标 RHS 的 Rss 等式: 由 `Equiv.eq_symm_apply` + `Rss.logVol_mk`/`rssEquiv` 把类等式化为 `logVol D U = lhs`（即 hvol）；或用 `Rss.mk_eq_mk_iff` 与 `qRegion`（QPilotRegion:314, logVol_qRegion:321）；
  3) `exact (numericalWall_iff_rss D).mpr ⟨U, hU, hI, hEq⟩`。
目标 B：`le_rhs_of_numericalWall : NumericalWall D -> qPilot.lhs <= rhs`（同理，用 numericalWall_iff.mp + corollary312Variant_iff）。
目标 C（真正内容，open）：`SSIneq D`（或等价 gap=0）；然后 `variant_of_ss_gap`（Gap.lean:543）→ variant → `cor312VariantHolds_of_wall`/`classicalABC_of_wall`（EtaAlg.lean:212/223）需要 Wall 而非 variant；实际用法：SSIneq → `wall_idAlg_iff`（IdentifiedCopies:488）得 `Wall D (idAlg D)` → `cor312VariantHolds_of_wall`（EtaAlg:212）需要对**所有 D** 的算法族（`fun D => idAlg D` 可行，因为 idAlg 是每个 D 的构造）→ `ClassicalABC`。
  即: `(forall D, SSIneq D) -> (forall D, Wall D (idAlg D)) -> Cor312VariantHolds -> ClassicalABC`。

## 7. 结论（给 Lead）

1. 逐字段映射完成：U/IsAdelic/InHullOfImage/Rss 等式四字段全部映射到 LANA 现成引理（详见 §2），且 `exists_adelic_iff` 已把"给定 x <= rhs 时的四字段组装"整体证明——**接线不是缺口**。
2. `NumericalWall D` 与 `Corollary312Variant (concreteVariantData D)`（即 `-|log q| <= -|log Theta|`）等价（Checks:61 + Statement:95）；因此"证明 NumericalWall"=证明 variant=此前 parked 的定性核心，不是 Rss 引理的机械拼接。
3. 若要走可操作路线，LANA 已把内容压到单条数值不等式 **SSIneq**（`(sFactor(nC)-1)*|log q| <= logVol(hull(VC(I)))`；MultiContainer:88），且有 SS -> variant（Gap:543）与 idAlg 等价（IdentifiedCopies:488）；缺口 G1=SSIneq（或 gap=0）本身。
4. `NonDerivable`（NonDerivable.lean:556）已证明 Step (xi) 不由 Thm311Package 字段导出（反例存在），即该不等式需要 ABC 强度/具体 provenance 的新输入；不应把 LANA 的 Rss/Scaling 引理当作已解决它的证据。
5. 本文件只读；所有引用为源码级（ported Wall/WallEquiv 19 文件 olean=0、均 queued），待 watchdog 编译后可再升级为 olean 级证据。

## 8. 我们自己的 A490 接线文件（本轮审查发现，重要）

在移植树 `tmp/sheaf/lana/iut/Iut/Wall/` 下发现两个**我们自己新写**的文件（不在 LANA 原仓库；源仓库对应路径不存在）：

### 8.1 `Iut/Wall/NumericalWallHullActual.lean`（hull lane (A490)，7.2KB，queued=yes, olean=no）

导入 `tmp.sheaf.lana.iut.Iut.Wall.IdentifiedCopies`；内容为 IsAdelic/InHullOfImage 侧 lemma 链：

| decl | 类型/作用 | 复用的现成引理 |
|---|---|---|
| hullActual_thetaImage_isAdelic | (Ind1)-image 区域 adelic | Rss.thetaImage_isAdmissible |
| hullActual_thetaImage_inImage | thetaImage 属于自身的 InImage | Rss.InImage（rfl 包含） |
| hullActual_thetaImage_inHullOfImage | thetaImage 在 hull of image 内 | Rss.InImage.inHullOfImage |
| hullActual_hullOf_thetaImage_isAdelic | hull(thetaImage) adelic | Rss.isAdmissible_hullOf |
| hullActual_hullOf_thetaImage_inHullOfImage | hull(thetaImage) 在 hull of image 内 | rfl 包含 |
| hullActual_archScale_le_archScale | archScale 对区域包含单调 | ArchScale 定义（Rss.archScale） |
| hullActual_archScale_hullOf_thetaImage_le | 0<t<=1 时 archScale t (hull thetaImage) <= hull thetaImage（= t*(a*O_I) ⊆ a*O_I） | LocalTheory.isHullRegion_of_mem_hullRegions、hull_mem_hullRegions、smul_smul_integralAt_infinite_subset |
| hullActual_inHullOfImage_archScale_of_le_one | 0<t<=1 且 U 在 hull of image => archScale t U 仍在 hull of image | 上两条组合 |
| hullActual_hullOf_thetaImage_package | hull(thetaImage) 的 IsAdelic and InHullOfImage 打包 | 前两条 |
| hullActual_lgp_package | LGP*S (Ind3) 的 IsAdelic and InHullOfImage 打包 | IdentifiedCopies.isAdelic_lgp、inHullOfImage_lgp |
| hullActual_numericalWall_iff_exists_logVol | **NumericalWall D <-> exists U, IsAdelic U and InHullOfImage U and logVol U = qPilot.lhs** | Checks.NumericalWall、Rss.etaQ、ValBPS.eta_eq_eta_iff（unfold/simp） |
| hullActual_exists_adelic_inHullOfImage_logVol | **x <= rhs => exists U, IsAdelic and InHullOfImage and logVol U = x**（用 distinguished image 的 hull 做 archScale） | rhs_eq_logVol_image、archScale、logVol_archScale、Real.exp_le_one_iff、hullActual_* 链 |

### 8.2 `Iut/Wall/NumericalWallRssActual.lean`（R_ss 侧，2.5KB，queued=yes, olean=no）

导入 `Iut/Wall/Checks` + `Iut/Wall/QPilotRegion`；内容为 R_ss 等式链：

| decl | 类型/作用 | 复用的现成引理 |
|---|---|---|
| rss_mk_eq_symm_qPilotLhs_of_logVol | 任意 adelic U，logVol U = qPilot.lhs => Rss.mk U = (rssEquiv D).symm (qPilot.lhs) | Rss.rssEquiv、Rss.logVol_mk、Equiv.apply_symm_apply |
| rss_mk_qRegion_eq_symm_qPilotLhs | qRegion 版本（用 logVol_qRegion） | QPilotRegion.qRegion/isAdelic_qRegion/logVol_qRegion |
| rss_mk_archScale_eq_symm_qPilotLhs_of_logVol | archScale 版本（用 logVol_archScale 调 log-vol） | Rss.logVol_archScale、isAdelic_archScale |
| numericalWall_of_adelicHull_logVol | U 的 IsAdelic+InHullOfImage+logVol=qPilot.lhs => NumericalWall D | numericalWall_iff_rss（Checks:69）+ rss_mk_eq_symm_qPilotLhs_of_logVol |

### 8.3 这两个文件对缺口的影响

1. **字段接线已由我们自己的文件完成**（源码级；二者均在队列、待 watchdog 编译）：
   - `hullActual_numericalWall_iff_exists_logVol` 已把 `NumericalWall` 的 `etaQ`/logVol 形式化简为 "存在 logVol = qPilot.lhs 的 adelic hull region"；
   - `hullActual_exists_adelic_inHullOfImage_logVol` 在给定 `x <= rhs` 时显式构造（distinguished image 的 hull + archScale），并附两条新的 archScale-hull 引理；
   - `numericalWall_of_adelicHull_logVol` 用 R_ss 等式把 U 转成 `NumericalWall`（经 `numericalWall_iff_rss`）。
2. **仍未消除唯一缺口**: 上述 `hullActual_exists...` 需要输入 `hx : x <= rhs`。取 x = qPilot.lhs 时，正是 `qPilot.lhs <= rhsData.rhs`（即 `Corollary312Variant (concreteVariantData D)`；Statement:89/95）。因此：
   - 已有我们文件 + LANA 引理可轻易写出桥接定理 `NumericalWall D <-> qPilot.lhs <= rhs`（两方向：`hullActual_numericalWall_iff_exists_logVol` + `logVol_le_rhs`；反向用 `hullActual_exists_adelic_inHullOfImage_logVol` + `numericalWall_of_adelicHull_logVol`）；
   - 但这仍只是把 NumericalWall 等价化为 variant/SSIneq，**不证明不等式本身**。
3. **与 LANA 的 `exists_adelic_iff` 的关系**: LANA 的 exists_adelic_iff（Rss:403）用 `D.thetaPilot`（ivLabels 并集）构造；我们的 hull 文件用 distinguished label 的 `thetaImage` + 新 archScale-hull 引理（`hullActual_archScale_hullOf_thetaImage_le` 等），得到同型结论。这是并行/重复构造（audit note）：二者都依赖同一 Rss/hull 引理；建议 canonical 采用我们的文件（直接产出 `NumericalWall` 形状），LANA 版本保留为参考；若两文件不需要都编译，可让 Lead 决定优先级。
4. **编译状态**: 两个文件均 `olean=no, queued=yes`，依赖的 Wall/Checks/IdentifiedCopies/QPilotRegion 也全部 queued/0 olean。等 watchdog 编译后需按日志确认：`(rssEquiv D).injective`、`Real.exp_le_one_iff`、`hullActual_archScale_hullOf_thetaImage_le` 的 `LocalTheory` 引理名在 4.32.2 可用性（预期可用，因为同 import 的 Rss.lean 用过同类引理）。

### 8.4 建议（供 mainline/Lead；本审计不写代码）

- 若目标是“把 NumericalWall 的接线做成可消费定理”，建议在 A490 文件基础上加一个小文件/小节：`numericalWall_iff_le_rhs : NumericalWall D <-> (concreteVariantData D).qPilot.lhs <= (concreteVariantData D).rhsData.rhs`（约 10-15 行，用 §8.3 两方向），**并明确文档化**：这只是等价化，不算证明 variant。
- 真正的下一步（数学内容）：证明 `SSIneq D`（`(sFactor (nC D) - 1) * |log q| <= logVol (hullOf (vcI D))`；MultiContainer:88），或等价地 `gap D = 0`（Gap:505/548）；该不等式与 idAlg/LGP-law 的 wall 等价（IdentifiedCopies:488、Constraints:201），且由 Gap:543 可推出 variant。当前 LANA 未证，且 NonDerivable 说明需要 ABC 强度/具体 provenance 的新输入。
- 不要把这 2 个 A490 文件 + `exists_adelic_iff` 的等价化当作 NumericalWall/variant 已证：它们只证明了 "NumericalWall ↔ qPilot.lhs ≤ rhs"。

## 9. 更新后的结论（A490）

1. RHS 四字段（U / IsAdelic / InHullOfImage / Rss 等式）的逐字段映射完整：全部可回溯到 LANA 现成引理（§2 表），且**我们自己的两个 A490 文件已把接线写成 Lean**（§8，queued 待编译）。
2. 由 `numericalWall_iff`（Checks:61）+ `corollary312Variant_iff`（Statement:95）+ 我们的 `hullActual_numericalWall_iff_exists_logVol`/`numericalWall_of_adelicHull_logVol`，`NumericalWall D` 等价于单条不等式 `qPilot.lhs <= rhsData.rhs`（即 `-|log q| <= -|log Theta|`）。
3. 因此该路线的最后数学内容 = variant 本身（或更可操作的 `SSIneq`/`gap=0`），不是字段接线；LANA 的 NonDerivable 结果也说明该内容不能被现有 Thm311 package/接口字段导出。
4. 若 Lead 认为“不是全新数学”，则精确表述应为：**字段接线是已有引理的拼接（我们已写好）**；但 “NumericalWall 成立” 仍等价于 variant/SSIneq，需要新的数值/解析输入，不能由拼接自动得到。
5. 本审计只读：未修改任何文件；引用为源码/行号级（port 的 Wall 19 files olean=0；我们的 2 文件 queued）。
