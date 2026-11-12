# A491 LANA 源码逐字段保真审计（只读）

范围: `tmp/sheaf/lana/iut/Iut/Wall/{BPS,EtaAlg,Checks,Constraints,Rss,QPilotRegion,MultiContainer,IdentifiedCopies}.lean`、`Iut/Cor312/*`（含 ThetaData/Basic）、`Iut/Concrete/*`（Container/ThetaRegion/Ind1Invariance/Literal 及 LocalConstruct 引用）。源仓库对照 `tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/`。
状态 caveat: port 的 Wall/WallEquiv 等 19 文件 + 大部分 iut 包均 queued、olean=0；本审计为**源码级**逐字段核对（行号来自 ported 文件），未编译验证；未修改任何文件、未改队列、未碰 watchdog。

## 1. 结构/字段总表

### 1.1 Wall/BPS.lean（[LANA] Definition 4.1.3–4.1.7；IUT III 的 BPS/F×µ-prime-strip）

| 结构/定义 | 位置 | 字段/内容 | 对应 paper 对象 | 构造性 | 可疑点 |
|---|---|---|---|---|---|
| GMData | L69 | G（拓扑群）、M（交换幺半群）、G↷M、compact : Set M | 局部 Galois 群 G_v 与 O^{x mu}_v 等 local 数据（IUT III §1; [LANA] §4.2） | 接口结构（数据 + 类型类） | compact 明说 "simplified: the term N_{v,G}"；G、M 无几何实现（仅 abstract iso） |
| GMIso | L86 | G ≃_t* G、M ≃* M、等变、compact 对应 | GM-data 同构 | 定义 | 无额外可疑 |
| EtUnitBPS | L136 | gm : V → GMData、iso_model : 每个与 model 抽象同构 | étale-unit BPS B(H)（[LANA] §4.2(c)） | 接口（抽象同构存在） | 无具体 coric/theta-link 数据 |
| ValBPS | L175 | C（一维实向量空间，finrank=1）、localPilot : V → C、pilot=Σbad localPilot、非零条件 | value-group BPS / pointed real line（[LANA] Def 4.1.3–4.1.5） | 接口；由 qVal/thetaVal 实例化 | **C 是实线而非论文的 value monoid**（见 §2.1）；无数值 monoid 乘法/序/几何来源 |
| ValBPS.Iso | L231 | C ≃_l[ℝ] C'、localPilot 对应 | [LANA] Def 4.1.4 | 定义 | — |
| BPS | L357 | et : EtUnitBPS、val : ValBPS | BPS = étale-unit + value-group（[LANA] Def 4.1.6） | 定义 | 缺 paper 的 F×µ 结构/prime-strip 几何数据 |
| BPS.Iso | L369 | et iso + val iso | [LANA] Def 4.1.6(2) | 定义 | — |
| pilot/sumMap/PF/pilotCoord/eta | L196/201/210/307/320 | pilot、sumMap: ⊕ℝ_v→C、PF=ker sumMap、C≅ℝ、eta x = x·pilotCoord | [LANA] (4-3)、Lemma 4.1.7、Remark 4.1.5、§9.2 | 定理/构造（真实线性代数证明） | eta 是 "pilot 打到 x" 的线性映射——这是 LANA 定义的 η 值线模型，不是 paper η_q |

### 1.2 Wall/EtaAlg.lean（η-algorithm 接口；IUT III Cor 3.12 proof Step (xi)；[LANA] §9.1）

| 字段/定义 | 位置 | 内容 | 对应 paper | 构造性 | 可疑点 |
|---|---|---|---|---|---|
| EtaAlg.model | L98 | Pl D → GMData（不透明） | étale-unit prime-strip 模型（[LANA] §4.2(c)） | 数据字段 | 无几何构造 |
| EtaAlg.Side | L100 | Hodge theaters（不透明类型） | IUT I 的 Θ^{±ell}NF-Hodge theater（[LANA] §9.1） | 数据字段 | 仅 Nonempty，无 theater 结构 |
| EtaAlg.etUnit | L104 | Side → EtUnitBPS | B(H)（[LANA] §4.2(c)） | 数据字段 | — |
| EtaAlg.out | L108-109 | (choice ι : B ≅ thetaBPS h) → Ind3 → Region D | η-algorithm 的输出 LGP·S（[LANA] §9.1 Steps 8-9） | 函数字段（任意满足后续条件） | **不是算法构造**；无 Steps 1-7 数据/计算 |
| ind12_acts_on_S (T1) | L112-114 | Ind1/2 作用 = Ind3 的置换（存在 τ） | IUT III Thm 3.11(i)；[LANA] §10.4 | 假设字段 | 只要求存在置换，弱 |
| etUnitOnly (T2) | L117-119 | out 只依赖 étale-unit 部分与 choice.et | [LANA] Remark 6.2.2 | 假设字段（强） | 强局部性条件；对 paper 算法是非平凡断言，这里直接假设 |
| realisation (T3) | L123-125 | 每个输出 IsAdelic 且 InHullOfImage | IUT III Thm 3.11(ii)/Cor 3.12 结论的一部分 | 假设字段（结论性强） | 直接假设输出在 adelic/hull；使 variant 推导部分循环（Checks 文档已承认） |
| Wall D A | L173 | 对所有 Θ-links，存在 choice+Ind3 使 etaAnab = etaQ | (9-1)/Step (xi)（[LANA] §9.2） | 定义（假设） | Wall 永不证明；只作 h : Wall 假设 |
| wall_iff_forall / exists_out_of_wall / variant_of_wall / cor312VariantHolds_of_wall / classicalABC_of_wall | L183/189/201/212/223 | wall ↔ 不含量词；wall → variant → Cor312 → ABC | 主链出口 | 已证（条件于 Wall） | — |

### 1.3 Wall/Checks.lean（NumericalWall；[LANA] §9.2/§10.3）

| 定义/定理 | 位置 | 内容 | 可疑点 |
|---|---|---|---|
| NumericalWall | L56 | ∃ U, IsAdelic U ∧ InHullOfImage U ∧ eta(logVol U)=etaQ | 等价于 variant（numericalWall_iff L61）；文档明说 (9-1) 是 real-number 等式，接口 (T1)-(T3) 太弱 |
| numericalWall_iff | L61 | NumericalWall ↔ Corollary312Variant (concreteVariantData D) | 证明靠 eta_eq_eta_iff + exists_adelic_iff；语义上循环/规格化 |
| numericalWall_iff_rss | L69 | RHS 用 Rss.mk/rssEquiv 重写 | 同上 |
| IsTrivial/LGPLaw/not_isTrivial_of_lgpLaw/wall_iff_of_lgpLaw | L83/93/98/112 | trivial instance、LGP 律、LGP 下的数值 wall | 文档承认 trivial instance 存在 iff variant；接口不足以编码 η^anab 来源 |
| trivialGM/trivialEtUnit/trivialAlg | L126/138/142 | trivial 实例满足 Wall | 证明接口弱 |
| exists_isTrivial_iff / exists_wall_iff | L162/173 | 存在 trivial/wall 算法 iff variant | 文档明说 wall 作为存在式 = variant（循环）；非循环需给定算法 provenance |

### 1.4 Wall/Constraints.lean（IUT III Thm 3.11/Remark 3.11.1 约束；[LANA] §8.2）

| 定义/定理 | 位置 | 内容 | 可疑点 |
|---|---|---|---|
| IPL | L97 | 每个 choice 下 Θ-pilot BPS 与 q-pilot BPS 有 pilot 保持同构 | 定理 ipl(L103) 对**任意** EtaAlg 证明 ⇒ IPL 条件近乎自动，弱于 paper IPL |
| SHESides | L110 | out = F h1 S = G h2 S（两侧可表达） | sheSides_iff(L116) 化简为 side-independent g；接口形式 |
| SHEq | L132 | 存在 choice+Ind3 使输出类 = qRegion 类 | sheq_iff_wall(L137)：SHEq 就是 Wall；文档说明 |
| DistinctSides | L145 | Nontrivial A.Side | — |
| Multiradial | L151 | 任意两 choice 输出差一个 Ind3 置换 | C6 |
| SideDependent | L157 | 存在两侧输出范围不同；not_sideDependent_of_multiradial L162 | C7 与 C6 矛盾 |
| ValDependent | L174 | 输出依赖 value-group 部分；not_valDependent L180 | C8 与 T2 矛盾 |
| SetTransport/APT | L191/196 | 输出 = 固定集映射 φ(S)；APT := ¬SetTransport | C9 的负形式 |
| WallDistinct | L222 | 在 distinct Hodge theaters 上的 wall；wallDistinct_of_wall L227、variant_of_wallDistinct L231 | C5 |
| HoloStructure | L244 | Ring : Side→Type、CommRing、Compatible : ... → Prop | 仅谓词，不与 out 耦合；exists_alien(L259) 用 Compatible:=False 构造 ⇒ (C10) 可被平凡满足（weak） |

### 1.5 Wall/Rss.lean（R_val/R_ss 与 log-volume；IUT III Prop 3.9 / Remark 3.9.5；[LANA] §5.2(e)/§8/§9.2–9.3）

| 对象 | 位置 | 内容 | 构造性 | 可疑点 |
|---|---|---|---|---|
| LocalConstruct.componentVol_le_of_subset / componentVol_smul_infinite | L63/75 | Haar log-volume 单调、archimedean rescale 加 log t | 已证（实数分析） | — |
| LocalTheory.mem_admissible_hull_iff / packetVol_eq / packetVol_le_of_subset / haar_proj_scaledIntegral_lt_top / processionVol_le_of_packetVol | L125/133/143/158/172 | 包 log-volume 与 hull 的比较 | 已证 | 依赖 LocalConstruct 的构造 |
| archRegion/archScale/archScale_region_finite+infinite/isAdmissible_archScale | L186/194/203/207/213 | archimedean 伸缩、保持 admissibility | 已证 | — |
| sum_tupleWeight/packetVol_archScale_infinite/globalVol_archScale/processionVol_archScale | L228/233/262/283 | 权重与 log t 计算 | 已证 | — |
| nC/VC/Region | L303/311/314 | ℓ*=(ℓ-1)/2；concrete container；区域 = capsule-indexed admissible | 定义 | — |
| IsAdelic | L319 | ∀ i, hull.IsAdmissible (U i) | 定义（interface class） | admissibility 由 hull system 提供（Concrete 实例化） |
| logVol/hullOf/thetaImage/InHullOfImage/InImage | L324/328/333/338/343 | log-vol；hull；单 (Ind1)-image；包含关系 | 定义 | thetaImage 公式来自 Concrete thetaPilotOn（input data；见 §3） |
| thetaImage_isAdmissible/InImage.inHullOfImage/rhs_eq_logVol(_image)/isAdmissible_hullOf/logVol_le_rhs | L346/350/356/360/365/374 | hull 的 admissibility、rhs=-|log Θ|、单调性上界 | 已证 | 依赖 rhsDataOn_singleton（Concrete/Ind1Invariance） |
| archScale/isAdelic_archScale/logVol_archScale | L390/393/397 | rescaling 保持 adelic、加 log t | 已证 | — |
| exists_adelic_iff | L403 | x ≤ rhs ⇔ ∃ U (adelic+hull+logVol=x)（用 hull+archScale 构造） | 已证（构造性） | — |
| Rss/Rss.mk/Rss.logVol/Rss.logVol_mk/Rss.mk_eq_mk_iff/Rss.logVol_injective | L446/450/453/456/460/464 | adelic 区域模等 log-vol；mk/投影/单射 | 已证（Quotient） | = paper R_ss 的集合商定义（[LANA] §9.2） |
| integralRegion/isAdelic_integralRegion/logVol_integralRegion/logVol_surjective/rssEquiv | L469/471/474/478/486 | integral 区域；log-vol 满射；R_ss ≅ ℝ | 已证（用 archScale 满射） | rssEquiv 依赖 archimedean 伸缩选择（log t 自由）；与 [LANA] §9.3 "another real line" 一致 |
| etaQ/logVol_etaQ_pilot | L501/505 | etaQ := (qVal).eta lhs（pilot ↦ -|log q|）；log-vol(η_q(pilot)) = lhs | 定义 + 已证 normalization | **建模选择**：不是字面 "pilot ↦ {q_v O_v} 的类"；由 QPilotRegion.etaQ_pilot_eq_mk 与构造 qRegion 对齐 |

### 1.6 Wall/QPilotRegion.lean 与 Wall/IdentifiedCopies.lean

- QPilotRegion: `powElt/powMap/powRegion/pow`(L70/95/113/136) 用 tensor 分量 unit 的缩放构造区域；`lgp_eq_pow`(139)、`proj_pow`(143)、`isAdelic_pow`(155)、`componentVol_powElt`(176)、`packetVol_pow_integral_finite`(220)、`globalVol_pow_integral`(264)、`logVol_pow_integral`(300) 计算 log-vol；`qRegion`(314) = pow with e=1, label=labOne, integralRegion；`isAdelic_qRegion`(316)、`logVol_qRegion`(321)（log-vol = qPilot.lhs）、`qRegion_first`(331)、`etaQReg`(343)/`etaQReg_eq_etaQ`(347)/`etaQ_pilot_eq_mk`(353)/`logVol_etaQ_pilot_eq_qRegion`(362)。
  保真: region 由 q_v 的 theta 值（`scaleElt`）缩放 log-shell/integral 构造，公式层面真实；但其与 paper {q_v O_v} 的等同是定义层（q^{j²}·O 在 label j=1 处），未见 "等于 paper q-pilot region" 的独立定理。
- IdentifiedCopies: `lgp`(169) = `fun i => lgpAt D i (S i)`（单位缩放，[LANA] §6.2(i) M=1·S）；`proj_lgp`(171)、`isAdelic_lgp`(183)、`lgp_le_thetaImage`(204)、`inImage_lgp`(222)、`inHullOfImage_lgp`(229)、`packetVol_lgp`(248)、`logVol_lgp`(281)、`logVol_lgp_integral`(444)（= -s·|log q|）；`idAlg`(468)（trivialGM、out=lgp、T1/T2/T3 逐项填充）、`idAlg_lgpLaw`(479)、`idAlg_not_isTrivial`(483)、`wall_idAlg_iff`(488)、`idAlg_wall_imp`(504)。
  保真: 这是**identified-copies 玩具算法**（文档自述 [LANA] §6.2/§10.2），不是 paper η-algorithm；用于说明 wall ↔ SSIneq 与非可导出性（NonDerivable），不可当作 paper η 构造。

### 1.7 Wall/MultiContainer.lean

- `SSIneq`(L88) = `(sFactor (nC D) - 1)·absLogQ ≤ logVol(hullOf(vcI))`：对应 [LANA] 的 Scholze–Stix 型 wall（IUT III Cor 3.12 Step (xi-d)-(xi-f)/IUT IV Thm 1.10）；`SSIneqNoHull`(L94)= 用 vcI 而非 hull；`ssIneq_of_noHull`(L99)。
- `EtaAlg.ThetaShift`(L105)：out 的 log-vol = -s·|log q| + logVol S（identified-copies log-vol 律）；`MultiContainer`(L114) = `{alg : EtaAlg D, kum : alg.Side → Scaling D}`；`VCh`/`Coric`/`vol`/`qRegionAt`/`kummer`/`kummerInv`/`ringAt` 等（L127–L180）。
- 保真: `kum` 是**给定的** mono-analytic scaling（Scaling.u : 每个 tensor 分量的 unit），不是从几何 Kummer 同构构造；`ringAt` 用它定义 "alien ring"（kummer_kmul 已证代数律）。MultiContainer 是接口数据，符合 [LANA] §6.2/§7.1 的 multi-copy 读法，但 κ/coricity 的几何来源未构造。

### 1.8 Wall/WallEquiv/*（非本次逐字段重点，但保真相关）

- Basic: `Lana91`/`Exists91`(L80/87)、`lana91_iff_wall`(95)、`wall_theaterAlg_iff_ss`(105)、`variant_of_ss`(168)、`variant_iff`(172)、`classicalABC_of_ss`(180)、`wall_facts`(187)：LANA §9.1/§9.2/§9.3 的等价形式链（已证）。
- Gap: `gap`(505)=rhs - logVol(lgp(hullOf(vcI)))，`gap_nonneg`(514)、`logVol_lgp_vcI_eq`(516)、`gap_eq_rhs_add`(523)、`ss_iff_le_rhs_sub_gap`(531)、`variant_iff_le_rhs`(537)、`variant_of_ss_gap`(543)、`ss_iff_variant_of_gap_eq_zero`(548)、`variant_and_not_ss_iff`(554)。
- NonDerivable: `Thm311Package`(118)、`counterexample`(484)、`exists_package_not_xi`(491)、`not_forall_xi`(543)、`classicalABC_of_forall_xi`(548)、`nonDerivability`(556)（Step (xi) 独立于 package，需 ABC 强度输入）。

### 1.9 Cor312/* 与 Concrete/* 关键结构

| 结构/定义 | 位置 | 字段/内容 | paper 对象 | 构造性/可疑点 |
|---|---|---|---|---|
| Corollary312VariantData | Cor312/Statement.lean:68 | data : InitialThetaData、qPilot : QPilotData、rhsData : RHSData | 组装 IUT I Def3.1 + taxis #34/#35 的 variant 输入包 | 定义；仅三字段，无 C_Θ/算法字段 |
| Corollary312Variant | Cor312/Statement.lean:89 | X.qPilot.lhs ≤ X.rhsData.rhs | IUT III Cor 3.12 的 q/Θ 比较（-|log q| ≤ -|log Θ|） | Prop 定义（无证明/无公理）；docstring L33-38 明说 out of scope |
| InitialThetaData | Cor312/ThetaData/Basic.lean:81 | F/Fbar、E、VBad、global : IsInitialThetaGlobalData、prime : AdmissiblePrimeData、orb : OrbicurveData、localData : LocalThetaData | IUT I Def 3.1(a)-(f) | 真实结构；含 chosen data + 条件结构；文档称 orbicurve/cores/Tate 由构造/引理支撑（taxis #38-#42）；部分字段是假设结构（见下） |
| AdmissiblePrimeData | ThetaData/AdmissiblePrime.lean:111 | ℓ、ℓ_prime、five_le、torsionBasis、rep、rep_spec、sl_le_range、ker_isOpen、galois_deg_prime、residueChar_coprime、PrimeToOrder | IUT I Def 3.1(b)-(c) | chosen data（basis/rep）+ 条件；rep_spec 把 rep 钉到真实 Galois 作用（好） |
| ValuationSection | ThetaData/LocalConditions.lean:135 | sectFin/sectInf:sections、liesOver | IUT I Def 3.1(e) | chosen section + 条件（真实） |
| LocalThetaData | ThetaData/LocalConditions.lean:186 | sect、local_diagram_cartesian、decomp、decomp_isClosed、tateX/tateC、bad_type、bad_theta_model、epsilon_graph | IUT I Def 3.1(e)-(f) | chosen data + 条件（Tate 结构可由 existence 填充）；注意 bad_type/bad_theta_model 是假设字段 |
| OrbicurveData | ThetaData/Orbicurve.lean:88 | （模型 orbicurve 与 cores 数据） | IUT I Def 3.1(d)；[CbGC]? | 构造/条件混合（未展开核对） |
| LargeVolumeContainerData | Cor312/Container.lean:88 | proc、toRational、fiberFintype、packet、logShell、logShell_isProduct、logShell_relCompact、logShell_finiteSupport、integral_subset_logShell_nonarch | IUT III Remark 3.1.1(ii)、Prop 3.1-3.2；[LANA] taxis #43 | interface（packet/logShell 是字段）+ Concrete 实例真实构造（LocalTheory.container） |
| AdmissibleRegion | Cor312/Container.lean:152 | region、finiteSupport | restricted product admissibility | 定义 |
| ContainerHullSystem | Cor312/ContainerHull.lean:47 | system、integral_admissible | IUT III Remark 3.9.5；taxis #45 | interface + Concrete hull 实例 |
| HullSystem | Cor312/HolomorphicHull.lean:111 | Admissible : Set (Set Total)、relCompact_of_admissible、hullRegions、hull 公理（最小/单调/幂等/...） | IUT III Remark 3.9.5(i)；taxis #45 | interface（hull 公理字段）；`HullSystem.ofExists` 构造具体 hull；**paper 的具体全纯 hull 结构未直接证明满足**（Concrete 实例做了） |
| LogVolumeData | Cor312/LogVolume.lean:79 | weight、weight_pos、weight_sum_one、componentVol、*_integral/预像律等 | IUT III Prop 3.9(iii)；Remark 3.1.1 | interface（componentVol 由字段给出 + 公理）+ Concrete 用 Haar/p-adic log 实例 |
| DirectSumPresentation | Cor312/PacketPresentation.lean:65 | Summand : C→Type、环/拓扑、integral、IsProductRegion/Borel... | IUT III Prop 3.1（tensor packets） | interface + Concrete tensor 实例 |
| Procession/Capsule | Cor312/Procession.lean:55/80 | labels、length、capsule、labels_mono | IUT III Prop 3.1-3.3 的 capsules/procession | 定义 |
| RationalPlace | Cor312/RationalPlace.lean:30 | finite p / infinite | v_Q ∈ V(Q) | 定义 |
| QPilotData | Cor312/LeftHandSide.lean:58 | badFinset、badFinset_spec、weight、weight_pos；logQ/absLogQ/lhs | q-pilot 的 log-volume（IUT IV proof Thm1.10 的规范化；[LANA] §8.1(a)） | 真实计算 (logQ 用 qOrder·log p)；**q-pilot 对象本身未构造**（docstring 明说只算 log-volume side） |
| RHSData | Cor312/RightHandSide.lean:65 | container、proc_standard、toRational_finite/infinite、vol、hull、thetaPilot、thetaPilot_hullAdmissible；rhs | -|log Θ| = processionVol(thetaHull)（IUT III Cor 3.12；[LANA] §8.3） | thetaPilot 是**输入数据**（不是 multiradial algorithm 输出；docstring L84-88 明说 out of scope）；rhs 为实数（paper 可为 +∞） |

### 1.10 Concrete/* 构造性

- `Concrete/Container.lean`: `LocalTheory.container σ n : LargeVolumeContainerData`（L280）由 tensor packets + log-shell 构造；`vol : LogVolumeData`（L378）用 normalized Haar log-volume（weights [k_w:Q_vQ]/[k:Q]）；`hull : ContainerHullSystem`（L470）用 packet-wise holomorphic hull（least hull regions）。docstring L9-38 明说 "Everything here is proved from LocalConstruct"（真实构造）。
- `Concrete/ThetaRegion.lean`: `thetaPilotOn`（L273）用 productRegion( thetaComponentOn ) 构造；`thetaFinite_eq`（L261）证明 finite 分量 = ⋃_{φ∈indAut} φ '' (scaleElt · shell)（Ind1 轨道！）；`thetaComponentOn_eq_integral` 证明好归约/非 ramified 处为 integral；`qPilot`（L348）= bad_finite.toFinset + weights inertDeg/finrank；`concreteVariantData`（L359）= {data:=D, qPilot:=D.qPilot, rhsData:=D.rhsData}；`concreteVariantDataLit`（L367）用 label permutations 并集。
- `Concrete/Ind1Invariance.lean`: `rhsDataOn_singleton`（L700）等（hull of single-label image 的 log-vol = rhs，Ind1 不变）；`Concrete/Literal.lean`: `rhsDataLit`、`rhs_le_rhsLit`（L84）。
- 保真: Concrete/Container 的 container/vol/hull 是真构造（来自 local field theory + p-adic log/Haar）；ThetaRegion 的 thetaPilotOn 公式是真实构造（Ind1 轨道上的 scaleElt·shell 并集），但**未证明它与 paper 的 theta-pilot 对象像的并集一致**（RHSData docstring 明说 multiradial algorithm out of scope；region 作为输入）。

## 2. 专项核实

### 2.1 ValBPS.C 是不是 paper 的 value-monoid 对象？

**结论: 不是。** `ValBPS.C` 是一维 **实向量空间**（`finrank_eq_one`），配 local pilots φ_v 与 pilot φ_C=Σ φ_v（BPS.lean L175-187；[LANA] Def 4.1.3-4.1.5），本质是 **pointed real line（value group 的对数/加法化模型）**；`qVal` 取 C=ℝ、localPilot=degrees（Pilots.lean L106-113），`eta` 是 pilot↦x 的线性映射。
论文/ IUT 的 value monoid（O^{x mu}_v 或 F×µ-prime-strip 的乘法部分）是**乘法幺半群对象**，带几何/étale 来源、序与正性；LANA 只在 log/degree 层面建模（对 log-volume 比较足够），乘性结构与几何实现未构造。
可疑点: 若引用 LANA 的 BPS 作为 "paper BPS 已构造" 则不成立——它是接口/对数化模型；[LANA] 自己的术语是 "value-group BPS"/"pointed real line"。

### 2.2 EtaAlg 字段与 η-algorithm 的关系

**结论: 是接口抽象，不是 η-algorithm 的构造。** EtaAlg 只有不透明的 model/Side/etUnit，加上**任意函数** out（无 Steps 1-9 数据流），并用 (T1) `ind12_acts_on_S`、(T2) `etUnitOnly`、(T3) `realisation` 三个假设字段约束。
- 对应 paper: η-algorithm 是 IUT III Cor 3.12 证明 Step (xi)（[LANA] §9.1）中由 Hodge theaters/Θ-links/coric data 构造的算法；LANA 只保留"输入 choice + Ind3 → 输出区域"的接口。
- 可疑: T2 是强局部性假设（output 只依赖 étale-unit 部分），T3 直接假设输出 adelic 且在 hull 内（paper 的结论之一），因此从 EtaAlg+Wall 推 variant 带循环性；Checks.L56-73、L162-181 与 NonDerivable 已明确承认接口太弱、wall 作为存在式 = variant；非循环仅对给定算法 provenance（Milestone 2-3）成立。

### 2.3 concreteVariantData 每个字段来源

- `data : InitialThetaData` ← IUT I Def 3.1（ThetaData/Basic.lean:81）；子字段 global/prime/orb/localData 为 chosen data + 条件结构（AdmissiblePrimeData 含 basis/rep 与 rep_spec 钉住真实 Galois 作用；LocalThetaData 的 tateX/tateC 可由 existence 填充，bad_type/bad_theta_model 是假设字段）。
- `qPilot : QPilotData` ← badFinset = D.bad_finite.toFinset（badFinset_spec 由 coe_toFinset 证）、weight = inertDeg/finrank（weight_pos 由 inertDeg_pos'/finrank_pos 证）；logQ 用 qOrder·log p；lhs=-logQ/(2ℓ)。真实计算，但**只算 log-volume side，q-pilot 对象本身未构造**（LeftHandSide docstring L40-44）。
- `rhsData : RHSData` ← container = LocalTheory.container D.placeSect nC（真实 tensor packet/log-shell 构造，Concrete/Container L280）；vol = LocalTheory.vol（normalized Haar，L378）；hull = LocalTheory.hull（hull 系统，L470）；thetaPilot = thetaPilotOn ivLabels（公式构造：productRegion of thetaComponentOn；finite 处 = Ind1 轨道并集，见 ThetaRegion L261 的 thetaFinite_eq；hull-admissible 由 thetaComponentOn_admissible 证）；proc_standard/toRational_* 由 rfl/定义。
  可疑: thetaPilot 是**给定数据**而非 multiradial algorithm 的输出（RHSData docstring L84-88）；rhsData 用 ivLabels（IUT IV 读法），rhsDataLit 用 litLabels（IUT III 的字面读法，Literal.lean）；paper 的 Θ-pilot 与 LANA 的 thetaPilot 公式的等同未证。

### 2.4 Rss.mk/rssEquiv/etaQ 与 paper R_val→R_ss

- **Rss**: `Rss := Quotient (Setoid.comap logVol ⊥)`（L446）—— adelic regions 模相等 procession-normalized log-volume；对应 [LANA] §9.2 R_ss = {T⊆VC(I) adelic measurable}/(equal volume)，也对应 IUT III Prop 3.9 的 log-volume 论域。**一致。**
- **rssEquiv**: `Equiv.ofBijective logVol`（L486），用 logVol 满射（archScale 调整，L478-483）。对应 [LANA] §9.3 "R_ss 是另一条 real line"；一致，但选择 archimedean 伸缩实现满射（log t 的 freedom），是标准选择。
- **etaQ**: `etaQ := (qVal D.bpsDegrees).eta D.qPilot.lhs`（L501）即 pilot↦lhs=-|log q| 的线性映射。paper η_q: R_val→R_ss 把 pilot 送到 {q_v O_v} 的类；LANA 通过 rssEquiv 把 R_ss 视同 ℝ，并在 Rss docstring L30-34 明说 "modelling choice"；`etaQ_pilot_eq_mk`（QPilotRegion L353）与 `logVol_etaQ_pilot`（Rss L505）证它与构造的 qRegion 一致。**一致（模 documented modelling choice）**，但 paper η_q 的 anabelian provenance 未建模——这正是 Checks/NonDerivable 指出的 wall 循环来源。

## 3. 可疑点分级

- **A. 已文档化的简化（不是隐藏）**: q-pilot object 未构造（只 log-volume）；theta-pilot region 是输入而非 multiradial 输出；container/log-volume/hull 是 interface abstraction（与 IUT III Prop 3.1-3.3/3.9 的对应按模块记录但不是定理，Statement docstring L44-53）；-|log Θ| 限定实数（paper 可为 +∞）；variant 非 published Cor 3.12 的等同（Statement L40-59）；R_ss ≅ ℝ 与 η_q 为 modelling choice；GMData.compact 简化；Corollary312Variant 不以公理/定理混入。
- **B. 过弱/过强接口**: T2/T3 是强假设（T3 直接假设 adelic+hull 结论）；IPL 对任意算法自动成立（弱）；HoloStructure 不与输出耦合（exists_alien 用 Compatible:=False）；MultiContainer.kum 是给定数据而非几何构造；ValBPS.C 是实线不是 value monoid；thetaPilotOn 公式与 paper 像的等同未证；NonDerivable 证明 Step(xi) 不能由 package 导出（需 ABC 强度输入）。
- **C. 真实构造（可作为可靠部分）**: Concrete/Container 的 container/vol/hull（来自 LocalConstruct 的 tensor packets/log-shells/Haar/p-adic log）；ThetaRegion 的 thetaPilotOn 公式与 thetaFinite_eq（Ind1 轨道并集）；qRegion/lgp 的缩放构造与 logVol 计算；Rss 商与 rssEquiv/logVol；qVal 的 degree pilots；TateFamily/初始 Theta-data 的多个构造（Tate 参数、torsion field、ValuationSection 等）——这些有真实证明（源码级，待编译验证）。

## 4. 结论（引用 LANA 时的保真边界）

1. LANA 是**接口级、诚实标注的 Cor 3.12 variant 形式化**：它把 q-pilot/Θ-pilot/container/hull/算法/κ/coricity 等 paper 对象抽象为数据字段或接口，proved 的部分主要是 TFT/local field/analysis、log-volume、Tate 结构、以及条件于 variant 的主定理链。
2. 它**不能**作为"paper 的 q-pilot object / multiradial algorithm / value-monoid / η-algorithm 已构造"的证据；这些在 LANA 中是 data/interface/assumption（§2 已逐项）。
3. 对 A490 NumericalWall 路线：NumericalWall 的字段接线（U/IsAdelic/InHullOfImage/Rss 等式）在 LANA 中都有真实引理支撑（Rss/Container/Concrete），但 wall 等价于 variant（Checks:61），其数学内容（SSIneq/gap=0/variant 不等式）仍是假设/开放；LANA 自己的 NonDerivable 也说明不能由 Thm311 package 导出。
4. 建议: 团队文档引用 LANA 时标注 (i) 对象是 interface 而非构造（尤其 q-pilot object/η-algorithm/value monoid/theta-pilot output）；(ii) LANA 的 proved 部分（Concrete/local field/log-volume/Rss）可作真实资产复用；(iii) 不要把 variant/Corollary312Variant 称为 IUT III Cor 3.12 的证明或形式化。
5. 本审计只读：所有引用为源码行号级（port 的 Wall/WallEquiv 19 文件 olean=0、queued），未修改文件/队列/watchdog；待 watchdog 编译后可复核 olean 级证据。

## 5. 附录：其余 Concrete/* 文件的结构扫描（无结构文件的说明）

| 文件 | 结构 | 对应对象/角色 | 可疑点 |
|---|---|---|---|
| Concrete/Container.lean | PlaceSection@196 | V(k)→V(K) 的 places section（IUT I Def 3.1(e) 的 V≅V_mod） | 真实构造（section + type-preserving 条件） |
| Concrete/Existence.lean | EllipticCurveData@62, CurveArithmetic@109, TateInputs@142, ModEllRepData@168, CurveInputs@367 | 构造 initial Θ-data 的输入数据包（椭圆曲线、算术、Tate 输入、mod-ℓ rep） | chosen data + 条件包；其"existence"依赖后续构造引理（未逐条复核） |
| Concrete/Invariants.lean | TowerArithmetic@287 | IUT IV Thm 1.10 的 tower 不变量（d_mod/e_mod/F_tpd 等） | 数据/计算层；未见可疑 |

其余 Concrete/* 文件（CurveArithmeticProved, CyclicSubgroup, GaloisPlaces, Ind1Invariance, Literal, LocalEstimate, LocalTheory, Main, ModEllRepConstruct, ModEllRepGalois, SectionAverage, SL2Image, TateInputsConstruct, ThetaRegion, TorsionFieldGalois）只含 def/theorem/abbrev（无 structure）；其中 Ind1Invariance/Literal/ThetaRegion/LocalTheory 的关键 def 已在 §1.10 列出。Concrete/LocalConstruct/*（Theory、Admissible、Haar、Hull 等）是底层 local field/analysis 构造库，本审计按引用核对（Container.lean L9-38 声明 "everything proved from LocalConstruct"），未逐文件展开。

（注: 我们自己在 A490 写的 `Iut/Wall/NumericalWallHullActual.lean`/`NumericalWallRssActual.lean`/`NumericalWallBridgeActual.lean` 不是 LANA 源码，不在本保真审计范围；其说明见 coord/NUMERICAL-WALL-GAPS.md §8。）
