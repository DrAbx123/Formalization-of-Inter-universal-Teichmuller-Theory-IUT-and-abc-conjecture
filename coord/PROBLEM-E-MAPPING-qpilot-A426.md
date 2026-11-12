# Problem E 测绘：EtTh realization / theta 层 / AbsTopIII05 现有闭包

日期：2026-11-11（Lead A426）。作者：齐波（qpilot）。性质：只读测绘，**不造新数学、不接线**。
Citable 口径：paper 文件 = results log EXIT=0 + olean 存在（checker-CITABLE 另行标注）；tree 文件 = `.lake` 内 olean 存在（冻结 tree 资产）。

## 0. 扫过的位置

- `LeanFormal/IUT/Foundations/Theta/`（OddTheta 系列，10 文件）
- `LeanFormal/IUT/IUTII/Theta/`（EtaleThetaQuotient/FiniteThetaPacket/ThetaLink* 等 10 文件）
- `LeanFormal/IUT/IUTII/Kummer/`（SourceLogShell* / MonoAnalyticLogShell* / VerticalLogKummer* 等）
- `LeanFormal/IUT/IUTII/Frobenioid/Example36*`（EtTh/Frobenioid 边界模型）
- `LeanFormal/IUT/IUTIII/`（Corollary312/StepXI 的 theta-hull/log-shell 锚点；Theorem311）
- `tmp/sheaf/xif/paper/EtTh00-13*`、`AbsTopIII01-14*`（paper 层）
- `tmp/` 历史目录：`root-dtheta-20261016`、`theta-route-20261017`、`source-theta-pilot-iq-20261018`、`odd-theta-nonvanishing-20261020`、`theta-link-resolution-20261020`、`fractional-absorption-20261018`（均只剩 probe/日志，无活跃实现）
- ported：`tmp/external/ported/{tauceti_belyi_core,flt_core,...}`（无 IUT theta 资产；TauCeti 的 theta 是 Jacobi/模形式 theta，与 IUT theta 无关；flt_core=RR 链，已用于 D）

## 1. Analytic theta foundation（Foundations/Theta）

| 文件 | 真对象/定理（file:line） | build | 对应原文/EtTh 行 | 缺口 |
|---|---|---|---|---|
| GaussianKernel.lean | `gaussExponent`(23), `thetaValue`(46), `realThetaValue`(70), `SignedLabel`(94), `theta_neg`(124) | olean ✓ | EtTh §1 经典 theta 值/符号 | 纯 q 级数模型 |
| OddTheta.lean | `oddThetaExponent`(75), `oddThetaSign_eq_pow`(94), `norm_oddThetaTerm`(150), `summable_oddThetaTerm`(301), `OddThetaRootData`(313), `OddThetaRootExistenceData`(333), `OddThetaPacketNormalization`(347) | olean ✓ | EtTh theta 函数/单位根/packet 归一化 | 无几何/étale 对象 |
| OddThetaNonvanishing.lean | `oddThetaExponent_one_le_of_not_mem`(13), `oddTheta_ne_zero_at_i`(44) | olean ✓ | theta 非零（EtTh 输入） | — |
| OddThetaNormalization.lean | `oddThetaSign_mul_i_zpow...`(14), `oddThetaFraction_eval`(29/45) | olean ✓ | 归一化 | — |
| OddThetaShift.lean / OddThetaShiftSum.lean | `oddTheta_shift`(Shift:14), `tsum_addRight_eq_tsum`(ShiftSum:14), `oddTheta_shift_tsum_of_pointwise`(32) | olean ✓ | theta 平移律（EtTh/§1） | — |
| OddThetaNegativeDecay.lean | `tendsto_quadraticExponential_mul_geometric_neg`(14) | **olean ✗（未构建）** | 负向衰减 | 需补构建 |
| OddThetaTermAlgebra.lean | `oddThetaShiftCoefficient`(77), `oddThetaTerm_shift`(85), `oddThetaTerm_shift_inv`(133) | **olean ✗（未构建）** | term 代数/平移 | 需补构建 |
| SignedLabelEquiv.lean | `equiv`(75), `translate`(100), `translate_add`(114) | olean ✓ | signed label 模型 | — |
| GaussianSquareSum.lean | `gaussianSquareSum_formula`(24), `normalizedGaussianDegree_eq_factor`(44) | olean ✓ | 高斯和归一化 | — |

结论：analytic theta kernel 是**真对象且大多已构建**；两个未构建文件（NegativeDecay/TermAlgebra）是明确可扩展点。该层对应 EtTh 的“theta function values/shift”行，不对应 geometric realization。

## 2. Theta-link / Étale theta / log-shell tree（IUTII）

| 文件 | 真对象/定理（file:line） | build | 对应原文 | 缺口 |
|---|---|---|---|---|
| IUTII/Theta/EtaleThetaQuotient.lean | `thetaDerivedSubgroup`(29), `thetaCommutatorKernel`(32), `ThetaQuotient`(40), `EllipticAbelianization`(43), `thetaToElliptic`(50), `thetaPowerKernel`(62), `ellipticPowerKernel`(69), `modLThetaProjection`(83) | olean ✓ | EtTh theta group quotient/mod-l 包（EtTh06/08/10/11/12/13 的 A-class 复用源） | 无 profinite/étale 几何实现 |
| IUTII/Theta/FiniteThetaPacket.lean | `FiniteThetaPacket`(26), `scale_pos`(45), `logVolume_eq_sum`(64) | olean ✓ | EtTh/III θ-packet log-volume | — |
| IUTII/Theta/ThetaLinkAssembly.lean | `thetaLink_unitPower`(57), `thetaLink_unique`(108), `sourceEvaluationOrbit`(148) | olean ✓ | theta-link 单位群/轨道 | 无 realized theta transformation |
| IUTII/Theta/ThetaLinkSourceCover.lean | `connectedTemperedCover_*`(124-140), `BaseFieldCoverModel`(157) | olean ✓ | tempered cover（EtTh §1 背景） | — |
| IUTII/Theta/UnitGeneratedMonoidComparison.lean | `unitGeneratedSubmonoid`(33), `unitPowerRepresentation`(112) | olean ✓ | unit-generated monoid 比较（theta 层） | — |
| IUTII/Theta/ConcreteSourceEtaleThetaBridge.lean | `thetaScale`(56), `thetaLogScale`(59), `sourceModel`(44) | olean ✓ | 具体 source theta 桥（EtTh07） | 无 geometric realization |
| IUTII/Frobenioid/Example36SourceTheta*.lean | `AnalyticThetaCarrier`(Generator:89), `analyticThetaValue_eq_tsum_nat`(Divisor:207), `thetaTau_im`(Series:80) | olean ✓ | EtTh/Frobenioid-theoretic manifestation 的**具体边界模型** | 无 Frobenioid 对象本身 |
| IUTII/Kummer/SourceLogShellCarrier.lean | `SourceLogShellDatum`(86: p,hp,K,Units,invariants,logMap), `pStar`(103), `preLogShell`(118), `logShell`(124), `unitLayer`(129) | olean ✓ | **Prop 5.8(ii) log-shell I(G) 的缩减载体** | 无 Γ^×_non 图/CMLF 范畴 |
| IUTII/Kummer/SourceLogShellAbsTopIIIBridge.lean | `SourceLogShellInvariantImageIdentification`(70), 校准定理(178), `invScaledUnitLayer`(133) | olean ✓ | **Cor 5.5 桥接卡的缩减形式（已在冻结校准模型上证明）** | 无 D^• 七行图 |
| IUTII/Kummer/MonoAnalyticLogShell*.lean | ArchPsiCns 校准(archSegment:51 等 14 字段)、CompactCarrier、FormalLogMul、PadicLog、MixedPacket | olean ✓ | Prop 5.8(iii)/(v) 的 arch/p-adic 校准载体 | 无 functorial algorithm |
| IUTII/Kummer/AbsoluteKummer{Continuity,Injection,Quotient}.lean, SourceThetaPilotIQContainment.lean | — | **olean ✗（3+1 未构建）** | bi-Kummer/绝对 Kummer（EtTh §4 深输入） | 构建缺口 |
| IUTII/Kummer/VerticalLogKummer*.lean | `VerticalLogKummer`(order layer) | olean ✓ | log-Kummer 纵向层（Prop 5.8 背景） | — |

## 3. AbsTopIII05 paper 层（01-14）

全部 paper 文件 EXIT=0 results + olean（除 `AbsTopIII05Section0ObjectsActual` 无 results 行/olean ✗，修编中）。

| 文件 | 真对象/定理 | 对应原文 |
|---|---|---|
| AbsTopIII01LogShellActual | `absTopIII_logShell_zero_mem`(36), `_add_mem`(41), `_invariant_unitLog_mem_logShell`(46) | Prop 5.8(v) 具体 log-shell 律 |
| AbsTopIII02LocalVolumesActual / 03Cor510Actual | 局部 log-volume 语句/Cor 5.10 有限 log-volume | Cor 5.10/Prop 5.7 |
| AbsTopIII04LogFrobeniusActual | `absTopIII_logFrobenius_unit_landing`(41), `def31IVRows`(47) | Def 3.1(iv) log-Frobenius 字典 |
| AbsTopIII05ReconstructionInputsActual | `DeepInput`(40), `absTopIIIDeepInputs`(48, 4 行 proved=false) | Prop 5.8(i)(ii)/Cor 5.5/Section-0 的 4 个 named deep inputs |
| AbsTopIII05RefinedActual（CITABLE 16） | `Prop58iLocalFieldReconstruction`(D1), `Prop58iiLogShellReconstruction`(D2), `Cor55LogFrobeniusCompatibility`(D3, bridgeAnchor 由 tree 定理填充), `OrientedGraphAnabelianData`(D4, zActionAnchor 由 chainTranslation_graphAut 填充), `RefinedDeepInputs` | D1-D4 typed 化；S3171RouteSlot 接线该文件已有但 A409 后不新增接线 |
| AbsTopIII06/07/08/09* | WeightedVolumeBridge / NormalizedLocalVolume / PvAdicScaling / ThetaHullScaling | Prop 5.7/Cor 5.10/III θ-hull |
| AbsTopIII10/11/12/13/14 | StatementLedger / IndexIds / AssetMap / PsiCnsAnchor / FieldScaling | 记录/校准档 |

## 4. EtTh realization rows（paper 层）

- EtTh00-13 全部 **EXIT=0 results + olean**（EtTh01 OddThetaSeries 引 Foundations/Theta/OddTheta；EtTh08 引 IUTII/Theta/EtaleThetaQuotient + EtaleTateDirection + OddTheta）。
- 真对象：EtTh01 `EtaleThetaKummerClass`(48)/`MonoThetaEnvironment`(62)/`EtaleThetaObject`(79)；EtTh06 `EtThThetaGroupObject`(51)；EtTh07 `etTh_oddThetaTerm_zero/neg_one`(36/40)；EtTh10 quotient laws(33-52)；EtTh11 rows(69: 11 行，3 行 class-B named)。
- class-B named（**无形式化**）：EtTh02 `etThDeepInputs` 10 项（Prop1.1/1.3/1.4/1.5/Thm1.6/Thm1.10/Prop3.2/3.4/§4 bi-Kummer）；EtTh11 rows 5-7（geometric realization / Frobenioid manifestation / actual theta transformation）。
- EtTh05 `etThPaperInputs` 4 项、EtTh01 `EtThPaperComponents` 7 行 = 原文 §1-§5 对应记录（非证明）。
- 条件接线（已存在，非 A426 新增）：`Mzk1EtThRealizationConsumerActual`（CITABLE 14）把 3 个 class-B 行装成 `EtThRealizationInput` 并接到 Thm25/GenEll 消费者；blu blocker 3 行 + no-port 结论。

## 5. IUTIII theta-hull / log-shell 锚点

| 文件 | 真对象 | 对应 |
|---|---|---|
| Corollary312/StepXI/ThetaPacketBridge.lean | `toPositivePacket`(25), `toPositivePacket_logVolume_eq_sum`(47), `finiteThetaPacketBridge`(79) | III θ-packet → log-volume（EtTh/III） |
| Corollary312/StepXI/HolomorphicHull/CardAMPLThetaBoundSupply.lean | `CardAMPLThetaBoundSupply`(78), `realVolume_le`(94), `cor312Conclusion`(193) | θ-bound supply（Cor 3.12 hull，AbsTopIII 5.7 归一化消费） |
| Corollary312/StepXI/SourceLogShellMuNQuotientCarrier.lean | `muNQuotient`(66), `muNQuotientMap`(70), `weightNLog`(101) | Ψ^×/μ log-shell 商（Prop 5.8 背景） |
| Corollary312/StepXI/HolomorphicHull/CardHullRealEdge*.lean | [AbsTopIII] Prop 5.7 (i)(a)(b) 文档锚点(14/70/423/441) | AbsTopIII 5.7 归一的 hull 消费 |

IUTIII 顶层只有 Corollary312 与 Theorem311；theta/AbsTopIII 具体内容集中在 Corollary312/StepXI/HolomorphicHull 与 ThetaPacketBridge。

## 6. 原文对象 ↔ 现有形式化 对照与缺口

### Prop 5.8(i)（本地域 group-theoretic reconstruction）
- 已有真对象：`SourceLogShellDatum`（p/p*/K/Units/invariants/logMap）、`pStar`(103)、`unitLayer`(129)、`preLogShell`(118)、`logShell`(124)；AbsTopIII01 log-shell 律；AbsTopIII05Refined D1 typed 接口。
- 缺口：absolute Galois group G_k、G_ab、O^◇_k/k^× 的嵌入像、group-theoretic 算法、Verlagerung functoriality、p,p*,p^f,[k:Qp],e,p^m 的“算法提取”→ 目前只有 involution 模型与数据字段，无算法定理。

### Prop 5.8(ii)（Γ^×_non 图 + log-shell I(G)）
- 已有：具体 log-shell 载体（D.logShell/preLogShell/unitLayer）；桥接卡等同（冻结校准模型已证）；AbsTopIII05Refined D2 typed；MonoAnalytic 校准档（archSegment 等）。
- 缺口：Γ^×_non-diagram in CMLF_TS^⊞（图/category of local fields）、functorial algorithm Ob(TG^⊢)∋G↦Γ^×_non(G)、k^∼(G) 重建、I(G)=p*⁻¹ I* 的“算法化”。

### Cor 5.5（global/panalocal mono-anabelian log-Frobenius compatibility）
- 已有：`SourceLogShellInvariantImageIdentification`(70) + 校准定理(178)（桥接卡缩减形式）；AbsTopIII04 unit landing；AbsTopIII05Refined D3 typed（bridgeAnchor 已填入）；L=Z / L†=WithBot Z 的原文对象（在 AbsTopIII05Section0ObjectsActual，修编中未绿）。
- 缺口：D^• 的七行 category diagram（𝕏/E^•、N^⊞_v、λ^⊞_v、κ^{An•}）、functorial compatibilities、mono-analyticization。

### Section-0 combinatorial data（oriented graphs Γ^×_v）
- 已有真对象：`FrobeniusPictureArrow`(79), `FrobeniusPictureGraphAut`(84), `graphAut_iff_stepPreserving`(106), `chainTranslation_graphAut`(112), `graphAut_eq_translation`(126)（Z-图 = 原文 Gamma 的具体模型，已证不变性）；theta-link graph reductions。
- 部分：`AbsTopIII05Section0ObjectsActual`（本批编写中：countably ordered sets、Order(E)、oriented graph/opposite、FinLinear、L/L†；当前 EXIT=1 未交付）。
- 缺口：general oriented graph/underlying graph/branches 全定义、pre-path/path 同构类、饱和集、Frobenius 图到 general graph 的 functor。

### EtTh realization deeper rows
- 已有：EtaleThetaQuotient 群商包（A-class）；Example36 Frobenioid 边界模型；OddTheta 分析核；EtTh00-13 条件/row 记录；AbsTopIII05Refined 的 typed realization bundle。
- 完全缺失（3 行 class-B）：(1) geometric realization of theta groups（profinite/etale）；(2) Frobenioid-theoretic manifestation；(3) actual theta transformation on realized object。

## 7. 可扩展点（供 Lead 排期；本轮不做）

1. 补构建 Foundations/Theta 两个文件（OddThetaNegativeDecay、OddThetaTermAlgebra）：机械、无新数学。
2. 补构建 IUTII/Kummer 的 AbsoluteKummer{Continuity,Injection,Quotient} 与 SourceThetaPilotIQContainment（bi-Kummer/EtTh §4 前置）。
3. 把 `SourceLogShellDatum.muNQuotient`（III StepXI 已有）+ log-shell 律整理成 Prop 5.8(ii) 的“具体 log-shell diagram”真实对象层（仍非算法）。
4. 完成 Section-0 objects 文件（countably ordered sets/Order(E)/oriented graph/L/L†；当前 EXIT=1）→ 真实 Section-0 对象层。
5. 建立 Frobenioid Example36 边界模型 ↔ EtTh05/EtTh11 Frobenioid 行的精确对应（现只有命名 row）。
6. Prop 5.8(i)/(ii)、Cor 5.5 的算法/diagram 部分：无现成 Mathlib/TauCeti 资产（已 grep 0），属新理论；保持 named 并写明原文对象。

## 8. 证据与限制

- paper 文件 EXIT=0 来自 results log（本轮采样）；tree 文件“citable”= 已构建 olean（冻结 tree 资产）。
- 未重新跑全树 lake build；tree 文件是否 checker-CITABLE 属 tree 验收入口，本测绘只记录构建状态。
- 未造新数学、未接线；GATE NOT PASSED；binding HOLD；registry frozen 14041/23066/18800。

## 9. A428 扩展状态（2026-11-11，机械构建缺口已清）

- 6 个构建缺口全部 **serial lake env lean EXIT=0 + olean**（pin 明细见 tmp/a428_gap_pins.txt）：
  - OddThetaNegativeDecay.lean（删与 OddTheta 重复的 summable_oddThetaTerm 块）SIZE=4872 sha=EB53F70E...
  - OddThetaTermAlgebra.lean（无需改）SIZE=6470 sha=93B903B8...
  - AbsoluteKummerInjection.lean（calc 方向 hk.symm→hk）SIZE=7792 sha=1C9FD6BC...
  - AbsoluteKummerContinuity.lean（按 IsLocallyConstant 新定义重写 + Set binder 显式 + U let；不再直接用 lift_mk）SIZE=3727 sha=C1FA60C2...
  - AbsoluteKummerQuotient.lean（新 lift_mk 签名：rw [absoluteKummerMapQuotient, QuotientGroup.lift_mk]）SIZE=3138 sha=70643142...
  - SourceThetaPilotIQContainment.lean（LinearMap.proj_apply () (...) → rfl）SIZE=9238 sha=C532C89B...
- 新 section 文件：coord/THETA-ETTH.md（theta analytic/LogShell/EtTh realization；E-1/E-4 资产、构建 pin、依赖边、named gaps）。
- 新骨架文件：coord/SKELETON-THETA-ETTH.md（T1-T5/E1-E4/L1-L7/A1-A5/R1-R2/I1-I3/B1-B2 节点表 + 依赖边 + 未映射/辅助文件盘点 + 成本排序扩展点）。
- 仍待：Prop 5.8(ii) 具体 diagram 对象层（Mzk1Prop58iiDiagramActual，下一步）；A5 Section0Objects 修编。
- GATE NOT PASSED；binding HOLD；pins 14041/23066/18800。

## 10. A437 扩展（JSON chain + Prop 5.8(ii) diagram object）

- coord/target-chain.theta-etth.json：31->32 nodes / 25->26 edges（新增 P58 = Mzk1Prop58iiDiagramActual；edges 仍全部来自真实 import）。
- Mzk1Prop58iiDiagramActual.lean：EXIT0 SIZE 10359；checker CITABLE 15 probe_ok；sha256 1BC1070E552FE55A2EB67D97EBD7592FAD82EF5172C99886C2247B4B2FF5672B；内容 = CMLFCarrier/NonDiagramModel/Prop58iiNamedInput(N1-N3)/Prop58iiDiagramObject/vertexRelations/cor55DiagramRows/calibration_vertexRelations；边界不变（named 算法、不接线）。
- 构建 pin：6/6 gap files 已绿（tmp/a428_gap_pins.txt）。

## 11. A440 paper-route JSON（target-chain.paper-theta.json）

- 383 nodes / 1082 edges（paper:* 355 + formal:* 28；NAMED 306 / CONDITIONAL 49 / GAP 28）。
- 来源：EtTh 301KB、GenEll/Arithmetic Elliptic Curves in General Position、AbsTopIII III 474KB、Noncritical Belyi Maps、Hodge-Arakelov Survey I/II、Explicit estimates in IUTeich 129KB。
- 显式映射：AbsTopIII 5.8/5.5/5.4/5.6/3.1/5.10；EtTh 1.1-1.5/1.6/1.10/3.2/3.4；GenEll 2.1/3.x/4.3/4.4；NCBelyi 2.1-2.5/3.1/3.2 → 对应 Foundations/Theta、IUTII/Theta、AbsTopIII*、xif AbsTopIII05Refined/L1-L2/P58 等锚点。
- 未形式化部分：NAMED/GAP（survey/estimates 路线 + 映射表外定理），不冒充证明。
