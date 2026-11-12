# 原文 xi-f 路线与命名约定

日期：2026-10-31。目的：防止把 normalized model、native 目标、SourceDefinition31Data contract、D5–D9 构造、paper-level Θ-link 目标混为一谈。

## 1. 五个不同层次（禁止同名）

| 层 | 名称 | 文件/对象 | 地位 |
|---|---|---|---|
| N | Normalized Xi-F | `PaperXiFFinalActual.paperLevelXiF_actual` / `ActualPaperXiFTarget T` | 已闭：normalized qVFam scalar ≤ normalized root theta hull log，T : SourceNativeInitialThetaData。**不是原文 Θ-link xi-f。** |
| T | Native Xi-F target | `SourceNativeInitialThetaData` 侧 q/hull | native 对象；与 SourceDefinition31Data 无现成桥。 |
| S | Source contract | `SourceDefinition31Data` / `OriginalInput` | contract 层；D5–D9 目标；目前未被 E1/E2 消费。 |
| D | D4–D9 assembly | `D4D9Supply` / `S1280SourceData_of_remaining` / `S1322SourceGap` | source assembly；`D4D9Supply.toSourceData` 无调用者。 |
| O | Original Θ-link xi-f | `ThetaLinkActual` / `PaperQPilotObject` / `PaperSignedHull` | 原文目标层；关键 identification 仍是 `Prop` 占位，尚无 inhabitant。 |

## 2. 强制命名

新文件/声明使用前缀：

- `NormXiF...`：normalized model
- `OrigXiF...`：原文 Θ-link 目标
- `Source...`：contract / SourceDefinition31Data
- `Native...`：native T
- `...Spec`：仍是命题占位，未构造
- `...Actual`：已 actual 构造
- `...Exact`：精确首字段，无 inhabitant

禁止：

- 用 `ActualPaperXiFTarget` 代指原文 Θ-link。
- 用 `SourcePilotRegionDataL` 代指 old `SourcePilotRegionData`。
- 用 `S1398D6Supply` 代指 D4D9Supply。
- 用 `S1403D789ConditionalSupply` 代指完整 D4D9。
- 用 `paper_*_identification : Prop` 证明其自身。
- 用 `Nonempty`/arbitrary inhabitant 填 `link_identification`。

## 3. 当前关键事实

- `PaperXiFFinalActual.paperLevelXiF_actual` 无条件、axiom-clean，但目标类型是 normalized tensor/hull，不是 Θ-link。
- 全库无字面 `FinalXiF`。
- `SourceDefinition31Data -> S605` 不是实际边；S605 输入 `SourceNativeInitialThetaData`。
- E1/E2 闭包不含 D5–D9。
- `ThetaLinkActual.link_identification : Prop` 无具体定义；`PaperQPilotObject` 四个 `paper_*_identification : Prop` 同样无具体定义。
- 因此原文 xi-f 当前是 **spec 未具体化**，不是“差一个证明”。

## 4. 下一步义务

1. 把 `PaperQPilotObject` 四个 `paper_*_identification : Prop` 改为具体命题（用 actual strip/lineBundle/logKummer/qPilot scalar）。
2. 把 `ThetaLinkActual.link_identification` 改为具体命题（用 actual q-pilot 与 signed hull 的 log-volume 比较）。
3. 构造 actual `PaperQPilotObject` / `PaperSignedHull` / `Indeterminacies`。
4. 把 `SourcePilotRegionDataL` / C3 q-scalar 接到 Θ-link q-pilot。
5. 最后才谈 E1/E2 normalized scalar 与 Θ-link scalar 的桥；若桥不存在，明确保留为不同命题。

## 5. 验收

- 每个 actual 文件：EXIT=0 + olean + allowed trio。
- 每个 exact 文件：明确 first field，不写 inhabitant。
- 每次报告必须标层：N/T/S/D/O。
- 不再新增 `...ConditionalSupply` 包装，除非有实际消费者。


## 6. 禁止简化（硬规则）

具体对象就是具体对象，不能为了闭合而换对象：

- 不把 bivariate ψ/ω 换成存在量词或抽象函数。
- 不把 division polynomial 求值换成任意多项式。
- 不把 nonterminal orbicurve 换成 point fiber/terminal stack。
- 不把 connected cover 换成 split K×K。
- 不把 HDD image 换成任意 Set/rank-one。
- 不把 Θ-link 的 line bundle/theta section 换成 Prop 或 Nonempty。
- 不把 Ind3 packet action 换成 changed carrier 上的 identity。
- 不把 q-pilot scalar 换成固定 q=1/5。
- 不把 SourceDefinition31Data 换成 native T。
- 不把 normalized ActualPaperXiFTarget 换成原文 Θ-link。

如果定理在具体对象上不成立，记录 exact obstruction；不要改成 1=1。


## 7. 2026-10-31 进度快照

- Route A：`S1444ReportAKPlaceQActual.lean` 是当前更完整的 route A 文件（F-place/K-place/q/order/valuation/norm/kernel-root 义务表）；已交 transport 编译，未验收。
- `S1413SourceKPlaceQComparisonActual.lean` 有实际 q 图，但编译仍有错误；仅历史/备选，不作已验收。
- O 层已验收（源代码 SHA 匹配 + olean 存在）：
  - OrigXiFPaperQPilotScalarActual（actual C3 q scalar；exact first field 是 source bad-family 标量识别）
  - OrigXiFPaperSignedHullActual（actual PaperSignedHull；exact 是 procession-normalization equality）
  - S1406PaperPolyIsoActual（actual polyIso 是 paper orbit 代表；SourceLabelAgreement 仍 exact）
  - S1446ReportCReadoutActual（route C readout pair；hcont/hS/S863ProductImageEq 仍 exact）
  - S1447ReportFMarkedTraceActual（route F value-layer marked trace；paper projection exact）
- D5 已验收：S1452（ZSMul bridge；NetEDSInput exact）、S1405 待 olean。
- 禁止把 N 层 `ActualPaperXiFTarget` 当 O 层；禁止把 changed carrier/conditional supply 当 actual。


## 8. 追加验收（2026-10-31）

- S1425KappaOxGActual：actual `S1399PaperOxGModule` inhabitant（ref strip (1,0)、actual link、GraphGroup、unit/action/equiv）；exact 是 paper algorithm `G ↦ O^x(G)` 与 `Aut(‡A) ≅ G_w`。SHA 363D3D12...，olean 存在。
- S1389PaperPolyIsoActual：actual PolyIsoAction 首字段（S1264/S1313/S1318 的 labelPerm = Fin.revPerm；S1318 actual -1 shell transport）；exact 是 S1318 `ActualZpShellAgreement`（source 没有 log-shell transport）与 tensor-level equality。SHA 874E07E5...，olean 存在。

- S1405TorsionCardinalityPortActual：源码 SHA DFCCD162... 匹配；olean 47C01038...，443552 bytes；EXIT=0；10 条导出定理 axon trio；exact 首字段是几何计数 / criterion+separability。

- OrigXiFPaperSignedHullActual 更新：当前 SHA 028483B0...（403 行，olean 232336 bytes）；旧的 8bdac10b 版本 superseded。actual thetaHull/determinant/signed log/ray 已构建；exact 只剩 procession-normalization bridge field。
- S1415MarkedTraceActual：route F value-layer actual marked trace；exact first field = BddAbove (sourceThetaHullLogValueSet)；C9 paper marked map/final-evaluation membership 仍 open。SHA E9FC3E99...，olean 存在。

- OrigXiFPaperLogKummerActual：actual SourceKummerArrow from an actual FPrimeStripEquiv phi; O-layer logKummer field actual；exact first field = Nonempty (FPrimeStripEquiv envStrip (sourceQPilotStrip boundary))；paper_logKummer_identification 仍未触及。SHA EA93526F...，olean 216712 B。

- OrigXiFThetaLinkIdentificationActual：link_identification 已具体化为
  (O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3) ∧
  (OrigXiFPaperQPilotLogVolume C3 ≤ OrigXiFSignedThetaHullLogVolume D)；
  link_implies_inclusion 已 actual 证明（由 scalar equality + signed-hull comparison，不把 ray membership 当输入）。两个 scalar 字段仍 exact。SHA 42AEFFD0...，olean 存在。
- S1460SourceFinitePlaceIndexActual：给定 actual e : V ≃ FinitePlace Fmod，actual SourceFinitePlaceIndex / IntegralInd3PlaceComparison / Ind3 carrier；当前 S1280 V=Unit 无此 equiv，exact 首字段是 source-faithful V=FinitePlace Fmod 的 concrete input。SHA 3DCE9189...，olean 存在。

- S1420PrePsiDerivativeActual：separable_iff_aeval_derivative_ne_zero 及 target ↔ IsCoprime ↔ Bezout ↔ Squarefree 全部等价；exact 首字段 S1420PrePsiDerivativeNonvanishing 等价于原目标，gcd 路线无松弛。SHA E5CA1AE4...，olean 存在。

- OrigXiFPaperBoundaryStripActual：actual O-layer boundary/strip；Label=ZxZ, Choice=I.family.index×Nat；core ind1/ind2 用 I.translate，ind3 层坐标（不是 level:=0）；θ log-volume 常量性、route_normal_form 证明；strip = sourceQPilotStrip boundary。SHA EC60AF24...，olean 358408 B。exact 是 paper q-pilot F^… strip identification（未触及）。

- S1426Ind2AnalyticSymmetryActual：actual local FPrimeStrip Kummer datum + shell equivalence + Ism representation on IQSpan；exact 首字段是 Ism 在 actual IQSpan 上的表示；archimedean complex conjugation 实际；regular/Complex 模型仅 non-vacuity。SHA 0B66B608...，olean 961720 B。

- S1428RealCuspValuationActual：actual cusp no-go（[0:1:0] 无正可变实坐标）；给定 actual cusp local parameter 时构造 norm/Haar epsilon + S1330RealCuspCoordinate；exact 首字段 S1428CuspLocalParameter。未用 q=1/5/log q。SHA ed44d811...，olean 待补。

- OrigXiFThetaLinkActual：O 层 actual ThetaLink structure；link_identification = 具体 S1458 命题；link_implies_inclusion actual；两个 scalar fields 为 structure exact 输入。SHA 68F8478F...，olean 59792 B。
- OrigXiFPaperQPilotFromSourceLActual：给定 boundary 构造五字段 actual PaperQPilotObject 数据；qPilotLogVolume = sourceQPilotSignedLog；exact 首字段 boundary，exact q scalar identification / thetaPacket identification 仍开放。SHA F7EEABC9...，olean 147176 B。

- S1444ReportAKPlaceQActual：route A 主文件 actual，53 declarations，olean 440432 B，SHA 9DCCF5E5...；F-place/K-place/comap/q/order=e*r/valuation/norm e*f/order-normalized e/root descent/ S605 route A residual 全部落地；exact 是 K-side Tate uniformization、S605 first field、根存在、S618 不编译。此文件优先于 S1413。
- S1413 当前 EXIT=0、SHA 16FF8607...，无 olean；保留为备选。
- S1377OmegaFormulaActual：elliptic net + intermediate nonzero => x/omega formula actual；exact 首字段 S1372EllipticNetAtPoint（Mathlib EDS TODO）；remove intermediate nonzero 需 torsion detection/generic point。SHA 1D2C3E7E...，olean 存在。

## 9. 术语硬定义（以后必须按此说）

- actual / 有构造：文件中有该类型的具体 inhabitant/构造，EXIT=0，olean 存在，公理只标准三件套。回答“有”。
- proven / 有证明：该命题有 Lean 证明。回答“有证明”。
- conditional actual / 有构造器：给定明确输入 X 构造 Y；X 本身没有 inhabitant。回答“有 Y 的构造器，但没有 X 的实例”。
- exact obligation / 无构造字段：只记录了类型或命题名，没有 inhabitant，没有 proof。回答“没有；只有一个待填类型/命题”。
- exact reduction / 等价归约：证明了目标 ↔ 某缺口，或 target ↔ exact field；目标本身仍未证。

禁止只写 actual 或 exact 而不说“有/没有、有什么、缺什么”。

## 10. 当前“有/没有”清单（2026-10-31）

- S1430：有 genericX/genericY/genericPoint/equation_genericX_genericY、psi/phi/omega function fields、mulByIntX/Y、CoordinatePullback/MapsInfinity/Isogeny、conditional mulByIntPullback/Isogeny、n=1 实例；没有 EquationMulByInt、MapsInfinityMulByInt、TautologicalPointMulByInt、ker_mulByIntIsogeny_eq_torsionBy。
- S1471：只有 genericX/genericY 坐标；没有 evalEval_genericX_genericY、genericPoint。已被 S1430 覆盖。
- S1465：只有更小基础层；已被 S1430 覆盖。
- S1466：有 degree/separableDegree/inseparableDegree 及乘法关系；没有 mulByIntFunctionField、IsCoprime Phi PsiSq、Algebra.IsSeparable、PrimeKernel。
- S1444：有 route A q 图、order=e*r、valuation/norm、kernel field/l-torsion basis、根必要障碍、S605 residual 等价；没有 S605 first field、K-side Tate uniformization、2l root。
- S1463：有 ThetaLink 结构、具体 link_identification、link_implies_inclusion 证明；没有 scalar_eq 与 signedHull_le 两个字段的实例。
- OrigXiFNormalizedBridgeExact：有 N 与 O 不同命题的 obstruction、exact bridge structure；没有 uniform bridge，也没有 qScalar_eq/thetaScalar_eq 实例。
- O 层已有构造：PaperQPilotScalar、PaperSignedHull、LogKummer、Boundary/Strip、Kappa O^x(G) module、polyIso action data、route C readout、route F value-layer trace。
- O 层没有构造：PaperQPilotObject 四个 identification、vertical coricity、paper q-pilot strip identification、q mark/paper output projection、C9 marked map/final-evaluation membership。
- D8：有 cusp no-go 与 conditional norm/Haar epsilon 构造器；没有 cusp local parameter。
- HDD：有 dependent E/hull/det/region laws；没有 S1215HDDLocalLattice（缺 rank>1 localization）。

- OrigXiFPaperQPilotObjectActual：有 actual OrigXiF PaperQPilotObject 与四个具体 identification 的证明；但有两点简化：ProcessionChoice 的 Preorder 用 le:=True，lineBundle 是 completion carrier 不是 true theta line bundle。不能当最终 paper object；R13 仍无构造。SHA EE6F36EE...，olean 15760 B。
- OrigXiFNormalizedBridgeExact：有 N 目标不同命题于 O 比较的 obstruction，以及只有两个 scalar 字段的 exact bridge；没有 uniform N->O bridge，也没有两个 scalar 等式实例。SHA 7C5936AE...，olean 275328 B。

- S1467FunctionFieldPullbackActual：有 genericX/genericY/genericPoint/equation/Point.map/fieldPullback/Isogeny structure 的实际构造；没有 TauCeti MulByInt/FunctionField（[n] isogeny/tautological point/kernel subtraction）。SHA 47682248...，olean 存在。
- S1431MulByIntDegreeActual：有 finrank_functionField=2、finrank_adjoin_mulByIntX=n²、degree_mulByIntIsogeny=n²（coprimality 条件下）、sepDeg（separability 条件下）；没有无条件 sepDeg[n]=n²。SHA 0B2D2A79...，olean 待补。
- S1422HDDDetActual：有 dependent hull Haar detData，条件于 DependentProductScalingChar；没有该 character 实例。SHA DEA6FF93...，olean 待补。
- S1457 OrigXiFPaperQPilotObjectActual：有 actual QPilotObject 与四个具体 identification 的证明；但 Preorder 用 le:=True，lineBundle 是 completion carrier 不是 O(-D)。必须替换后才算完整对象。SHA EE6F36EE...，olean 384720 B。

- S1429 follow-up：有证明旧 completion-root 首字段为空（ConcreteCompletionRootObstruction 被 refute；SourcePilotRegionData IsEmpty）；因此旧 completion-valued C3 schema 不可能构造，L-side 是唯一路线。

- S1419D6NonterminalStackActual：有 actual HyperbolicOrbicurve（非 terminal、signature oncePunctured、non-point stack fiber）；没有 OrbicurveFundamentalGroupData。olean 262232 B。
- S1448ReportENormalizedNormActual：有零分支 AbsoluteValue 与条件 spectral 公式；没有 ScalarExtensionCompatibility。olean 422336 B。
- S1422HDDDetActual：有 dependent hull detData；没有 DependentProductScalingChar。olean 441536 B。
- S1479 OrigXiFPaperQPilotObjectPreorderActual：有实际 Ind3Step Preorder；lineBundle 仍是 completion carrier，不是 O(-D)。olean 384872 B。

- S1476HDDRankActual：有 actual rank-2 free arithmetic vector bundle localization，inhabit 了 S1215/S1418 首字段类型；但它不依赖 Theorem311Output，不是论文 output-dependent HDD lattice。SHA 7EA9DE70...，olean 361832 B。
- S1498KSideTateTransportActual：有 actual completionMap 与 coordinateChange.map（F-side comparison -> K-completion）；没有 realizesCurve / canonicalIsElliptic / points（exact first missing transport = realizesCurve）。SHA 5B3DB224...，olean 存在。
- S1477OScalarBridgeActual：有 scalar_eq/signedHull_le 的精确归约与充分条件（qPilotLogVolume≤-1 -> signedHull_le）；没有 O 结构 inhabitant。SHA B5294C7D...，olean 426160 B。

- S1424ThetaSectionActual：有 actual analytic theta line bundle/global section 与算术 q_v^(j^2) divisor/零除子识别；没有 source-curve geometric theta line bundle/global section（R13 仍无）。SHA B0806482...，olean 230096 B。

- S1500HDDOutputDependentActual：有 exact target structure S1500OutputDependentHDDLattice（output/place-dependent rank-2 lattice family）；没有 inhabitant，首缺是 free rank-2 lattice 与 S1402 image 的实际绑定。未用 output-independent lattice/constant unit image 冒充。SHA 1602D93E...，olean 383424 B。

- S1501/S1505：有证明的负面结果：rational tensor RatT ⊗_Q Q_p 与 SourceBlk 之间不存在 Q_p-linear equivalence（RatT 是无限维 Q_p，SourceBlk 有限维）。正确比较只能是 canonical surjective map（带 kernel/quotient）或 integral lattice-level comparison。不要声称 equivalence。

## 11. 禁止再用 exact 一词

以后报告一律不用 exact。按下面说：

- constructed / 有构造：Lean 中有具体 inhabitant。
- proved / 有证明：命题已证。
- missing / 没有构造：只有类型或命题名，没有 inhabitant。
- unproved / 没有证明：命题未证。
- conditional constructor / 条件构造器：给输入 X 能造 Y，X 没有实例。
- reduction / 等价归约：证了目标 ↔ 缺口；目标本身仍未证。

旧文中的 exact 一律读作“没有构造/没有证明/待填缺口”，不得读作“精确已完成”。

## 12. English status labels (authoritative)

Use only these labels from now on:

- [BUILT] concrete inhabitant/construction exists in Lean.
- [PROVED] the proposition has a Lean proof.
- [MISSING] only a type or proposition is recorded; no inhabitant exists.
- [UNPROVED] the proposition has no proof.
- [CONDITIONAL] a constructor from explicit input X to output Y exists; X has no inhabitant.
- [REDUCTION] target is proved equivalent to a missing gap; target itself is still unproved.

Do not use ambiguous status words. Say what exists and what does not.

- S1491NormEDSNetActual: [BUILT] IsEllipticNet.normEDS, IsEllipticNet.of_even_odd, rel3_normEDS, rel3_special_normEDS, isEllipticNet_ψ, isEllipticNet_evalEval_ψ; [PROVED] all; olean 5141080 B. This removes the EDS-net blocker for S1377/S1481.
- S1495IsogenyKernelActual: [BUILT] translationFixingSubgroup and Isogeny.ker; [PROVED] n=1 kernel equality; [CONDITIONAL] general n equality on TautologicalPointMulByInt; [MISSING] that input. olean 1020280 B.
- S1503SourceNativeBridgeActual: [BUILT] NativeBridgeExact/NativeInputBridgeExact definitions and donorOfBridge conditional constructor; [MISSING] NativeInputBridgeExact inhabitant; no fake native donor. olean 16688 B.
- S1502DependentScalingCharActual: [PROVED] character from product scaling measure; [MISSING] S1502ProductScalingMeasure / local prime scaling / product Haar decomposition; [UNPROVED] DependentProductScalingChar. olean 78448 B.

- S1487OQPilotScalarEqualityActual: [PROVED] scalar_eq holds for faithful one-place bad family; two/multi-place bad family gives actual counterexample and no OrigXiFThetaLinkActual inhabitant; for S1280 Gaussian single bad place reduces to order_bad = order_C3. SHA 4A0D0DAF..., olean 591240 B.
- S1475ReportCExactInputsActual: [PROVED] S1086Q1URegionMeasurable unconditional; S1086Q1UImageContainment reduces to qPilotQ1URegion subset paperLambdaORegion -> S1087CoeffLe; S863 follows from S841PointwiseAbsorption. [MISSING] S1087CoeffLe. SHA 8AA83A4F..., olean 455968 B.

- S1524PlaceCompletionComparisonActual: [BUILT] placeAbove v / comap / completionComparison v→w; [MISSING] section evaluation R→Completion v. Structural issue: S1423 module is over F, target Completion v is over Fmod; S1504/S1423 cannot fill QPilotObject.lineBundle over Fmod. Native donor route (S1494/S1532) is the viable lineBundle route. SHA 48A8B777..., olean exists.

- S1554SignedHullFromQActual: [PROVED] signedHull_le with no missing inequality; [BUILT] OrigXiFThetaLinkActual for arbitrary O and actual signed-hull D, conditional only on S1527 input R : S1280RemainingClauses l (D5-D9 explicit params) and D9 compat Props. No native lineBundle D. olean 136384 B, SHA 8680F77B...
- S1545CorrectedGaussianKLiftActual: [BUILT] s1545CorrectedK from GaussianTorsionBasis b and hlarge : SL2 ≤ range; K=gaussianKernelField b, kernelField ≠ ⊥, finrank ≠ 1, 2 ≤ finrank. Conditional on b/hlarge. SHA A1DDEE5C...

- S1484ThetaObjectActual: [BUILT] actual curve divisor carrier, puncture divisor, theta line bundle = inverse S1423 line bundle, nonzero section, zero divisor [P], simple zero, affine/infinity split; [MISSING] geometric theta divisor {q_v^(j^2)} and identification with [P]. SHA CF87AE24..., olean 571920 B.
- S1577CuspPsiEvalActual: [PROVED] polyEvalCusp psi_n=n, ringEvalCusp, polyToField psi_n != 0 for n != 0; S1569 corrected affine recursion unconditional. SHA 087C2733..., olean 304200 B.
- S1567AbsNormNatGeneratorActual: [PROVED] Ideal.absNorm=natGenerator, S1087CoeffLe. SHA ADE25099..., olean 62712 B.
- S1554SignedHullFromQActual: [PROVED] signedHull_le; [BUILT] R -> OrigXiFThetaLinkActual; R=D5-D9 missing. SHA 004234E4..., olean 136384 B.
