# SURVEY-qpilot — 现有资产调研：Theta/EtTh 与 AbsTopIII 前置对象（IUT 3.12）

Read-only survey for Lead A469/A470; no Lean written here, no node ownership changed.
Sources: coord/REPO-ROUTE-INDEX.md, coord/repo-route-index-data.json,
coord/uncovered-leanformal-triage.qpilot.tsv, dag/declaration-dag.json,
dag/THEOREM-DAG.md, coord/target-chain.iut-pre-abc.json,
coord/target-chain.theta-etth.json, coord/skeleton docs, LeanFormal tree.

Evidence notation: OLEAN_FRESH = tree olean present per REPO-ROUTE-INDEX;
EXIT0 = last EXIT=0 row in tmp/xif_guarded_results.log; CITABLE = EXIT0 + fresh olean +
probe axioms subset [propext, Classical.choice, Quot.sound].

## 1. Paper prerequisite objects (my region: Theta/EtTh pre-objects + AbsTopIII 01/02/05)

| # | paper object (source) | needed-for (Cor 3.12 path) | existing Lean (file : declarations) | evidence | existing DAG node id(s) | status |
|---|---|---|---|---|---|---|
| 1 | Initial Theta data + Def 3.1 clusters (IUTchI) | theta-link input | LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean, SourceDefinition31RootLemmas.lean | OLEAN_FRESH | iut-pre-abc:InitialTheta.data, iut-pre-abc:InitialTheta.definition31 | TREE_ASSET |
| 2 | Concrete initial-theta C-stage (Example 3.2/3.6 link) | theta-link assembly | LeanFormal/IUT/IUTII/Theta/ConcreteSourceEtaleThetaBridge.lean:cStage | OLEAN_FRESH | iut-pre-abc:InitialTheta.cStage, iuti-ii:IUTII.Theta.ConcreteBridge | TREE_ASSET |
| 3 | Theta-link procession/assembly | theta-link | LeanFormal/IUT/IUTII/Theta/ThetaLinkAssembly.lean | OLEAN_FRESH | iut-pre-abc:ThetaLink.procession, iut-skeleton:Thetas | TREE_ASSET |
| 4 | Etale theta quotient / power kernels / mod-l | theta group quotients | LeanFormal/IUT/IUTII/Theta/EtaleThetaQuotient.lean | OLEAN_FRESH | iut-pre-abc:ThetaLink.quotient, theta-etth:E1 | TREE_ASSET |
| 5 | Odd theta series q-expansion/signs/terms | absolute theta data | LeanFormal/IUT/Foundations/Theta/OddTheta*.lean | OLEAN_FRESH | theta-etth:T1,T2,T3,T4 | TREE_ASSET |
| 6 | Gaussian kernel / Gaussian square sum / signed labels | Gaussian/LGP | LeanFormal/IUT/Foundations/Theta/OddThetaTermAlgebra.lean etc. | OLEAN_FRESH | theta-etth:T5, iut-skeleton:Gaussian | TREE_ASSET |
| 7 | Absolute theta data (Θ-pilot absolute theta function data) | theta-pilot carrier | no single Lean object: anchors (5)+(6)+Example36 analytic theta carrier | PARTIAL | theta-etth:T1-T5/E5, theta-etth:X1 | GAP (no absolute theta data carrier) |
| 8 | Gaussian/LGP compatibility (θ×log compatibility) | q-pilot/theta-pilot comparison | no compatibility theorem; Gaussian examples + Hodge theater concrete | PARTIAL | iut-skeleton:Gaussian, iut-pre-abc:HodgeTheater.concrete, theta-etth:T5 | GAP (no LGP compatibility theorem) |
| 9 | Theta-pilot IQ containment (source theta pilot) | theta-pilot | LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment.lean | OLEAN_FRESH | iut-pre-abc:Gap.thetaPilotIQContainment, iuti-ii:IUTII.Kummer.SourceThetaPilot, theta-etth:TPI | TREE statements, paper-level NAMED |
| 10 | Theta-pilot precise carrier (X-mu packet) | theta-pilot precision | LeanFormal/IUT/IUTII/Kummer/SourceLogShellXMuPacket.lean | OLEAN_FRESH | iut-pre-abc:ThetaPilot.carrier | NAMED (precision gap) |
| 11 | q-pilot object / arithmetic divisor degree | q-pilot | LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotBaseChange.lean; IUTIV/Estimates/ArithmeticDivisorDegree.lean | OLEAN_FRESH | iut-pre-abc:QPilot, QPilot.arithmeticDivisor | GAP (precise construction) |
| 12 | EtTh ten class-B deep inputs | EtTh realization | tmp/sheaf/xif/paper/EtTh02DeepInputsActual.lean (statement rows) | EXIT0 (statement only) | iut-pre-abc:Gap.etthDeepInputs, theta-etth:EDA | NAMED |
| 13 | EtTh geometric realization of theta groups (EtTh row 5) | EtTh class-B | no proof; conditional consumer bundle | EXIT0/CITABLE (consumer conditional) | e-deep:E4.etthConsumer, e-deep:E4.etthGap, theta-etth:R2 | CONDITIONAL/NAMED |
| 14 | EtTh Frobenioid-theoretic manifestation (EtTh row 6) | EtTh class-B | no proof; Example36 boundary + row-6 carrier package | EXIT0 (carrier-level) | theta-etth:P58R, theta-etth:ETR, theta-etth:X1 | NAMED (carrier-level conditional) |
| 15 | EtTh actual theta transformation (EtTh row 7) | EtTh class-B | no proof | statement rows only | theta-etth:ETR | NAMED |
| 16 | AbsTopIII01 log-shell/log-Frobenius objects | log-shell transfer | LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean; SourceLogShellAbsTopIIIBridge.lean; Example36LogShellFrobeniusAction.lean | OLEAN_FRESH | iut-pre-abc:LogShell.I, LogShell.logFrobenius, KummerLogShell.bridge; theta-etth:A1 | TREE_ASSET/PROVED |
| 17 | AbsTopIII02 Gaussian/theta convolution objects | theta convolution | no dedicated Lean object; partial anchors (6)+(8) | PARTIAL | theta-etth:T5, iut-skeleton:Gaussian | GAP |
| 18 | AbsTopIII05 Prop 5.8(i) anabelian reconstruction | anabelian reconstruction | our P58i concrete layer: tmp/.../Mzk1Prop58iConcreteActual.lean, Mzk1AbsTopIII05RefinedConcreteActual.lean, Mzk1Prop58iTargetActual.lean, Mzk1P58iInvariantsAlgorithmActual.lean | EXIT0 (serial+watchdog); CITABLE for P58I/P58II files | iut-pre-abc:Gap.absTopIII58_55, theta-etth:P58I,P58IC,P58IT,P58ALG | CONDITIONAL (named group-theoretic algorithm) |
| 19 | AbsTopIII05 Prop 5.8(ii) Gamma^x_non diagram | anabelian reconstruction | tmp/.../Mzk1Prop58iiDiagramActual.lean, Mzk1P58iiDiagramRowsActual.lean, Mzk1P58iiVertexArrowsActual.lean, Mzk1P58iiBridgeRowsActual.lean, Mzk1P58iiCMLFActual.lean, Mzk1P58iiCMLFImageActual.lean | EXIT0/CITABLE (P58II); CMLF image pending retry | theta-etth:P58,P58IDR,P58VA,P58BR,CMLF,CMLFI | CONDITIONAL (paper CMLF categories/Γ^x_non NAMED) |
| 20 | AbsTopIII05 Cor 5.5 D^bullet diagram | global/panalocal compatibility | tmp/.../Mzk1P58iiCor55RowsActual.lean, Mzk1Section0Saturated*.lean | EXIT0 (C55D/SAT/SATS; SATC pending) | theta-etth:C55D,P58BR,SAT,SATS,SATC | CONDITIONAL (D^bullet construction NAMED) |
| 21 | Section-0 oriented graphs/order/path-pair combinatorics | Section-0 pre-objects | tmp/.../AbsTopIII05Section0ObjectsActual.lean, Mzk1Section0LinearGraphActual.lean, Mzk1Section0CountablyOrderedActual.lean, Mzk1Section0SaturatedActual.lean | EXIT0/CITABLE (A445 31 decls) | iut-pre-abc:Section0.*, iut-skeleton:Section0, theta-etth:A5 | CONDITIONAL/PROVED |
| 22 | Log-shell / theta carrier compatibility (theta-link log-shell) | theta carrier transfer | partial: KummerLogShell.bridge + our IKT/CMLF image functoriality | EXIT0 (IKT/CMLF; CMLFI pending) | iut-pre-abc:KummerLogShell.bridge, theta-etth:IKT,CMLF,CMLFI | CONDITIONAL |
| 23 | IUTIII StepXI theta-packet bridge + muN quotient | IUT III linkage | LeanFormal/IUT/IUTIII/Corollary312/StepXI/ThetaPacketBridge.lean, SourceLogShellMuNQuotientCarrier.lean | OLEAN_FRESH | iutiii:IUTIII.STEPXI.THETA_PACKET_BRIDGE, LOGSHELL_MUN; theta-etth:I1,I2,I3 | TREE_ASSET |

## 2. Summary (for Lead)

- paper prerequisite objects listed: 23
- with existing Lean asset (tree or our EXIT0/CITABLE layer): 19/23
- reused existing DAG node ids: 30+ over iut-pre-abc (17), theta-etth (15+), iut-skeleton (5), e-deep (3), iutiii (2), iuti-ii (4)
- true gaps (new nodes needed; see coord/target-chain.iut-pre-qpilot.json):
  QP.absThetaData (absolute theta data carrier), QP.gaussianLGP (Gaussian/LGP compatibility),
  QP.absTopIII02Convolution (AbsTopIII02 object), QP.logShellThetaCarrierCompat (log-shell/theta
  carrier compatibility), QP.etthRow5/6/7 (EtTh class-B paper-level proofs),
  QP.absTopIII05Prop58i/ii, QP.absTopIII05Cor55 (paper-level aggregation over existing local
  nodes; no new mathematics claimed).
- No GATE change; binding HOLD; registry 14041; no new axiom/sorry.


## 3. A475 exhaustive-search evidence (repo-wide, read-only; no "needs breakthrough" claims)

Search scope: LeanFormal/ (whole tree), tmp/ (tmp/sheaf incl. xif/paper; tmp/external incl.
promachina-iut-lean and flt-lean; excluding .lake/.git/n8-*), papers/motizuki_corpus/, coord/,
dag/; 111,559 text files scanned by keyword (case-insensitive, multi-term variants).

| keyword | files with hits | found/reuse conclusion |
|---|---|---|
| absolute theta / absoluteTheta | 9 / 26 | **found**: tmp/external/promachina-iut-lean/Iut/Foundations (IUTIIAbsoluteThetaLabel, SourceTheorem311, SourceHodgeArakelovEvaluation) — reuse as external anchor |
| theta-pilot / thetaPilot / ThetaPilot | 678 / 1056 / 1056 | **found**: LeanFormal/IUT/ABCBridge/Bridge + IUTII/Kummer + tree ThetaPilotCarrier; reused via tree assets |
| q-pilot / qPilot / QPilot | 1511 / 2865 / 2865 | **found**: LeanFormal/IUT/ABCBridge/Geometry + IUTIII/Corollary312/ArithmeticQPilot*; reuse anchors |
| HTLink | 12 | **found**: tmp/sheaf/xif/paper/Mzk1HodgeTheaterLinkLawsActual.lean (HTLink structure) |
| Gaussian / LGP | 2210 / 2200 | **found**: tree Foundations/Theta/Gaussian* + IUTII/Kummer/LGP/packet assets; reuse |
| CMLF | 46 | only our P58ii CMLF files + logs/sweep; **no standalone upstream CMLF formalization found** (repo currently lacks it; adapt = P58iiCMLF model + CMLF2) |
| Gamma^x_non / gammaXNon | 28 / 4 | found only in AbsTopIII05* statement/refined files (paper-level); no construction found |
| theta convolution | 28 | found only in our Mzk1AbsTopIII02ThetaConvolutionActual + paper link list; no upstream formalization |
| schemeSideMaps | 20 | **found**: tmp/sheaf/xif/paper/Mzk1SchemeSideMapsActual.lean (existing asset) |
| sectionMap / placePoint | 110 / 53 | found tree InitialTheta Definition31* etc. (existing assets) |
| ProblemDApplicability | 4 | **found**: tmp/sheaf/xif/paper/Mzk1ProblemDApplicabilityActual.lean (existing, currently EXIT1) |
| fixedBetaChoice / f4b / numMaxP | 2 / 11 / 0 | fixedBetaChoice only DAG node json; f4b only S3135/S3137 assets + ledger logs; numMaxP 0 hits in repo text |

Reuse actions taken (A475):
* stage-4 schemeSideMaps, IUT IV §1->§2, R9 audit, H7/Ob9: existing assets found ->
  our duplicate named-input helpers were deleted (not registered); created
  Mzk1IUTIVReuseIndexActual.lean which re-uses the only EXIT0 asset
  (Mzk1IUTIVSec1Sec2GapActual) and records the remaining existing files as anchors
  (their oleans absent at this revision, not re-imported).
* absolute theta / theta-pilot / q-pilot / Gaussian / LGP: existing assets found ->
  our carrier files are glue over them (no duplication), as noted in fragment nodes.
* CMLF / Gamma^x_non / theta convolution: repo-wide search found no upstream formalization
  (0 standalone objects) -> adapted minimal model files (P58iiCMLF, CMLF2,
  AbsTopIII02ThetaConvolution); recorded as "repo currently missing (with search evidence)",
  NOT as needing a mathematical breakthrough.

## 4. A475 cross-region reuse (skeleton/hull/stage4/target) — search + actions

Additional exhaustive searches (same scope, 111,559 files):

| term | hits | action |
|---|---|---|
| HDD | 111 files | found Mzk1HDDObjectActual (no olean -> adapted copy Mzk1HDDObjectAdaptedActual) + S1215/S1238/S1154 olean assets -> Mzk1SkeletonHDDReuseActual |
| hCor312 / hSlack / Sources1995_2015 | 0 / 0 / 0 | repo currently missing (0-hit snapshot); skeleton DEF categories only, no upstream asset to reuse |
| schemeSideMaps / IUT IV Sec2 / R9 audit / H7-Ob9 | existing tmp interfaces (no oleans for some) | adapted copies created: Mzk1{ SchemeSideMaps, IUT4Sec2Interface, R9AuditConsumer, H7Ob9Interface }AdaptedActual (A475 "copy old file into new file" rule) |
| ABCBridge target | tree oleans | Mzk1IUT312TargetReuseActual re-exports ABCConjecture/cor312ToABCBridge_heightBound/ABCFrontier |

No "needs mathematical breakthrough" wording; all remaining skeleton names (hCor312/hSlack/Sources1995_2015) recorded as repository-missing with 0-hit evidence.


## 5. A477 只读资产清单（file:declaration；仓库已有/无）

Search scope (read-only): LeanFormal/, tmp/sheaf/xif/paper/, tmp/external/promachina-iut-lean/
(plus earlier full-repo keyword scans). 78 candidate declarations checked; 78 present (6 initial
misses were name-case/typo and corrected). No Lean written, no fragment/extra-targets change.

### 5.1 Theta series / Gaussian / labels — 仓库已有
- GaussianKernel: realThetaValue, gaussExponent, thetaValue, thetaValue_eq_of_eq_neg
- GaussianSquareSum: gaussianSquareSum, gaussianSquareSum_formula, normalizedGaussianDegree, normalizedGaussianDegree_eq_factor
- OddTheta / OddThetaShift / OddThetaShiftSum / OddThetaTermAlgebra / OddThetaNegativeDecay / OddThetaNormalization / OddThetaNonvanishing: oddTheta, oddThetaTerm, oddThetaSign, oddThetaExponent, oddThetaShiftCoefficient, oddTheta_shift, oddThetaFraction_eval(_unconditional), oddTheta_ne_zero_at_i, oddThetaTerm_shift(_inv)
- SignedLabelEquiv: SignedLabel, translate, sum_translate, card_signedLabel, equiv/translate laws

### 5.2 Example36 analytic theta / correspondence — 仓库已有
- Example36SourceThetaGenerator: AnalyticThetaCarrier, analyticThetaQExpansion, analyticThetaCarrierConcrete, gaussianFiveThetaQ
- Mzk1Example36EtThCorrespondenceActual: Example36EtThCorrespondence, etthExample36_qExpansion_eq_kernel, etthExample36_concrete_q, example36EtThCorrespondence_nonempty
- Example36LogShellFrobeniusAction: principalUnitFrobenius, principalUnitLogShellFrobenius, example36LogShellFrobeniusAction_summary

### 5.3 Theta-link / theta-pilot — 仓库已有
- IUTII/Theta/EtaleThetaQuotient: ThetaQuotient, thetaToElliptic, thetaPowerKernel, ellipticPowerKernel, modLThetaProjection, thetaCommutatorKernel_le_derivedSubgroup, thetaCenter_le_center
- IUTII/Kummer/SourceThetaPilotIQContainment: sourceLogShellTensorGenerator, sourceThetaPilotProductMap, sourceThetaPilotIQPacket, possibleImage_subset_of_generator_mem
- IUTII/Kummer/SourceLogShellXMuPacket: SourceLogShellXMuChainSupply, chainEquiv_image_logShell, left/right_packet_map
- StepXI/HolomorphicHull/SourceImageHull: ThetaPilotCarrier
- external promachina: IUTIIAbsoluteThetaLabel (SourceThetaEvaluation.lean), SourceIUTIIHodgeArakelovThetaPilot (SourceHodgeArakelovEvaluation.lean), SourceTheorem311LocalData (SourceTheorem311.lean)

### 5.4 Kummer / log-shell — 仓库已有
- AbsoluteKummerInjection: absoluteKummerMap, absoluteKummerMap_eq_one_iff
- AbsoluteKummerContinuity: isLocallyConstant_absoluteKummerMap, continuous_absoluteKummerMap
- AbsoluteKummerQuotient: absoluteKummerMapQuotient_injective, nthPowerSubgroup
- SourceLogShellCarrier: SourceLogShellDatum, pStar, pStar_pos, preLogShell, unitLayer, logShell, preLogShell_subset_unitLayer
- SourceLogShellAbsTopIIIBridge: SourceLogShellInvariantImageIdentification, invScaledUnitLayer, logShell_eq_invScaledUnitLayer_of_invariantImageIdentification, codomainKummerContained_of_invariantImageIdentification, sourceLogShellCalibration_invariantImageIdentification
- MonoAnalyticLogShellCompactCarrier: preLogShell/unitLayer/logShell variants

### 5.5 AbsTopIII05 / Section-0 — 仓库已有
- AbsTopIII05ReconstructionInputsActual: absTopIIIDeepInputs (4 kinds)
- AbsTopIII05RefinedActual: Prop58iLocalFieldReconstruction, Prop58iiLogShellReconstruction, Cor55LogFrobeniusCompatibility, OrientedGraphAnabelianData
- Mzk1Prop58iiDiagramActual: NonDiagramModel, Prop58iiNamedInput, Cor55DiagramRow, cor55DiagramRows
- AbsTopIII05Section0ObjectsActual: OrientedGraph, CountablyOrdered, OrderwiseConnected, PrePath, IsSaturatedPathPairSet, frobeniusPictureGraph, Cor55L/Ldagger
- Mzk1FrobeniusGraphAutClosureActual / Mzk1ChainTranslationLawActual: FrobeniusPictureGraphAut_inv/_mul, chainTranslation_add

### 5.6 EtTh — 仓库已有
- EtTh02DeepInputsActual: EtTh 10 deep-input statements
- EtTh05FrobenioidBoundaryActual: etThFrobenioidBoundary
- EtTh11ThetaRealizationRowsActual: etTh11_thetaPowerKernel_mono, etTh11_ellipticPowerKernel_mono, 7-row realization record

### 5.7 StepXI / QPilot — 仓库已有
- ThetaPacketBridge: toPositivePacket, toPositivePacket_logVolume_eq_sum, _log_det, _positive, _neg_invariant
- SourceLogShellMuNQuotientCarrier: muNQuotient, muNQuotientMap_surjective, weightNLog, weightNLog_pow, muNPowEnd
- APT/IPL/SHE + CertificateHullWiring(Realization) + HullDeterminantLogVolumeReduction
- ArithmeticQPilotBaseChange/GlobalNormalization/LogVolume: qNorm_pos, qNorm_lt_one, localSignedLog_neg, localLogMagnitude_pos, localSignedLog

### 5.8 真缺失短清单（仓库现有资产未覆盖的证明/构造；均有搜索证据）
1. CMLF_TS/CMLF_TF paper categories themselves（仅有具体模型 CMLFHom；无上游形式化）
2. Gamma^x_non diagram 构造（仅有 statement/model skeleton：AbsTopIII05ReconstructionInputs/Refined + 有限 NonDiagramModel）
3. AbsTopIII05 Prop 5.8(i) group-theoretic reconstruction algorithm（有 concrete invariants/target/conditional input，无算法本体）
4. AbsTopIII05 Cor 5.5 D^bullet seven-row global/panalocal 构造（有 L/L† 模型与行数据骨架）
5. AbsTopIII02 convolution theorem（仅有有限 Gaussian 卷积模型）
6. EtTh 十个 class-B deep inputs 的证明（仅有 statement rows / anchors）
7. EtTh realization rows 5-7 证明（geometric realization / Frobenioid manifestation / theta transformation；仅有 carrier/conditional 骨架）
8. absolute theta data 的统一 paper 对象（仅有分量：AnalyticThetaCarrier/oddTheta/InitialTheta + external labels）
9. theta-pilot precise 对象构造与 N4-N7 source-to-arithmetic comparison（仅有 components/containment/X-mu packet）
10. q-pilot precise 对象构造（仅有 arithmetic base-change/log-volume/normalization components）
11. log-shell/theta carrier compatibility paper-level（仅有 model-level CMLF image laws）
12. IUTchIII Cor 3.12 顶层 assembly/target（DAG target node GAP；仅有 T0/T1/T3 bridge/frontier 接口）

DAG（只读）：validation ok=true, problems=0, conflicts=0.


## 6. A477 olean 资产 → DAG 映射（只读扫描；未改 fragment）

Read-only scan: existing olean assets whose path matches my-area keywords (theta|etth|kummer|hull|
abstopiii|stepxi|qpilot|hodge|froben|gaussian|signedlabel|logshell|section0), mapped against
ALL fragment nodes' files arrays.

- candidates: **1655** olean assets (LeanFormal 444, tmp/sheaf/xif/paper 1211, tmp/external 0 with olean)
- mapped to an existing DAG node: **319**
- unmapped: **1336**
- by category (total/mapped): theta 659/83, kummer+logshell 192/52, etth 45/19,
  abstopiii+section0 59/19, hull 311/41, stepxi/qpilot 217/40, other 172/65.

Priority unmapped assets in my core region (sample; full list in tmp/qpilot_a477_mapping.json):


Constraint note (A477 pause): no new nodes/new Lean; therefore the 1336 unmapped olean assets
are recorded read-only here; mapping them into the DAG would require either (a) adding them to
existing nodes' files (fragment edit) or (b) new tree-asset nodes — both paused by A477, pending
Lead decision. True missing (proof/construction) list stays §5.8 (12 items).


### 6.1 Core-region mapping detail (read-only)
Core candidate set (Foundations/Theta, IUTII/Kummer, IUTII/Theta, IUTI/InitialTheta,
IUTI/HodgeTheater, IUTII/Frobenioid/Example36 tree files + theta/etth/kummer/abstopiii/
gaussian/signedlabel tmp-paper files), with olean present:
- candidates: **944**
- already mapped to an existing DAG node: **195**
- unmapped: **749** (priority list: tmp/qpilot_a477_core_unmapped.json)

Unmapped assets are mostly tree InitialTheta/HodgeTheater submodules (ArithmeticData,
ConcreteInitialTheta*, Definition31D2/D4*, HodgeTheater History/LinkVolumeTransport/
PrimeStripCore/LocalPrimePlaces) and tmp theta/EtTh helper files. Under A477 pause these are
NOT added to the DAG (that would require fragment edits or new tree-asset nodes). Recorded
read-only; decision pending Lead.


### 6.2 Dependency-closure + heuristic DAG mapping (read-only, A477)

Computed via import closure of all existing DAG node files (1,092 existing node files →
dependency closure 1,995 repo files), against core-region unmapped olean assets:

- core unmapped assets: **749**
- covered already by the DAG dependency closure (imported transitively by a DAG node file): **144**
- not reachable: **605**
- of those 605, heuristic token mapping finds an existing DAG node target for **all 605** (needs
  semantic review; no new node/fragment changes were made under A477 pause). Top targets:

  - e-deep:E1.absTopIII05Inputs: 385
  - hull:PRE.IUTII.KUMMER.STATEMENT: 86
  - e-deep:E1.absTopIII05Refined: 38
  - e-deep:E4.etthConsumer: 27
  - hull:PRE.IUTII.PILOTS.STATEMENT: 26
  - e-deep:E4.example36: 20
  - hull:PRE.THETAPILOT.CONSTRUCTION.STATEMENT: 15
  - e-deep:E1.logShellBridge: 4
  - e-deep:iuti-source-def31-dual-alignment: 2
  - hull:PRE.IUTI.INITIALTHETA.STATEMENT: 1

Machine-readable mapping: tmp/qpilot_a477_fullmap.json (withTargetList/noTargetList).
True missing (proof/construction) remains §5.8 (12 items); the 605 are existing olean assets to
be attached/mapped by an owner decision, not missing mathematics.
