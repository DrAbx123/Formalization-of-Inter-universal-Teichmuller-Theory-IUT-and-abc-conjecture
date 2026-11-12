# MASTER SKELETON — IUT 3.12 → ABC: chain, layers, nodes, last mile, coverage
(mainline 主笔, Lead A429; intake register preserved below; no proofs, no gate edit)

Gate anchor: canonical V150@18248/CFC6CE08 (+v151-v157); GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041 / record 18800; C/D/E rows EXCLUDED from gate (A409/A410/A414).

## 1. FINAL CHAIN (bottom-up; status marked)
```
ABCConjecture (ABCBridge/Statement.lean:32 def; plus abcConjecture_iff_* equivalences)
  ^ [PROVED FROM interface]
cor312ToABCBridge_abcConjecture (ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:446 theorem)
  ^ [PROVED from height bound]
cor312ToABCBridge_heightBound (same file; heightWeightBound_of_normalizedVolumeComparison)
  ^ [CONDITIONAL on interface fields]
Cor312ToABCBridgeInterface (same file; structure: hullData + epsilonComparison delta hdelta fields)
  ^ [CONDITIONAL routes]
concrete bridges: ABCFrontier (ABCBridge/Bridge/ABCFrontier.lean:187 def; bridgeInterface_of_frontier:199; abcConjecture_of_frontier:213; ABCFrontierRealLine:259/reduce_realLine:268)
  + S3131PaperRouteSkeletonActual (3584B: PaperRouteResidualData:31, comparisonOfResiduals:45, bridgeOfResiduals:57, abcConjecture_of_paperRouteResiduals:66)
  + S3131PaperRouteABCBridgeActual (1057B: paperRouteABC_of_families:18) + HeightReduction/RegionReduction/FieldStatements/ComparisonIn variants
  ^
IUT IV sec1 display / comparison (S3171IUTIVSection1DisplayActual (6921B; thm110_final_display) + Statement/Estimates/Inputs + S3171UniformHeightConsumer)
  ^ [CONDITIONAL on (b) UndilatedHeightBound and (c) UndilatedRegionBound]
IUT IV estimates (LeanFormal/IUT/IUTIV: Section1 13808B, Section2 27185B, ArithmeticDivisorDegree 94950B, Different* 13417/11364/7327B, Archimedean* 17650/29837B, StepV* 3183/12974/6482B)
  ^
Corollary 3.12 target (S2717Cor312FullTargetActual: S2717UpperGap:81, PaperCor312Full:103, S2717_full_iff_hupper:185) + StepXI consumers (Corollary312 90 files incl StepXI 83; Cor312ComparisonGapReduction:306; Cor312CarrierRealizationSpec 34057B)
  ^
IUT III Theorem 3.11 assembly (Theorem311/SourceTheorem311Assembly 54529B: SourceTheorem311Layers:47, assemble:60, t1_recovered:81/t2:85/t3:89, output_recovered:93; 100 files in Theorem311)
  ^ [CONDITIONAL on source P1P2 bundle, H1/H2, LGP, etc.]
IUT I/II + Foundations objects: Hodge theater (IUTI 69), Frobenioid/EtTh/log-shell (IUTII 194), theta analytic/log-shell/RR (Foundations 539)
```
Parallel rational-component route (Mzk1 2.x, gate L4): B1 fold PROVED -> B2 finite-beta base PROVED -> B3 rational 2.4 target PROVED -> C degree/measure PROVED + BaseCaseProvider PROVED (StepProvider' named) -> B5 Lemma2.3 rational/Moebius PROVED; D-BASE + D-RR PROVED (bridge/finite-map named); H6 precise PROVED (GenEll15 precise existence named). This route feeds the GenEll/Thm2.5 wiring (HOLD) and is NOT yet connected to the Cor312->ABC chain above.

## 2. LAYERED GRAPH
| layer | contents | file count | key files/objects | gaps |
|---|---|---|---|---|
| L0 Foundations | log/function field/RR/theta analytic | 539 | LogShellFrobeniusPower/Consumer/General/P2Boundary; Foundations/Theta (10 files: OddTheta q-series/Nonvanishing/Kernel); Foundations/AlgebraicGeometry (QlTheta series, units, etc.); RR via flt_core (Mzk1RRProvedActual 4757 B3A67DEE probe_ok) | build gaps OddThetaNegativeDecay/TermAlgebra, AbsoluteKummer*/SourceThetaPilotIQContainment; most tree assets not re-checked |
| L1 IUT I Hodge theatre | 69 | HodgeTheater/SourceThetaLinkGraphAutomorphismReduction etc.; Frobeniod links at IUTII boundary | interface-level; no full Hodge-theater construction |
| L2 IUT II Frobenioid/EtTh/log-shell | 194 | EtaleThetaQuotient, FiniteThetaPacket, ThetaLinkAssembly, SourceLogShellCarrier, SourceLogShellAbsTopIIIBridge (24 decls), Example36* (19374/50169B), Kummer/log-shell analytic family | Prop 5.8(i)(ii)/Cor5.5 algorithm parts named; EtTh02 10 deep named; EtTh11 rows5-7 named |
| L3 IUT III theta-hull/StepXI/Cor312/Theorem311 | 190 (Cor312 90, StepXI 83, Theorem311 100) | SourceTheorem311Assembly (conditional); HullDeterminantLogVolumeReduction (34929B, matrixLogDet laws); CardAMPLThetaBoundSupply (hull<=theta); Cor312ComparisonGapReduction:306; S3131*/S3171* xif deliverables | Cor312 ⇔ S2717UpperGap (S2804); assembly depends on named source layers |
| L4 IUT IV estimates | 14 | Section1/2, ArithmeticDivisorDegree, Different tower, Archimedean tensor metrics, StepV averages | (b)/(c) named; no final uniform inequality |
| L5 ABCBridge | 164 (Bridge 18, Geometry 123) | Statement.lean:32 ABCConjecture; Cor312ToABCBridgeInterface (446); ABCFrontier + Reductions/PointwisePremise/Singleton/HeightWeightRefutation; ABCResidue/Discriminant geometry | interface fields unproved; concrete D construction absent |
| xif paper deliverables | 12165 .lean files (paper dir) | n/a | Mzk1 2.x bottoms, restated interfaces, gate tables, E/Foundation inventories, audit files | thousands not individually mapped; see coverage |

## 3. NODE TABLE (selected; full map in coord/E-EXISTING-CLOSURE-MAP.md + FOUNDATION-FIRST-PLAN.md)
| id | node | Lean file:decl | status | deps | consumers |
|---|---|---|---|---|---|
| N0 | ABCConjecture | LeanFormal/IUT/ABCBridge/Statement.lean:32 | DEFINED (statement; equivalence lemmas) | ABCInequality | final target |
| N1 | cor312ToABCBridge_abcConjecture | Cor312ToABCBridgeInterface.lean:446 | CONDITIONAL PROVED (from heightBound + equivalence) | N2,N0-equivalence | final target |
| N2 | cor312ToABCBridge_heightBound | Cor312ToABCBridgeInterface.lean (heightWeightBound_of_normalizedVolumeComparison) | CONDITIONAL PROVED | N3 | N1 |
| N3 | Cor312ToABCBridgeInterface (fields hullData/epsilonComparison) | same file structure | NAMED interface | hull/log-volume objects | N2 |
| N4 | ABCFrontier / bridgeInterface_of_frontier / abcConjecture_of_frontier | ABCBridge/Bridge/ABCFrontier.lean:187/199/213; ABCFrontierRealLine:259/reduce_realLine:268 | CONDITIONAL reductions PROVED | N3; IUT IV (b)/(c) | N1 |
| N5 | Paper-route residual bridge | S3131PaperRouteSkeletonActual:31/45/57/66; S3131PaperRouteABCBridgeActual:18 | CONDITIONAL route PROVED | N4 residual families | N4 |
| N6 | Cor312 target ⇔ upper gap | S2717Cor312FullTargetActual:69/81/103/185 | CONDITIONAL equivalence PROVED | hull/log-volume objects | N5 |
| N7 | IUT IV display | S3171IUTIVSection1DisplayActual (thm110_final_display); Statement/Estimates/Inputs/UniformHeightConsumer | CONDITIONAL (on (b)/(c)) | N8 | N6 |
| N8 | IUT IV estimates | LeanFormal/IUT/IUTIV/{Section1,Section2,ArithmeticDivisorDegree,Different*,Archimedean*,StepV*} | TREE ASSET (olean per inventory; not re-checked) | Foundations | N7 |
| N9 | Theorem 3.11 source assembly | Theorem311/SourceTheorem311Assembly:47/60/81/85/89/93 | CONDITIONAL assembly PROVED | SourceH1H2Construction etc. | L3 Cor312 |
| N10 | Cor 3.12 StepXI consumers | IUTIII/Corollary312 (90 files): Cor312ComparisonGapReduction:306, Cor312CarrierRealizationSpec | CONDITIONAL/TREE | N9; IUT II | N6 |
| N11 | H6/GenEll route | GenEll05Theorem21Actual:theorem21_i_implies_ii (PROVED); GenEll10bH6Mzk1Wiring:h6_genEll_transfer_of_mzk1 (conditional); GenEll15GeometricCoreAssembly:recast laws; GenEll17BelyiPairConversion | PARTIAL; H6 precise PROVED; GenEll15 precise existence NAMED | Mzk1 bottoms | Thm2.5 wiring (HOLD) |
| N12 | Mzk1 bottom layer (B1-B6b) | fold Mzk1BetaAvoidingFoldActual 27144/E07D7038; W1 BaseActual 10430/691DFC7F; Rational24Bottom 5781/A4D82E80; C 37958/76D71E7D; BaseCase 4728/14F5F5A7; Lemma23Sep 6624/1AC876CD; Moebius 6400/66D16886; BaseCase bridge 5119/743514F1; D Foundation 14032/0F74F433; RRProved 15877/813224A5; RRInterface 8895/7BD88E7D | BOTTOM PROVED (CITABLE+probe_ok) | Mathlib/flt_core | C StepProvider'/D construction |
| N13 | StepProvider' geometry | Mzk1NestedInductionStepProviderActual 5647/CD14AEB3 (f0Map/f0Map_comp/stepSetP; stepTransport_of_goal) | PARTIAL; CVCompositionLawF NAMED; geometry f1/f2/f4 PROVED; fixed-beta/P1 measure named | C layer | Problem C gap |
| N14 | D scheme<->field bridge / finite map / line bundle iso | Mzk1GeomCoreFoundationActual:14032 (scheme layer PROVED); bridge/finite-map named | PARTIAL | D base/RR | H6/GenEll |
| N15 | E deep rows | E-1 AbsTopIII05 (refined D1-D4; Prop5.8 algorithm named); E-2 H5 O^x (normalization/hull bound named; SG3b blocker); E-3 H7/Ob9 (both-sided named); E-4 EtTh (realization 3 named + EtTh02 10 deep named); E-5 IUT IV (b)/(c) named | NAMED/class-B (TREE assets exist) | deep theory | L7/L8 frozen |
| N16 | binding HOLD | Mzk1Thm25UnconditionalActual (+probe), Mzk1Lemma22FullGateActual, Mzk1Lemma24BaseCaseComplex in tmp/xif_hold_files.txt | HOLD (not un-HOLD, not queued) | consumer + restated full gate | n/a |

## 4. LAST-MILE LIST (shortest chain from current bottoms to ABC)
1. (L5) Fill Cor312ToABCBridgeInterface fields concretely: hullData + epsilonComparison height/region inequalities (N3); existing conditional routes: ABCFrontier (N4) + S3131PaperRoute* (N5).
2. (L4) Produce IUT IV (b) UndilatedHeightBound and (c) UndilatedRegionBound with real objects (no shortcut; S2802 distinction; S2804 target S2717UpperGap; S3171 display is conditional on them).
3. (L3) Make Theorem311 assembly's source layers actual (SourceTheorem311Layers inputs: H1/H2, LGP, source P1P2 bundle, hull/determinant normalization) — currently conditional assembly (N9) fed by TREE assets.
4. (L3) Cor312 proof: N9 -> N10 -> N6 route; currently only conditional/interface; Cor312 ⇔ UpperGap (S2717) recorded.
5. (L2/E) Close E named rows needed by steps 2-4: AbsTopIII05 Prop5.8 algorithm parts, H5 O^x normalization/hull bound, H7/Ob9 both-sided, EtTh realization rows; build first mechanical gaps OddThetaNegativeDecay/TermAlgebra, AbsoluteKummer*/SourceThetaPilotIQContainment.
6. (L0/L1) RR/theta analytic/log-shell foundation: RR now PROVED (flt_core, N12/B6b); theta analytic ODDTHETA build gaps; log-shell/Frobenius family real.
7. (rational route) C StepProvider' (CVCompositionLawF + geometric f0/f5 transport + P1 measure) -> Problem C paperScopeLemma24Statement unconditional -> GenEll Thm2.1 (ii)=>(i) consumer (GenEll05 inputs) -> Thm2.5 wiring (must consume h22/h24; binding HOLD until real consumer + restated full gate).
8. Never: conditional shell as proof; no un-HOLD; no closure claim before all real objects; inequalities only hard construction.

## 5. SEARCH COVERAGE
- Trees scanned: LeanFormal/IUT entire tree (IUTI 69, IUTII 194, IUTIII 190 [Cor312 90, StepXI 83, Theorem311 100], IUTIV 14, Foundations 539, ABCBridge 164 [Bridge 18, Geometry 123], Audit 5, Verification 1 = 1176 .lean files); tmp/external/ported roots (flt_core RR chain 5 files green; tauceti_belyi_core/tauceti_rr drift status known); tmp historical dirs (root-dtheta/theta-route/theta-link-resolution/odd-theta-nonvanishing/source-theta-pilot-iq/fractional-absorption etc.: probes/logs only, no active implementation); xif paper 12165 .lean files (keyword-scan based; not individually mapped).
- Docs scanned/merged: dag/README.md (6 anchors only; dependencies_complete:false), C3_CONSUMER_CHAIN_CLOSURE.md (22 files S2888-S2909, 23/23 trio), coord/ENDGAME-DEPENDENCY-LEDGER.md, coord/FINAL-STATUS-20261110.md, IUT_SUBTARGETS.md (M0-M5 route), THEOREM311_{A2_INITIAL_THETA_QUANTIFIERS,A2_SOURCE_COMPLETION_CHECKLIST,DEPENDENCY_AUDIT,TO_312_100_TASKS}.md, coord/OPEN-HARD-PROBLEMS.md, E/Foundation/PROBLEM-E docs.
- Keyword scans: AbsTopIII, logShell, log-Frobenius, O^x, ThetaPilot, ThetaHull, Ob9, EtaleTheta, Frobenioid, uniformHeight, height-volume, 2.4/nested induction, H6, RR, line bundle, StepXI, Cor312, thm110.
- Repo route index (stepxi A440): 897 files (LeanFormal 93 + tmp 804) by filename patterns Route|Contract|Reduction|Alternat|Frontier|Skeleton|Obligation|Supply|Gap|Paper|Strategy|Candidate|Attempt; categories route 238 / paper-layer 414 / gap 104 / attempt 95 / candidate 29 / obligation 14 / alternative 3; citable EXIT0 186 / EXIT1 11 / NO_RESULTS_LINE 607 / OLEAN_FRESH 82 / OLEAN_MISSING 11; **uncovered by coord route docs 671/897 (LeanFormal 37 + tmp 634)** = user "还有更多" set; RED caution files (last EXIT1, do not cite green) listed in coord/REPO-ROUTE-INDEX.md; next: lattice/mainline triage uncovered LeanFormal semantic reducers -> add coverage rows here. See coord/SKELETON-GAPS.md §2d.
- UNMAPPED (not individually traced; exist but no consumer/edges): Foundations/AlgebraicGeometry bulk (QlTheta series, units, adic/geometry files); IUTII Kummer/Frobenioid bulk beyond cited anchors; ABCBridge/Geometry 123 files; IUTIII Theorem311 100 files beyond SourceTheorem311Assembly; IUTIII Corollary312 83 StepXI files beyond cited consumers; xif paper thousands of audit/intermediate files; tmp historical dirs. These are registered in coord/SKELETON-GAPS.md (lattice) for follow-up.

## 6. MERGE REGISTER (lattice intake, preserved)
| # | section | source file(s) | owner | status |
|---|---|---|---|---|
| S1 | Bottom-layer frontier | FOUNDATION-FIRST-PLAN.md | lattice | live; B1-B6b bottom + NY |
| S2 | E extension plan | E-EXTENSION-PLAN.md | lattice+mainline | live; asset-first order |
| S3 | E existing closure map | E-EXISTING-CLOSURE-MAP.md | mainline | delivered/merged |
| S4 | qpilot E mapping | PROBLEM-E-MAPPING-qpilot-A426.md | qpilot | delivered |
| S5 | IUT IV inventory | FOUNDATIONS-IUTIV.md | stepxi | delivered |
| S6 | Canonical gate stable rows | IUTExternal35GateV150Actual.lean | lattice/Lead | live: 3 stable rows |
| S7 | Open hard problems | OPEN-HARD-PROBLEMS.md | lead/team | reference |
| S8 | Skeleton gaps register | SKELETON-GAPS.md | lattice | live |
| S9 | IUT I/II skeleton section | SKELETON-IUTI-II.md (16067B) | abc | LANDED (A430) |
| S10 | IUT IV/ABCBridge skeleton section | SKELETON-IUTIV-ABCBRIDGE.md (17349B) + skeleton-iutiv-abcbrige-edges.tsv (25128B) | stepxi | LANDED (A430) |
| S11 | IUT III hull skeleton section | SKELETON-IUTIII (hull) | hull (ETA requested) | MISSING |
| S12 | THETA-ETTH skeleton section | THETA-ETTH.md (7095B) + SKELETON-THETA-ETTH.md (8197B) | qpilot | LANDED (A437) |
| S13 | Repo-wide route/contract index | REPO-ROUTE-INDEX.md (237469B sha d6bd9339) + repo-route-index-data.json (493065B sha 84e3001f) | stepxi (A440) | DELIVERED; uncovered 671/897 triage pending |

MERGE RULES: section authors land files; mainline 主笔; lattice keeps S8; pins must be fresh EXIT0+probe_ok; tree assets marked; no proofs/gate edits; named stays named; gate rows only 3 stable; latest verified pin wins.

*No proofs, no gate effect; GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041 / record 18800.*
---

## 7. LEAD OUTLINE RECONCILIATION (Lead A430; MASTER-SKELETON-OUTLINE.md merged)
- Final chain per Lead outline: G0 ABCConjecture (ABCBridge/Statement.lean:32) -> G1 cor312ToABCBridge_abcConjecture (Cor312ToABCBridgeInterface.lean:446) -> G2 Cor312ToABCBridgeInterface (:404 named; nonempty_iff_abcConjecture:605) -> G2' ABCFrontier/ABCFrontierRealLine (:213/:309/:337/:354; abcFrontier_iff_abcConjecture) -> G3 Cor312/Theorem311 hull-volume (IUTIII; SourceTheorem311Assembly etc.) -> G4 IUTIV arithmetic transition/estimates + ABCBridge/Geometry IQHull/Hull series -> G5 IUTIII theta-hull/StepXI/log-shell -> G6 IUTII EtTh/Frobenioid/log-shell -> G7 IUTI Hodge theater/source -> G8 Foundations.
- Bottom layer per Lead outline B1-B7 (B7 = Mzk1RRInterfaceActual 8895B 7BD88E7D); B6b D-RR verified this session.
- NEW VERIFIED PINS in this round (mainline): `Mzk1StepProviderPrimeActual` CITABLE 11/6312B sha CCE61640D10BB1D2 probe_ok (C StepProvider' module); `Mzk1GeomCoreBridgeInterfaceActual` CITABLE 6/6352B sha E23A014B8DF8FE05 (D bridge interface). `Mzk1CVCompositionFActual` currently RED 2546B (EXIT1; in progress). New unverified: Mzk1GeomCoreRRBridgeActual 5226B, Mzk1GeomCoreBridgeLegacyActual 6277B (D bridge pair; fresh pins to be reported).
- Section files landed: `coord/SKELETON-IUTI-II.md` (16067B, abc), `coord/SKELETON-IUTIV-ABCBRIDGE.md` (17349B) + `coord/skeleton-iutiv-abcbrige-edges.tsv` (25128B, stepxi); S12 THETA-ETTH LANDED (A437: THETA-ETTH.md 7095B + SKELETON-THETA-ETTH.md 8197B); still missing: SKELETON-IUTIII (hull) - ETA requested (S11).
- Coverage (Lead numbers): LeanFormal/IUT 1176 files (IUTI 69, IUTII 194, IUTIII 190, IUTIV 14, Foundations 539, ABCBridge 164, Audit 5, Verification 1); tmp/sheaf/xif/paper 12790; tmp/external/ported 2163. To supplement: target-related declarations not in old docs (grep Corollary312/Theorem311/SourceTheorem311Assembly/StepXI/hull/Ob9/EtTh/AbsTop/Frobenioid/Hodge/theta-link); tmp historical valuable implementations; future public LANA documents.
- LAST-MILE order per Lead outline (1-7): (1) C StepProvider' (geometry f1/f2/f4 + CVCompositionLawF + fixed-beta extra) -> C unconditional; (2) D bridge/finite-map construction; (3) E build gaps (OddThetaNegativeDecay/TermAlgebra, AbsoluteKummer*, SourceThetaPilotIQContainment, Section0Objects); (4) E extension asset-first (Prop5.8(ii) diagram, Example36<->EtTh, algorithms named); (5) IUT III/IV high-level (Cor312 hull-volume real; H5/H7/AbsTopIII/EtTh named rows); (6) IUT IV comparison fields (height<=region volume, region<=weight) + S2717UpperGap; (7) final acceptance (locked target, comparator, axiom audit, paper semantics, same-version build).
- No proofs/new math in this file; no gate edit; GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08.

### A432 SECTION/PIN SYNC (mainline)
- S9 SKELETON-IUTI-II.md (abc, 16067B/82 lines): SIGNED OFF (IUTI 69 + IUTII 194 node graph; IUTII->IUTIII interface table: EtTh realization / log-shell / Frobenioid transport / theta pilot-IQ; unmapped mass + build gaps + honesty footer).
- S10 SKELETON-IUTIV-ABCBRIDGE.md + skeleton-iutiv-abcbrige-edges.tsv (stepxi): SIGNED OFF (178-module graph IUTIV 14 + ABCBridge 164; 25128B/178 rows; 172 fresh oleans; MISSING 4 modules; STALE 2; no actual sorry/axiom; final-chain edges verified G0-G1-heightBound-thetaBound-Cor312EpsilonArithmeticComparison; two named IUT IV section2 gaps = height_le_normalizedRegionVolume + regionVolume_le_normalizedWeight; bridge alternatives IFACE-only; ABCFrontierHeightWeightRefutation blocks additive-bound factorization).
- FOUNDATIONS-IUTIV.md extended to 27163B (A426): REAL closure R1-R19, MODEL/IFACE M1-M5/I1-I9, extension plan; citable probe _FOUNDATIONS-IUTIV-CitableProbe EXIT0 (trio for deg_pullback/ndeg_pullback/Prop17/Prop21ii/processionAverage/stepVPaperLogVolumeBound/measure_hull_lt_top/hull_logVolume_lt_top/sum_completionNormDegree/cor312ToABCBridge_abcConjecture).
- S11 SKELETON-IUTIII MISSING (hull; ETA requested); S12 THETA-ETTH MISSING (qpilot; ETA ~20min combined with SKELETON-THETA-ETTH).
- NEW PINS: Mzk1GeomCoreBridgeLegacyActual CITABLE 5/6277B sha 37CFC7924953AA0F (D bridge legacy wiring); Mzk1GeomCoreRRBridgeActual RED 5226B sha 418A4F7F (in progress); Mzk1GeomCoreBridgeInterfaceActual CITABLE 6/6352B E23A014B; Mzk1StepProviderPrimeActual CITABLE 11/6312B CCE61640.
- E-EXTENSION-PLAN E-5 line update: FOUNDATIONS-IUTIV.md 27163B (A426; §6 REAL closure R1-R19 / §7 MODEL-IFACE / §8 extension plan); SKELETON-IUTIV-ABCBRIDGE.md + edges TSV delivered (A429); citable probe results:210254.
### A433 REGISTER PIN EXACTNESS (stepxi artifact hashes; mainline record)
- S10 artifacts (fresh): `coord/SKELETON-IUTIV-ABCBRIDGE.md` 19550B sha256 1ed0c2c7e4e4fe22; `coord/skeleton-iutiv-abcbrige-edges.tsv` 25128B sha256 300af6c2be2a7c04; `coord/FOUNDATIONS-IUTIV.md` 27297B sha256 68a143b377c58d59; pins sidecar `coord/skeleton-iutiv-abcbrige-pins.txt` holds canonical pin V150@18248/CFC6CE08 (+ registry 14041/record 18800/GATE NOT PASSED/binding HOLD); TSV format kept stable (no pin column; machine-safe). Update rule: sidecar only on canonical pin/artifact change; TSV rows only on module add/remove or olean status flips (MISSING 4 / STALE 2 as listed).

## 8. OFFICIAL ROUTE LAYER (paper: Formalization of IUT (2026-04); Lead A439/A440)
Per Mochizuki official formalization text: Stage 1-5 strategy + section4 skeletal Lean code (four triangles BPS/mlt.rep/hull+det/dsc/HDD/SHE/APT/IPL/3.11.5/3.12comparison).
Repo counterparts: LeanFormal/IUT/IUTIII/Corollary312/{Routes,Comparison,Obligations}.lean; Corollary312/StepXI/{Contract,IPL,SHE,APT}.lean. Paper-route fragment: coord/target-chain.paper-routes.json (19 nodes/29 edges; hull) covers Stage1-5 with real decl names: Routes.lean Cor312Route/Cor312RouteCertificate(.conclusion:42)/mochizuki3115Construction:51/mochizuki3115ToCor312:71; Comparison.lean cor312Conclusion_of_contract:7; Contract.lean StepXIContract:32/Cor312Conclusion:46/cor312_of_constructed_stepXI:49; APT.lean SourceAlgorithmicParallelTransport:163/SourceAPTStatement:308/SourceAPTSlotAssembly:332/aptSlot_evidence:353/sourceAlgorithmicParallelTransport:419; TateQPilotJComparison qPilotLogVolume:45; S3128 Stage1 readouts (HDD hull/det, BPS/IPL, comparison, fourth triangle, SHE, APT).
Status split (honest): PROVED/tree (qPilot TateQPilotJComparison, hullDet HullDeterminantLogVolumeReduction + S3128 HDD readouts); CONDITIONAL (stage1/stage2/thm311/HDD/APT/thm311_5/cor312comparison/BPS/mltRep); NAMED/GAP (stage3 IUTchI-II no Lean link, stage4 early results, stage5/IUTIV ExpEst, thetaPilot object, dsc no decl, SHE/IPL stubs + Obligations).
Paper-theta fragment: coord/target-chain.paper-theta.json (383 nodes/1082 edges, paper:* 355 + formal:* 28 anchors; status NAMED 306/CONDITIONAL 49/GAP 28; sources EtTh/AbsTopIII/GenEll/NCBel/Hodge-Arakelov/Explicit estimates; explicit formal mappings e.g. AbsTopIII 5.8->A4/P58, 5.5->L2, EtTh 1.1-1.5->EtTh01, 1.6/1.10->EtTh02, GenEll 2.1->GenEll05, NCBel 2.1->Lemma21/2.2->P1Interface/2.3->MoebiusP1/2.4->CVLaw/2.5->Thm25Concl).
Route families (coord/ROUTE-MENTIONS.md): R1 direct-readout/fixed-shell ARCHIVED; R2 eta-algorithm ACTIVE/EXPERIMENTAL; R3 paper Stages1-5/four triangles AUDIT MAP; R4 N8 closure DESIGN; R5 endgame Option-B PREPARED; R6 3.11.5 label CONCEPT; R7 abc paper-lambda PARTIAL; R8 historical probes DEAD; R9 weighted q PARTIAL; R10 prestack OBSTRUCTION. Obstructions: SG3b tensor Haar, S2826 region, S2804 UpperGap, modelIndex, NativeC3, direct-readout invalidated, fixed-shell degeneracy.

## 9. DAG STATUS (A438/A441)
- Import graph: 123410 files / 36617 edges; validator ok=true; cyclic_components=0 (S3139 cycle fixed by direct imports).
- Declaration DAG: fragments = main target-chain.json + iuti-ii + iutiii + iutiv-abc + theta-etth + paper-routes + paper-theta + foundation + e-deep; merged via tools/dag_merge2.mjs => 689 nodes / 1451 edges / 0 conflicts; tools/dag_validate_decl.mjs => problems=0. paper fragments not all last yet (rename zz-paper* or explicit sort in tool when strict paper-last required).
- New fragments by mainline: coord/target-chain.foundation.json (B1-B7 + C StepProvider'/CVCompositionF/f0/degree + D bridge + HOLD + gate node); coord/target-chain.e-deep.json (E1-E5 deep/named routes; IUTIV Estimates paths fixed to LeanFormal/IUT/IUTIV/Estimates/).
- Still pending: coord/PAPER-ROUTES.md (full paper->repo route extraction; PAPER-INDEX.json 158880B index + REPO-ROUTE-INDEX.md 237469B (stepxi) as inputs); S11/S12 section files landed (SKELETON-IUTIII 11596B, SKELETON-THETA-ETTH 8626B, THETA-ETTH 7095B).

## 8. UNCOVERED LEANFORMAL ROUTE/CONTRACT TRIAGE (stepxi A440 follow-up; candidate coverage rows; owner confirmation pending)

Source: `coord/uncovered-leanformal-triage.tsv` (13578B sha 496a2032df77b97c04dd6feab65c236f14bd7221c97e6b03fb776701e6dd6530); 37 rows = uncovered LeanFormal route/contract files from REPO-ROUTE-INDEX §4; columns file/category/route_tags/key_declarations/citable_compile/proposed_master_route/suggested_owner/priority/note.

Owner split: mainline 3, shehdd 1, hull 18, lattice 5, qpilot 7, stage4 3. Priority: P1 28, P2 9. Compile: OLEAN_FRESH 29, OLEAN_MISSING 8.

**Caveat:** proposed route/owner is a proposal; owners must confirm semantic role before these become MASTER coverage rows. **OLEAN_MISSING files are NOT built/citable now** (investigate before citing); P1 = triage priority only, not a citable claim. No gate edit.

| # | file | cat | tags | compile | proposed route | owner | prio |
|---|---|---|---|---|---|---|---|
| 1 | `ABCBridge/Geometry/FreyOddReduction.lean` | route | unmapped | OLEAN_FRESH | ABCBridge/Frey conductor-torsion layer (MASTER L5/L8 vicinity; FreyJ/h | mainline | P1 |
| 2 | `ABCBridge/Geometry/FreySplitMultiplicativeReduction.lean` | route | unmapped | OLEAN_FRESH | ABCBridge/Frey conductor-torsion layer (MASTER L5/L8 vicinity; FreyJ/h | mainline | P1 |
| 3 | `ABCBridge/Geometry/FreyTwoAdicMinimalReduction.lean` | route | unmapped | OLEAN_FRESH | ABCBridge/Frey conductor-torsion layer (MASTER L5/L8 vicinity; FreyJ/h | mainline | P1 |
| 4 | `Audit/Diagnostics/LegacyContracts.lean` | route | unmapped | OLEAN_FRESH | Audit/diagnostics (legacy contracts; coverage-only, no route claim) | shehdd | P2 |
| 5 | `Foundations/AlgebraicGeometry/SourcePsiActualMinimalModelReduction.lean` | route | unmapped | OLEAN_MISSING | L0/L6 Source Psi model/reduction family (source geometric foundation;  | hull | P1 |
| 6 | `Foundations/AlgebraicGeometry/SourcePsiCorrectedReductionSpecialFiber.lean` | route | unmapped | OLEAN_MISSING | L0/L6 Source Psi model/reduction family (source geometric foundation;  | hull | P1 |
| 7 | `Foundations/AlgebraicGeometry/SourcePsiIntegralModelReduction.lean` | route | unmapped | OLEAN_MISSING | L0/L6 Source Psi model/reduction family (source geometric foundation;  | hull | P1 |
| 8 | `Foundations/AlgebraicGeometry/SourcePsiReductionActualConstruct.lean` | route | unmapped | OLEAN_MISSING | L0/L6 Source Psi model/reduction family (source geometric foundation;  | hull | P1 |
| 9 | `Foundations/AlgebraicGeometry/SourcePsiReductionTypeActual.lean` | route | unmapped | OLEAN_MISSING | L0/L6 Source Psi model/reduction family (source geometric foundation;  | hull | P1 |
| 10 | `Foundations/AlgebraicGeometry/SourcePsiStableReductionFinal.lean` | route | unmapped | OLEAN_MISSING | L0/L6 Source Psi model/reduction family (source geometric foundation;  | hull | P1 |
| 11 | `Foundations/AlgebraicGeometry/SourcePsiStableReductionFinalConsumer.lean` | route | Consumer | OLEAN_MISSING | L0/L6 Source Psi model/reduction family (source geometric foundation;  | hull | P1 |
| 12 | `Foundations/AlgebraicGeometry/SourcePsiStableReductionFromSource.lean` | route | unmapped | OLEAN_MISSING | L0/L6 Source Psi model/reduction family (source geometric foundation;  | hull | P1 |
| 13 | `Foundations/Analysis/SourceContractionRadius.lean` | route | unmapped | OLEAN_FRESH | unclassified | lattice | P2 |
| 14 | `Foundations/Geometry/ConvexHullVertexSupReduction.lean` | route | Hull | OLEAN_FRESH | unclassified | lattice | P1 |
| 15 | `Foundations/Geometry/GenericNodalReduction.lean` | route | unmapped | OLEAN_FRESH | unclassified | lattice | P1 |
| 16 | `Foundations/Geometry/LocalReduction.lean` | route | unmapped | OLEAN_FRESH | unclassified | lattice | P1 |
| 17 | `Foundations/Geometry/ReductionBaseChange.lean` | route | unmapped | OLEAN_FRESH | unclassified | lattice | P1 |
| 18 | `Foundations/Geometry/TateCurveLocalReduction.lean` | route | unmapped | OLEAN_FRESH | L0/L6 Tate uniformization + local/stable reduction contracts (p-adic a | qpilot | P1 |
| 19 | `Foundations/Geometry/TateStableReductionBoundary.lean` | route | unmapped | OLEAN_FRESH | L0/L6 Tate uniformization + local/stable reduction contracts (p-adic a | qpilot | P1 |
| 20 | `Foundations/Geometry/TateUniformizationContract.lean` | route | unmapped | OLEAN_FRESH | L0/L6 Tate uniformization + local/stable reduction contracts (p-adic a | qpilot | P2 |
| 21 | `Foundations/Geometry/TateUniformizationPointMapReduction.lean` | route | unmapped | OLEAN_FRESH | L0/L6 Tate uniformization + local/stable reduction contracts (p-adic a | qpilot | P1 |
| 22 | `Foundations/PAdicAnalytic/TateContraction.lean` | route | unmapped | OLEAN_FRESH | L0/L6 Tate uniformization + local/stable reduction contracts (p-adic a | qpilot | P2 |
| 23 | `Foundations/PAdicAnalytic/TateContractionGeneral.lean` | route | unmapped | OLEAN_FRESH | L0/L6 Tate uniformization + local/stable reduction contracts (p-adic a | qpilot | P2 |
| 24 | `IUTI/InitialTheta/ReductionPlacePartition.lean` | route | unmapped | OLEAN_FRESH | IUT I InitialTheta reduction/place partition/candidates (L? pre-IUT IV | stage4 | P1 |
| 25 | `IUTI/InitialTheta/SourceDefinition31D2Candidate.lean` | candidate | unmapped | OLEAN_FRESH | IUT I InitialTheta reduction/place partition/candidates (L? pre-IUT IV | stage4 | P2 |
| 26 | `IUTI/InitialTheta/SplitReductionInput.lean` | route | unmapped | OLEAN_FRESH | IUT I InitialTheta reduction/place partition/candidates (L? pre-IUT IV | stage4 | P1 |
| 27 | `IUTII/Frobenioid/Example36LocalContraction.lean` | route | unmapped | OLEAN_FRESH | L7 Frobenioid example/local contraction (EtTh/Frd layer) | qpilot | P2 |
| 28 | `IUTIII/Corollary312/StepXI/SourceRouteDeterminantNormalization.lean` | route | IUTIII | OLEAN_FRESH | IUT III Cor 3.12 StepXI (source route determinant / SHE transport obli | hull | P1 |
| 29 | `IUTIII/Corollary312/StepXI/SourceSHETransportObligations.lean` | obligation | IUTIII | OLEAN_FRESH | IUT III Cor 3.12 StepXI (source route determinant / SHE transport obli | hull | P2 |
| 30 | `IUTIII/Theorem311/ConcreteRouteUniqueness.lean` | route | IUTIII | OLEAN_FRESH | IUT III Theorem 3.11 route/contract layer (MASTER N/G pre-Cor312) | hull | P1 |
| 31 | `IUTIII/Theorem311/Indeterminacy/Ind1Reduction.lean` | route | IUTIII | OLEAN_FRESH | IUT III Theorem 3.11 Ind1/Ind2 reduction (MASTER G? pre-Cor312) | hull | P1 |
| 32 | `IUTIII/Theorem311/Indeterminacy/Ind2Reduction.lean` | route | IUTIII | OLEAN_FRESH | IUT III Theorem 3.11 Ind1/Ind2 reduction (MASTER G? pre-Cor312) | hull | P1 |
| 33 | `IUTIII/Theorem311/Output/MultiradialAlgorithmGeneralRouteNormalForm.lean` | route | IUTIII | OLEAN_FRESH | IUT III Theorem 3.11 route/contract layer (MASTER N/G pre-Cor312) | hull | P1 |
| 34 | `IUTIII/Theorem311/Output/MultiradialAlgorithmReduction.lean` | route | IUTIII | OLEAN_FRESH | IUT III Theorem 3.11 route/contract layer (MASTER N/G pre-Cor312) | hull | P1 |
| 35 | `IUTIII/Theorem311/ParametricRouteAlgebra.lean` | route | IUTIII | OLEAN_FRESH | IUT III Theorem 3.11 route/contract layer (MASTER N/G pre-Cor312) | hull | P1 |
| 36 | `IUTIII/Theorem311/SourceFiniteRouteNaturality.lean` | route | IUTIII | OLEAN_FRESH | IUT III Theorem 3.11 route/contract layer (MASTER N/G pre-Cor312) | hull | P1 |
| 37 | `IUTIII/Theorem311/SourceTheorem311ReferenceContract.lean` | route | IUTIII | OLEAN_FRESH | IUT III Theorem 3.11 route/contract layer (MASTER N/G pre-Cor312) | hull | P2 |



### 8b. PER-OWNER TRIAGE ARTIFACTS (stepxi A440 follow-up; verified by lattice)
- Paste-ready coverage table: `coord/uncovered-leanformal-coverage-rows.md` (8634B sha 84bb2a88f7005135...) — MASTER §8 column format, 37 rows sorted by owner then priority, relative paths, per-owner split, caveat (owner confirmation needed; OLEAN_MISSING not citable; P1 triage only). Use for a direct §8 replacement/extend once owners confirm.
- Per-owner TSVs (9 columns; header+rows): hull `coord/uncovered-leanformal-triage.hull.tsv` (7121B sha d8e2c31a4481d749; 18 rows); lattice `...lattice.tsv` (1579B sha 27dfa48e583c02bc; 5); mainline `...mainline.tsv` (1197B sha 51970e3e51a29be4; 3); qpilot `...qpilot.tsv` (2729B sha 5ddf452f63dad231; 7); shehdd `...shehdd.tsv` (383B sha d2b5c519b0640017; 1); stage4 `...stage4.tsv` (1119B sha 0aa621edcbf08c65; 3).
- Counts unchanged/verified: mainline 3, hull 18, qpilot 7, stage4 3, lattice 5, shehdd 1; P1 28/P2 9; OLEAN_FRESH 29/OLEAN_MISSING 8. Per-owner TSVs can be handed to owners for semantic-role confirmation; no proof claim from tables.

## 10. PAPER/ROUTE COVERAGE SYNC (A442; A448 continuous mode)
- A448 continuous DAG mode: `tools/dag_next.mjs` actionable 77 / blocked 7 / ready 18; `tools/dag_merge3.mjs` formal DAG 297/350/0; blocked register `coord/DAG-BLOCKED.json` (policy: do not attack; pick DAG-NEXT). Merge/registration docs: `coord/TARGET-CHAIN-MERGE.md`; gaps/blocked docs: `coord/SKELETON-GAPS.md`.
- `coord/PAPER-ROUTES.md` delivered (mainline): per-paper route map (IUT I-IV, Explicit estimates, Essential Logical Structure, Alien Copies, EtTh, AbsTopIII, GenEll, NCBel, Frobenioid I-II, Combinatorial Anabelian I-IV, Hodge-Arakelov + surveys, Theta Convolution, Report/FAQ/Program/Classical roots) + official Stage1-5/four-triangle layer + 10 route families + obstructions + uncovered triage + honesty notes.
- DAG fragments latest: paper-routes 46 nodes/76 edges (43571B, hull; Stage1-5+§4+IUT III/IV steps); paper-theta 383/1082 (qpilot); foundation 21/17; e-deep 23/17; iuti-ii 31/37; iutiii 29/23; iutiv-abc 36/52; legacy-dag 89/147; main 26/21. Declaration DAG merge: **716 nodes / 1498 edges / 0 conflicts**; dag_validate_decl problems=0.
- Coverage triage: coord/uncovered-leanformal-triage.tsv 13578B sha 496a2032 (37 rows, owner split mainline 3/shehdd 1/hull 18/lattice 5/qpilot 7/stage4 3; P1 28/P2 9; OLEAN_FRESH 29/OLEAN_MISSING 8) imported as candidate coverage table (§8 lattice); OLEAN_MISSING not citable until built.
- Still open: owner confirmation of proposed semantic roles/routes for uncovered files; PAPER-ROUTES deep-read per-theorem expansion can continue; paper-last strict ordering in merge tool optional.
### A443 uncovered-coverage artifacts registered (stepxi; HOLD on confirmations)
- Artifacts consolidated in **§8b** (paste-ready table `coord/uncovered-leanformal-coverage-rows.md` 8634B sha 84bb2a88; per-owner TSVs hull d8e2c31a/lattice 27dfa48e/mainline 51970e3e/qpilot 5ddf452f/shehdd d2b5c519/stage4 0aa621ed; counts verified P1 28/P2 9; OLEAN_FRESH 29/OLEAN_MISSING 8; OLEAN_MISSING not citable).
- HOLDDEN: owner semantic-role confirmation deferred (no new claims); can replace/extend section8 once owners confirm.

### A445 declaration-DAG split + D/E pins (mainline)
- FORMAL declaration DAG (target-chain fragments only): 296 nodes / 348 edges / 0 conflicts; dag_validate_decl problems=0. Sources: main 26/21, e-deep 23/17, foundation 21/17, iuti-ii 31/37, iutiii 29/23, iutiv-abc 36/52, legacy-dag 89/147, routes 9/8, theta-etth 32/26.
- PAPER maps split (not in formal DAG; heuristic label/mention graphs create cycles): moved to coord/paper-chain/: paper-routes, paper-theta, paper-iut12, web-routes, route-mentions (42770 mention nodes), paper-labels (20091 label nodes). They remain research maps only; no paper node is PROVED by repo evidence. (If a paper DAG is needed, validate with kind-filtering and/or curated edges only.)
- E-1 Section0Objects: AbsTopIII05Section0ObjectsActual CITABLE 31/11621B sha 970AA5AA probe_ok (UnderlyingGraph/OrientedGraph.underlying/Branch/PrePath/Path/PathPair/IsSaturatedPathPairSet; rows 9; saturated-set combinatorics + path composition named).
- C: Mzk1CVCompositionFActual current disk pin 2752B sha 706859EC CITABLE 5 probe_ok (cvCompositionLawF_proved + stepTransport_of_goal_proved); earlier 2589 reading superseded.
- D: Mzk1GeomCoreFiniteMapRouteActual CITABLE 6/8109B 08C4D547 probe_ok (finiteMapData_of_construction; preciseWitness_of_route/recast_of_route; named: actual finite-map construction + psi^*O(1)=O(D)/no line-bundle API). Mzk1GeomCoreLineBundleInterfaceActual CITABLE 8/6042B 0945A965 probe_ok (LineBundlePullbackInterface root-neutral; finrank_functionFieldSections_eq PROVED; degree_eq_of_interface; sectionImage_mem; remaining named: actual O(D) sheaf/actual psi* pullback/uniformizer-order compatibility).
- Gate NOT PASSED; binding HOLD; FINAL PIN V150@18248/CFC6CE08; registry 14041; L8 frozen.
