# PAPER-ROUTES — paper corpus → repo Lean nodes (mainline, Lead A440; research map, no proofs/gate)

Sources: `papers/motizuki_corpus/text/` (257 txt), `coord/PAPER-INDEX.json` (158880B auto-index: per-file size/section_count/sections/theorem_like), `coord/REPO-ROUTE-INDEX.md` (237469B, stepxi; 897 route/contract-family files, 671 uncovered), `coord/ROUTE-MENTIONS.md` (route families R1-R10), `coord/IUT_SUBTARGETS.md`, `THEOREM311_*.md`, `IUTIV-SECTION1-PLAN.md`, `OPEN-HARD-PROBLEMS.md`, `E-EXISTING-CLOSURE-MAP.md`. Paper citations are corpus text files (auto-index heuristic: section headers start-of-line labels; theorem-like counts are approximate, not a formal theorem list).

## 1. Official formalization route (Formalization of IUT (2026-04).txt; 9 sections, 3 theorem-like)
- Stage 1-5 strategy + §4 skeletal Lean code: four triangles BPS/mlt.rep/hull+det/dsc/HDD/SHE/APT/IPL/3.11.5/3.12comparison.
- Repo counterpart nodes: IUTIII/Corollary312/{Routes,Comparison,Obligations}.lean; Corollary312/StepXI/{Contract,IPL,SHE,APT}.lean; S3128 Stage1 readouts; HullDeterminantLogVolumeReduction; TateQPilotJComparison.
- DAG fragment: coord/target-chain.paper-routes.json (hull; Stage1-5 + §4 + IUT III/IV steps; nodes 42/edges 70 as of latest expansion). Status: PROVED/tree (qPilot, hullDet, S3128 HDD readouts); CONDITIONAL (stage1/2, thm311, HDD, APT, thm311_5, cor312comparison, BPS, mltRep, IUT III thm311/cor312, triangles, IUT IV sec1/sec2/thm1_10); NAMED/GAP (stage3/4/5, thetaPilot, dsc, SHE/IPL stubs, IUT III §0/prop3_1/prop3_2, IUT IV §0/§3/prop1_6/1_8/1_9).

## 2. Main paper route table (selected; paper → repo node → status)
| paper (corpus) | structure (auto-index) | repo correspondence | status |
|---|---|---|---|
| Inter-universal Teichmuller Theory I | 15 sections, 104 theorem-like | IUT I: HodgeTheater/SourceInitialTheta/Definition31*/SourceEtaleStack (IUTI 69 files) | TREE ASSET/PARTIAL (source-supplied named parts) |
| IUT II | 5 sections, 97 theorem-like | IUT II: Frobenioid (141 files), Kummer (44), Theta (9): EtaleThetaQuotient, FiniteThetaPacket, ThetaLinkAssembly, SourceLogShellCarrier/Bridge, Example36* | TREE ASSET mixed; EtTh02 deep named; log-shell real reductions |
| IUT III | 5 sections, 56 theorem-like | IUT III (190 files): Corollary312 (90; StepXI 83), Theorem311 (100): SourceTheorem311Assembly conditional; Routes/Comparison/Obligations; Contract/IPL/SHE/APT | CONDITIONAL assembly; hull/determinant/StepXI interfaces; S2717UpperGap endpoint |
| IUT IV | 6 sections, 43 theorem-like | IUT IV Estimates (14 files: Section1/Section2/ArithmeticDivisorDegree/Different*/Archimedean*/StepV*) + S3131/S3171 paper-route deliverables + Cor312ComparisonGapReduction:306 | TREE ASSET + CONDITIONAL display; two named section2 comparison fields = last bridge edge; S3171 thm110_final_display conditional on hCor312/hSlack |
| Explicit estimates in IUTeich | 0 sections, 52 theorem-like | IUTIV/Estimates + S3131PaperRoute* reductions + S2717UpperGap | PARTIAL: real estimates/tree; propagation log-cond estimates and (b)/(c) uniform height-vs-volume named |
| Essential Logical Structure of IUT (466KB; 68 sections, 28 thr) | §1-§10 columns (IUT I-V + marked-up versions, 20 sections each) | (a) IUT I-V §1-§10 route labels: no theorem nodes, mapping to HodgeTheater/log-theta-lattice/Θ-Hodge-theater/holomorphic hull chapters (IUTI/II/III) | MAP only (no Lean declarations per heading) |
| Alien Copies, Gaussians, and IUT (87 sections, 62 thr) | survey route (legacy/context) | no direct Lean node; historical route family R8 DEAD per ROUTE-MENTIONS; Gaussian kernel assets in Foundations/Theta | NAMED/context |
| The Etale Theta Function and its Frobenioid-theoretic Manifestations (9 sections, 80 thr) | Prop 1.1/1.3/1.4/1.5, Thm 1.6/1.10, Prop 3.2/3.4, §4 | EtTh00-13 xif paper rows; EtaleThetaQuotient/Example36*; Mzk1EtThRealizationConsumer (CITABLE 14; 11-row: 3 named + 8 proved; EtTh02 10 deep named; EtTh11 rows5-7 named) | CONDITIONAL/NAMED |
| Absolute Anabelian Geometry III (IUT IV §? AbsTopIII corpus) | AbsTopIII 5.8(i)(ii), Cor 5.5, Cor 5.10, Prop 5.7 | SourceLogShellAbsTopIIIBridge (24 decls), AbsTopIII01/03/04 xif; AbsTopIII05Refined D1-D4 typed (D3/D4 discharged); algorithm parts named; Cor5.10 concrete; Prop5.7 normalization cited by CardHullReal* | PARTIAL: real anchors; Prop5.8/Cor5.5 algorithms NEW THEORY named |
| Arithmetic Elliptic Curves in General Position (GenEll) (33 thr) | Thm 2.1 (i)=>(ii) / (ii)=>(i); §4 | GenEll05Theorem21Actual (theorem21_i_implies_ii PROVED; Theorem21ReductionInputs; paper_epsilon_absorption); GenEll10bH6Mzk1Wiring (h6_genEll_transfer_of_mzk1 conditional); GenEll15GeometricCoreAssembly; GenEll17BelyiPairConversion | PARTIAL: (i)=>(ii) proved; (ii)=>(i) needs noncritical Belyi (A/C route) + H6 precise wiring; HOLD for Thm2.5 binding |
| Noncritical Belyi Maps (8 thr) | Lemma 2.1(a)-(d); 2.2; 2.3; 2.4 (lines 163-206); 2.5; 3.1/3.2 | Mzk1Lemma21*; P1MorphismInterface; Mzk1Lemma23Separation/Moebius (B5); CVLaw/RestatedLemma24 (B3); Mzk1Thm25Conclusion; Cor31 rows | Lemma 2.1/2.3 rational PROVED; 2.2 rational gate F=Q PROVED (B1-B3); 2.4 F=Q base + CV law PROVED; full-Qbar 2.2/2.4 named (nested induction/descent); 2.5 conditional (binding HOLD) |
| Frobenioid I-II (Example 3.6 etc.) | Frobenioid formalism, Example 3.6 | IUTII/Frobenioid (141 files): SourceModel/SourceCurveGalois/Example36TateUniformization/SourceEtaleThetaTheory/PrimeStripsFrobenioidLinks | TREE ASSET; H5 O^x parts named; no port needed (tree exists) |
| Combinatorial Anabelian Geometry I-IV (69/97/88/100 thr) | G_k reconstruction/graph combinatorics | IUTI HodgeTheater/Anabelian; Foundations AlgebraicGeometry anabelioid interfaces; SourceThetaLinkGraphAutomorphismReduction | TREE ASSET/interface; no full reconstruction formalization |
| Hodge-Arakelov Theory of Elliptic Curves (143 sections, 110 thr) + Surveys I (16 sec/6 thr), II (5 sec/25 thr) | Theorem A/B, Theta convolution, Gaussian | Foundations/Theta (OddTheta q-series/sign/kernel/Nonvanishing/SignedLabelEquiv 10 files); IUTI HodgeTheater geometric core; Cartier/theta-convolution not fully formalized | PARTIAL: analytic theta foundation exists; Hodge-Arakelov geometric core source-supplied |
| The Scheme-theoretic Theta Convolution (23 sections, 28 thr) | Theta convolution scheme theory | No direct Lean node beyond Foundations/Theta analytic layer; scheme-theoretic convolution absent | GAP/NAMED (new theory if pursued) |
| Report on preprints (Cor 3.12 / Thm 3.11 / Thm 1.10) | 14 theorem-like listing | IUTIII/IV docs route (IUT_SUBTARGETS M0-M5; THEOREM311_*); repo chain G0-G8 | AUDIT MAP only |
| FAQ on IUTeich / IUT Program / Classical roots of IUT / IUT-report-2025-10 | 0-27 sections, mostly survey | no Lean nodes; context for route families R1-R10 | CONTEXT |

## 3. Four-triangle / Stage letter route (official layer)
- Stage 1: BPS + mlt.rep data (S3128 BPS/IPL readouts; conditional)
- Stage 2: HDD hull+det (S3128 HDD readouts; HullDeterminantLogVolumeReduction tree)
- Stage 3: dsc (no Lean declaration; NAMED; IUTchI-II links absent)
- Stage 4: early results (no Lean; NAMED)
- Stage 5: APT/IPL/SHE + 3.11.5 + 3.12 comparison (APT.lean SourceAPTStatement/SourceAPTSlotAssembly/sourceAlgorithmicParallelTransport; IPL/SHE stubs + Obligations; 3.11.5 concept; cor312Conclusion_of_contract conditional)
Repo statuses: qPilot/hullDet/HDD tree-or-conditional; BPS/IPL/APT conditional; dsc/SHE/IPL/3.11.5/stage3-5 named/gap; IUTIV ExpEst stage5 paper-only.

## 4. Additional routes found beyond prior docs (stepxi REPO-ROUTE-INDEX triage; user 'there is more')
- 897 route-family files scanned (LeanFormal 93 + tmp paper 804); 671 uncovered by coord route docs (LeanFormal 37 + tmp 634).
- LeanFormal triage priority (semantic reducers/contracts not in route docs): ABCBridge/Geometry/FreyOddReduction, FreySplitMultiplicativeReduction, FreyTwoAdicMinimalReduction; Foundations/Geometry/TateUniformizationContract, TateUniformizationPointMapReduction, TateCurveLocalReduction, TateStableReductionBoundary, ReductionBaseChange, GenericNodalReduction, LocalReduction; Foundations/PAdicAnalytic/TateContraction(+General); Foundations/AlgebraicGeometry/SourcePsi*Reduction* (8); IUTI/InitialTheta/ReductionPlacePartition/SplitReductionInput/SourceDefinition31D2Candidate; IUTII/Frobenioid/Example36LocalContraction; IUTIII/Theorem311/Indeterminacy/Ind1Reduction, Ind2Reduction, ConcreteRouteUniqueness, ParametricRouteAlgebra, Output/MultiradialAlgorithmReduction + GeneralRouteNormalForm, SourceFiniteRouteNaturality, SourceTheorem311ReferenceContract; Corollary312/StepXI/SourceRouteDeterminantNormalization, SourceSHETransportObligations; Audit/Diagnostics/LegacyContracts. Recommend adding these as coverage rows/nodes when routes are claimed.
- RED (last EXIT1; do-not-cite): PaperThetaLinkConsumerActual; S3128Stage1ModelHullGapConsumerActual; S3128Stage1PaperRootHullConsumerActual; S3128Stage1PaperSGapLeastActual; S3128Stage1PaperSHullClosureThetaConsumerActual; S3128Stage1PaperSHullQPilotConsumerActual; S3128Stage1PaperSVsGapConsumerActual; S3131PaperQFormulaE1Actual; S3131R2ReductionActual; S3131R2ReductionV2Actual; S3136Gap2AdditiveThetaFormActual.
- OLEAN_MISSING 11 files (see REPO-ROUTE-INDEX §); incl ABCBridge/Bridge/ABCGap2FiniteC3Supply, SourcePsi reduction family, IUTI SourceDefinition31DualContractAlignment, Theorem311/SourceK1K2CardReduction.

## 5. Route families (coord/ROUTE-MENTIONS.md, 10 families)
| family | status | note |
|---|---|---|
| R1 direct-readout/fixed-shell | ARCHIVED | invalidated route |
| R2 eta-algorithm | ACTIVE/EXPERIMENTAL | EtaValueGroupLine/EtaIntegralStructureS/EtaRssNontrivialActual zero sorry; target_accepted=false |
| R3 paper Stages1-5 + four triangles | AUDIT MAP | BPS absent named; dsc missing; APT evidence only |
| R4 N8 closure (dsc+APT+IPL) | DESIGN | no Lean closure |
| R5 endgame Option-B model | PREPARED/AWAIT GO | no closure |
| R6 3.11.5 label | CONCEPT | string never in papers |
| R7 abc paper-lambda | PARTIAL | rational component delivered |
| R8 historical probes | DEAD | context only |
| R9 weighted q | PARTIAL | — |
| R10 prestack | OBSTRUCTION | — |

## 6. Obstructions / paper-side gaps recorded
- SG3b tensor Haar product identity (no actual product-Haar formula; coord/SG3B_TENSOR_HAAR_BLOCKER.md).
- S2826 C3 region vs fractional-lattice region not actual (blocker).
- S2804 Cor312 reduces to single analytic S2717UpperGap; theta-pilot carrier/hull/log-volume actual, upper gap missing.
- S2802 height dictionary != height-volume inequality.
- modelIndex obstruction; NativeC3 sorry; direct-readout invalidated; fixed-shell degeneracy (ROUTE-MENTIONS §C).
- IUT IV paper gaps: Prop 1.1/1.2/1.4/1.5(general)/1.8, Thm 1.10 actual log-volume estimate, explicit PNT constants; E-5 (b)/(c).

## 7. Honesty / usage
- Paper citations are corpus txt with auto-index heuristics (sections may double-count marked-up variants; theorem-like counts approximate). No claim that a paper result is formalized unless a repo node/status says so.
- This document adds no math and no gate rows; repo statuses are latest verified pins where marked (mainline checker), otherwise TREE ASSET/prior inventory.
- DAG integration: paper nodes belong in coord/target-chain.paper*.json (paper: prefix; status NAMED/GAP allowed; never PROVED unless repo evidence). Existing: paper-routes (42/70 latest), paper-theta (383/1082). Declaration DAG merged & validated (689 nodes/1451 edges/0 conflicts; decl validator problems=0).
- Gate: V150@18248/CFC6CE08; GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041 / record 18800; no un-HOLD.