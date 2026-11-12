# SKELETON — IUTI (69 files) + IUTII (194 files) node graph (aibi, Lead A429; research only, no gate)

Scope: map the IUTI/IUTII tree modules: Hodge theater objects, Initial-Theta, log-shell, Frobenioid (Example 3.6 suite), EtaleThetaQuotient, Tate uniformization, source theta pilot; per module list key files + declarations + status + dependencies + consumers; mark the IUTII -> IUTIII interfaces (EtTh, log-shell, Frobenioid transport, theta pilot). No new math, no wiring, no gate edit.

Conventions (same as IUT-EXTERNAL-OBJECTS-INVENTORY / FOUNDATIONS-IUTIV):
- TREE ASSET = LeanFormal/IUT file with olean present per prior inventories, NOT re-checked in this survey.
- CITABLE = fresh EXIT0 + checker probe_ok (xif paper files, mainline-audited).
- statement-only / class-A reuse / class-B named as in coord/FOUNDATIONS-IUTIV.md.
- Counts: IUTI 69 .lean files; IUTII 194 = Frobenioid 141 + Kummer 44 + Theta 9.

## 1. IUTI / HodgeTheater (Hodge theaters, theta-link combinatorics, Definition 3.1 carriers)

| module | key files | representative declarations | status | consumers |
|---|---|---|---|---|
| source Hodge theater family | SourceHodgeTheaterFamily.lean (40KB); SourceHodgeTheaterFamilyLawsReduction (33KB); SourceHodgeTheaterFamilySourceReduction (17KB); SourceHodgeTheaterHistoriesReduction (13KB) | structure SourceHodgeTheaterFamily; theater; theater_injective; theater_eq_iff; link_refl_at/link_symm_at/link_trans_at; link_q; link_scale; link_q_symm/link_q_trans; link_scale_symm/link_scale_trans | TREE ASSET (real structure + link laws) | IUTI theta-link reductions; IUTII Theta; source-theta carriers |
| Hodge theater core / history / prime strip | HodgeTheaterCore; History; PrimeStripCore; LocalPrimePlaces; LinkVolumeTransport; ConcreteHodgeTheaterExample; ConcreteIntegralHodgeTheaterExample | core Hodge theater data; history/link objects; prime strips; local prime places; link volume transport; concrete examples | TREE ASSET | InitialTheta; Frobenioid prime strips |
| theta-link combinatorics | SourceThetaLinkGraphAutomorphismReduction (11KB); SourceThetaLinkDisplacementReduction (20KB); SourceThetaLinkArithmeticDisplacementReduction (12KB); SourceThetaLinkDivisorMonoidDisplacementReduction (18KB) | FrobeniusPictureArrow; FrobeniusPictureGraphAut; graphAut_step; graphAut_translation; chainTranslation; chainTranslation_graphAut; graphAut_eq_translation (automorphisms = translations); displacement reductions | TREE ASSET (used by CITABLE AbsTopIII05RefinedActual D4) | AbsTopIII05Refined (D4 anabelian data); EtTh/theta-link |
| Definition 3.1 carriers / gates | SourceDefinition31CarrierConsolidation; SourceDefinition31A2GateReduction; SourceDefinition31DualContractAlignment; SourceDefinition31NativeContractBridgeReduction; SourceDefinition31SignQuotientSupplyReduction; SourceClauseAssemblyUnitsReduction (24KB) | Definition 3.1 carrier structures; A2 gate; dual contract alignment; native contract bridge; sign quotient supply; clause assembly units | TREE ASSET | InitialTheta Definition31 cluster; Kummer sign/unit quotient |
| geometric core / etale stack supply | SourceGeometricCoreFieldUnitsReduction (20KB); SourceEtaleStackInstanceSupplyReduction (12KB); SourceTheaterRealization (12KB); SourceObligations | geometric core field units; etale stack instance supply; theater realization; SourceObligations | TREE ASSET | Frobenioid Example36 source model; IUTIII Cor312 |

## 2. IUTI / InitialTheta (Initial Theta data, Definition 3.1 arithmetic, Tate/place data)

| module | key files | representative declarations | status | consumers |
|---|---|---|---|---|
| initial theta data | SourceInitialThetaData.lean (182KB); SourceArithmeticPrelude (16KB); SourceCompletion (52KB); SourceClauseConstructors (52KB) | initial theta data structures; arithmetic prelude; completion; clause constructors | TREE ASSET | IUTII Kummer log-shell; IUTIII StepXI |
| root lemmas / Definition 3.1 quantifiers | SourceDefinition31RootLemmas (207KB); SourceDefinition31Quantifiers (69KB); SourceDefinition31Boundary (59KB); SourceDefinition31D0D11Aligned (64KB); Definition31D0D11FromSource | D0-D11 alignment; root lemmas; quantifier slots; boundary; D2/D3/D4 roots/supplies; D4FK descent; D4TateQ identification; D5-D8 root | TREE ASSET | Frobenioid Example36; Kummer source packets |
| place partition / local valuation | SourceDefinition31PlacePartition; SourcePlacePartitionReduction (45KB); SourceDefinition31LocalValuationSections; SourcePlaceSelection; SourceLocalTateBoundary | place partitions; local valuation sections; place selection; local Tate boundary | TREE ASSET | Frobenioid global place data; Tate uniformization |
| orbicurve / torsion / sign | SourceDefinition31OrbicurveInstance; SourceSignQuotientConstruction; SourceTorsionCarrierReduction; SourceTorsionRankOneQuotient; SourceTorsionTransport | orbicurve signature; typeOneOne/typeOneLTorsion signatures and genus/puncture rfl lemmas; sign quotient; torsion carrier/rank-one/quotient | TREE ASSET | Kummer K1/K2 boundary; EtTh |
| concrete initial theta | ConcreteArithmeticExample; ConcreteInitialThetaCStage (16KB); ConcreteInitialThetaLinks; ConcreteInitialThetaLocalArithmetic; ConcreteInitialThetaFiniteArithmetic; ConcreteInitialThetaTransport; ConcreteInitialThetaCObligations; ConcreteFinitePlaceBoundary | concrete initial theta C-stage; links; local/finite arithmetic; transport; finite place boundary | TREE ASSET | IUTII Theta ConcreteSourceEtaleThetaBridge (cStage/packet/parameter/quotient/theater abbrevs) |

## 3. IUTII / Frobenioid (Example 3.6 suite, prime strips, local monoids) — 141 files

Group | key files | representative declarations | status | consumers
---|---|---|---|---
Example36 source model | Example36SourceModelBackend; ...BackendBalance(+Group); SourceModelDivisor; SourceModelFunctor; SourceModelBackend; SourceCurve/SourceFrobenioidBridge; SourceObjectBridge | concreteStageModel; source model backend/balance; source model divisor/functor; curve/frobenioid bridge | TREE ASSET | Theta ConcreteSourceEtaleThetaBridge; Frobenioid transport |
Example36 curve / Galois | Example36CurveScheme; Example36CurveProjectiveClosure(+DirectGlue, 60KB/29KB); CurveConnectedness; CurveEtaleCovers; CurveGaloisCategory (37KB); SpecCover*; GSetEtaleEquivalenceAssembly (103KB); GSetToEtaleAlgebra (58KB) | projective closure; etale covers; Galois category; Spec cover equivalences; GSet-etale equivalence assembly; etale-to-algebra | TREE ASSET | EtTh realization; Cor312 |
Example36 Tate uniformization | Example36TateUniformization (50KB); TateGaloisAction (50KB); TateModuleProfinite (44KB); TateInverseJCanonical; EllipticCurveTateHigherLevel; EllipticCurveAnabelioid; EllipticCurveSourcePiCard | concreteFiveTateParameter; concreteFiveTateCurve and norm/delta/c4 lemmas; Tate module profinite; Galois action; inverse J; higher level | TREE ASSET | theta-link theta packet; EtTh |
Example36 theta / log-shell | Example36SourceEtaleThetaTheory (19KB); SourceThetaGenerator; ThetaGeneratorFeasibility; ThetaSeries; LogShellLattice (29KB); LogShellFrobeniusAction (17KB); LogDomainActual; LogKummerMap; SourceLogKummerIdentification; SourceLogLinkCompatibility | sourceEtaleThetaTheory (fivePrimeLabel, sourceCurve eqs, delta); concreteLogShellField; principalUnitLogShell_mem_iff; unitLog_principalUnit_eq_log1p; log-shell Frobenius action; log-Kummer map | TREE ASSET | AbsTopIII log-shell; Cor312 StepXI hull; Kummer log-shell |
Example36 Frobenioid transport | Example36FrobenioidTransport (40KB); PrimeStripFrobenioidCategorySkeleton (34KB); PrimeStripFrobenioidCards; PrimeStripFrobenioidSkeletonCards; PrimeStripFrobenioidValueGroupRationality; PrimeStripsFrobenioidLinks; SourceKappaOrbitUnitsActionSupply; SourceKappaOrbitFactorizationProvider; ValueMap* files | unitsMapOfRingHom (+apply/one/mul/pow/id); PlaceLocalizationTransport; deltaAdd_transport(_infinite); ramificationIndex_pos_int; prime-strip Frobenioid category skeleton/cards/value group rationality; kappa orbit units/factorization | TREE ASSET | Frobenioid transport interface to IUTIII; H5 O^x |
Example36 completion / local data | Example36CompletionEmbedding/IntoAlgCl/Isometry/NormFormula(+Actual); Gaussian*; LocalGaloisInvariantMonoid; LocalIdealValuation; LocalValueData; LocalContraction; GlobalIdealFamily(+Actual); GlobalPlaceData; NumberFieldPlaceData/CompletionBridge | completion embedding/isometry/norm formulas; Gaussian places/strips; local Galois invariant monoid; local ideal valuation; global place data | TREE ASSET | theta-link packet; log-shell |
local Kummer / prime strip (non-Example36) | LocalIntegralMonoid; LocalIntegralFPrimeStrip; LocalIntegralUnitKummer/EvaluationImage; LocalMLFPair/Bridge; LocalPrimeStrip; LocalTorsionCyclotome/Units; PrimeStrips(+Construction); PrimeStripDegree/Arithmetic; FinitePlaceFractionalIdealUnitQuotient; LocalFractionalIdealUnitQuotient; LocalGroupificationAction | local integral monoid; local (F) prime strips; unit Kummer/evaluation image; MLF pair; torsion cyclotome/units; prime strips construction/degree; fractional ideal unit quotients | TREE ASSET | Kummer O^x / H5; Frobenioid cards |

## 4. IUTII / Kummer (log-shell, Kummer classes/roots, mono-analytic log-shell) — 44 files

| module | key files | representative declarations | status | consumers |
|---|---|---|---|---|
| source log-shell | SourceLogShellCarrier (23KB); SourceLocalLogShellDatum; SourceLogShellAbsTopIIIBridge (19KB); SourceLogShellActionCompatibility; SourceLogShellActualTensorSpan; SourceLogShellCarrierTwistContainer; SourceLogShellCodomainClosure; SourceLogShellTensorLegCompletion | sourceLogShellStar/pStar; structure SourceLogShellDatum; preLogShell/logShell/unitLayer; codomainKummerContained; zero_mem_preLogShell; SourceLogShellInvariantImageIdentification; invariantImageIdentification_iff_unitLayer_subset; ..._iff_forall_log_mem; codomainKummerContained_of_invariantImageIdentification | TREE ASSET (bridge lemmas reused by CITABLE AbsTopIII05Refined D3) | AbsTopIII05/06/07; Cor312 StepXI |
| log-shell packets / tensors | SourceLogShellIQTensorPacket; SourceLogShellXMuPacket; SourceLogShellMuNQuotientCarrier; SourceLogShellTensorLegCompletion; SourceLogShellCodomainClosure; SourceLogShellActualTensorSpan | IQ tensor packet; X-mu packet; muN-quotient carrier; tensor leg completion | TREE ASSET | theta-link; H5/H6 hull |
| Kummer classes/roots | KummerClass; KummerGaloisClass; CanonicalKummerMap; KummerPolynomial; KummerRootRatio; CompatibleRoots; NatRootSystem; RationalRootSystem; RootRealization; AlgebraicClosureKummerRoots; TimesMuIsm | Kummer class/galois class; canonical Kummer map; Kummer polynomial/root ratio; compatible roots; root systems; root realization | TREE ASSET | EtTh theta packets; Cor312 |
| etale/absolute Kummer | ConcreteEtaleKummerBridge/Direction; AbsoluteKummerContinuity/Injection/Quotient; ContinuousKummerGerm; LocalGaloisKummerAction; LocalUnitKummerMap/Injectivity | etale Kummer bridge/direction; continuous Kummer germ; local Galois Kummer action; unit Kummer map/injectivity | TREE ASSET; BUILD GAP: AbsoluteKummer*.olean missing per qpilot A426 mapping | IUTIII Cor312; EtTh |
| mono-analytic log-shell | MonoAnalyticLogShellFormalLogMul (65KB); MonoAnalyticLogShellArchPsiCnsCalibration; MonoAnalyticLogShellCompactCarrier; MonoAnalyticLogShellMixedPacket; MonoAnalyticLogShellPadicLog; MonoAnalyticLogShellProbe; MonoAnalyticIndTopModuleData | formal log multiplication; arch psi-CNS calibration; compact carrier; mixed packet; p-adic log; module data | TREE ASSET | log-shell transport; H5/H6 |
| source theta pilot | SourceThetaPilotIQContainment (9KB); SourceUnitLogTensorLanding; K1K2BoundaryReduction; SourceK1K2ArchUpperSemiBridge; LocalFieldRigidity | IQ containment; unit-log tensor landing; K1/K2 boundary reduction; arch upper semi bridge | TREE ASSET; BUILD GAP: SourceThetaPilotIQContainment.olean missing per qpilot | theta-link; Cor312 |

## 5. IUTII / Theta (EtaleThetaQuotient, theta link, finite theta packet) — 9 files

| module | key files | representative declarations | status | consumers |
|---|---|---|---|---|
| etale theta quotient | EtaleThetaQuotient.lean (6KB) | thetaDerivedSubgroup; thetaCommutatorKernel; thetaCommutatorKernel_le_derivedSubgroup; ThetaQuotient; EllipticAbelianization; thetaToElliptic(+_mk); thetaPowerKernel; ellipticPowerKernel; ModLThetaQuotient | TREE ASSET | IUTIII EtTh realization rows; Cor312 |
| theta packet / link | FiniteThetaPacket; ThetaLinkAssembly; ThetaLinkSourceCover; UnitGeneratedMonoidComparison; EtaleTateDirection | thetaLink_unitPower; thetaLink_embeddedUnit; thetaLink_generator; thetaLinkSymm_apply; thetaLink_source/target_representation; thetaLink_unique; thetaLink_unitEquiv_ext; unitGeneratedMonoid comparison | TREE ASSET | theta-link layer; IUTIII |
| concrete theta bridge | ConcreteSourceEtaleThetaBridge (27KB); ConcreteSourceHistoryLinkBridge (26KB) | cStage; packet; parameter; quotient; finiteLabel; roots; theater; sourceModel abbrevs; concrete source theta/history bridges | TREE ASSET | AbsTopIII theta; Mzk1 EtTh consumers |

## 6. IUTII -> IUTIII interfaces

| interface | IUTII source | IUTIII consumer | status |
|---|---|---|---|
| EtTh realization | IUTII/Theta (EtaleThetaQuotient, ConcreteSourceEtaleThetaBridge) + IUTII/Kummer (KummerClass, CompatibleRoots) | IUTIII/Corollary312/StepXI (EtTh consumers, CertificateHullWiring, CardAMPLThetaBoundSupply) | real assets + class-B deep inputs EtTh02 (10 named D-inputs) |
| log-shell | IUTII/Kummer SourceLogShell* + IUTII/Frobenioid Example36LogShellLattice/Frobenius | IUTIII/Corollary312 StepXI HolomorphicHull; xif AbsTopIII01/03/05 (CITABLE 05Refined) | real carriers + named Prop 5.8/Cor 5.5 content |
| Frobenioid transport | IUTII/Frobenioid Example36FrobenioidTransport; PrimeStripFrobenioid*; SourceKappaOrbit* | IUTIII Frobenioid/StepXI transport rows; H5 O^x gap list | real stars/cards + named O(-)^{-1} normalization |
| theta pilot / IQ | IUTII/Kummer SourceLogShellXMuPacket / SourceThetaPilotIQContainment; IUTII/Frobenioid Example36SourceThetaDivisor/Generator | IUTIII Cor312 Q-pilot/hull comparisons (S3132* slots) | real packets; H4/H5 named |

## 7. Unmapped / mechanical findings (search of Source*/Concrete*/Example36*)

- Example36 suite is the dominant un-mapped mass (141 files): full Frobenioid source-model/curve/Tate/theta/log-shell transport stack; no single consumer file aggregates it (consumers are scattered IUTIII Cor312 StepXI + xif paper EtTh*/AbsTopIII*).
- BUILD GAPS (mechanical, per qpilot A426 mapping; not rechecked here): oddThetaNegativeDecay.lean / OddThetaTermAlgebra.lean olean missing; AbsoluteKummer{Continuity,Injection,Quotient}.lean oleans missing; SourceThetaPilotIQContainment.olean missing.
- Paper-object gaps (not mechanical): Prop 5.8(i)(ii) reconstruction, Cor 5.5 global/panalocal log-Frobenius compatibility, Section-0 general oriented graph/Order(E)/paths theory beyond Z-graph model; EtTh02 ten class-B deep inputs; tensor Haar product blocker (coord/SG3B_TENSOR_HAAR_BLOCKER.md); C3 fractional-lattice region blocker (coord/S2826_C3_REGION_FRACTIONAL.md); L2 cohomology statement-only (GeoAn/SemiAn/EtTh).
- HodgeTheater/InitialTheta are object layers consumed mainly by IUTI/IUTII themselves; the only direct xif-paper consumers found are AbsTopIII05RefinedActual (graph automorphisms D4 via SourceThetaLinkGraphAutomorphismReduction) and EtTh*/Mzk1 EtTh consumers via ConcreteSourceEtaleThetaBridge/EtaleThetaQuotient.

## 8. Status / honesty

- This is a RESEARCH SKELETON, not a gate artifact: no gate edit, no wiring, no new theorems; statuses TREE ASSET are prior-inventory claims, not re-verified in this survey.
- Gate NOT PASSED; binding HOLD; L8 frozen; pins registry 14041 (no registry edits).
- Cross-references: coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md, coord/FOUNDATIONS-IUTIV.md, coord/PROBLEM-E-INVENTORY.md, coord/PROBLEM-E-MAPPING-qpilot-A426.md, coord/E-EXISTING-CLOSURE-MAP.md, coord/ENDGAME-DEPENDENCY-LEDGER.md.
