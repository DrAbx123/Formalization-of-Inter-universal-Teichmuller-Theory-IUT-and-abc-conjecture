# E — EXISTING CLOSURE MAP (mainline/李维, Lead A426; research only, no new math, no gate)

Scope: Problem E = deep IUT inputs (E-1..E-5). Sources: LeanFormal/IUT whole tree (IUTI 69 files, IUTII 194, IUTIII 190, IUTIV 14, Foundations 539, ABCBridge 164), tmp historical implementations + ported assets (tmp/external/ported/*, tmp/sheaf/xif/paper/*), coord inventories (IUT-EXTERNAL-OBJECTS-INVENTORY, IUTIV-SECTION1-PLAN, S2802/S2804/S2826/SG3B, PROBLEM-E-INVENTORY, FOUNDATION-FIRST-PLAN). External: LANA project (ZEN/U-Tokyo/Kyoto IUT computer-assisted verification, zen.ac.jp announcement) and Mochizuki source PDFs for definitions.

Conventions: 'CITABLE' = mainline has fresh EXIT0 + checker probe_ok (naming: xif paper files). 'TREE ASSET' = LeanFormal/IUT file with olean present per prior inventories, NOT re-checked in this survey (mark honestly). Extension points list what is missing to approach the paper object; no new proof attempts here.

## E-1 AbsTopIII05 (deep local-field/log-shell reconstruction + log-Frobenius compatibility + Z-graph anabelian data)
### Existing real objects
- `LeanFormal/IUT/IUTII/Kummer/SourceLogShellAbsTopIIIBridge.lean` (18827B, 24 decls): `SourceLogShellDatum` + `SourceLogShellInvariantImageIdentification:70`, `invariantImageIdentification_iff_unitLayer_subset:76`, `..._iff_forall_log_mem:85`, `codomainKummerContained_of_invariantImageIdentification:98`, `invariantImageIdentification_of_invariants_eq_top:104`, `..._iff_invariants_eq_top_of_injective:114` — real bridge between invariant image and unit-layer (TREE ASSET; olean per inventory).
- `LeanFormal/IUT/IUTII/Kummer/MonoAnalyticLogShellArchPsiCnsCalibration.lean` + `MonoAnalyticLogShellProbe` etc. (log-shell analytic calibration; TREE ASSETS).
- `LeanFormal/IUT/IUTIV/ArithmeticDivisorDegree.lean` (94950B): `heightWeight`, `hTerm`, divisor-degree machinery (per IUTIV plan lines 1214/1221/1225/1310; TREE ASSET).
- `tmp/sheaf/xif/paper/AbsTopIII01LogShellActual.lean`; `AbsTopIII03Cor510Actual` (Cor 5.10(i) finite log-volume concrete, per IUTIV-SECTION1-PLAN §3); `AbsTopIII05ReconstructionInputsActual` (DeepInput x4; `absTopIIIDeepInputs_none_proved`); `AbsTopIII05RefinedActual` (CITABLE 16/10562B sha 08816FDE probe_ok): D1 `Prop58iLocalFieldReconstruction`, D2 `Prop58iiLogShellReconstruction`, D3 `Cor55LogFrobeniusCompatibility` (bridgeAnchor discharged from SourceLogShellAbsTopIIIBridge), D4 `OrientedGraphAnabelianData` (zActionAnchor discharged from chainTranslation_graphAut), `refinedDeepInputKinds_eq_original` rfl linkage, `S3171RouteSlot` + `s3171RouteSlot_display_and_abc` (reuses thm110 display).
### Extension points (distance to paper object)
- Prop 5.8(i)(ii) reconstruction content (p, p*, p^f, [k:Q_p], e, unit layer/image, log-shell diagram functoriality) is NAMED in refined file; not constructed.
- Cor 5.5 global/panalocal log-Frobenius compatibility and Section-0 combinatorial data named; local log-Frobenius iteration exists separately (E-2 files).
- Genuine anabelian reconstruction (tempered fundamental groups / log-shell as scheme-level object) absent; only abstract Prop fields.
### Obstructions / failed routes
- No AbsTopIII/anabelian formalization in pinned Mathlib or TauCeti (grep 0); port-on-demand found none; deep theory not available as lemma.
- Direct field/structure realizations would require Frobenioid/anabelioid APIs that are not modeled in tree (IUTI HodgeTheater files exist but interface-level, per IUT-EXTERNAL-OBJECTS-INVENTORY).
### Reuse suggestions
- Use SourceLogShellAbsTopIIIBridge invariantImageIdentification lemmas as discharged anchors (already done in D3); reuse log-shell/Frobenius power family for local content; keep Prop 5.8 reconstruction as paper-scope named with typed fields (refined D1/D2) rather than free Prop.
- External definition sources for paper scope: Mochizuki, [AbsTopIII] (kurims.kyoto-u.ac.jp/~motizuki); 'anabelioid'/'Frobenioid' terms PDF.

## E-2 H5 O^x stabilization (+ det/tensor bookkeeping)
### Existing real objects
- `tmp/sheaf/xif/paper/Hull09H5GapsActual.lean` (5405B; CITABLE per prior audits): `hull09_scalingUnits_subset_hull`, `hull09_hull_eq_closure`, `hull09DetTensorBookkeeping_exponent`, `hull09_ray_mem_iff` — hull/volume inequality framing PROVED.
- `LeanFormal/IUT/Foundations/AlgebraicGeometry/LogShellFrobeniusPower.lean` (3577B, 4 decls): `localUnitFrobenius_iterate:32`, `localUnitFrobenius_log:43`, `localUnitFrobenius_iterate_log:53`, `principalUnitLogShellFrobenius_iterate_apply:64` (TREE ASSET) — local unit Frobenius iterates (H5/H7 fuel).
- `.../LogShellFrobeniusConsumer.lean` (2502B, 5): `frobeniusPowerConsumer_apply:23`, `_apply_nsmul:31`, `logShellScale_eq_prime_of_ne_two:40`, `frobeniusPowerConsumer_apply_logShellScale:47`; `...ConsumerGeneral.lean` (4451B); `...P2Boundary.lean` (3268B) (TREE ASSETS).
- `LeanFormal/IUT/IUTII/Frobenioid/SourceKappaOrbitUnitsActionSupply.lean:12` (O^x units action), `SourceKappaOrbitFactorizationProvider.lean:33`; `IUTII/Kummer/SourceLogShellCodomainClosure.lean:290` (O^x) (TREE ASSETS).
- `tmp/sheaf/xif/paper/Hull06DetTensorActual.lean` (det/tensor bookkeeping); `Hull11PreciseConsumerActual` 5862B sha D0C2250A probe_ok (precise H6 witness consumed).
### Extension points
- H5 full `O(-)^{-1}` normalization and `hull <= image-volume` inequality remain class-B named in Hull09/Hull11 lines; det/tensor bookkeeping only exponent-level.
- Consumer wiring of H5 named inputs into Hull11/13 hypotheses still string/Prop level.
### Obstructions / failed routes
- SG3b tensor Haar product identity `actualC3LogShellTensorLogVolume C3 = packetLogVolume packet`: NO actual product-Haar formula; exact first error recorded in `coord/SG3B_TENSOR_HAAR_BLOCKER.md` (set-level image only, no measure pushforward; no fake packet).
- `coord/S2826_C3_REGION_FRACTIONAL.md`: C3 region vs fractional-lattice region formula NOT actual (precise blocker); `S349C3TensorLatticeRegionActual` gives lattice region only.
### Reuse suggestions
- Reuse LogShellFrobeniusPower/Consumer for H5 local O^x content; keep full O(-)^{-1} normalization as named with exact required inequality; do not attempt tensor Haar product without real measure-pushforward API (port-on-demand first).

## E-3 H7 / Ob9 arbitrary iterate
### Existing real objects
- `tmp/sheaf/xif/paper/Hull08Ob9LogLinkActual.lean` (5921B): `HullOb9Inputs`, `hull_ob9_interface`, `hull_ob9_repClass_congr` PROVED interface/rep-class congruence.
- `Hull12Ob9BoundTransferActual.lean` (4453B): `hull12_upperBound_transfer`, `_base` — ONE-SIDED upper-bound transfer PROVED.
- `Hull13H7Ob9ComparisonConsumerActual.lean` (4543B): `HullH7Ob9ComparisonInputs`, `hull13_h7ob9_comparison` (Cor312 conclusion AND one-sided base bound); `Hull13TwoSidedBoundActual.lean` (5260B sha 79F714C0 probe_ok): `HullH7Ob9TwoSidedInputs`, `hull13_twoSided_bound`, `hull13_twoSided_upper_projection` (both-sided bound framework, upper projection proved).
- `LeanFormal/IUT/Foundations/AlgebraicGeometry/LogShellFrobeniusPower.lean` iterate lemmas (above) provide the local iterate content; `Indet01/02/03` finite-instance laws (A35 layer).
### Extension points
- Both-sided (arbitrary-iterate independence) bound remains named deep Ob9; one-sided transfer + upper projection proved; no unconditional two-sided theorem.
### Obstructions / failed routes
- No found counterexample; obstruction is absence of arbitrary-iterate uniform bound (paper-level deep). Named as deep class-B; no fake axiom.
### Reuse suggestions
- Build both-sided bound from Hull12 one-sided + Hull13 two-sided framework; need only the missing deep inequality; keep named explicit with paper line.

## E-4 EtTh realization deeper rows
### Existing real objects
- `LeanFormal/IUT/IUTII/Frobenioid/Example36SourceEtaleThetaTheory.lean` (19374B, 24 decls), `Example36SourceThetaGenerator.lean`, `Example36TateUniformization.lean` (50169B, 69 decls) — concrete Example 3.6 theta/étale-theta/Tate uniformization source-generation (TREE ASSETS).
- `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/`: `HaarTranslateRealLineLogFrobeniusCompatibility.lean:27` (LogFrobenius compatibility), `HaarTranslateRealLineLogCompatibility.lean:11`, `HaarTranslateRealLineShellHomotopyRadialAngular.lean:298`, `CertificateComparisonBridge.lean:40` (ThetaHull), `HullDeterminantLogVolumeReduction.lean` (34929B, 39 decls; `HullDeterminantLogVolumeFrozenSpec:123`/`_holds:153`, `matrixLogDet_mul_posDef:179`, `_smul_posDef:187`, `_kronecker_posDef:197`, `_pow_posDef:213`) (TREE ASSETS).
- xif paper: `EtTh07ConcreteBridgeActual`, `EtTh07ThetaFunctionValuesActual`, `EtTh08ThetaTransformationActual`, `EtTh09ThetaShiftCorollariesActual`, `EtTh10ThetaQuotientLawsActual`; `EtTh11ThetaRealizationRowsActual` (theta/elliptic power-kernel monotonicity, mod-L projection sujective), `EtTh12ThetaQuotientKernelRowsActual` (quotient/kernel laws), `EtTh13ModLFactorizationActual` (mod-L factorization); `Mzk1EtThRealizationConsumerActual` CITABLE 14/11293B sha C12C6CAC probe_ok (11 rows: 3 class-B named = geometric realization / Frobenioid representation / actual theta transform; 8 proved/reused), conditional thm25/genEll consumer wiring, 3 blocker rows.
### Extension points
- Scheme-level theta realization and Frobenioid representation of theta remain named; realization deeper rows (paper's actual theta-transform content) absent.
- No portable EtaleTheta/ThetaGroup/Frobenioid asset (grep 0 in tree/TauCeti/Mathlib); port-on-demand none.
### Obstructions / failed routes
- External: no formalization found; LANA project is the only known computer-assisted verification effort (external, not a Lean asset).
### Reuse suggestions
- Reuse Example36 concrete theta/Tate uniformization + HaarTranslate LogFrobenius compatibility + HullDeterminant matrixLogDet as real substrate; keep 3 named realization rows with exact paper statements; no fake packet.

## E-5 IUT IV §1 (uniform height-vs-volume / final log-volume estimates)
### Existing real objects
- `LeanFormal/IUT/IUTIV/`: `ArithmeticDivisorDegree.lean` (94950B; heightWeight/hTerm/divisor-degree), `ArchimedeanTensorMetric.lean` (17650B), `ArchimedeanMultiTensorMetric.lean` (29837B), `DifferentDegreeUpperBound.lean` (13417B), `DifferentTameEquality.lean` (11364B), `DifferentTowerEstimate.lean` (7327B), `ElementaryEstimates.lean` (8030B), `Section1.lean` (13808B), `Section2.lean` (27185B), `StepVDivisorAverage.lean`, `StepVDistinguishedSlotAverage.lean`, `StepVProcessionAverage.lean` (12974B) (TREE ASSETS).
- `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/`: `SourceUnitRegionHaarDataActual.lean` (sourceHaarActualOriginalInput:346, ImageRealization:374, UnitRegion:407, Data:416, :458; per PRIOR-ART-INDEX), `IQCarrierConcreteModel.lean` (interface:193, logShellPoint:230, hunit:303/315, hweightvol:346), `CardAMPLThetaBoundSupply` (hull<=theta), `HullDeterminantLogVolumeReduction`.
- `LeanFormal/IUT/ABCBridge/Bridge/`: `Cor312ComparisonGapReduction.lean:306` (cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegion...), `Cor312CarrierRealizationSpec.lean` (34057B, 21 decls), `ABCFrontier*.lean` (height-volume references).
- xif paper: `S3131PaperRouteSkeletonActual`, `S3131PaperRouteABCBridgeActual`, `S3131PaperRouteHeightReductionActual` (undilated => (b)), `S3131PaperRouteRegionReductionActual` (undilated => (c)), `S3131PaperRouteFieldStatementsActual`, `S3131RouteComparisonIn*`, `S3137` route objects; `S3171IUTIVSection1StatementActual` (4742B), `S3171IUTIVSection1EstimatesActual` (2879B), `S3171IUTIVSection1InputsActual` (3351B), `S3171IUTIVSection1DisplayActual` (6921B; thm110_final_display exact display), `S3171UniformHeightConsumerActual` (4449B; undilatedHeightBound_of_valuation_bound), `S3171AuditIUTIVSection1`, `S3171IdsActual`.
- Actual hweightvol inequality: `S2752FinalHweightvolActual`/`S2752_hweightvol` (per S2804: ACTUAL); S3131 reductions; `S2717UpperGap` (Cor312 target reduces to it; S2804); `S2822PointRealizationRouteActual` (point realization actual, 59552B olean per S2822).
### Extension points
- (b) `UndilatedHeightBound` and (c) `UndilatedRegionBound` remain class-B named (IUTIV-SECTION1-PLAN; S3171 files conditional); final display conditional on them.
- Uniform height-vs-volume comparison not constructed; region-relative-to-hull/weight inputs named.
### Obstructions / failed routes
- `coord/S2802_HEIGHT_COMPARISON_INVENTORY.md`: point-height dictionary is NOT the height-volume inequality (key distinction; no shortcut).
- `coord/S2804_COR312_INVENTORY.md`: Cor 3.12 currently a real reduction to ONE analytic inequality `S2717UpperGap` (theta-pilot carrier/hull/log-volume, local log-shell interfaces, H1/H2 actual; missing upper gap + ATheta geometric objects + D-Theta realization gate).
- `coord/S2826_C3_REGION_FRACTIONAL.md`: C3 fractional-lattice region formula not actual (blocker); `SG3B_TENSOR_HAAR_BLOCKER.md`: no product-Haar formula.
- `coord/FRD-I-II-S3128-GAP.md`: FRD I-II port route has `Over.mapId_eq` motive mismatch (recorded gap per line 97).
### Reuse suggestions
- Reuse ArithmeticDivisorDegree + Archimedean tensor metrics + Different tower estimates + StepV averages + IQCarrier/Hull determinant + S3131 reductions; keep (b)/(c) named with exact inequalities; target S2717UpperGap as the single analytical endpoint (S2804).

## Cross-cutting: external citable references
- LANA project (ZEN Mathematics Center + international collaboration) — computer-assisted verification project for IUT theory: https://zen.ac.jp/news/zmcpostevent0331e (also JP announcement https://zen.ac.jp/news/zmcpostevent0331). Context for external verification; not a Lean asset.
- Mochizuki source papers for paper-scope definitions: [IUT I-IV], [AbsTopIII], 'On the terms anabelioid and Frobenioid' — https://www.kurims.kyoto-u.ac.jp/~motizuki/ (e.g. https://www.kurims.kyoto-u.ac.jp/~motizuki/On%20the%20terms%20'anabelioid'%20and%20'Frobenioid'.pdf).
- Search finding: no existing Lean/Coq/Isabelle formalization of IUT/AbsTopIII/Frobenioid/theta realization was found; current repo assets are the only known formal substrate (plus LANA, in progress externally).

## Summary table
| item | real objects (examples) | citable status | missing layer | reuse |
|---|---|---|---|---|
| E-1 AbsTopIII05 | SourceLogShellAbsTopIIIBridge (24 decls); AbsTopIII05Refined 10562B 08816FDE; AbsTopIII01/03 | CITABLE (refined); TREE (bridge) | Prop5.8(i)(ii) reconstruction, Cor5.5 global/panalocal, Section-0 combinatorial data | discharged anchors D3/D4; typed refined fields |
| E-2 H5 O^x | Hull09H5Gaps; LogShellFrobeniusPower/Consumer/General/P2Boundary; KappaOrbit units files; Hull06/Hull11Precise | Hull09 TREE/prior-audit; others TREE | O(-)^{-1} normalization, hull<=image-volume inequality; tensor Haar product | reuse Frobenius iterate/consumer for local units |
| E-3 H7/Ob9 | Hull08/12/13 + Hull13TwoSided 5260B 79F714C0; LogShellFrobeniusPower iterates; Indet01-03 | Hull triples CITABLE per prior audits; two-sided 5260 verified | both-sided arbitrary-iterate bound | one-sided + upper projection frame |
| E-4 EtTh | Example36* (19374/50169); HaarTranslate LogFrobenius/Log compatibility; HullDeterminant 39 decls; EtTh07-13 rows; EtThRealizationConsumer 11293 C12C6CAC | TREE + CITABLE consumer | scheme-level theta realization, Frobenioid representation, actual theta transform | Example36 + HaarTranslate + matrixLogDet as substrate |
| E-5 IUT IV §1 | IUTIV Section1/2/ArithmeticDivisorDegree/Archimedean/Different/StepV; SourceUnitRegionHaarData/IQCarrier; Cor312GapReduction:306; S3131*/S3171*; S2717UpperGap | TREE + S3171 citable conditional; S2752 hweightvol ACTUAL | (b) UndilatedHeightBound, (c) UndilatedRegionBound, uniform height-volume inequality | target S2717UpperGap; reuse display chain |

## Integration note
- lattice has `coord/E-EXTENSION-PLAN.md` skeleton; this map is research-only (no new math, no gate, no wiring). No gate edit; GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041.
## QPILOT A426 MAPPING CROSS-REFERENCE (coord/PROBLEM-E-MAPPING-qpilot-A426.md, 11KB; merged summary)
qpilot surveyed tree/tmp under read-only discipline; key additions to the above:

### Analytic theta foundation (Foundations/Theta, 10 files)
- Real objects/theorems: OddTheta q-series (oddThetaSign/term/shift/summability), OddThetaRootData/PacketNormalization, Nonvanishing, SignedLabelEquiv, GaussianKernel/SquareSum (file:line listed in qpilot doc).
- BUILD GAPS (mechanical): `OddThetaNegativeDecay.lean`, `OddThetaTermAlgebra.lean` olean missing.
### Theta-link / Etale / log-shell (IUTII)
- Real: `EtaleThetaQuotient` (thetaDerivedSubgroup/thetaCommutatorKernel/ThetaQuotient/EllipticAbelianization/power kernels/mod-l projections), FiniteThetaPacket, ThetaLinkAssembly/SourceCover, UnitGeneratedMonoidComparison, ConcreteSourceEtaleThetaBridge (oleans present). `SourceLogShellCarrier` (SourceLogShellDatum p/p*/K/Units/invariants/logMap; preLogShell/logShell/unitLayer) + `SourceLogShellAbsTopIIIBridge` are real reduction carriers for Prop 5.8(ii)/Cor 5.5.
- BUILD GAPS: `AbsoluteKummer{Continuity,Injection,Quotient}.lean`, `SourceThetaPilotIQContainment.lean` oleans missing (bi-Kummer/EtTh §4 prerequisites).
### AbsTopIII05 paper layer
- `AbsTopIII01..14` xif paper files: all EXIT0+olean (except `AbsTopIII05Section0ObjectsActual` being edited); 01 log-shell laws / 03 Cor5.10 / 04 logFrobenius unit landing / 05ReconstructionInputs (4 named) / 05Refined (CITABLE 16; D1-D4 typed; D3/D4 anchors discharged from tree) / 06-09 volume-scaling / 10-14 ledger-psi-field-scaling.
### EtTh realization rows
- EtTh00-13 all EXIT0+olean; real objects EtaleThetaKummerClass/EtaleThetaObject/MonoThetaEnvironment/EtThThetaGroupObject/quotient laws/oddTheta term rows.
- class-B unformalized = EtTh02 ten deep inputs (Prop1.1/1.3/1.4/1.5/Thm1.6/Thm1.10/Prop3.2/3.4/§4) + EtTh11 rows 5-7 (geometric realization / Frobenioid manifestation / actual theta transformation). Conditional consumer Mzk1EtThRealizationConsumerActual CITABLE 14 (status-only).
### IUTIII anchors
- ThetaPacketBridge.toPositivePacket/theta logVolume; HolomorphicHull/CardAMPLThetaBoundSupply (realVolume_le/cor312Conclusion); SourceLogShellMuNQuotientCarrier.muNQuotient/weightNLog; CardHullRealEdge* (AbsTopIII Prop 5.7 normalization citation). Top layer only Corollary312/Theorem311.
### Paper-object gaps (Prop 5.8/Cor 5.5/Section-0)
- Prop 5.8(i) missing G_k/G_ab, O^◇/k^× image embeddings, group-theoretic algorithm, Verlagerung functoriality; Prop 5.8(ii) missing Γ^×_non diagram/CMLF categories and Ob(TG^⊢)∋G↦Γ^×_non(G) algorithm; Cor 5.5 missing D^• seven-row category diagram/global-panalocal compat (bridge card reductions proved); Section-0 missing general oriented graph/underlying graph/branches/countably ordered sets/Order(E)/pre-path/path iso classes/saturated sets - only Z-graph model (FrobeniusPictureArrow/Aut/chainTranslation_graphAut real) + Section0Objects being edited.
### Expansion order (per qpilot, cost-ordered)
1. build OddThetaNegativeDecay/TermAlgebra; 2. build AbsoluteKummer*/SourceThetaPilotIQContainment; 3. organize SourceLogShellDatum.muNQuotient+logShell laws into Prop 5.8(ii) concrete diagram object layer; 4. finish Section0Objects; 5. match Example36 Frobenioid boundary model to EtTh05/11 Frobenius rows; 6. Prop 5.8(i)(ii)/Cor 5.5 algorithmic parts = new theory (grep 0 assets in tree/TauCeti/Mathlib) -> keep named.
### Ported/tmp note
- No IUT theta port (TauCeti theta = Jacobi/modular, unrelated; flt_core RR chain separately landed A424). Historical tmp dirs (root-dtheta/theta-route/theta-link-resolution/odd-theta-nonvanishing/source-theta-pilot-iq/fractional-absorption) only probes/logs, no active implementation.

## D-RR BOTTOM EVENT (A427; mainline verification)
- hull `Mzk1GeomCoreRRProvedActual` EXIT0 15877B sha 813224A54A838673; checker WITH _Mzk1GeomCoreRRProvedProbeActual = CITABLE 14 decls probe_ok TRUE; `zero_divisor_exists_proved` PROVED with NO named inputs (hRR=functionFieldRiemannRoch_proved, hdual=flt_core ell_eq_zero_deg_neg + canonical bound + punctureDivisor=|T|); only flt_core root; base pencil layer reintroduced; legacy flt_test Foundation retained (scheme layer legacy due flt_th deps). => D-RR = BOTTOM.
- C StepProvider prelim: `Mzk1NestedInductionStepProviderActual` CITABLE 8/5647B sha CD14AEB3 probe_ok: f0Map/f0Map_comp/eval_eq_aeval_self/stepSetP, stepTransport_of_goal conditional on named CVCompositionLawF; geometry f1/f2/f4 proved; CVCompositionLawF + fixed-beta + P1 measure completion remain named (NY-2).