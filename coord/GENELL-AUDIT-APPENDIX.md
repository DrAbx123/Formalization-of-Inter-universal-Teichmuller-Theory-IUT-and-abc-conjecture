# GENELL AUDIT APPENDIX (shehdd checker/audit/watch)

STEP 0 prior-art: queries height_le_weighted_logDiff|height_le_volume|volume_le_weight|genEll_transfer|thetaBound / weight_le_theta|RegionRelativeToHullAndWeight|hpoint|hweightvol|uniform.*height.*volume / GenEll Theorem 2.1 -> hits LeanFormal 4+74, paper 30+204, gap-exploration 2, vendor 24+44, corpus 1 -> reuse|adapt (no re-proving); new precedents in coord/PRIOR-ART-INDEX.md §G.

Task: GenEll formalization (Lead plan coord/GENELL-FORMALIZATION-PLAN.md §3). Registry FROZEN 14041 — no reopen/re-pin during GenEll work.

## Audit protocol (per batch)
1. STEP 0 line first (deep search + PRIOR-ART-INDEX sections A-F; append new precedents).
2. Per file: results.log last line EXIT=0; olean fresh; ACTUAL declarations (theorem/def/structure; no doc-only); declaration list matches report.
3. `tools/xif_citable_check.ps1 -File <f> -Probe <p>` => CITABLE (olean_fresh/last_exit/declarations/probe_ok).
4. Probe kernel: trio-only or no-axiom; ZERO sorryAx; report changed footprint.
5. Corpus fidelity: §1 99-604, §2 606-687 (Thm 2.1), §3 738-1199, §4 1200-1425; paper-proved-but-unformalized = precisely named paper-input (corpus line + status), never fake proofs.
6. No re-proving existing assets; no vendor imports (separate lake; explain instead).
7. Append audit row to this appendix + ledger.
8. Pins: registry 14041 / gate 23066 / record 18800 (frozen).

## Existing assets (STEP 0; all CITABLE, reuse only)
| file | decls | src bytes | src sha256 (prefix) |
|---|---|---|---|
| S3131BDClassCompositionActual.lean | 4 | 1149 | 7020035F4728B71561642426 |
| S3136BDClassChainToolActual.lean | 8 | 3110 | 84CE9D7678BACB669782A5BA |
| S3131GenEllPaperInputActual.lean | 4 | 1980 | D9749F3FE64FFB6EAD5E67C5 |
| S3131GenEllInputDetailedActual.lean | 7 | 2147 | 3D73BDCB2C1733010E6DA174 |
| S3131GenEllEquivalenceShapeActual.lean | 3 | 831 | D0CF6EF8D4320EA2E22752A9 |
| S3131GenEllShapeStatementsActual.lean | 4 | 1860 | 32F2863D6B59222153E25EF4 |
| S3131IUTIVTheoremAInputActual.lean | 3 | 1181 | 82B241221529BD7F8E7D73B6 |
| S3132IVGenEllShadowAdapterActual.lean | 3 | 3137 | 478A687EA4A53A78D0F2AFC6 |

## GenEll batch audit rows
| batch | file | status | decls | checker | probe | notes |
|---|---|---|---|---|---|---|
| P0 | GenEll00NamingActual.lean | EXIT=0 1610B | 2 | pending batch | GenEllP0Probe | observed |
| P0 | GenEll01BasicActual.lean | compiling | 7 | pending | GenEllP0Probe | §1 basics 99-604 |
| P0 | GenEll05Theorem21Actual.lean | compiling | 7 | pending | GenEllP0Probe | Thm 2.1 615-687 |
| P0 | GenEll06Section3StatementsActual.lean | compiling | 5 | pending | GenEllP0Probe | §3 738-1199 |
| P0 | GenEll07Section4StatementsActual.lean | compiling | 5 | pending | GenEllP0Probe | §4 1200-1425 |
| P0 | GenEll08MainReductionActual.lean | compiling | 5 | pending | GenEllP0Probe | main reduction |
| P0 | GenEllP0Probe.lean | queued | - | - | - | prints theorem21_i_implies_ii etc. |

## Watch list (paper-level, next)
- (c) weight<=theta + hpoint/dictionary (hull half free via CardAMPL); (b) height<=volume, volume<=weight+thetaBound+D; GenEll Thm 2.1 statement; route bridges sameC/capsule-label/stage4-unit-map/invariance; Theta R2/hc DATA/H1 H4 H5 H6.
- Reuse cells: Cor312ComparisonGapReduction:306 hull theta; IQCarrierConcreteModel:346/:386 hpoint/hweightvol; S3135HeightVolumeReuse/S3135HeightWeightAtPaper shapes; vendor :8056/:9900 reference only.

## P0 batch audit (2026-11-10 05:37, shehdd)

| file | status | decls | checker | src sha256 |
|---|---|---|---|---|
| GenEll00NamingActual.lean | EXIT=0 1610B fresh | 2 | CITABLE | B25E757B034489016CA2130A5BD3997BF4EB7955F4263327F472296935E71098 |
| GenEll01BasicActual.lean | EXIT=0 2086B fresh | 7 | CITABLE | F127339DE0AD68EAC306F66F6F34C082109209786F17B01AA9E2391958445489 |
| GenEll05Theorem21Actual.lean | EXIT=0 3037B fresh | 7 | CITABLE | A35802C9620EBEADD2471412921F550B0E9411A44069243D2C21AC73178DC620 |
| GenEll06Section3StatementsActual.lean | EXIT=1 (fixing) | 5 | - | recursion-depth error at line 40 |
| GenEll07Section4StatementsActual.lean | EXIT=1 (fixing) | 5 | - | recursion-depth error at line 34 |
| GenEll08MainReductionActual.lean | pending | 5 | - | not compiled yet |
| GenEllP0Probe.lean | pending | - | - | not compiled yet |

Audit notes: GenEll00 = naming map (9 rows, rfl length); GenEll01 = paper layer basics
(PaperHeight/PaperLogDiff/PaperLogCond/BDClassOn/CompactlyBoundedSubset + 4 citations);
GenEll05 = Thm 2.1: (i)=>(ii) PROVED trivially (restriction to K), (ii)=>(i) registered as
exact PAPER-INPUT (Theorem21_ii_implies_i_required + Theorem21ReductionInputs):
honest, no fake closure. Fidelity caveat: GenEll01/05 are abstract shape layers
(X : Type; ht/logDiff/logCond functions) - paper-specific number-field/curve data
(Def 1.2/1.5, Example 1.3) not yet instantiated; track in later P0/P1 batches.
Recursion-depth errors in GenEll06/07 likely from rfl/decide on large literal
lists/strings - recommend splitting literal lists into chunks or proving lengths via
decide on small computed lists; flagged to mainline.


## GenEll/AbsTopIII/Mzk1 audit rows (2026-11-10 05:40, shehdd)

| file | status | decls | checker | src sha256 |
|---|---|---|---|---|
| GenEll06Section3StatementsActual.lean | EXIT=0 4481B fresh | 3 | CITABLE | 34921AD1BBD651D04C4FAC60DD14AF45B874784F47F0AF8391EBBD1F08DB2997 |
| GenEll07Section4StatementsActual.lean | EXIT=0 3741B fresh | 3 | CITABLE | 62C02C0B3A9881CC72B221EA956D88EB63B781635B706FE953320F138B891144 |
| GenEll08MainReductionActual.lean | EXIT=0 2423B fresh | 5 | CITABLE | 073E147F5076F36F0541C0C73215B766E360A05F67AE6E1C4D0D4AC34DD0F1FF |
| Mzk1Section2StatementsActual.lean | EXIT=0 3617B fresh | 3 | CITABLE | CCD8FF39B1F7358BCF8493C3022613A13FE72755302D2D3BEC9620B98737BB01 |
| Mzk1ProvabilityClassificationActual.lean | EXIT=0 3102B fresh | 4 | CITABLE | 25D01CC3B01A3A3B61DB70BC41C811F2F61C0B4B151825A090A65CC81631A093 |
| AbsTopIII02LocalVolumesActual.lean | EXIT=0 5205B fresh | 3 | CITABLE | BA87BF7F0A71B0A82F7156570A61ED6D5DC9E4D6FB81ACA3FAC126B5BBE8E181 |
| GenEll05Theorem21Actual.lean | EXIT=1 (extension in progress; old CITABLE 3037B superseded) | 8 | - | - |
| AbsTopIII06WeightedVolumeBridgeActual.lean | pending | 6 | - | - |

AbsTopIII corpus anchors (Lead): Prop 5.7 7915, Prop 5.8 8059, Cor 5.10 8494, Def 3.1(iv) 3424-3520, Def 5.6, section-0 graph 1269. In-repo concrete-part formalization: CardHullReal*/HaarTranslate*/SourceLogShellAbsTopIIIBridge/MonoAnalyticLogShellArchPsiCnsCalibration/SourceThetaLinkGraphAutomorphismReduction; deep anabelian reconstruction = named input (audit against overclaim).
Mzk1 P2: statement/classification ledgers honest (class rows, no fake proofs).
Fidelity watch: GenEll01/05 abstract shape; paper-specific Def 1.2/1.5/Ex 1.3 instantiation pending.

## GenEll P0 final audit + H6/AbsTopIII rows (2026-11-10 05:43, shehdd)

| file | status | decls | checker | src sha256 |
|---|---|---|---|---|
| GenEll05Theorem21Actual.lean (final) | EXIT=0 3759B fresh | 8 | CITABLE probe_ok (GenEllP0Probe) | 65EA8074F66FF7B6E0E5EF2B5C658AFF40F9432215C63B3C7D248AD7A1F1F323 |
| GenEll06Section3StatementsActual.lean | CITABLE | 3 | - | 34921AD1BBD651D04C4FAC60DD14AF45B874784F47F0AF8391EBBD1F08DB2997 |
| GenEll07Section4StatementsActual.lean | CITABLE | 3 | - | 62C02C0B3A9881CC72B221EA956D88EB63B781635B706FE953320F138B891144 |
| GenEll08MainReductionActual.lean | CITABLE | 5 | - | 073E147F5076F36F0541C0C73215B766E360A05F67AE6E1C4D0D4AC34DD0F1FF |
| GenEll10H6ClosureActual.lean | EXIT=0 3263B fresh | 4 | CITABLE | 2DBB8F297D206955B24CF50F81B2E44949816DF8CFF1242DD382003FDBF9DA8F |
| AbsTopIII02LocalVolumesActual.lean | CITABLE | 3 | - | BA87BF7F0A71B0A82F7156570A61ED6D5DC9E4D6FB81ACA3FAC126B5BBE8E181 |
| AbsTopIII06WeightedVolumeBridgeActual.lean | CITABLE | 6 | - | C9073F6A5CA0E43546D6B67BC03166869F429A99E71474559C2A4B89D0001FA5 |
| GenEll02bProofActual.lean | RED EXIT=1 (fix sent) | 5 | - | witness sign: use C not -C (IsBDLe 3-arg orientation f~g with g-f<=C) |
| GenEll04bProp17ChainActual.lean | pending | 4 | - | - |

GenEllP0Probe kernel result: theorem21_i_implies_ii trio; 4 citation/naming rfl lengths NO-AXIOM; ZERO sorryAx.
GenEll10 H6: INTERFACE-LEVEL closure only (uses shadow record genEll_transfer field); file honest that GenEll statement + deep inputs remain named paper-inputs — audit PASS as interface closure, NOT paper-level.
AbsTopIII batch probe pending.
Registry frozen 14041 / gate 23066 / record 18800; no reopen.


## P0 complete + AbsTopIII probe rows (2026-11-10 05:46, shehdd)

| item | status | checker | notes |
|---|---|---|---|
| GenEll04bProp17ChainActual.lean | EXIT=0 2323B fresh | CITABLE 4 decls sha 2F20D88785FFE85B6AFCDA2A032369216C66DD0D4A30F2248F1E1DA54F473F0B | Prop 1.7 chain |
| GenEll02bProofActual.lean | fix applied (mainline): witness C not -C + qualified 3-arg S3136BDClassChainToolActual.IsBDLe; fresh compile requeued | pending recheck | was RED linarith |
| GenEllP0Probe.lean | EXIT=0 652B fresh | kernel 1 trio + 4 no-axiom, zero sorryAx | P0 probe |
| _AbsTopIIIBatchProbe.lean | EXIT=0 946B fresh | all 5 footprints NO-AXIOM, zero sorryAx | AbsTopIII/Mzk1/GenEll06/07 rows |

P0 set status: 00/01/04b/05/06/07/08 CITABLE; 02b fix pending fresh compile; 02-based propagations tracked.
Registry frozen 14041 / gate 23066 / record 18800; no reopen.


## P0 final + AbsTopIII completion audit (2026-11-10 05:54, shehdd)

GENELL P0 FINAL COMPLETE: GenEll02bProofActual GREEN CITABLE 2308B 5 decls sha 1A47622C0088BF2FC3B60A6B591BBE9EF7BC8570DCB5B83FF7CE3630173FF860 (two fixes: fully qualified 3-arg S3136 IsBDLe in both theorems; witness -C via Classical.choose to avoid propRecLargeElim). Also CITABLE: GenEll00/01/01b/04b/04c/05/06/07/08/09/11. Probes: GenEllP0Probe 1 trio + 4 no-ax; GenEllP0AbcProbe3 2 trio (s3135_hBox_nonneg, prop17_of_differentTheoryInput); zero sorryAx.
ABSTOPIII COMPLETE: AbsTopIII01LogShellActual GREEN CITABLE 3856B 7 decls sha 5692B882E2A4FA60113D698612CAAC18D663426B52E6B586E6314E7B8AB0884A (capitalization fix AbsTopIIILogShellAnchors); 02/03/04/05/06/10/11 CITABLE; _AbsTopIIIBatchProbe EXIT=0, ledger/index + absTopIIILocalVolume/le_theta footprints NO-AXIOM, zero sorryAx.
P3 watch: GenEll09 consumer + GenEll11 route interface CITABLE (interface level); GenEll10 H6 interface-level only; no fake unconditional closure.
Registry frozen 14041 / gate 23066 / record 18800; no reopen.


## Mzk1 proof batch + AG/Indet stream audit (2026-11-10 05:57, shehdd)

| item | status | checker | notes |
|---|---|---|---|
| Mzk1Cor31Cor32Actual.lean | EXIT=0 3694B fresh | CITABLE 5 decls sha C71920D92A396B7ED2A3D245A025CE6B... | Cor 3.1/3.2 rows + reduction plan |
| Mzk1Lemma23Actual.lean | EXIT=1 (stage4 fixing) | - | non-existent Complex.dist etc.; fix guidance sent (generic dist/dist_comm/dist_triangle; dist_eq_norm; stray lambda token) |
| _Mzk1ProofBatch2Probe.lean | pending | - | depends on Lemma23 |
| AG_FLT_Def_..._Repartitions.lean | EXIT=0 5827B fresh | CITABLE 19 decls | AG/Indet parallel stream |
| AG_FLT_Def_..._DivisorClassGroup.lean | EXIT=0 17864B fresh | CITABLE 72 decls | def-heavy |
| AG02FunctionFieldActual.lean | EXIT=0 3077B fresh | CITABLE 7 decls | function field |
| Indet02BPSMultiradialUpToActual.lean | EXIT=0 5994B fresh | CITABLE 12 decls | BPS multiradial |

Audit note: AG/Indet streams are separate definition workstreams (not counted as paper-level theorem evidence); Mzk1 finite case = class-A fragment with paper deep input still named.
Registry frozen 14041 / gate 23066 / record 18800.


## Batch AD audit (2026-11-10 06:02, shehdd)

| file | status | decls | checker | sha256 |
|---|---|---|---|---|
| Mzk1Lemma23Actual.lean | EXIT=0 3424B fresh | 3 | CITABLE | 2E6CC5BFCF258B12882C9B09F4746C0C... (probe: 2 no-ax + trio, zero sorry) |
| GenEll05bChainWiringActual.lean | EXIT=0 3096B fresh | 2 | CITABLE | EE6FD8D40B8BDC4C94A637C0F3F80783... |
| AbsTopIII07VolumeLogShellBridgeActual.lean | EXIT=0 3383B fresh | 3 | CITABLE | 2B7C481A8955EA790553C74C433C12AB... |
| S3132ThetaSideEndgameRowsActual.lean | EXIT=0 2881B fresh | 5 | CITABLE | D4FF3278FBEDE22295F4E2B9172C5C00... |
| AbsTopIII08PvAdicScalingActual.lean | EXIT=1 (stage4 fixing) | 3 | - | invalid instance binder :43/:54; unknown absTopIII_* :61-63 |
| AbsTopIII09ThetaHullScalingActual.lean | EXIT=1 (stage4 fixing) | 2 | - | Function expected :53 |
| _AbsTopIIIHullBatch2ProbeActual.lean | pending | - | - | hull batch probe |

Theta endgame watch: rows track R2 exactly (R1 free) + hc DATA + H1/H4/H5/H6; honesty audit maintained.
Registry frozen 14041 / gate 23066 / record 18800.


## AbsTopIII batch-2 complete + S3171 probe audit (2026-11-10 06:10, shehdd)

| item | status | checker/probe | sha256 |
|---|---|---|---|
| AbsTopIII07VolumeLogShellBridgeActual.lean | EXIT=0 3383B fresh | CITABLE 3 decls | 2B7C481A8955EA790553C74C433C12AB... |
| AbsTopIII08PvAdicScalingActual.lean | EXIT=0 3727B fresh | CITABLE 3 decls | CD77090C3711935DCCFFFE644B08B308... |
| AbsTopIII09ThetaHullScalingActual.lean | EXIT=0 3365B fresh | CITABLE 2 decls | B7F14E1DF0EB5DED9455ABB002F1FB10... |
| _AbsTopIIIHullBatch2ProbeActual.lean | EXIT=0 720B fresh | 4 footprints ALL TRIO, zero sorry | - |
| S3171IUTIVSection1StatementActual.lean | EXIT=0 4742B fresh | CITABLE 6 decls | 404BBF4164E0DF56457702BF4B0B3953... |
| S3171IUTIVSection1Probe.lean | EXIT=0 370B fresh | all 3 footprints NO-AXIOM | - |

AbsTopIII statement/reduction layer: 01-11 batches all audited CITABLE (01-06/10/11 + 07/08/09; 02/06 green earlier). S3171 statement layer for (b) family audited (statement-layer only; no paper-level claim). Registry frozen 14041 / gate 23066 / record 18800.


## GenEll Thm 3.8 + EtTh batch audit (2026-11-10 06:19, shehdd)

| file | status | checker | sha256 |
|---|---|---|---|
| GenEllThm38HeightBoundsActual.lean | EXIT=0 4501B fresh | CITABLE 4 decls | CD0D99CF44F239C5942A79B94CB87351... (8-row height-asset ledger + 23040 identity) |
| EtTh00Stage0LedgerActual.lean | EXIT=0 3163B fresh | CITABLE 5 decls | A2D98DC9C11EB7C4BA4E5A7001C5C01D... |
| EtTh01StatementActual.lean | EXIT=0 5012B fresh | CITABLE 4 decls | 8F8D111D4DED93438B416887DDB125D0... (probe 4 NO-AX) |
| EtTh02DeepInputsActual.lean | EXIT=0 2742B fresh | CITABLE 4 decls | EF8C821C824D1340A797288D2E498AEC... (deep inputs honest; all_unproved flag) |
| EtTh05PaperInputsActual.lean | EXIT=0 2467B fresh | CITABLE 4 decls | CAEEB501CDA6A81D50C1E45DEC2F4497... |
| EtTh03EtaleThetaGroupActual.lean | EXIT=0 2484B fresh | CITABLE 4 decls | E550E892D3C1CC9E82541DB48B844728... (fixed) |
| EtTh04QPilotDataActual.lean | RED (linarith/type mismatch; guidance sent) | - | - |
| _EtThProbeActual.lean | pending | - | - |

Honesty audit: EtTh02 etThDeepInputs_all_unproved flag documents that deep inputs remain unproved/named — no fake closure. Thm 3.8 asset ledger is input-layer only.
Registry frozen 14041 / gate 23066 / record 18800.


## ExpEst + AG batch audit (2026-11-10 06:20, shehdd)

| file | status | checker | sha256 |
|---|---|---|---|
| ExpEst02ElementaryEstimatesActual.lean | EXIT=0 3310B fresh | CITABLE 7 decls | 3BB8360624EC86CC4275712DF14849F2... (PNT/prime-reciprocal/Chebyshev-theta as named paper-inputs + ClassA 8/ClassB 3 indexes) |
| AG91AgIndexIdsActual.lean | EXIT=0 7392B fresh | CITABLE 3 decls | BBA7BE687DA1DA8329D41B5B2A5BF251... |
| AG92AgDependencyGraphActual.lean | RED (defeq/type mismatch; guidance sent) | - | - |
| AG90MathlibAuditActual.lean | editing (stale) | - | - |

Honesty: ExpEst paper-inputs (PNT/Chebyshev) NOT proved; class indexes data-only.
Registry frozen 14041 / gate 23066 / record 18800.

## Frd01 + AbsTopIII10 re-audit (2026-11-10 06:24, shehdd)

| file | status | checker | sha256 |
|---|---|---|---|
| Frd01StatementActual.lean | EXIT=0 5139B fresh | CITABLE 5 decls | 8D328F35470FBAAF8AC981C1C4E8E5EE... (DivisorialMonoidData/ModelFrobenioidData/FrobeniusActionData/FrobenioidObjectLayer/FrdPaperComponents; universe fix landed) |
| AbsTopIII10StatementLedgerActual.lean | EXIT=0 7467B fresh | CITABLE 3 decls | 0287B1B6988B53F06EB66DEDE61B9D17... (19-row statement ledger) |

Remaining reds in flux: EtTh04, AG92, Mzk1Lemma21Real, AbsTopIII13, S3132ThetaSideBundleWithData, AG90 (stale); owners notified.
Registry frozen 14041 / gate 23066 / record 18800.
