# CANONICAL GATE DRAFT V3 — CORRECTED SCOPE (NON-CANONICAL)

**Status:** DRAFT V3 (non-canonical; gate table itself remains FROZEN — this file is NOT the canonical gate table). Author: 拉蒂/lattice.
**Basis:** draft V2 + mainline review C1-C12 (coord/CANONICAL-GATE-DRAFT-V2-REVIEW-mainline.md) + shehdd S3260 audit + mainline A321 feed (coord/IUT-PREREQUISITES-REMAINING.md) + xref (coord/CORRECTED-TARGET-XREF.md).
**Pins:** registry 14041 / gate in flux / record 18800; L8 frozen; no registry edits; no Lean edits; no gate-table writes.

**GATE NOT PASSED; binding HOLD; FINAL ROWS suspended; no closure claims.**

## 0. C1-C12 APPLICATION MAP

| correction | applied in V3 |
|---|---|
| C1 BelyiCvBridge green (4563B/CITABLE 5; cast formula NAMED TODO) | S3.4 rewritten |
| C2 add RestatedLemma22InterfaceActual (6012->8624B/CITABLE 13 after update; src FDA5B47D; probe 200004) | S3.1+3.2 |
| C3 add RestatedLemma24InductionActual (8184->9555B/CITABLE 14; named inputs) | S3.1; S4 |
| C4 add CritValue staging (3417B/CITABLE 4) + S3257 audit row | S3.5 |
| C5 consumer design latest pin 9329B/18E57C92 (not 8715) | S3.6 |
| C6 L4 overclaim fixed: F=Q CONDITIONAL wiring + named base input; coverage wording RESOLVED by Lead A323/A324 | S1, S2 |
| C7 remove legacy Mzk1Lemma22BaseProviderStatement; exact named list (7 items, proved:=false) | S4 |
| C8 remaining gate items expanded (corrected 2.2/2.4 rows; full gate not started; consumer; H6 assigned; upstream search; HOLD list) | S5 |
| C9 republish template: paper lines + audit IDs + Lead wording + fresh hash re-verification | S6 |
| C10 S3236/S3232/S3223 marked OLD TARGET / HISTORICAL | S3.7 |
| C11 decision rows A313/A314/A318/A319/A320/A321/A322 | S7 |
| C12 CVLawProof duplicate counted once | S3.4+note |

## 1. COVERAGE LINE

**CANONICAL COVERAGE LINE (Lead A323/A324; verbatim; use everywhere):** 'F=Q conditional wiring delivered (named beta-avoiding Belyi base input) + full-Qbar reduction named (not complete)'.
**C6 wording RESOLVED by Lead A323/A324:** because the corrected base provider (F=Q base case) is class-B named, the line was amended; adopted canonical line:
> 'F=Q conditional wiring delivered (named beta-avoiding Belyi base input) + full-Qbar reduction named (not complete)'.
Footnote for coverage notes: the F=Q base input is named class-B BetaAvoidingBelyiBaseInput; the F=Q base case is NOT proved; see S4.

## 2. GATE ROWS L0-L8 (authoritative current; mainline A321 feed, C6-corrected)

| Layer | Status | Evidence | Remaining for PASS |
|---|---|---|---|
| L0 curves/function fields | CLOSED/PASS | E1 defs CITABLE; AG01/02 | none |
| L1 divisors/height-weight | CLOSED/PASS | tree asset + AG03 | none |
| L2 cohomology | CLOSED/PASS | AG05 Cech CITABLE; AG_FLT_CechPromotion | none |
| L3 RR/Serde | CLOSED/PASS (ported) | promotions CITABLE; ported assets non-gate | none |
| L4 Belyi/finite maps | PARTIAL | **F=Q conditional wiring delivered (named base input BetaAvoidingBelyiBaseInput)** - restated interfaces + CV law + L2.3/HPRES numeric evidence + conditional assembly skeleton; Mzk1 2.1 ALL PROVED; FiniteMapData resolved. NOTE: F=Q base case NOT proved (old S3236 provider targeted old degenerate goal; see S3.7) | **first F=Q component NOT complete** (named base input class-B blocked); FULL Qbar layer named: (D) finite-Galois PROVED + infinite fixed field class-B + 2.3 Moebius over Qbar/C + AlgebraicNestedInductionInput class-B |
| L5 GenEll | PARTIAL (statement layer citable) | GenEll05 (i)=>(ii) PROVED; GenEll10b H6 wiring; GenEll15/16/17 citable | (ii)=>(i) consumer needs noncritical Belyi existence + H6 precise GeometricCore; corrected-2.4 consumer not wired |
| L6 AbsTopIII | PARTIAL | 01/03/07/08/09 complete citable; H1-H5/H7 closed w/ class-B leftovers; H6 PARTIAL | H6 precise-ification assigned 胡尔 Mzk1GeometricCorePreciseActual; AbsTopIII05 deep named |
| L7 EtTh/Theta | PARTIAL | EtTh07-13 citable; theta power-kernel anti-monotonicity PROVED | realization deeper rows class-B named |
| L8 IUT IV section1 | FROZEN/NOT PASSED | S3171 IUTIVSection1 green; thm110 display conditional | needs L0-L7 gaps close + inputs (b) uniform height-vs-volume; remains FROZEN |

## 3. DELIVERED GREEN COMPONENTS (rational/C-point layer; green != closure)

### 3.1 Restated interfaces / target / CV law

| component | evidence | status |
|---|---|---|
| RestatedLemma22InterfaceActual | A332 mainline-verified NEW pin: EXIT0 SIZE 8698B, CITABLE 13 decls, src E0B711D4 / olean 131456 52331642, probe 1063 (coverage row amended); supersedes 8624/13; decls Mzk1Lemma22Target (C-point)/Good/Mzk1Lemma22Target_iff_exists_Good (PROVED)/Mzk1Lemma22InductionStatement (NOT proved)/target_of_induction (PROVED)/Mzk1Lemma22CVCompat (CVCompositionLawStatement AND SpecialSetPreservationStatement); F=Q scope + AlgebraicNestedInductionInput + polyEvalP1AC | GREEN interface; InductionStatement named (conditional file pending stage4) |
| RestatedLemma24InterfaceActual | CURRENT verified (A328 lattice re-check): EXIT0 **6611B, CITABLE 10 decls probe_ok TRUE** (CV def refined + scope note; abc owner); **src sha 0526AD1D55D66DA1949D4BF6F401224809AB6B348F303AF03E58105861960468; olean 80344B sha 82F2093D8EBF682897C533764BDC022A2A8B47E376AA84B698054EF956CDF7C8**; earlier pin 5255B/9 STALE. Mzk1Lemma24Target (C-point/specialSet/unramified), CVInvariant, CVCompositionLawStatement, SpecialSetPreservationStatement; audit S3248: C-points PASS, no targetSet/unramifiedAt loophole PASS, degenerate-witness check PASS. Re-verify at republish; abc owner confirmation pending | FRESH GREEN (audit interface-only; pin refreshed) |
| RestatedLemma24InductionActual | S3260/A322: EXIT0 SIZE 9555B, CITABLE 14 decls; proves s3135_polyEvalP1_comp, s3135_CVInvariant_comp, s3135_RestatedStep_cvInvariant; statement layer RestatedState/RestatedMeasureLE/RestatedBaseStatement/RestatedStep/RestatedInductionConclusion/RestatedInductionAssemblyStatement; adds named inputs BetaAvoidingBelyiBaseInput, CorrectedStepProviderPaperInput, CorrectedAssemblyPaperInput | GREEN conditional statement layer; NOT closure |
| LayerAAlgebraicInductionActual (abc; NEW GREEN A332) | CITABLE 4 decls 3485B: paperMeasure Qbar; AlgebraicNestedInductionStatement := PaperScopeLemma24Statement; s3135_AlgebraicNestedInduction_iff; LayerAStatus | **Layer A statement ROW (statement/named only, NOT closure)**; S3263 audit file (2988) pending shehdd confirmation |
| RestatedLemma24CVLawActual | S3255: CITABLE 5 decls 3918B sha 9EE41ECD (probe_ok, zero sorry): criticalValuesOverC_eq, CVCompositionLaw PROVED, SpecialSetPreservation PROVED, CVCompat PROVED | GREEN (single canonical count; see C12) |

### 3.2 Induction/2.2 interface + helpers

| component | evidence | status |
|---|---|---|
| Mzk1Lemma22StepInterfaceQActual | S3249: CITABLE 4 decls 2698B C74EE6FF probe_ok; explicit Q-membership step interface; named TODO supported by next item | GREEN interface |
| Mzk1Lemma22StepInterfaceQProofActual | S3252: CITABLE 1 decl 3831B B480D0F5 probe_ok zero sorry; step_interface_of_hypotheses_proof PROVED (phi=gPoly D; targetS=S.image polyMapPoints; H-on-image via S3238; card decrease card_image_gPoly_lt; unramified gChoice_unramified) | GREEN; bugfix #2 proof landed |
| Mzk1Lemma22FullShapeHelpersActual | S3249: CITABLE 9 decls 3403B DD987A8A probe_ok; critValues_comp_subset + union PROVED; BaseGoodData/baseGoodPoly/degree/derivative PROVED; CritIn01 over C; no True/toy | GREEN helpers |

### 3.3 L2.3 normalization + HPRES / conditioned gate

| component | evidence | status |
|---|---|---|
| Mzk1Lemma23NormalizationActual | S3229: CITABLE 6 decls 6520B B21C1493; s3135_normalization_exists PROVED | GREEN |
| Mzk1Lemma24NormalizationTransferActual | S3230: CITABLE 21 decls 12033B 2E673AC3 probe_ok zero sorry; transfer_statementShape/P1Affine inverse laws | GREEN (L2.3 evidence) |
| Mzk1Lemma22HypPreservationActual | S3233: CITABLE 14 decls 6825B CB0F53B6; components 1-4 PROVED | GREEN |
| Mzk1Lemma22HypPreservationSeparationActual | S3237: CITABLE 4 decls 9136B C86E19B8; separation (5) PROVED => HPRES 1-5 COMPLETE | GREEN |
| Mzk1Lemma22HypPreservationCanonicalActual | S3242: CITABLE 4 decls 4111B 7E575EA9 | GREEN |
| Mzk1Lemma22ConditionedActual | S3238: CITABLE 2 decls 2054B 60FA5B9B; hyp_preservation_full + of_hypotheses PROVED | GREEN |

### 3.4 Mobius Q/C + CV bridge (C1) + duplicate note (C12)

| component | evidence | status |
|---|---|---|
| Mzk1MoebiusP1Actual (Q-typed source) | S3253: CITABLE 12 decls 7832B 4D63BB55 probe_ok zero sorry; composition det mult; mapPoints_nonconstant case split; derivativeNumerator != 0 => CV empty; specialSetQ mapsTo; inversion permutes specialSet | GREEN Q-typed source |
| Mzk1MoebiusP1C (C-typed variant) | S3256: CITABLE 14 decls 6995B probe_ok; A305 layering: design 9329B 18E57C92 unique Q-typed source; qpilot extension separate; C-file distinct | GREEN; no dup/cycle |
| Mzk1BelyiCvBridgeActual | **C1/A319/S3260: EXIT0 SIZE 4563B, CITABLE 5 decls, probe_ok TRUE**; belyiPolynomial_critIn01 (C-point critical values subset {0,1}, REAL PROOF), gPoly_eq_belyi21_comp, belyi21_derivative_root_reexport; derivative-aeval CAST FORMULA remains NAMED TODO (stage4 signature) | GREEN; cast formula named |
| hull CVLawProof 3217B | redundant duplicate of S3255 CV law | counted ONCE (S3255); not a second credit |

### 3.5 CritValue staging (C4)

| component | evidence | status |
|---|---|---|
| Mzk1Lemma22CritValueActual | A310/C4: EXIT0 SIZE 3417B, CITABLE 4 decls; aeval_cast_eval PROVED; CritValueInImageStatement NAMED item (i) with 5-row TODO ledger; no fake theorem | PARTIAL staging |
| S3257CritValueBaseProviderAuditActual | A310/C4: 2602B audit record citable | audit row |

### 3.6 Consumer design (C5)

| component | evidence | status |
|---|---|---|
| Mzk1Thm25P1CompositeConsumerDesignActual | A325/A326 latest pin: CITABLE 12 decls, 10500B, src C82269A6, probe 201950; 9 rows; availableMoebiusAssets 12; named inputs h22 + h24Base + algebraicNestedInduction + mobius + cvCompositionLaw + cPointCriticalValueLift. Earlier pins 9329B/18E57C92 (S3258), 8715B/90123C46/AC95FFC6 (A305), 8098B/90638394 (A301) are STALE; re-verify at republish | STATEMENT/DESIGN ONLY - NOT closure; consumer LAST |

### 3.7 HISTORICAL / OLD TARGET rows (C10) - NOT gate evidence

| item | evidence | marking |
|---|---|---|
| Mzk1Lemma24BaseProviderActual S3236 (CITABLE 3 decls 6893B 67175237) | rational base provider for OLD degenerate goal | OLD TARGET / HISTORICAL - NOT valid for restated base; replaced by class-B BetaAvoidingBelyiBaseInput |
| Mzk1Lemma24AssemblyActual S3232 (CITABLE 7 decls 5215B 2944F69C) | old Mzk1Lemma24Goal skeleton | OLD TARGET / HISTORICAL - retarget pending (CorrectedAssemblyPaperInput) |
| S3223 2.4 (G)(F)(D)(M) interface evidence | 17 files CITABLE per owner audit; old-target named residuals M1a/M1b/M2 | OLD TARGET / HISTORICAL - progress evidence only |
| S3244 integrity correction; S3246 assignments; S3258 scope decision (historical); S3259/S3260/S3261 CITABLE 3 each; S3264/S3265 audits citable (GDerivAeval/InductionProof/TargetImpliesFullShape/BaseProviderRestated/R22+LayerA); S3178 34248B; S3260 audits; S3178 32082B; AG08 8743 src B324A717; S3180Mzk1Ids 9318 src 17347AE6 | records | citable records, not gate evidence |

## 4. NAMED INPUTS (Lead A324 exact list, 7 rows; all proved := false; may NOT be consumed as proved)

| # | named input | paper source | status/obstruction |
|---|---|---|---|
| 1 | BetaAvoidingBelyiBaseInput | Lemma 2.4 rational base (paper 144-160) | class-B CONFIRMED. qpilot A326 upstream evidence: ABSENT - TauCeti Belyi.lean only q(S)/CV control, no q(beta) avoidance; Mathlib grep 0; FLT/port none; port trial tauceti_belyi_ff in progress. Obstruction verbatim (S3260): (i) TauCeti Belyification gives q(S) subset {0,1}, CV(q) subset {0,1} but NO q(beta) control (may be 0/1); (ii) composing with rational affine A breaks CV subset {0,1} unless A=id (CV(BoA)=A^{-1}(CV B) subset A^{-1}{0,1}); (iii) |S|<=3 parameterized B_{m,n} only when S subset {0,1,m/(m+n)} and need exclude finitely many beta (B^{-1}(1)); no general rational beta-avoiding Belyi in current assets. qpilot search DONE = ABSENT (A326); port trial tauceti_belyi_ff in progress. proved:=false |
| 2 | Mzk1Lemma22RestatedBaseProviderStatement (hbase) | conditional 2.2 induction hbase (restated 2.2 base-provider named statement) | **RESTATED 2.2 base-provider named statement (hbase)** - NEW symbol, stage4 writing, linked to conditional hbase of Mzk1Lemma22InductionProofActual; NOT the old degenerate StepProvider/BaseProviderStatement and NOT old-target evidence. (A327 label clarification; old name 'Mzk1Lemma22BaseProviderStatement' retired in V3 to avoid ambiguity.) proved:=false |
| 3 | CPointCVInImageStatement | item (i) C-strengthened Lemma 2.1(b) | NAMED item (i) (Mzk1Lemma22CritValue staging; 5-row TODO); derivative-aeval cast formula pending stage4 signature (bridge file now green for critIn01, cast only); proved:=false |
| 4 | CorrectedStepProviderPaperInput | paper 195-203 f0-measure-decrease + transport composition | named; S1a/S1b/S2/S3/S2-i proved pieces available; proved:=false |
| 5 | CorrectedAssemblyPaperInput | paper 179-206 assembly over restated target/CVInvariant | named; old assembly skeleton historical; proved:=false |
| 6 | AlgebraicNestedInductionInput | paper 179-206 algebraic m/d descent step (class-B) | named (A313); proved:=false |
| 7 | AlgebraicClosureFixedFieldPaperInput | infinite Galois fixed field over Qbar (class-B) | named; proved:=false |

**Removed:** legacy Mzk1Lemma22BaseProviderStatement-as-old-symbol and old-target Mzk1Lemma22BaseProvider statement usages are NOT cited (A324: use hbase link above; never cite old-target symbols). Conditional file-level items pending: Mzk1Lemma22InductionProofActual (stage4), Mzk1Lemma24BaseProviderRestatedActual (abc); not counted as inputs proved.
**Paper-level deep inputs also named (see S5):** [Mzk1] GeometricCore (free Prop fields defect; H6 precise-ification assigned 胡尔 Mzk1GeometricCorePreciseActual); AbsTopIII05 deep; infinite-Galois fixed field; Qbar-level 2.3 Mobius application; class-B algebraic nested induction.
### 4a. PENDING / UNVERIFIED rows (Lead one-off subagents; A327)

These rows are placeholders ONLY: add values/status only AFTER mainline verification (fresh EXIT0/checker/probe).
No claim may cite them as evidence before verification.

| item | subagent assignment | status |
|---|---|---|
| CritValueInImage proof (item (i)) | one-off subagent; unique new file | PENDING/UNVERIFIED |
| gPoly derivative-aeval cast formula | one-off subagent; **Mzk1GDerivAevalActual CITABLE 11 decls 9077B sha 480A7445 probe_ok TRUE (shehdd S3264)**: derivative_gPoly_eq(+of_even), gPoly_deriv_aeval(Even n)+of_any_n+cast, lam_cast_ne_zero, gPoly_deriv_aeval_eq_zero_iff, gPoly_deriv_aeval_zero_cases; 7-row ledger; probe trio only | GREEN CANDIDATE (PENDING mainline verification) |
| Moebius over Qbar (application wiring) | one-off subagent; unique new file | PENDING/UNVERIFIED |
| polyEvalP1-aeval-specialSet bridge | one-off subagent; unique new file | PENDING/UNVERIFIED |
| Target -> FullShape adapter | one-off subagent; **Mzk1TargetImpliesFullShapeActual CITABLE 10 decls 11657B 16F51D7C probe_ok TRUE (shehdd S3264)**: Mzk1Lemma22Target_to_fullShape, mzk1Lemma22TargetImpliesFullShape (真证明), fullShape_of_good, fullShape_of_induction; 9-row ledger | GREEN CANDIDATE (PENDING mainline verification) |
| Beta-avoiding Belyi CONSTRUCTION ATTEMPT IN PROGRESS (Lead A329/user directive) | S6 Mzk1BetaAvoidingBelyiSmallActual (|S|<=3 explicit); S7 Mzk1BetaAvoidingBelyiRationalActual (general rational inductive); hull parametric core Mzk1BetaAvoidingReductionActual (beta-tracking exists_card_image_lt: f(beta) notin {0,1}, f(beta) notin f(S); bad parameters finite) | PENDING/UNVERIFIED - class-B BetaAvoidingBelyiBaseInput REMAINS until verified; success would upgrade Layer R base named -> PROVED (hypothetical, not claimed) |
| Mzk1GeometricCorePreciseActual (H6 precise) | hull; assigned 胡尔 | PENDING/UNVERIFIED - RED (hull) |
| Mzk1Lemma22InductionProofActual (conditional 2.2) | stage4; assigned 司徒 | **CONDITIONAL GREEN CANDIDATE (shehdd S3264/S3265): CITABLE 8 decls 7922B 5490AE9C probe_ok TRUE; mzk1Lemma22_induction_conditional (hbase : BaseProviderStatement) (hstep : StepProviderStatement) : Mzk1Lemma22InductionStatement PROVED; mzk1Lemma22_target_conditional PROVED; named inputs listed (BaseProviderStatement card<=3; StepProviderStatement 3<card explicit gPoly + C-point CV-in-image); 6-row ledger; F=Q scope NOT closure**; PENDING mainline verification (trigger (b)) |
| Mzk1Lemma24BaseProviderRestatedActual (conditional 2.4 base) | abc; assigned 艾比 | **CONDITIONAL GREEN CANDIDATE (shehdd S3265): CITABLE 5 decls 4732B 5486CCEA probe_ok TRUE; s3135_target_of_betaAvoidingBelyiBase + s3135_restatedConclusion_of_providers (hbase+mu+well-founded lex+CorrectedStepProviderPaperInput => RestatedInductionConclusion; hwf.fix + next_beta_avoid invariant); named class-B inputs; F=Q tag; no closure**; PENDING mainline verification (trigger (b)) |
| LayerAAlgebraicInductionActual | abc; assigned 艾比 | **RESOLVED GREEN (A332): moved to delivered Layer A statement row (S3.1); statement/named only, not closure; S3263 audit pending shehdd** |
## 5. REMAINING IUT GATE ITEMS (C8 expanded)

1. **H6 PARTIAL** - GenEll transfer wired only via explicit GeometricCore hypothesis (GenEll10bH6Mzk1Wiring, Hull07H6Interface conditional, Hull11H6Mzk1Upgrade named reduction hypotheses). Precise-ification assigned 胡尔: Mzk1GeometricCorePreciseActual.
2. **Corrected 2.2:** Mzk1Lemma22InductionStatement NOT proved; Mzk1Lemma22InductionProofActual conditional file pending stage4 (hbase/hstep/CPointCVInImageStatement -> InductionStatement -> target_of_induction).
3. **Corrected 2.4:** base provider (Mzk1Lemma24BaseProviderRestatedActual), step provider, assembly conditional files pending abc; Layer A statement files pending.
4. **Full gate not started** (no file); real consumer (2.4 o 2.3 o 2.2) NOT wired (design only).
5. **Upstream search:** beta-avoiding Belyi existence assigned qpilot (unlock BetaAvoidingBelyiBaseInput).
6. **Thm25 binding HOLD / Thm2.5 unconditional NOT claimed** - A277 defect 4 (conclusion uses hcore only; GeometricCoreWitness free Prop fields). HOLD file list (tmp/xif_hold_files.txt): Mzk1Thm25Unconditional (+probe), Mzk1Lemma22FullGateActual (old invalid path), Mzk1Lemma24BaseCaseComplex (deprecated); un-HOLD only by explicit Lead decision after real consumer + restated full gate.
7. **Deep inputs / class-B named:** AbsTopIII05 deep construction; H6 GeometricCore precise-ification (free Prop fields); H5 q-side O^x stabilization; H7/Ob9 arbitrary-iterate bound (deep class-B; Hull12 one-sided only); EtTh/theta realization deeper rows; IUT IV section1 inputs (b) uniform height-vs-volume (L8 frozen until L0-L7 close).
8. **L8 FROZEN** - IUT IV section1 display/Cor 3.12/GeometricCore assembly not to proceed until full self-write conditions + real consumer.
9. **Ported/non-gate** - ported assets and paper red-tracked items are NOT gate rows (asset record only); no gate count change.

## 6. ONE-TIME REPUBLISH TEMPLATE (C9 expanded; only after conditional wiring green + Lead FINAL ROWS)

1. Create NEW clean gate-table Lean file (new path; rows compact <1800 chars; do NOT edit frozen historical gate files).
2. Insert S1 coverage line verbatim + Lead-confirmed wording (C6); include footnote if line unchanged.
3. Insert delivered rational/C-point rows (S3) with fresh EXIT0 SIZE / checker CITABLE / probe_ok / src sha / olean sha; re-verify ALL cited hashes at final pins (stale owner-reported pins superseded ONLY by fresh checker runs).
4. Insert named-input rows (S4) each with paper source lines + owner audit ID + proved:=false; never as proved.
5. Insert remaining gate items (S5: H6 PARTIAL, corrected 2.2/2.4 pending, full gate not started, deep inputs, L8 frozen) and verdict: GATE NOT PASSED unless Lead explicitly upgrades; no Thm2.5 unconditional claim while HOLD.
6. History rows: old gate paths corrupt/frozen; duplicate backups non-canonical; old-target files DEPRECATED-UNDER-CORRECTED-TARGET (xref).
6b. Every named input row lists paper source lines + owner audit ID + proved:=false (C9).
7. Run checker + probe; report fresh pin values to shehdd for ONE audit.
7b. Coverage wording confirmed by Lead (C6) before queueing republish (C9).
8. Only after shehdd audit + Lead approval may the canonical label move; update ledger/STATE with pins (registry 14041 / gate = new pin / record 18800; L8 frozen; no registry edits).
8b. Fresh re-verification of ALL cited hashes at final pins before republish; no stale hashes (C9).
9. While HOLD persists: do NOT queue/un-HOLD binding files; un-HOLD only by explicit Lead decision after real consumer + restated full gate.

Preconditions: conditional wiring green (CV law + C-point CV-in-image cast formula + corrected providers + assembly + real consumer) AND Lead-approved FINAL ROWS AND shehdd audit slot; else keep this draft non-canonical and gate frozen.

**Lead A331: draft V3 approved FINAL (keep as-is; basis for FINAL ROWS). TRIGGER TYPES (four): (a) 5 one-off subagent files verified by mainline; (b) 司徒 conditional induction / 艾比 conditional base green; (c) 胡尔 H6 precise delivered; (d) beta-avoiding construction success (would upgrade Layer R base named -> PROVED). All PENDING/UNVERIFIED until fresh green + mainline verification; no counting before that.**

## 7. DECISION RECORDS (C11)

| decision | content |
|---|---|
| A313 scope split | CANONICAL COVERAGE LINE (amended by Lead A323/A324): 'F=Q conditional wiring delivered (named beta-avoiding Belyi base input) + full-Qbar reduction named (not complete)'; option (i) scope |
| A314 | scope decision continuation/recording (per A313/A321) |
| A318 | conditional versions allowed/required (named hypotheses; non-closure) |
| A319 | BelyiCvBridge green + base provider class-B blocked |
| A320 | assignments issued (胡尔/齐波/拉蒂/司徒/艾比/史蒂/谢德) |
| A321 | mainline deliverable coord/IUT-PREREQUISITES-REMAINING.md (L0-L8 rows) |
| A322 | mainline review of draft V2 (C1-C12; this V3) |
| A323 | Lead decision: coverage line amended; BelyiCvBridge GREEN; restated rows + pins; L4 wording; named-input 7 rows (use latest verified pins) |
| A324 | Lead decision recorded: canonical coverage line verbatim; C1-C12 adopted; named inputs exactly 7 proved:=false; label Mzk1Lemma22BaseProviderStatement as restated 2.2 base-provider named statement (hbase link); no old-target symbols |
| S3258 scope decision (historical wording, retained); S3261CoverageAmendmentActual citable (amended canonical coverage line replaces S3258/A313 wording; S3258 kept as history); S3260 audits; S3178 32082B | records |

## 8. OPEN ITEMS FOR LEAD

1. C6 wording: CLOSED - Lead A323/A324 canonical line adopted verbatim; no further action (A328 F4 closeable).
2. Approve V3 structure before FINAL ROWS; then shehdd one audit.
3. Confirm HOLD list and un-HOLD conditions.

---
*Draft V3 - non-canonical; prepared by 拉蒂/lattice under gate freeze. No gate-table writes, no Lean edits, no closure claims. Hashes as owner-reported (S3223-S3260, A277-A322) and subject to fresh re-verification at republish.*
