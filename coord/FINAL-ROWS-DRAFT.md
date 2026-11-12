# FINAL ROWS DRAFT — CORRECTED SCOPE (NON-CANONICAL)

**Status:** DRAFT (Lead A340; NON-CANONICAL; gate table NOT written). Basis: draft V3 FINAL (Lead A331) + mainline A332 pins + shehdd S3264/S3265/S3263 audits + lattice re-verification (this draft).
**Pins:** registry 14041 / gate in flux / record 18800; L8 frozen; no registry edits; no Lean edits; no gate-table writes.

**COVERAGE LINE (amended canonical, verbatim):** 'F=Q conditional wiring delivered (named beta-avoiding Belyi base input) + full-Qbar reduction named (not complete)'.

**VERDICT: GATE NOT PASSED; binding HOLD; FINAL ROWS subject to Lead review + fresh verification; no Thm2.5 unconditional claim.**

## 1. READINESS / TRIGGER STATUS (for FINAL ROWS)

| trigger | item | status |
|---|---|---|
| (a) one-off subagents | GDerivAeval (deriv-aeval cast formula) | GREEN CANDIDATE: CITABLE 11 decls 9077B sha 480A74450D2301D9 probe_ok (shehdd S3264); mainline verification pending |
| (a) one-off subagents | TargetImpliesFullShape (adapter #5) | GREEN CANDIDATE: CITABLE 10 decls 11657B sha 16F51D7C1B1AD32E probe_ok (shehdd S3264); mainline verification pending |
| (a) one-off subagents | CritValueInImage proof (A344 spec repair) | **CANDIDATE AUDITED (S3268): Mzk1CritValueInImageProofActual CITABLE 32 decls 22392B sha E96DAF70 probe_ok TRUE (axioms trio) (Lead A344): literal 0/1 target KERNEL-CHECKED REFUTED (s3135_critValueInImage_refuted / counterexample); true theorem critValueInImageStatement_proved (IMAGE-BASED CV-in-image) + belyiNormGPoly_critValue_zero_or_one (normalized repair) - honest spec repair; awaiting shehdd audit** |
| (b) conditional induction | Mzk1Lemma22InductionProofActual | GREEN CANDIDATE: CITABLE 8 decls 7922B sha 5490AE9C9E3F69C6 probe_ok (S3264/S3265); conditional induction_conditional (hbase, hstep) : InductionStatement PROVED; target_conditional PROVED; F=Q scope NOT closure; mainline verification pending |
| (b) conditional base | Mzk1Lemma24BaseProviderRestatedActual | GREEN CANDIDATE: CITABLE 5 decls 4732B sha 5486CCEA6ABDC736 probe_ok (S3265); target_of_betaAvoidingBelyiBase + restatedConclusion_of_providers (hbase+mu+wf lex+CorrectedStepProviderPaperInput => RestatedInductionConclusion; hwf.fix+next_beta_avoid); class-B inputs named; no closure; mainline verification pending |
| (c) H6 precise | Mzk1GeometricCorePreciseActual | **TRIGGER (c) AUDIT PASS (shehdd S3266; size correction confirmed S3267): CITABLE 7 decls, CURRENT FRESH EXT0 SIZE 4025B sha F19EEEC7EB6233526CAB035248F1152D7D58907F054021981160F5423A91BD36, probe _Mzk1GeomCorePreciseProbeActual 159B probe_ok TRUE; olean 185688 sha 5E6A3D3F97B61C3251A3FB8D755EFFA9103D893CE68FA3C317FED5EF14683BFC. CORRECTION: shehdd S3266 cited 6658B (stale size; sha F19EEEC7 matches current 4025B). Non-vacuity: MapsTToZero = real vanishing; UnramifiedOverZero := fm.LevelSetsGenericallyEtale (ported finite-map real geometry, not True); PullbackIsoDegree = real cardinality bookkeeping; NO free Prop fields; RecastPrecise = named class-B existence. Named TODOs honest (toOld assembly; line-bundle iso; existence class-B). H6 gate layer remains PARTIAL (wiring/reduction hypotheses; no closure claim)** |
| (d) beta-avoiding construction | S6/S7/hull | **Lead A342 candidate: Mzk1BetaAvoidingBelyiRationalActual EXIT0 SIZE 16885B (S7) - base |S|<=2 PROVED + exists_betaAvoiding_of_step (BetaAvoidingStep) CONDITIONAL (step named BetaAvoidingStep); tauCetiStep_not_betaAvoiding etc. **S3269 AUDITED GREEN: Mzk1BetaAvoidingBelyiRationalActual CITABLE 15 decls 25002B sha 1DE5AC5D probe_ok TRUE: base |S|<=2 PROVED (exists_betaAvoiding_card_le_two) + step NAMED BetaAvoidingStep (exists_betaAvoiding_of_step conditional); CritIn01/affine/linear comp support PROVED; tauCetiStep_not_betaAvoiding negative result honest; FINAL ROWS (d) = base |S|<=2 proved + step NAMED BetaAvoidingStep (pending mainline verification; class-B retained). **A349 CORRECTION (one-off #10, honest): Mzk1BadParamProofActual EXIT0 18633B sha E6E18A44...: ORIGINAL badParamSet_finite/exists_good_param KERNEL-CHECKED REFUTED (B(kp,kq)(u)=(B(p,q)(u))^k; p=q=1,u=1/2 => badParamSet=univ; critical point u=p/(p+q) => Bad=univ); corrected sharp theorems PROVED: badParamSet_finite_iff (finite <=> B!=1 and B!=-1), badParamSet_finite_of_ne, exists_good_param_of_ne_one; collision variant also FALSE (B(1,1)=4X(1-X) symmetric => collision set univ); CONSEQUENCE: beta-avoiding step needs avoid critical/equal B-values or re-normalize; BetaAvoidingStep remains NAMED; original plan premise wrong (recorded)** |
| (a) one-off #10 | Mzk1BadParamProofActual | **CITABLE 35 decls 18633B sha E6E18A44 probe_ok (S3271): scaling PROVED (belyiConst_scaling; belyiEvalQ_scaling); ORIGINAL refuted kernel-checked: not_badParamSet_finite (p=q=1,u=1/2 => badParamSet=univ via badParamSet_one_one_half+infinite_univ), not_exists_good_param (forall k B(1,1)(1/2)=1), not_collision_finite_statement (B(1,1)=4X(1-X) symmetric; u=1/4 vs 3/4); corrected sharp PROVED: badParamSet_finite_iff (finite <=> B!=1 and !=-1), badParamSet_finite_of_ne, exists_good_param_of_ne_one, collisionParamSet_finite_iff; honest premise correction; pending mainline verification** |
| beta auxiliary | Mzk1BelyiMaximizerActual (one-off, S3270 AUDITED GREEN) | **CITABLE 13 decls 15271B sha C64236AC probe_ok TRUE (axioms trio): belyiPolynomial_eval_eq_one_iff (Q/R/C); weighted AM-GM belyi_max_ineq + equality belyi_max_eq_iff; eval_belyiPolynomial_lt_one/le_one; belyiMaximizerStatement_proved; 6 rows; beta-avoiding step KEY lemma (pairing with badparam exists_good_param to assemble exists_card_image_lt_beta NOT yet proven - recorded); pending mainline verification** |
| beta auxiliary | Mzk1BetaAvoidingBelyiSmallActual (S6, VERIFIED fresh A367) | **SHEHDD S3278 S6 AUDIT PASS: CITABLE 34 decls 36171B sha 2F326056 probe_ok TRUE (checker WITH _S3278S6Probe; olean 1407400B sha 7C261506F957674A; axioms trio; disk=logged EXIT0 36171 match); supplement material (PENDING Lead approval; SMALL IN-PLACE beta-row update only, no republish): |S|<=2 fully proved; interior |S|=3 fully proved; exterior parity partial (exists_belyi_three_of_gt_of_odd / lt_of_odd); canonical_exterior_bad_point B12(4/3)=1; example_exterior; REMAINING NAMED blocker BelyiBetaAvoidingExteriorStatement (proved:=false; outer Belyi R(1)=0 obstruction; needs different inner Belyi)** |
| beta auxiliary | hull Mzk1BetaAvoidingReductionActual | **CITABLE 3 decls 2914B sha E94D7E39 probe_ok but STATEMENT-ONLY: BetaAvoidingReductionStatement NAMED class-B; 5-row ledger; exact blocker: TauCeti construction B=1 branch collision; maximizer uniqueness/explicit (m,n) not in tree => not counted as proof; pending mainline verification** |

## 2. PROPOSED FINAL ROWS (ready text; canonical table content)

| id | evidence | remaining | status |
|---|---|---|---|
| L0 curves/function fields | E1 defs CITABLE; AG01/02 | none | CLOSED/PASS |
| L1 divisors/height-weight | tree asset + AG03 | none | CLOSED/PASS |
| L2 cohomology | AG05 Cech CITABLE; AG_FLT_CechPromotion | none | CLOSED/PASS |
| L3 RR/Serde (ported) | AG_FLT promotions CITABLE; ported assets non-gate | none | CLOSED/PASS |
| L4 Belyi/finite maps | F=Q conditional wiring delivered (restated interfaces + CV law + L2.3/HPRES numeric evidence + conditional assembly skeleton); named base input BetaAvoidingBelyiBaseInput class-B | first F=Q component NOT complete; full Qbar layer named ((D) finite-Galois PROVED + infinite fixed field class-B + 2.3 Moebius Qbar/C + AlgebraicNestedInductionInput class-B) | PARTIAL |
| L5 GenEll | GenEll05 (i)=>(ii) PROVED; GenEll10b/15/16/17 citable | (ii)=>(i) consumer needs noncritical Belyi existence; H6 precise; corrected-2.4 consumer not wired | PARTIAL |
| L6 AbsTopIII | 01/03/07/08/09 complete citable; H1-H5/H7 closed w/ class-B leftovers | H6 precise candidate (stale until verified); AbsTopIII05 deep named | PARTIAL |
| L7 EtTh/Theta | EtTh07-13 citable; theta anti-monotonicity PROVED | realization deeper rows class-B | PARTIAL |
| L8 IUT IV section1 | S3171 IUTIVSection1 green; thm110 display conditional | L0-L7 gaps + inputs (b) uniform height-vs-volume | FROZEN/NOT PASSED |
| Delivered restated target layer | RestatedLemma24Interface 6611B/10 (src 0526AD1D; olean 82F2093D); RestatedLemma24CVLaw 3918B/5 9EE41ECD; RestatedLemma22Interface 8698B/13 src E0B711D4 probe 1063; RestatedLemma24Induction 9555B/14; LayerAAlgebraicInduction 3485B/4 probe_ok (statement only) | none for interface; statements/named inputs remain | GREEN (interface/statement layer) |
| Delivered induction/CV/bridge layer | StepInterfaceQ 2698B C74EE6FF + Proof 3831B B480D0F5; FullShapeHelpers 3403B DD987A8A; Mzk1BelyiCvBridge 4563B/5; CritValue staging 3417B/4 (item (i) NAMED); GDerivAeval 9077B 480A7445 (candidate); TargetImpliesFullShape 11657B 16F51D7C (candidate) | cast formula/CPointCVInImage NAMED; conditional files pending verification | GREEN/CANDIDATE (pending mainline verification where noted) |
| Delivered L2.3/HPRES/conditioned | Normalization 6520B B21C1493; Transfer 12033B 2E673AC3; HPRES 6825B CB0F53B6; Separation 9136B C86E19B8; Canonical 4111B 7E575EA9; Conditioned 2054B 60FA5B9B; Mobius Q 7832B 4D63BB55; C 6995B/14; consumer design 10500B/12 C82269A6 (design only) | consumer LAST; design not closure | GREEN (numeric/interface; consumer design conditional) |
| Conditional induction/base files | InductionProof 7922B/8 5490AE9C (conditional; named hbase/hstep); BaseProviderRestated 4732B/5 5486CCEA (conditional; named class-B) | real consumer + restated full gate not wired; trigger (b) candidate pending mainline verification | GREEN CANDIDATE (conditional; NOT closure) |
| H6 | Mzk1GeometricCorePreciseActual **CITABLE 7 decls 4025B sha F19EEEC7 (olean 5E6A3D3F; probe_ok TRUE, trigger c audit PASS)**; non-vacuous (real vanishing/etale/cardinality conditions; no free Prop fields); named TODOs honest (toOld assembly; line-bundle iso; existence class-B) | H6 gate layer remains PARTIAL (GenEll transfer wiring/reduction hypotheses named); no closure claim | PARTIAL (precise component GREEN; layer PARTIAL) |
| Named inputs (7, proved:=false) | BetaAvoidingBelyiBaseInput / Mzk1Lemma22RestatedBaseProviderStatement (hbase) / CPointCVInImageStatement / CorrectedStepProviderPaperInput / CorrectedAssemblyPaperInput / AlgebraicNestedInductionInput / AlgebraicClosureFixedFieldPaperInput | named inputs supply paper-level obligations; may NOT be consumed as proved | NAMED (proved:=false) |
| Binding / Thm2.5 | Thm25 binding files HOLD (tmp/xif_hold_files.txt: Mzk1Thm25Unconditional, Mzk1Lemma22FullGateActual, Mzk1Lemma24BaseCaseComplex) | un-HOLD only by explicit Lead decision after real consumer + restated full gate; no Thm2.5 unconditional claim | HOLD |

## 3. REPUBLISH CHECKLIST (one-time; after Lead approval + fresh verification)

1. Fresh re-verify ALL cited pins via tools/xif_citable_check.ps1 -File <f> -Probe <p>; replace stale owner-reported values (esp. H6 4025B disk vs 6658B last EXIT0; consumer design side pins; conditional candidates need mainline verification).
2. Coverage line verbatim (section S1) + Lead-confirmed wording.
3. Every named-input row: paper source lines + owner audit ID + proved:=false.
4. No Thm2.5 unconditional claim; GATE NOT PASSED unless Lead explicitly upgrades; binding HOLD remains.
5. History rows: old gate paths corrupt/frozen; duplicate backups non-canonical; old-target files DEPRECATED (xref).
6. New clean gate-table Lean file (new path; compact rows <1800 chars); checker+probe; report fresh pin to shehdd for ONE audit.
7. Only after shehdd audit + Lead approval: move canonical label; update ledger/STATE; keep pins registry 14041 / gate = new pin / record 18800; L8 frozen; no registry edits.
8. No queue/un-HOLD of binding files unless explicit Lead decision after real consumer + restated full gate.

## 4. BLOCKERS / OPEN ITEMS BEFORE REPUBLISH

1. H6 Mzk1GeometricCorePreciseActual: TRIGGER (c) AUDIT PASS (CITABLE 7, fresh EXIT0 4025B sha F19EEEC7, probe_ok; shehdd S3266); included as delivered precise component row. H6 GATE layer still PARTIAL (wiring/reduction named) - no closure claim.
2. Conditional induction/base files are conditional; they need mainline verification and a real consumer (2.4 o 2.3 o 2.2) before any claim; named inputs remain.
3. beta-avoiding construction is WIP (maximizer/badparam); if it fails keep class-B BetaAvoidingBelyiBaseInput + blocker.
4. One-off subagents: only GDerivAeval and TargetImpliesFullShape have cited candidate greens; others (CritValueInImage proof #3, Moebius over Qbar #4, polyEvalP1-aeval-specialSet bridge, one-off #9/#10) still WRITING/PENDING/UNVERIFIED (Lead A342) - portal remains PENDING, no counting.
5. Binding HOLD: Thm25 unconditional path files on HOLD; no un-HOLD without explicit Lead decision.

---
*FINAL ROWS DRAFT - non-canonical; prepared by 拉蒂/lattice under gate freeze (Lead A340). No gate-table writes, no Lean edits, no closure claims. Hashes verified at time of drafting unless marked stale; all pins subject to fresh re-verification at republish.*

---

## §5 PROBLEM E — ASSET INVENTORY (mainline deliverable; prepared for merge)

Source: `coord/PROBLEM-E-INVENTORY.md` (mainline/李维, 7119B; Lead A398). Citable standard (A393): fresh EXIT0 + checker WITH probe probe_ok; no audit chain. Scope: deep IUT inputs / L7-L8 deep rows. NO gate rows until verified; FINAL PIN V150@16111/84837B0B unchanged.

| id | assets (verified/provided) | status | consumer / immediate small task |
|---|---|---|---|
| E-1 AbsTopIII05 | `AbsTopIII05ReconstructionInputsActual` 3685B (`structure DeepInput`, `absTopIIIDeepInputs : List DeepInput`, length=4); AbsTopIII01LogShell, 07/08/09 green modules, 10StatementLedger, 11IndexIds, 12AssetMap | CLASS-B NAMED / NOT PROVED (L6 deep input) | IUT IV §1 display / L8 frozen; immediate: type DeepInput fields w/ paper lines, expose typed consumer interface |
| E-2 H5 O^x + det/tensor | `Hull09H5GapsActual` 5405B: scalingUnits_subset_hull, hull_eq_closure, DetTensorBookkeeping_exponent, ray_mem_iff PROVED | PARTIAL - H5 gap reduced to class-B O^x stabilization; det/tensor bookkeeping PROVED | thm110 log-volume/height (L8); Hull11/Hull13; immediate: integrate ray/det lemmas into typed consumer hypotheses |
| E-3 H7 / Ob9 | `Hull08Ob9LogLinkActual` 5921B: HullOb9Inputs, hull_ob9_interface, hull_ob9_repClass_congr PROVED; `Hull12Ob9BoundTransferActual` 445B transfer | PARTIAL - one-sided transfer/interface PROVED; full H7 arbitrary-iterate bound DEEP CLASS-B NAMED (L6) | L8 frozen / thm110; immediate: replace comparison-input fields by typed Props w/ exact paper lines, record one-sided vs both-sided |
| E-4 EtTh realization rows | `EtTh11ThetaRealizationRowsActual` 4337B PROVED: theta/elliptic power-kernel mono, modLThetaProjection_surjective, modLThetaToElliptic; EtTh12/13 assets | PROVED rows (power-kernel mono, quotient/kernel, mod-L); scheme-level realization class-B (L7) | L7/L8 route; immediate: enumerate which EtTh11/12/13 theorems feed L8 (typed consumer), mark scheme-level named with paper lines |
| E-5 IUT IV §1 uniform height-vs-volume | S3171IUTIVSection1StatementActual 4742B, EstimatesActual 2879B, InputsActual 3351B, DisplayActual 6921B, S3171UniformHeightConsumer | statement/estimates/display/consumer citable conditional; uniform height-vs-volume input (b) + region-relative-to-hull/weight CLASS-B NAMED (L8 FROZEN) | IUT IV §1 display / Cor 3.12; immediate: typed Prop list + exact statement of input (b), connect UniformHeightConsumer to Hull11/13 |
| E-6 H6 (mostly resolved) | Mzk1GeometricCorePreciseActual 7/4025B F19EEEC7 probe_ok; Mzk1GeomCorePreciseToOldActual 9/7043B 1FA662D1 probe_ok; one-off D candidate Mzk1GeomCoreRRWitnessActual (in progress, no pin) | precise schema + toOld PROVED; GenEll15 precise existence class-B; H6 gate layer PARTIAL | Hull11 H6 upgrade; immediate: replace Hull11H6 inputs by precise witness and prove hull11_h6_upgrade from GenEll15 precise statement |
| E-7 deep consumer support files | Mzk1P1ConsumerDeepInputsActual 8722B (P1 consumer named inputs typed); Mzk1HullEInputsActual 8035B (H5/H7 named inputs -> GenEll Cor312 conditional assembly) | support inventory; named inputs explicit; no closure | P1 consumer / GenEll assembly; pins pending fresh EXIT0+checker; no gate rows |

Notes: (1) merge mainline inventory sections on delivery (this section is merge-ready; no numbers/claims changed); (2) none of E-1..E-7 is a new closure row - all remain named/class-B/conditional; (3) no un-HOLD, no queue binding, no registry edits; (4) binding HOLD remains; L8 FROZEN; GATE NOT PASSED.

## §6 PROBLEM A-D — SKELETON IMPLEMENTATIONS IN PROGRESS (mainline A398; event-level)

User-provided skeletons live in `coord/` (outside citable tree on purpose). One-off agents fill proofs; NO gate rows until fresh EXIT0 + checker WITH probe probe_ok; no audit handoff (A393). Canonical gate unchanged: FINAL PIN = V150@16111/84837B0B (+v151-v156); GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041 / record 18800; no registry edits; sorry/axiom/fake closure forbidden.

| problem | skeleton | one-off agent / target file (in progress) | target statement |
|---|---|---|---|
| A - fold route | `coord/ProblemA_FoldSkeleton.lean` 9393B (fold induction: enlarge S by rational aux points so beta has S-points both sides; fold step a=min S, c=max S, b=second smallest < beta; affine A with A a=0, A c=1, r=A b=m/(m+n); B_{m,n} fold) | `Mzk1BetaAvoidingFoldActual` (in tree, no fresh pin yet) | `betaAvoiding_all : forall S beta, beta notin S -> BetaAvoidingAt S beta` (Problem A / class-B BetaAvoidingBelyiBaseInput full proof attempt) |
| B - explicit Moebius | `coord/ProblemB_Lemma23Skeleton.lean` 3269B (N(x)=C*eps/(lam-x), lam=beta+eps, (C+1)*eps<=dist(beta,S); N(beta)=C, |N(alpha)|<=1, N(infinity)=0; reverse triangle inequality only) | `Mzk1Lemma23MoebiusActual` + `Mzk1Lemma23ExplicitActual` (in tree, no fresh pin yet) | explicit rational Moebius for paper Lemma 2.3 (separation/normalization; rational coefficients; exact N(beta)=C and |N(alpha)|<=1) |
| C - nested induction (D,N) | `coord/ProblemC_NestedInductionSkeleton.lean` 6731B (measure D=largest degree over Q of S-point, N=count of degree-D points, lex; NO Galois-stable sets; add conjugates of alpha0; S1=S union roots f0; S-=f0(S1) union f0(roots f0-); recursion = Lemma 2.4 reduction to rational case) | one-off agent in progress; target file not yet present in tree (record pin when green) | nested (D,N)-induction for Lemma 2.4 over Qbar (paper lines 163-206); replaces (m(S),d(S)) bookkeeping |
| D - function-field pencil | `coord/ProblemD_GeometricCoreSkeleton.lean` 4630B (construct g with zero divisor exactly sum T; deg D>=2g+1; RR/pencil; consumer only needs psi^-1(0)=T with multiplicity one; line-bundle iso is construction, not used afterwards; deg psi=|T| follows from fibre) | `Mzk1GeomCoreRRWitnessActual` (in tree, no fresh pin yet) | H6 GeometricCore precise witness via function field / RR pencil (replaces line-bundle iso deep input; solves Problem D named class-B existence) |

Status discipline: all four are IN PROGRESS / not citable; no gate rows; no closure claims; if any file reaches fresh EXIT0+checker probe_ok, record event-level pin in ledger/STATE and propose a supplement row after Lead approval only.
