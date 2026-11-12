# FOUNDATION-FIRST PLAN (Lead A414) — bottom-layer frontier for IUT 3.12 prerequisites

**Canonical gate UNCHANGED:** V150@18248/CFC6CE08 (+v151–v157) after v157 stable rows; GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041 / record 18800; no registry edits; no un-HOLD; no queue binding.

**Policy (A409/A410/A414):** v157 keeps ONLY three stable true-theorem rows (fold PROVED / finite-β corrected base PROVED / ∞-β spec repair). C/D/E rows are NOT added to the gate until their foundation objects are stable; they are tracked here instead.

## BOTTOM-LAYER FRONTIER TABLE

Columns: 前置是否全证 = are all prerequisites PROVED?; 是否已接线 = is the layer wired to a consumer?

| id | layer | evidence / pin | 前置是否全证 | 是否已接线 | notes |
|---|---|---|---|---|---|
| B1 | fold (Problem A) | `Mzk1BetaAvoidingFoldActual` EXIT0 27144B sha E07D70385B47E4F9EB408FF312FC40FC9DF96DE169B239D2D6702A81A6D9011E; CITABLE 23 probe_ok; `betaAvoiding_all : ∀ S β:ℚ, β∉S → BetaAvoidingAt S β`; axioms trio | **YES (全证)** | **YES** — used by W1 finite-β base; consumer wiring via A406 adapter | supersedes small-case-only status; full-Qbar reduction remains named (no closure) |
| B2 | finite-β corrected base | W1 `Mzk1BetaAvoidingBaseActual` EXIT0 10430B sha 691DFC7F42FD3725FA865B27495B0239A77AB07A385CD8FCCB6CB64CA88B01D9 (`betaAvoidingBelyiBaseInputCorrected_proved`, `not_betaAvoidingBelyiBaseInput`, `Mzk1Lemma24Target_finite_beta`) + `Mzk1Consumer24AdapterUnconditionalActual` CITABLE 12/10264B 60DC8BC2 probe_ok (unconditional h24Base slot) | **YES (全证; from fold)** | **YES** — unconditional consumer adapter (class-B premise removed) | original ∞-β statement REFUTED (spec repair v157); finite-β only; full-Qbar named |
| B3 | rational 2.4 target (finite-beta) | **BOTTOM PROVED**: Mzk1Rational24TargetBottomActual EXIT0 5781B sha A4D82E806D431283 CITABLE 11 probe_ok (Rational24TargetFiniteBeta := BetaAvoidingBelyiBaseInputCorrected; rational24TargetFiniteBeta_proved from fold; BaseProviderRestatedFinite proved; oldBaseProviderPremise_refuted); plus RestatedLemma24Interface/CVLaw/rational 2.2 gate pins | **YES (all prerequisites proved for finite-beta target)** | **YES (F=Q low-level wiring)** — consumer24 adapter/wiring F=Q finite beta; full-Qbar not wired | no paper closure; gate L4 PARTIAL; infinite-beta premise refuted |
| B4 | C degree-measure layer (nested induction D,N) | `Mzk1NestedInductionActual` **A421 pin: EXIT0 37958B sha 76D71E7D...; CITABLE 43 decls probe_ok** (supersedes 37783/81E23174; ledger text only); 28 theorems; measure_stepSet_lt etc.; **BaseCaseProvider PROVED (B4b)**; **StepProvider = only remaining C named** | **PARTIAL** — degree-measure layer proved; BaseCaseProvider connectable to fold; StepProvider geometric construction still being built | **NO** — not wired to gate; C/D/E rows excluded from v157 per A410 | foundation object stabilizing; do not add gate row yet |
| B4b | C BaseCaseProvider (bottom) | **A419: `Mzk1NestedInductionBaseCaseActual` EXIT0 4728B sha 14F5F5A73FE03066...; CITABLE 4 decls probe_ok; `baseCaseProvider_proved`** + **A425 B3-C bridge: `Mzk1Rational24BaseCaseBridgeActual` CITABLE 7 decls 5119B sha 743514F1 probe_ok; `baseCaseProvider_discharged`** — BaseCaseProvider PROVED from fold/finite-beta base (prereqs B4+B2 proved); B3->C bridge PROVED | **YES (全证)** | **YES** — BaseCaseProvider wired into nested-induction providers (B4) | B4b -> BOTTOM; **C residual = StepProvider' only** |
| B6 | D-BASE (RR-independent pencil base) | **A422 BOTTOM: `Mzk1GeomCoreFoundationActual` EXIT0 14032B sha 0F74F433...; CITABLE 15 decls probe_ok; RR-independent pencil base PROVED; scheme layer PROVED; bridge/P^1 named** | **YES (全证 for base)** | **YES (base) — pencil base available to D layer; RR-dependent part named** | D split: D-BASE bottom; D-RR-dependent zero_divisor_exists still named (hRR/hdual); no gate row |
| B6b | D-RR base (BOTTOM A427; D bridge A435) | **A427: `Mzk1GeomCoreRRProvedActual` EXIT0 15877B CITABLE 14 probe_ok: `zero_divisor_exists_proved` with NO named; hRR + hdual DISCHARGED => D-RR -> BOTTOM**; **A435 D bridge pins: `Mzk1GeomCoreRRBridgeActual` CITABLE 4/5752B sha 506DCCD8; `Mzk1GeomCoreBridgeLegacyActual` CITABLE 5/6277B sha 37CFC792; `Mzk1GeomCoreBridgeInterfaceActual` CITABLE 6/6352B sha E23A014B; A445 typed interface pins: `Mzk1GeomCoreFiniteMapRouteActual` 6/8109B 08C4D547 probe_ok; `Mzk1GeomCoreLineBundleInterfaceActual` 8/6042B 0945A965 probe_ok => **D TYPED INTERFACE CLOSED; D STATUS PARTIAL** (PROVED: interface fields + finrank_functionFieldSections_eq / degree_eq_of_interface / sectionImage_mem + finiteMapData_of_construction + preciseWitness_of_route / recast_of_route; NAMED: actual finite-map construction, actual O(D) sheaf / psi* pullback / uniformizer-order compatibility, psi^*O(1)=O(D) iso content)**; prior: RR Mzk1RRProvedActual 3/4757B B3A67DEE probe_ok; RRInterface 9/8895B 7BD88E7D probe_ok; D-BASE 14032B 0F74F433 CITABLE 15 probe_ok | **YES (D-RR bottom)** | **YES (bridge interface proved) — remaining D: finite map + line bundle iso** | no gate row |
| B5 | Lemma 2.3 Möbius | `Mzk1Lemma23SeparationActual` 5/6624B 1AC876CD probe_ok (`s3135_separation_rat` + `_value` PROVED rational 2.3; `QbarSeparationPaperStatement` statement-only); `Mzk1Lemma23MoebiusActual` CITABLE 8/6400B 66D16886 probe_ok (explicit rational N(x)=Cε/(λ−x)); `Mzk1Lemma23ExplicitActual` 18742B (explicit proof; pin pending) | **PARTIAL** — rational 2.3 PROVED; Qbar statement named | **NO** — not wired to gate yet | paper lines 136-143/181-186; rational coefficients explicit |

### NOT-YET layers (not stable; excluded from gate)

| id | layer | evidence / pin | 前置是否全证 | 是否已接线 | notes |
|---|---|---|---|---|---|
| NY-1 | D-RR-dependent zero_divisor_exists (RR now PROVED) | **A424: RR PROVED — `Mzk1RRProvedActual` EXIT0 4757B (flt_core independent closure; axioms trio) => D-RR critical path UNBLOCKED; next `Mzk1RRInterfaceActual` + Foundation migration flt_core. D-BASE remains BOTTOM (`Mzk1GeomCoreFoundationActual` 14032B 0F74F433 CITABLE 15 probe_ok); D-RR-dependent zero_divisor_exists to be re-proved against real RR; bridge/P^1 named; legacy RRWitness 2804B** | **NO** — RR existence is the unique named input; port in progress | **NO** | H6 precise witness route; do not gate-row until RR ported/verified |
| NY-2 | C StepProvider prerequisite (A434 update) | C `Mzk1NestedInductionActual`; A424 StepProvider' restatement (beta'=f0(beta)); **A434: `Mzk1StepProviderPrimeActual` 11/6312B sha CCE61640 probe_ok; `Mzk1CVCompositionFActual` 5/2752B sha 706859EC probe_ok (CVCompositionLawF PROVED; stepTransport_of_goal_proved) => CVCompositionLawF REMOVED from named; `Mzk1Lemma24DegreeFoundationActual` 16/6204B sha 6346B15D** | **StepProviderPrime PROVED; CVCompositionLawF PROVED; remaining C: f4 measure transfer + assembly; fixed-beta named** | **NO** — geometric construction in progress | **NO** | connects C to algebraic nested induction; wait for green pin |
| NY-3 | E deep inputs | AbsTopIII05 (class-B deep input); H5 O^x stabilization class-B; H7/Ob9 full arbitrary-iterate bound class-B; EtTh scheme-level realization class-B; IUT IV §1 uniform height-vs-volume class-B | **NO** — all named/class-B | **NO** | L7/L8 frozen; no closure |

## STATUS EVENT LOG (foundation-first)

- 2026-11-10 23:40: v157 three stable rows executed in canonical V150 (fold PROVED / finite-β corrected base PROVED / ∞-β spec repair); new canonical pin V150@18248/CFC6CE08. B1/B2 fully proved and wired (B2 via unconditional consumer); B3 conditional/wired F=Q; B4 partially proved/not wired; B5 rational proved/not wired; NY-1..NY-3 not stable. No gate rows for C/D/E (A409/A410/A414). GATE NOT PASSED; binding HOLD; L8 FROZEN.

Prepared by lattice under Lead A414; notes only, no gate effect.

- 2026-11-11 00:29 (A445): DAG split formal 296/348/0 (paper fragments moved coord/paper-chain as research maps, cyclic, not declaration DAG); new pins Section0Objects 31/11621 970AA5AA; LineBundleInterface 8/6042 0945A965; FiniteMapRoute 6/8109 08C4D547; CVCompositionF 5/2752 706859EC (2589 stale). No gate edit.
- 2026-11-11 00:35 (A448): StepProviderPrime NS 6157/B AB9AF3BC probe_ok (supersedes 6312/CCE61640); LineBundleBridge 4883/C9BBF600 pending fresh EXIT (not citable); known OLEAN_MISSING red tree builds - do not cite. No gate edit.

- 2026-11-11 00:31 (A446 CORRECTION): LineBundleInterface/FiniteMapRoute are TYPED INTERFACE/route layers — PROVED = interface fields + finrank_functionFieldSections_eq/degree_eq_of_interface/sectionImage_mem + finiteMapData_of_construction + preciseWitness_of_route/recast_of_route; NAMED = actual finite-map construction, actual O(D) sheaf/psi* pullback/uniformizer-order compatibility, psi^*O(1)=O(D) iso content. **D STATUS: PARTIAL (typed interface closed; actual construction named)**; do NOT record D remaining PROVED.

- 2026-11-11 00:11 (A435): D bridge: RRBridge CITABLE 4/5752 sha 506DCCD8; BridgeLegacy CITABLE 5/6277 37CFC792; BridgeInterface CITABLE 6/6352 E23A014B; D remaining: finite map + line bundle iso. DegreeFoundation file = Mzk1Lemma24DegreeFoundationActual 6204B 6346B15D (verified). CVCompositionF checker CITABLE 5/2752 706859EC probe_ok. No gate edit.

- 2026-11-11 00:09 (A434): NY-2: StepProviderPrime 11/6157 AB9AF3BC probe_ok (A448 supersedes 6312/CCE61640); CVCompositionF 5/2752 706859EC probe_ok (CVCompositionLawF PROVED; stepTransport_of_goal_proved) => CVCompositionLawF removed from named; DegreeFoundation fresh 16/6204 6346B15D; remaining C: f4 measure transfer + assembly; fixed-beta named. No gate edit.

- 2026-11-11 00:01 (A427): (1) D-RR -> BOTTOM: Mzk1GeomCoreRRProvedActual 15877B CITABLE 14 probe_ok (zero_divisor_exists_proved no named; hRR+hdual discharged). (2) C StepProvider prerequisite: Mzk1NestedInductionStepProviderActual 5647B CITABLE (stepTransport_of_goal conditional on CVCompositionLawF); NY-2: geom f1/f2/f4 + CVCompositionLawF + fixed-beta named. Gate untouched.

- 2026-11-10 23:59 (A426): RRInterface Mzk1RRInterfaceActual CITABLE 9/8895B sha 7BD88E7D probe_ok => RR interface proved (only flt_core root); remaining D-RR: Foundation migration + hdual discharge + ell_sub_single_add_one + zero_divisor_exists_proved. No gate edit.

- 2026-11-10 23:54 (A425): B3-C bridge Mzk1Rational24BaseCaseBridgeActual CITABLE 7/5119B sha 743514F1 probe_ok (baseCaseProvider_discharged) => BaseCaseProvider wired; C residual = StepProvider' only. RR Mzk1RRProvedActual CITABLE 3/4757B sha B3A67DEE probe_ok => D-RR critical path removed; B6b added; NY-1 re-scoped (RR proved -> interface/migration pending -> zero_divisor_exists re-proof); NY-2 StepProvider' reformulation note. Gate untouched.

- 2026-11-10 23:50 (A424): (1) RR PROVED: Mzk1RRProvedActual 4757B EXIT0 (flt_core independent closure; axioms trio) => D-RR critical path unblocked; next Mzk1RRInterfaceActual + Foundation flt_core migration. (2) C StepProvider SPEC DEFECT: fixed-beta beta-notin-S' not guaranteed => restate StepProvider' (beta'=f0(beta)); f1/f2/f4/f5 provable; f3 eliminated; fixed-beta extra argument named. No gate edit.

- 2026-11-10 23:48 (A422): D split: D-BASE = Mzk1GeomCoreFoundationActual 14032B 0F74F433... CITABLE 15 probe_ok (RR-independent pencil base PROVED; scheme layer PROVED; bridge/P^1 named) -> BOTTOM; D-RR-dependent zero_divisor_exists named hRR/hdual -> NOT-YET; legacy RRWitness 2804B. No gate edit.

- 2026-11-10 23:46 (A421): C pin updated to 37958B/76D71E7D... (CITABLE 43 probe_ok; supersedes 37783/81E23174); BaseCaseProvider PROVED (B4b); StepProvider only named; no gate edit.

- 2026-11-10 23:44 (A419): C BaseCaseProvider PROVED: Mzk1NestedInductionBaseCaseActual EXIT0 4728B CITABLE 4 probe_ok (baseCaseProvider_proved); prereqs B4+B2 proved => B4b -> BOTTOM; remaining C named = StepProvider only; D/E remain NOT-YET. No gate edit.

- 2026-11-10 23:43 (A417): B3 bottom proved: Mzk1Rational24TargetBottomActual EXIT0 5781B sha A4D82E80... CITABLE 11 probe_ok (rational 2.4 target finite-beta unconditionally proved from fold; old inf-beta premise refuted); stepxi inventory coord/FOUNDATIONS-IUTIV.md 16984B referenced. No gate edit; FINAL PIN V150@18248/CFC6CE08.

- 2026-11-10 23:41 (A415 correction): B4 C pin corrected to 37783B/81E23174 (CITABLE 43 probe_ok; supersedes 37766/A12C73AE); NY-1 D RRWitness currently RED 17032B/52189656 (editing) + Pencil 19322B/DEA52239 pending fresh EXIT0; NY-1 kept. Mainline appendix C/D/E construction plans present below.


---

## MAINLINE APPENDIX (Lead A409/A410): C/D/E paper-faithful construction plans (notes only; no gate edit)

Verified pins (mainline, fresh checker WITH probes, 23:40):
- C: `Mzk1NestedInductionActual` EXIT0 37783B sha 81E231748041E18D (CITABLE 43 decls probe_ok; 28 theorems; supersedes 37766/A12C73AE).
- W1: `Mzk1BetaAvoidingBaseActual` EXIT0 10430B sha 691DFC7F (CITABLE 16 probe_ok; corrected finite-beta base PROVED; infinity refuted).
- v157: V150 EXIT0 18248B sha CFC6CE08; CITABLE 2 probe_ok; olean 361816B sha 9F490113; three stable rows correct.
- D: `Mzk1GeomCoreRRWitnessActual` currently RED 17032B sha 52189656 (editing); `Mzk1GeomCorePencilActual` 19322B DEA52239 pending fresh EXIT0; RR port tauceti_rr in progress (Pencil.lean EXIT1).

### C — paper Lemma 2.4 nested (m,d) induction (paper lines 163-206)
Paper definition/construction: S finite subset P1(Qbar), beta notin S; Galois-stable replacement; m(S)=max reduced degree [F:Q]-1, d(S)=sum reduced degrees attaining m; nested induction on (m,d): pick alpha0 with [Q(alpha0):Q]=m(S)+1; normalize by Lemma 2.3 + positive rational scaling (|alpha|<=1, |beta| large); f0=monic minpoly alpha0; S'=f0(S) union f0(roots f0'); f0(beta) notin S'; reduced-degree drop for alpha' in f0(roots f0') (deg f0'<=d0-1); prove m(S')<m(S) or (m equal and d(S')<d(S)); recurse and compose; field-of-definition/infinite-fixed-field descent.
Existing real assets: `Mzk1NestedInductionActual` real defs degQ/maxDeg/numMax/conjSet/critSet/stepSet; PROVED isIntegral_Qbar, degQ_pos, degQ_zero, degQ_aeval_le, degQ_critValue_lt, degQ_moebius, minpoly_map_ne_zero, mem_conjSet_iff, self_mem_conjSet, aeval_derivative_eq_zero_of_mem_critSet, zero_mem_stepSet, maxDeg_stepSet_le, numMax_stepSet_lt, measure_stepSet_lt, exists_stepSet_measure_lt, nested_induction_terminates, induction_with_invariant, provider-level `paperScopeLemma24Statement_of_providers`, maxDegP_image_ofFinite, numMaxP_image_ofFinite; 17-row ledger. `coord/ProblemC_NestedInductionSkeleton.lean` bookkeeping (D=largest degree, N=#degree-D points; no Galois-stable set; C=4 universal constant; Gauss-Lucas; |f0|<=2^d, |f0(beta)|>=3^d). `Mzk1Lemma23SeparationActual`/`Mzk1Lemma23MoebiusActual` rational 2.3 P1/Moebius PROVED.
Gap: (1) BaseCaseProvider from B2 fold (abc wiring in progress); (2) geometric StepProvider (f0 construction, CV image inclusion, S' bookkeeping with point-at-infinity and Moebius poles; measure lemmas already proved; stage4 in progress); (3) map layer assembly (polynomial composition, P1(Qbar)->P1(Qbar) conversion, provider instantiation); (4) infinite fixed field (class-B named; finite Galois descent PROVED). No conditional shell substitution; no paper closure.

### D — H6 GeometricCore via function field (paper lines 222-265)
Paper construction: D=sum T, deg D>=2g+1; RR for D and D-t gives l(D)-l(D-t)=1; take h in L(D) outside union L(D-t) (infinite field not finite union of proper subspaces); h has simple poles exactly at T; g=1/h; psi^*O(1)=O(D); deg psi=|T|; rest of Thm 2.5 only needs zero divisor of g = sum T (simple).
Existing assets: `coord/ProblemD_GeometricCoreSkeleton.lean` (construction; deep input = function-field RR + l(E)=0 for deg E<0 + deg K=2g-2; no Cartier/Picard/pencil API needed). Precise H6 layer PROVED: `Mzk1GeometricCorePreciseActual` (4025B F19EEEC7 probe_ok), `Mzk1GeomCorePreciseToOldActual` (7043B 1FA662D1 probe_ok), `GenEll15GeometricCoreAssemblyActual` recast laws, `Hull11PreciseConsumerActual` (5862B D0C2250A probe_ok). Function-field candidates: `Mzk1GeomCoreRRWitnessActual` (editing; zero_divisor_exists/l-facts), `Mzk1GeomCorePencilActual` (19322B DEA52239 pending), ported `AlgebraicCurve.FunctionFieldRiemannRoch` (flt_test definitions) + qpilot tauceti_rr port (in progress; drift fixes needed).
Gap: (1) RR layer must become real: port/compile the exact function-field RR theorem qpilot is working on; (2) construct L(D)/l(D)-l(D-t)=1/h-outside-union/g=1/h in tree; (3) replace named precise-witness existence with constructed pencil; (4) wire GenEll15/Hull11 precise consumers only after RR is real. Do not gate-row until RR verified.

### E — deep IUT inputs (AbsTopIII05 / H5 O^x / H7-Ob9 / EtTh realization / IUT IV §1)
Existing real objects (see coord/PROBLEM-E-INVENTORY.md for full tables): AbsTopIII05RefinedActual (10562B 08816FDE; CITABLE 16 probe_ok): D1 Prop58iLocalFieldReconstruction/D2 Prop58iiLogShellReconstruction/D3 Cor55 bridge anchor discharged/D4 Z-graph action anchor discharged; refinedDeepInputKinds_eq_original rfl linkage; S3171RouteSlot wiring. H5: Hull09H5Gaps PROVED framing; blockers = H5 full O(-)^{-1} normalization + hull<=image-volume inequality (named); SG3b tensor Haar product blocker (no actual product-Haar formula; exact first error; no fake packet). H7/Ob9: Hull08 interface + Hull12 one-sided transfer PROVED; Hull13 two-sided bound (5260B 79F714C0 probe_ok; upper projection; deep Ob9 arbitrary-iterate named). EtTh: EtTh11/12/13 PROVED rows; EtThRealizationConsumer (11293B C12C6CAC probe_ok; 11-row inventory 3 named+8 proved; conditional wiring; no portable asset). IUT IV §1: IUTIV-SECTION1-PLAN maps Thm1.10 objects; S3171 statement/estimates/inputs/display/uniformHeightConsumer citable conditional; (b) UndilatedHeightBound and (c) UndilatedRegionBound named; height dictionary != height-volume inequality (S2802); C3 region formula not actual (S2826); Cor312 reduces to S2717UpperGap (S2804).
Gap/next: write paper-scope definitions for each named deep input + exact required inequality/construction (hard construction, no shortcut); keep typed consumption graph; no L7/L8 consumer wiring until premises are real. No portable anabelian/log-geometric assets (grep 0); no port action.

### IUT IV §1 tracking (stepxi)
Assets S3171* + IUTIV-SECTION1-PLAN; (b)/(c) named; display conditional; L8 FROZEN. Next: align statement layer with real C/D objects once constructed.

### Next actions (owners)
- abc: C BaseCaseProvider from B2 fold; record consumer/premises.
- stage4: C geometric StepProvider construction (f0 + CV image inclusion + bookkeeping).
- hull: D merge RRWitness+Pencil into one real construction once RR real; keep D out of gate.
- qpilot: PRIORITY finish RR port (tauceti_rr; Pencil.lean EXIT1) or port only the RR theorem needed - decides D zero_divisor_exists unconditional.
- stepxi: IUT IV §1 statement alignment; no high-level wiring.
- mainline: verify fresh pins only; no gate rows for C/D/E until stable; event records.

Rules: only B-class wired (B1/B2 now; B3 F=Q low-level; B4 after BaseCaseProvider; B5 rational); NOT-YET D/StepProvider/E stay unwired; no paper/Cor312/ABC closure; FINAL PIN V150@18248/CFC6CE08; GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041.
### v157 PIN SYNC (mainline A416; event)
- CANONICAL V150 EXIT0 18248B; src sha CFC6CE08A9633B381170AB3FE6399B30436F8380D7E65E3243235D39BF3DBFC0; olean 361816B sha 9F490113815F4A551E649D87FFA3FBC8CD02CC1856FEAAE6EF1589C96D7F9486; CITABLE 2 probe_ok; three stable rows (fold / finite-beta base / infinity-beta spec repair); NAMED INPUT 1 updated (original refuted; corrected finite-beta PROVED).
- B1 row pin: unchanged source `Mzk1BetaAvoidingFoldActual` 27144B E07D7038 CITABLE 23 probe_ok; used in v157 gate row 'Problem A fold PROVED (v157)'.
- B2 row pin: W1 `Mzk1BetaAvoidingBaseActual` 10430B 691DFC7F CITABLE 16 probe_ok; gate row 'Problem A finite-beta corrected base PROVED (v157)'; consumer adapter CITABLE 12/10264 60DC8BC2 probe_ok.
- C current pin correction: `Mzk1NestedInductionActual` 37783B sha 81E231748041E18D CITABLE 43 decls probe_ok (28 theorems) — supersedes 37766/A12C73AE in table above.
- D status: RRWitness RED 17032B sha 52189656 (editing); Pencil 19322B DEA52239 pending fresh; RR port in progress (qpilot priority).
- GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL = V150@18248/CFC6CE08; registry 14041.

### A417 bottom-layer additions (mainline verified; event)
- B3-rational bottom: `Mzk1Rational24TargetBottomActual` EXIT0 5781B sha A4D82E806D431283 CITABLE 11 decls probe_ok (probe _Mzk1Rational24BottomProbe 1110B): Rational24TargetFiniteBeta := BetaAvoidingBelyiBaseInputCorrected; rational24TargetFiniteBeta_proved (from B1 fold via B2 W1); Mzk1Lemma24Target_finite_beta_bottom; BaseProviderRestatedFinite/baseProviderRestatedFinite_proved; mzk1Lemma24Target_of_betaAvoidingBelyiBaseCorrected; oldBaseProviderPremise_refuted (old inf-beta premise FALSE; not used); restatedBaseStatementFinite_bottom/restatedInductionConclusionFinite_bottom re-exported PROVED. => rational 2.4 base layer now unconditionally proved for finite beta (F=Q). No ABC/Cor312 wiring.
- IUT IV foundations inventory: `coord/FOUNDATIONS-IUTIV.md` (16984B; stepxi) - REAL/MODEL/IFACE/GAP classification of IUT IV §1 & 3.11->3.12 foundations; cross-referenced with IUTIV-SECTION1-PLAN and IUT-EXTERNAL-OBJECTS-INVENTORY §L8. No wiring.
- Consequences for frontier: B3 (rational 2.4 target finite-beta) now has PROVED bottom object; remaining high-level wiring stays frozen per A409/A414; C BaseCaseProvider can consume B2/B3-bottom; D/E unchanged (NOT-YET).
- GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041.

### A419 C BaseCaseProvider PROVED (mainline verified; event)
- `Mzk1NestedInductionBaseCaseActual` EXIT0 4728B sha ? (file pin; checker WITH probe CITABLE 4 decls probe_ok; probe Mzk1NestedInductionBaseCaseProbeActual 157B): `exists_rat_eq_of_degP_le_one`; **`baseCaseProvider_proved : BaseCaseProvider` PROVED unconditionally** (identity polynomial f=X; rationalization of points of degP<=1; S_phi=S rationalized; f'=1 no critical points; infinity handled).
- Consequences: C `paperScopeLemma24Statement_of_providers` base premise DISCHARGED; remaining C named provider = **StepProvider (P1 geometric map layer)** only. B4b row becomes BOTTOM (all prereqs proved: B4 degree/measure + B2 fold base); StepProvider remains NOT-YET.
- Note: file name is `Mzk1NestedInductionBaseCaseActual` (not Mzk1BaseCaseProviderActual); owner may update C file's historical ledger row (line ~695) to reflect discharge.
- GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041.

### A421 C ledger consistent (pin update; event)
- `Mzk1NestedInductionActual` EXIT0 37958B sha 76D71E7D8965BC20224C0CC5552FB58551F986BF3CA91D076A089A322A90E997 (supersedes 37783/81E23174; only ledger/status text changed, theorems identical); checker WITH probe CITABLE 43 decls probe_ok TRUE.
- Ledger state: BaseCaseProvider row NAMED -> PROVED (evidence baseCaseProvider_proved, identity polynomial, unconditional); assembly row CONDITIONAL (StepProvider named); StepProvider = ONLY remaining named blocker; sorryItems shrunk to StepProvider only.
- GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041.

### A422 D consolidation verified (mainline; event)
- `Mzk1GeomCoreFoundationActual` EXIT0 14032B sha 0F74F4336AA08DFE590128B0...; checker WITH probe CITABLE 15 decls probe_ok TRUE (probe 357B).
- Canonical D foundation: (PART1) RR-INDEPENDENT BASE PROVED (re-exported from Pencil): ell_drop_of_rr, exists_mem_notMem_of_proper, PencilData, exists_simple_pole_function, exists_function_with_zero_divisor, GeometricCoreZeroDatum, exists_geometricCore_zeroDatum, zeroSet_eq_T, zero divisor lemmas, Curve.punctureDivisor (+sub_single_le/degree=|T|), MapsTToZeroOn family. (PART2) NOT-YET: zero_divisor_exists consumes named hRR : FunctionFieldRiemannRoch K F and hdual dual-vanishing; requires |T|>=2g+1; extraction only. (PART3) SCHEME LAYER PROVED with vacuity fix: FibreOverZeroEq/mapsTToZero/eq_zeroLocus, Mzk1GeometricCoreWitnessPreciseRestated, restatedToPrecise/Old, recast_of_restated, restatedWitness_of_data, recastRestated, consumer links. NOT-YET: scheme<->function-field bridge (no API linking fm.f on U to F); finite map to P^1 remains named.
- `Mzk1GeomCoreRRWitnessActual` now 2804B (2 decls; legacy/supplementary ledger) CITABLE; no longer the canonical source.
- FRONTIER: D-BASE (RR-independent) -> BOTTOM (all prereqs Mathlib/ported flt_test + Pencil); D-RR-dependent (zero_divisor_exists) and D scheme->function-field/P^1 bridge remain NOT-YET until RR real.
- GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041.

### A424/A425 RR proved + StepProvider' reformulation + B3-C bridge (mainline verified; event)
- **RR PROVED**: `Mzk1RRProvedActual` EXIT0 4757B sha B3A67DEE4CDF656A CITABLE 3 decls probe_ok TRUE (probe _S3234RRProvedProbe 288B EXIT0; axioms trio): `functionFieldRiemannRoch_proved : AlgebraicCurve.FunctionFieldRiemannRoch K F` via flt_core independent closure (5 serial files green; no flt_th/flt_test duplication). => **D-RR critical path REMOVED**.
- Next D: qpilot `Mzk1RRInterfaceActual` (flt_core interface re-export RR/ell_neg/2g-2) -> hull migrates D Foundation to flt_core root -> `zero_divisor_exists_proved` (hRR+hdual discharged) => D-RR to BOTTOM. FRONTIER: add B6b D-RR base row (RR proved; interface/migration pending; zero_divisor_exists re-proof next); NY-1 re-scoped 'RR proved -> unblocked'; flt_test version legacy.
- **C StepProvider spec defect + reformulation**: fixed-beta `beta notin S'` not guaranteed => approved **StepProvider' (beta' = f0(beta))**; f1/f2/f4/f5 provable, f3 eliminated by reformulation; fixed-beta extra argument registered NAMED; NY-2 updated. Next stage4 `Mzk1StepProviderPrimeActual` (f1/f2/f4 then f5 composition transport; old-interface equivalence via NAMED alpha0/Galois choice).
- **B3-C bridge**: `Mzk1Rational24BaseCaseBridgeActual` EXIT0 5119B sha 743514F101E6466D CITABLE 7 decls probe_ok TRUE (probe _Mzk1Rational24BaseCaseProbe): baseCaseProvider_discharged; ProblemCResidual := StepProvider (exact single residual); paperScopeLemma24Statement_of_provedBaseCase; rational24_and_baseCase_proved; rational24Target_finite_beta_available; 8 rows recording B3 vs C layer relation (B3 fixes {inf,0,1} over Q finite beta; C arbitrary rational S_phi; both proved). C base case discharged; only StepProvider' (reformulated geometric layer) remains named.
- stage4 fresh: Mzk1F0StepGeometryActual CITABLE 21/8202B BC6B35F1; Mzk1Lemma24DegreeFoundationActual CITABLE 16/6175B (probe _Mzk1DegreeFoundationProbe) [owner-reported; mainline re-verify pending].
- GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041; no un-HOLD.

### A426 RR interface verified (qpilot; mainline; event)
- `Mzk1RRInterfaceActual` EXIT0 8895B sha 7BD88E7DE060C131B822A2099A387C388EE8BE9CBC9351303BDA93C669EB7DAC; checker WITH probe CITABLE 9 decls probe_ok TRUE (probe _S3235RRInterfaceProbe 561B EXIT0). Only imports flt_core root (no flt_th/flt_test duplicate definitions).
- Content: functionFieldRiemannRoch_interface; ell_eq_zero_of_degree_neg_interface; degree_canonicalDivisor_interface (=2g-2, via flt_core ModularCurve p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax + stichtenothGenus; named = RiemannGenusReachedAt/weil-maximality/ConstantsAreBase); degree_single_interface; deg_eq_one_interface; Curve.punctureDivisor + degree_punctureDivisor=|T| on flt_core types; ell = AdelicIndex abbrev; 7 rrInterfaceRows with source file/line + olean status.
- Pin fix: _S3234RRProvedProbe now full names; probe EXIT0; Mzk1RRProvedActual checker WITH probe CITABLE 3 probe_ok (sha B3A67DEE).
- D next: hull Foundation migration to flt_core root; hdual discharge via interface; `ell_sub_single_add_one` has no existing flt_core lemma (can be built from ell=finrank LSpace + lSpace_mono + degree_single at hull/pencil layer or qpilot next batch); then `zero_divisor_exists_proved` -> D-RR bottom.
- GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041.

### A434 C StepProvider' advancement (mainline verified; event)
- `Mzk1StepProviderPrimeActual` CITABLE 11/6312B sha CCE61640D10BB1D2 probe_ok: StepProvider' definition (beta' = f0 beta); f1 exists_maxDegP_finite; f2 stepSetP1 + membership incl infinity; StepProviderFixedBetaChoiceInput NAMED (fixed-beta extra); rows.
- `Mzk1CVCompositionFActual` CITABLE 5/2752B sha 706859ECBF840F7A probe_ok (upgraded from RED): `cvCompositionLawF_proved` (CVCompositionLawF PROVED via derivative_comp+aeval) + `stepTransport_of_goal_proved` (minpoly transport with CV input discharged) => named CVCompositionLawF REMOVED.
- `Mzk1Lemma24DegreeFoundationActual` CITABLE 16/6204B sha 6346B15DFB6BD6EF probe_ok (fresh pin; supersedes 6175).
- C remaining: f4 P1 measure transfer + StepProvider' assembly with baseCaseProvider_proved -> C assembly switch; fixed-beta extra named.
- FRONTIER NY-2 updated: geometry f1/f2/f4 + CVCompositionLawF now PROVED; remaining = f4 measure transfer + assembly + fixed-beta named. No gate edit; GATE NOT PASSED; binding HOLD; FINAL PIN V150@18248/CFC6CE08; registry 14041; L8 frozen.
