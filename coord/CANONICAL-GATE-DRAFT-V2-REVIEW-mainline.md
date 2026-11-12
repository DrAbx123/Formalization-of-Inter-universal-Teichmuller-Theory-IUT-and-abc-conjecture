# MAINLINE REVIEW — coord/CANONICAL-GATE-DRAFT-V2.md (non-canonical gate draft)
Author: 李维/mainline. Date: 2026-11-10. Gate frozen; this review does NOT write the gate table.

Overall: structure and honesty framing are good (non-canonical, coverage line, named inputs proved:=false, no closure, HOLD respected). Apply corrections C1-C12 before Lead FINAL ROWS.

## C1. STALE: BelyiCvBridge no longer red
§2.4 says 'awaits hull BelyiCvBridge (4952B, red/fixing)'. UPDATED (A319, mainline verified):
`Mzk1BelyiCvBridgeActual` EXIT0 SIZE=4563, checker CITABLE 5 decls, probe 201678:
`belyiPolynomial_critIn01` (C-point critical values subset {0,1}), `gPoly_eq_belyi21_comp`, `belyi21_derivative_root_reexport`;
derivative-aeval CAST FORMULA remains NAMED TODO pending stage4 signature.

## C2. MISSING: RestatedLemma22InterfaceActual (2.2 single source)
Add to §2.2: EXIT0 results:201140 SIZE=6012; checker CITABLE 9; src FDA5B47D / olean 97712 1A4B8F1A; probe _RestatedLemma22Probe 200004;
decls Mzk1Lemma22Target (C-point)/Good/Mzk1Lemma22Target_iff_exists_Good (PROVED)/Mzk1Lemma22InductionStatement (NOT proved)/target_of_induction (PROVED)/Mzk1Lemma22CVCompat/CVCompat pair = abc's CVCompositionLawStatement AND SpecialSetPreservationStatement.

## C3. MISSING: RestatedLemma24InductionActual updated with conditional named inputs
§2.1 should add: abc updated file EXIT0 SIZE=8184, CITABLE 13 (A306): proves s3135_polyEvalP1_comp, s3135_CVInvariant_comp, s3135_RestatedStep_cvInvariant; statement layer RestatedState/RestatedMeasureLE/RestatedBaseStatement/RestatedStep/RestatedInductionConclusion/RestatedInductionAssemblyStatement;
adds named inputs BetaAvoidingBelyiBaseInput, CorrectedStepProviderPaperInput, CorrectedAssemblyPaperInput (must be in §3 table, proved:=false).

## C4. MISSING: RestatedLemma22Interface CVCompat ties to hv? Add green evidence list
Also add Mzk1Lemma22CritValueActual EXIT0 3417, CITABLE 4 (A310; minimal staging) and S3257CritValueBaseProviderAuditActual 2602 2602B as audit row; CritValueInImageStatement NAMED item (i).

## C5. STALE consumer design pin
§2.5 cites 8715B/90123C46/AC95FFC6 (that was A305). Later shehdd record S3258 states design 9329B sha 18E57C92 (unique Q-typed source layering). Fix: cite latest owner-reported pin (9329B/18E57C92) and require re-verification at republish; keep 'design only NOT closure'.

## C6. OVERCLAIM in L4 row (IMPORTANT)
L4 says '2.4 F=Q component (base m(S)=0 + rational Belyi existence supported S3236/...)'. Hull A319: corrected base provider BLOCKED -> class-B BetaAvoidingBelyiBaseInput; S3236 rational base provider targets OLD degenerate Goal and is NOT valid for restated base. Rewrite L4 delivered part as:
  'F=Q CONDITIONAL wiring delivered (restated interfaces + CV law + L2.3/HPRES numeric evidence + conditional assembly skeleton), with named base input BetaAvoidingBelyiBaseInput; first F=Q component NOT complete.'
COVERAGE LINE QUESTION for Lead: canonical line currently 'F=Q component delivered + full-Qbar reduction named (not complete)' is ambiguous because corrected base provider (F=Q base case) is class-B named. Recommend amended line:
  'F=Q conditional wiring delivered (named base input BetaAvoidingBelyiBaseInput) + full-Qbar reduction named (not complete)'
await Lead wording decision before republish; until then keep draft line verbatim with footnote.

## C7. §3 named inputs table: remove legacy Mzk1Lemma22BaseProviderStatement
It is the OLD degenerate-target name; do NOT list as named input. Replace with the A318 conditional hypotheses: hbase / hstep / CPointCVInImageStatement, plus file-level conditionals Mzk1Lemma22InductionProofActual (stage4) and Mzk1Lemma24BaseProviderRestatedActual (abc).
Full §3 list should be exactly:
  (1) BetaAvoidingBelyiBaseInput (rational base; blocked obstruction: no q(beta) control in TauCeti Belyification; affine can't preserve CV subset {0,1}; parameterized family only partial) - proved:=false
  (2) CorrectedStepProviderPaperInput (corrected step provider) - false
  (3) CorrectedAssemblyPaperInput (assembly over restated target/CVInvariant) - false
  (4) AlgebraicNestedInductionInput (paper 179-206 m/d descent step) - false
  (5) AlgebraicClosureFixedFieldPaperInput (infinite Galois fixed field) - false
  (6) CPointCVInImageStatement (item (i); staging only) - false
  (7) hbase/hstep of conditional 2.2 induction - false
All with paper source lines and 'proved := false'; named inputs may NOT be consumed as proved in any gate row.

## C8. §4 remaining gate items: add corrected 2.2/2.4 layer rows
Add: (a) corrected 2.2: Mzk1Lemma22InductionStatement NOT proved (conditional file pending stage4); (b) corrected 2.4: base provider/step provider/assembly conditional files pending abc; (c) full gate not started (no file); (d) real consumer 2.4 o 2.3 o 2.2 not wired (design only); (e) H6 precise-ification assigned hull; (f) upstream beta-avoiding Belyi search assigned qpilot; (g) binding HOLD (Thm25Unconditional + FullGate + BaseCaseComplex in tmp/xif_hold_files.txt).

## C9. §5 republish template: add audit/wording steps
Add steps: (6b) every named input row lists paper source lines + owner audit ID + proved:=false; (7b) coverage wording confirmed by Lead (C6); (8b) fresh re-verification of ALL cited hashes at final pins (stale owner-reported pins superseded only by fresh checker runs); keep one-time constraint.

## C10. §2.6 historical rows: mark explicitly
Mark S3236 (old base provider), S3232 assembly skeleton, S3223 residuals as 'OLD TARGET / HISTORICAL, not gate evidence'; do not mix with delivered rows.

## C11. Add A318/A314/A313 references
Add decision rows: A313/A314 scope split (option i; coverage); A318 conditional versions allowed/required (named hypotheses; non-closure); A319 bridge green + base class-B; A320 assignments; A321 deliverable link. These are decision/record rows, not gate rows.

## C12. Consistency: duplicate CV law evidence
Keep hull CVLawProof 3217B marked duplicate counted once vs S3255 (draft already does); ensure §3/§2 do not count it twice.

## Verdict
Draft is NOT ready for canonicalization: apply C1-C12, resolve C6 wording with Lead, then update draft V3 and keep non-canonical until Lead FINAL ROWS. No closure; GATE NOT PASSED; binding HOLD; FINAL ROWS suspended.