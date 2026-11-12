# V157 ROW DRAFT (NON-CANONICAL; compacted per Lead A409 to STABLE true-theorem rows only)

**Status:** prepared material only; NO gate edit until W1 pin + Lead approval. Canonical gate unchanged: V150@16111/84837B0B (+v151–v156). GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041 / record 18800; no registry edits; no un-HOLD; no queue binding.

**A409 scope:** keep only stable true-theorem rows: (1) Problem A fold PROVED; (2) Problem A finite-β corrected base PROVED (fold + unconditional consumer slot; W1 pin pending); (3) ∞-β spec repair (original input REFUTED; corrected finite-β statement). REMOVED from this draft: all Problem E wiring/consumer adapter rows (parked until base is stable; not part of v157).

## 1. VERIFIED PINS (lattice/mainline checks)

| item | pin | status |
|---|---|---|
| Problem A fold | Mzk1BetaAvoidingFoldActual EXIT0 SIZE 27144B; src sha E07D70385B47E4F9EB408FF312FC40FC9DF96DE169B239D2D6702A81A6D9011E; CITABLE 23 decls probe_ok; betaAvoiding_all : ∀ S β:ℚ, β∉S → BetaAvoidingAt S β; axioms trio | **STABLE / PROVED** |
| finite-β unconditional consumer slot | Mzk1Consumer24AdapterUnconditionalActual CITABLE 12 decls 10264B sha 60DC8BC2 probe_ok (probe _Mzk1Unconditional24AdapterProbe 1206): unconditional h24Base; class-B premise removed; infinity-β original refuted/not used | **STABLE / CITABLE** |
| W1 corrected finite-β base | Mzk1BetaAvoidingBaseActual 10430B sha 691DFC7F42FD3725 (+ Mzk1BetaAvoidingBaseBridgeActual 4059B sha 1A83D2EBE1835F68) | **PENDING fresh EXIT0/checker -> pin TBD** |

## 2. STABLE ROW DRAFTS (apply in ONE in-place revision after W1 pin + Lead approval; no republish)

### (1) Problem A fold PROVED row
```
("Problem A fold PROVED (v157)", "Mzk1BetaAvoidingFoldActual EXIT0 SIZE 27144B src sha E07D70385B47E4F9EB408FF312FC40FC9DF96DE169B239D2D6702A81A6D9011E; CITABLE 23 decls probe_ok; betaAvoiding_all : forall S beta : Q, beta notin S -> BetaAvoidingAt S beta (axioms trio): rational beta-avoiding Belyi for ALL finite S via fold induction; supersedes small-case-only status", "full-Qbar reduction remains named; no paper closure", "GREEN (Problem A fold PROVED)")
```
### (2) Problem A finite-β corrected base PROVED row
```
("Problem A finite-beta corrected base PROVED (v157)", "BetaAvoidingBelyiBaseInput corrected finite-beta version PROVED from fold betaAvoiding_all (Mzk1BetaAvoidingFoldActual; all finite S); wired UNCONDITIONALLY into consumer via Mzk1Consumer24AdapterUnconditionalActual CITABLE 12 decls 10264B sha 60DC8BC2 probe_ok (probe _Mzk1Unconditional24AdapterProbe 1206): unconditional h24Base, class-B premise removed; infinity-beta original input REFUTED/not used", "W1 Mzk1BetaAvoidingBaseActual 10430B sha 691DFC7F pending pin; full-Qbar named; no paper closure", "GREEN (finite-beta corrected base; W1 pin pending)")
```
### (3) ∞-β spec repair + NAMED INPUT 1 text
```
Events: original BetaAvoidingBelyiBaseInput statement FALSE as written (beta quantifier includes infinity; q(infinity)=infinity in specialSet unavoidably) => original input REFUTED; corrected statement quantifies finite beta only.

("NAMED INPUT 1", "BetaAvoidingBelyiBaseInput: beta-avoiding rational Belyi PROVED for all finite S via fold (Mzk1BetaAvoidingFoldActual betaAvoiding_all; 27144B E07D7038; CITABLE 23); ORIGINAL infinite-beta input REFUTED (beta quantifier includes infinity; q(infinity)=infinity in specialSet); corrected finite-beta input PROVED (W1 Mzk1BetaAvoidingBaseActual PIN TBD)", "proved:=false retained until W1 pin; corrected finite-beta status", "NAMED (original refuted; corrected W1 pending pin)")
```
### (4) L4 row addition
```
L4 evidence append: "; general BetaAvoidingStep superseded by fold (no longer needed): betaAvoiding_all over finitely many rational points via fold induction"
```

## 3. NOTES INDEX for mainline (old-doc alignment; no gate effect)

- IUT_SUBTARGETS.md:242-243 route goals (2) one-family Cor 3.12 and (3) negative/independence check; :268 M0-M5 route; :311-333 Cor 3.12 not proved per paper; interfaces are not proofs.
- THEOREM311_DEPENDENCY_AUDIT.md:283,796 IUT IV estimates / ABC bridge downstream pending; :446-472 Cor 3.12 Step (xi) + IUT IV (IUTIV/Estimates/Section1.lean:5-9, Section2.lean:5-9 pending; type-correctness != proved); :562 lana-project iut4-sec1 only downstream numeric kernel; :770-771 upstream construction still needed (IPL/SHE/APT, holomorphic hull, determinant normalization, q/Theta membership).
- THEOREM311_TO_312_100_TASKS.md:43 task 9 dependency graph; :132,149 F 85-100 assembly incl determinant/normalization/log-volume/membership.
- THEOREM311_A2_SOURCE_COMPLETION_CHECKLIST.md:444-455 + THEOREM311_A2_INITIAL_THETA_QUANTIFIERS.md:518-525 append-only geometric core/place binding: SourceSignQuotientGeometricCore source-supplied; does not construct geometric core/bad reduction/cusp origin.
- Mapping: old entries concern Problem E (deep inputs) and Problem D (geometric core) upstream boundaries; no contradiction with v157 stable rows; Problem A fold PROVED is new green; no paper closure.

## 4. EXECUTION PLAN (after W1 pin + Lead approval; ONE in-place edit; no republish)

1. Add fold PROVED row; add finite-beta corrected base PROVED row; update NAMED INPUT 1 (only after W1 pin); append L4 fold note.
2. No Problem E wiring rows in v157 (parked per A409); coverage/HOLD/other named inputs/L8 FROZEN/GATE NOT PASSED unchanged.
3. Recompile V150; fresh checker WITH probe; report new canonical pin to Lead/mainline.
4. No un-HOLD; no queue binding; no registry edits; no closure claims.

Prepared by lattice (Lead A409 compaction); no gate edit yet.

