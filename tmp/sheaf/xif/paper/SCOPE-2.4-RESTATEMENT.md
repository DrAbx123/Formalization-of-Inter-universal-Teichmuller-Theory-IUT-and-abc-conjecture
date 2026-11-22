# 2.4 restatement scope split (abc / aibi, after mainline A311 verification)

Status: binding HOLD; gate NOT PASSED; no closure claimed. Registry frozen 14041.

## Verified facts
1. Paper [Mzk1] Lemma 2.4 is ALGEBRAIC-input: S subset P1(Qbar) finite, beta in Qbar minus S, conclusion f in Qbar(x) with S_phi subset P1(Qbar), phi(S) subset S_phi, phi(beta) not in S_phi, phi unramified over P1 minus S_phi, plus the field-of-definition clause.
2. Restated interface currently in Lean uses P1(Q) inputs (P1Point Q, Mzk1Lemma24Target over Finset (P1Point Q)), per Lead A280 vocabulary for stage4 alignment.
3. The nested measure m/d (max/sum of reduced degrees of fields of definition) is trivial on rational points: all reduced degrees are 0. Hence the rational-only statement cannot carry the paper induction and cannot be claimed as paper Lemma 2.4.

## Recommended scope split (mainline option (i), pending Lead decision)
- Layer R (rational-input component): current restated 2.4 target (q in Q[X], q(S) subset specialSet Q, q(beta) not in specialSet Q, CV_C(q) subset {0,1}, C-point unramified away from {0,1}). Named class-B input at this layer: BetaAvoidingBelyiBaseInput (hull attempting proof).
- Layer A (algebraic-input paper layer): S subset P1(Qbar), beta in Qbar minus S, f in Qbar(x), S_phi subset P1(Qbar), field-of-definition clause. Needs: descent (D) via Mzk1Lemma24DescentActual finite-Galois PROVED + AlgebraicClosureFixedFieldPaperInput class-B; 2.3 separation; 2.2 Qbar target (stepxi RestatedLemma22InterfaceActual currently P1(Q)-typed); measure machinery on algebraic points (reducedDegreeOfPoint/mOfPoints/dOfPoints PROVED) + S1a/S1b/S2/S2-i assets.
- Shared CV vocabulary and proofs: RestatedLemma24InterfaceActual (specialSet, criticalValuesOverC, CVCompositionLawStatement PROVED, SpecialSetPreservationStatement PROVED, s3135_CVCompat_proved).

## Honesty constraints
- No file may state or imply that paper Lemma 2.4 is complete under rational-only scope.
- Named dependencies stay named: BetaAvoidingBelyiBaseInput, CorrectedStepProviderPaperInput, CorrectedAssemblyPaperInput, AlgebraicClosureFixedFieldPaperInput.
- Any change of input vocabulary (P1(Q) to P1(Qbar)) must be coordinated with Lead, mainline, stepxi (2.2 single source) and lattice (INDEX/ledger).
