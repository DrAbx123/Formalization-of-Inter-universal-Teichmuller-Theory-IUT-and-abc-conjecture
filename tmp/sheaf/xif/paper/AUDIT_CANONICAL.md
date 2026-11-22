# CANONICAL AUDIT (consolidated; supersedes scattered audits)

Purpose: collect the existing audit results, resolve contradictions, and mark
which prior audit items are invalid.  Do not re-audit from scratch.

## 0. Authority order

1. Rendered paper pages / machine underline extraction (`annotated.txt`,
   `SYMBOL_SIGNIFIER_REGISTRY.md`, `Q_SYMBOL_AUDIT.md`).
2. Paper text Cor 3.12 / Def 3.8 / Thm 3.11 / Remark 3.9.5.
3. `CURRENT_PATH_NOTES.md` sections 9-13.
4. `FULL_OBJECT_AUDIT.md`, `TARGET_STRENGTH_LEDGER.md`.
5. `OBJECT_ALIGNMENT_AUDIT.md`, `AUXILIARY_BRANCHES.md`, `PAPER_TEXT_ALIGNMENT.md`.

## 1. Authoritative symbol fact: q[2u] is a 2l-th root

Machine underline extraction (`annotated.txt`, IUT I page 71 / IUT III page 173):

  q[1u]_v  = q-parameter (single underline under q)
  q[2u]_v  = q[1u]_v^(1/2l)  (two underlines under q)

Explicit annotated lines:
  q[2u]_v = q[1u]^{1/2l}
  theta values: q[2u]^{j^2} in Fig. 3.4

Rendered page III page 173, Fig. 3.4 shows `{q^{j^2}}` with DOUBLE underline
under q.  Therefore paper Theta values are

  (q[2u]_v)^(j^2) = q_v^(j^2/(2l)),

NOT q_v^(j^2).

## 2. INVALID prior audit item (must not be used)

`CURRENT_PATH_SIMPLIFICATION_AUDIT.md` section
`PAPER CHECK: 2l is an indeterminacy, not an exponent denominator`
and its S25 conclusion (`direct q_v^(j^2) branch is correct`) are WRONG.
They ignored the double underline in Fig. 3.4.  Any later agent conclusion
based on S25/PAPER CHECK (e.g. `no completion root needed`, `q5 root gap is
not relevant`) is invalid.

The root-extension branch had the correct EXPONENT (q_v^(j^2/(2l))) but the
WRONG CARRIER (L = rootNormedExtension instead of K_v).

## 3. Target (frozen)

IUT III Cor 3.12:

  -|log(Theta)| >= -|log(q)|,

  -|log(Theta)| = procession-normalized mono-analytic log-volume of the
    holomorphic hull of the union of possible images of a Theta-pilot object
    relative to Kummer isomorphisms, subject to (Ind1),(Ind2),(Ind3).

  -|log(q)| = procession-normalized mono-analytic log-volume of the image of
    a q-pilot object, same Kummer isomorphisms, NOT subject to Ind1/2/3.

Theta values are q[2u]^(j^2), j=1,...,l*, with mu_{2l} indeterminacy.
q-pilot log is ord_v(q_v)*log(p_v) (IUT III 7475-7480).

## 4. Confirmed correct objects

- Initial Theta-data / source fields.
- C3 multi-factor tensor packet: actual multi-factor region, compactness,
  IQ, addHaar, log-volume (paper local A is multi-factor; qVFam Unit is not paper).
- Ind1 multi-factor reindex `PrcAutomorphismTensorAction` (actual).
- q_v family `qVFamily` (actual).
- classical q-pilot log = sum weight*ord_v(q_v)*log p_v (actual).
- ThetaLabel = {j // 0<j} (actual positive representatives).
- algebraic-closure root/theta values (correct exponent, WRONG carrier).
- completion root conditional API (`TwoLthRootQVActual`, `HalfRootInCompletion`).

## 5. Confirmed wrong / auxiliary / surrogate (consolidated)

### Invalid
- `q_v^(j^2)` (single-underlined q power) as paper Theta: WRONG.
- `thetaPacket.scale = q_parameter^(j^2)` as paper Theta: WRONG.
- L = rootNormedExtension / RootL / RootBaseLZeta / rootTensorBlock as paper
  Theta carrier: AUXILIARY (correct exponent, wrong carrier).
- `sourceQTensorLambdaOHull = Set.univ` (old arbitrary-o definition): WRONG
  (fixed later to unit-reference image; do not use the old version).
- hull = unitBall with log 0: WRONG.
- closure(image) as lambda-O hull: WRONG.
- Dirac/counting measure as Haar/mu_log: WRONG.
- `qPilot = c_norm*log p` or normalized norm as paper qPilot: WRONG.
- `S317` coefficient-scaled completion Theta image: SURROGATE.
- `UnifiedCarrier = qVFamTensorBlock ⊗_Qp RootBaseLZeta`: double-counts K0;
  WRONG carrier.
- `FinalL = AlgebraicClosure` carrier: not finite/locally compact; AUXILIARY.
- `qVFamTensorV = Unit`: one-factor specialization, not paper A; AUXILIARY.

### Auxiliary normalization (not target)
- transported qPilot Haar / product CLE (S232/S247/S280/S304/S306).
- Haar factor norm^d for arbitrary lambda (S284/S290/S295/S300).
- duplicate normalized logs (S301 vs qside hullLog).
- commonHaarOnL=rootNormedHaar, thetaScalingHaarFactor=rootHaarFactor.

## 6. Real gaps (ordered)

G1. Completion root q[2u]_v = q_v^(1/2l) in K_v.
    Paper: IUT I line 3707 (2-torsion, Def 3.1(b)).
    Source: only Torsion23Rational = AllNTorsionRational 6; no bridge.
    Counterexample: Q_5 has no 2l-th root of 5; so the actual q_v must be
    proved to be a 2l-th power.  `TwoLRootExistenceGap` /
    `HalfRootCompletionGap` / `MissingCompletionRootFromTorsion23` all unproved.

G2. Multi-factor A/C3 carrier and A <-> C3.tensorIndex place agreement.
    Paper A is an n-capsule, generally n>1.  qVFam Unit is not paper A.
    Existing exact gap: `PrimeStripC3PlaceComparisonRequired`.

G3. Ind2/Ind3 actual actions on the multi-factor C3 packet and the union of
    possible images under Ind1/2/3.  Ind1 actual reindex exists.

G4. Literal lambda-O holomorphic hull on the C3/IQ carrier and the
    procession-normalized mu_log with average over j in F_l^×.
    Repo's value-level `sourceHolomorphicHull` is not literal (the repo itself
    records `literalHullInterface_impossible`).

G5. Actual Theta-pilot and q-pilot Frobenioid objects, and their images.
    qVFamily is only the q_v input; QPilotObject structure not inhabited.

G6. Identify q-pilot image log-volume with classical q-pilot log.

G7. Literal Kummer isomorphisms on the IQ/C3 carrier.

G8. Final StepXIContract / IQHullLogVolumeInterface construction.

G9. Source assembly not directly on Cor3.12 critical path but still open:
    cusp epsilon realization, D7 per-place local group, exact-sequence splitting.

## 7. Construction order

1. G1: prove q_v is a 2l-th power in K_v from 2-torsion, or exact missing
   theorem.  Without this, no paper Theta value exists.
2. G2: replace qVFam Unit by C3 multi-factor carrier and prove A/index/place.
3. G3: Ind2/Ind3 and possible-image union on C3.
4. G4: literal lambda-O hull + procession mu_log on C3/IQ.
5. G5: actual pilot Frobenioid objects and images.
6. G6/G7: q-pilot log identification and Kummer isomorphisms.
7. G8: final comparison.

## 8. Audit provenance

- Symbol/underline: `SYMBOL_SIGNIFIER_REGISTRY.md`, `Q_SYMBOL_AUDIT.md`,
  `annotated.txt`.
- Exponent: `CURRENT_PATH_NOTES.md` sec. 9-13; `FULL_OBJECT_AUDIT.md` E4/E5.
- Wrong direct-q branch: `FULL_OBJECT_AUDIT.md` E5; this file supersedes
  `CURRENT_PATH_SIMPLIFICATION_AUDIT.md` S25/PAPER CHECK.
- Target strength: `TARGET_STRENGTH_LEDGER.md`.
- Object alignment: `OBJECT_ALIGNMENT_AUDIT.md`, `PAPER_TEXT_ALIGNMENT.md`.
- Auxiliary branches: `AUXILIARY_BRANCHES.md`.
- Root gap: `ROOT_EXISTENCE_GAP.md`.

## 9. DECISIVE CORRECTION: completion q-root card is impossible

`S342QVFamilyRootImpossibleActual.lean` proves, from the actual qVFamily order and
clause (c) coprimality:

  qVFamilyTwoLRootCard_impossible : not Nonempty (QVFamilyTwoLRootCard)
  natRootSystem_impossible : not Nonempty (NatRootSystem (qVUnit T b))
  twoLthRootData_impossible : no completion TwoLthRootData

Reason: a completion 2l-th root forces (2l) | order(q), contradicting
Coprime(order(q), l).  Kummer/Hensel surjectivity cannot change the order.

Therefore:

- EVERY completion-root theta value/file is INVALID as a paper object:
    PaperCompletionThetaValueActual.lean
    S325CompletionThetaMuOrbitActual.lean
    S330QVFamilyRootCardActual.lean
    S313CompletionThetaSideObjectActual.lean (root part)
    CompletionBlockThetaImageActual.lean (root part)
  These are conditional on an impossible card; do not use them as paper Theta.

- The paper root does NOT live as an element of the completion.  Paper IUT I
  Example 3.2(iv) places q_v^{1/2l} in the orbifold structural sheaf
  O^{tri}(T_x), not in K_v.  The repo explicitly records that the orbifold
  structural sheaf carrier is missing (`qParameterTwoLRootDescent`, pending).

- L = rootNormedExtension is also not the paper carrier (wrong carrier).

## 10. Correct next object

Construct the actual orbifold structural sheaf / root-stack carrier
O^{tri}(T_x) (the paper's O^⊵(T_X^Kv)) and the section q_v^{1/2l} in it,
then define q[2u]^(j^2) and the mu_{2l} action on that carrier, and only then
its log-volume.  This is the real hard object; there is no completion short-cut.

## 11. INVALID completion-root dependencies (S342/S346 reset)

Status: INVALID as paper objects.  S342 proves no completion root/root system
for the actual qVFamily (order coprime l vs (2l)|order).  Any file that assumes
such a root has a false hypothesis and cannot be used as a paper Theta object;
its proofs remain only conditional/formal.

INVALID or INVALID-AS-PAPER:

- TwoLthRootQVActual.lean
  twoLthRoot / TwoLthRootData / TwoLRootExistenceGap; the gap is now
  impossible, not open.  Do not use as completion root API.
- BadPlaceHalfRootSupplyActual.lean
  HalfRootInCompletion / HalfRootCompletionGap; impossible for qVFamily.
- BadPlaceHalfRootCriterionActual.lean
  HalfRootInCompletion_iff_exists and norm consequences; only the impossibility
  direction is valid; the half-root datum itself is INVALID.
- S313CompletionThetaSideObjectActual.lean
  completionThetaRoot/Image/Hull/Haar/CompletionThetaSideObject; all root data
  conditional on impossible NatRootSystem.  INVALID as paper.
- S310CompletionSameCarrierPairActual.lean
  completion root-system pair; INVALID.
- LGPPhiInputActual.lean
  lgpTwoLthRoot / lgpThetaValue / LGPThetaRootSystemGap; conditional on an
  impossible completion NatRootSystem.  INVALID as paper.
- LGPPhiInputFromAlgebraicClosureActual.lean
  lgpTwoLthRootAlgClosed; only an algebraic-closure surrogate, NOT the paper
  O^tri root-stack carrier.  AUXILIARY, not paper.
- PaperCompletionThetaValueActual.lean
- S325CompletionThetaMuOrbitActual.lean
- S330QVFamilyRootCardActual.lean
- S343CompletionThetaC3TensorActual.lean
- CompletionBlockThetaImageActual.lean (root part)
  All INVALID as paper; conditional on the impossible completion root/card.

NOT affected by the completion-root invalidity:

- S327C3IndActionsActual.lean: Ind1/2/3 conditional actual actions; no root.
- S348C3CarrierIdentificationGapActual.lean: exact carrier-identification gap;
  no root.
- S342QVFamilyRootImpossibleActual.lean: valid impossibility theorem.
- S346OrbifoldStructuralSheafActual.lean: valid exact missing spec for the
  correct carrier O^tri(T_x)/root stack; no fake carrier.

Correct paper carrier: O^tri(T_x)/root stack (S346 spec), currently exact
missing (OrbifoldStructuralSheafRootSectionRequired), not Completion/K_v and
not L = rootNormedExtension.  No completion short-cut; no inequality.
