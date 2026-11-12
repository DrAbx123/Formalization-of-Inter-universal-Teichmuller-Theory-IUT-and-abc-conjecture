# OLD-SCHEMA-MIGRATION — completion-root impossibility and L-carrier worklist

Status: READ-ONLY analysis, 2026-11-12. The negative criterion is a paper-level proof
sketch (not yet Lean); the migration list is a worklist. No files outside coord modified.

## 1. concreteQUnit and the unconditional negative criterion

Definition chain:
- ConcreteC3DonorActual.lean:48 concreteQCandidate I place :=
  Classical.choice (finitePlaceQCandidate_nonempty place.val).
- ConcreteC3DonorActual.lean:62 concreteQUnit I place :=
  candidateUnits (K := I.initial.arithmetic.Fmod) place (concreteQCandidate I place).
- SourcePilotRegion.lean:50 candidateUnits place q := Units.mk0 q.q q.q_ne_zero.
- FinitePlaceQCandidate (LocalQParameter.lean:39): q ≠ 0 and
  (Valued.v q : WithZero (Multiplicative Int)) < 1.
- exponent (LocalQParameter.lean:67) := -Multiplicative.toAdd (WithZero.unzero valuation);
  exponent_pos (:71) and order (:81)/order_pos (:84).

Claim: for every finite place and every q candidate,
  ¬ Nonempty (NatRootSystem (candidateUnits place q)).
Proof sketch (paper-level):
1. Let e := q.exponent. From q.valuation_lt_one and q ≠ 0, e > 0.
2. Suppose R : NatRootSystem (candidateUnits place q).
3. For every n ≠ 0, NatRootSystem.pow_self gives R.root n ^ n = candidateUnits place q.
4. Apply the completion valuation Valued.v to both sides. The value group is
   WithZero (Multiplicative Int); write v(R.root n) = ofAdd(-k) with k in Int. Multiplicativity
   gives n * k = e.
5. Choose n = e + 1 (> 0). Then e = (e+1)*k with k integer; the only integer solution has
   k = 0, hence e = 0, contradicting e > 0.
Thus no NatRootSystem exists for any q candidate with positive order. In particular this is
NOT merely "non-square": roots of all n are impossible, so it is stronger than a Legendre/
residue argument. No specific I or place is needed; every actual finite place with a
q candidate (finitePlaceQCandidate_nonempty) satisfies the hypotheses.
Numerical sanity (Sage/p-adic): q = p in Q_p has no square root for odd p by valuation
parity; but the all-n argument above is the formal statement, not a numerical check.

Status of the proof: paper-level, should formalize; the key facts available are
exponent_pos, NatRootSystem.pow_self, Valued.v multiplicativity, and WithZero.unzero.
Remaining formal work: a clean lemma extracting the integer exponent of a completion unit
and the arithmetic e = (e+1)*k contradiction. No missing Mathlib theorem expected.

Consequences:
- CompletionRootBlock (S1391:146) requires roots : NatRootSystem C.qUnit; by
  completionRootBlock_nonempty_iff (S1391:221), it is empty for every actual q.
- Therefore old SourcePilotRegionData is **not merely unconstructed; it is impossible**
  for the concrete q; oldSourcePilotRegionData_nonempty_of_completionRootBlock is vacuous.
- S1408 sourcePilotRegionDonorsOfLBlock requires the old block B; its old route cannot be
  inhabited. The L-carrier route is forced.

## 2. L-carrier replacement already in tree

- S1391 SourcePilotRegionDataL (S1391:244), actualSourcePilotRegionDataL (:329),
  sourcePilotRegionLToCore (:285): green (olean 1237696 B).
- Mzk1QPilotLineLActual.lean (source, no olean) defines the L-carrier chain:
  QPilotLineActualL (C1,C2,C3L), PaperQPilotObjectActualL, QPilotIdentificationActualL,
  qPilotIdentificationActualL_nonempty_of_object (PROVED in source),
  qPilotLineActualL_nonempty_of_fields, and an 8-row ledger marking CompletionRootBlock
  BLOCKED (old) and SourcePilotRegionDataL GREEN.
- OrigXiFPaperQPilotFromSourceLActual.lean builds the actual paper q-pilot object:
  OrigXiFPaperQPilotOfBoundary (b : first-field type) with actual oneColumn/lineBundle/
  logKummer/qPilotLogVolume; green (olean 147176 B). This is the usable L paper object.
- C1/C2 remain source obligations: QPilotLineActualL needs C1 : SourceInputBinding and
  C2 : SourceLogKummerData I C1; C2 is constructible from C1 (C2Actual), C1 has no
  unconditional instance (A933).

## 3. Old-schema consumer inventory

Counts (grep, 2026-11-12):
- files mentioning CompletionRootBlock: 5
  (S1391, S1408, Mzk1QPilotLineLActual, S1408Probe0, S1408Probe0Adapted)
- files mentioning the old type SourcePilotRegionData: 808 occurrences across
  tmp/sheaf/xif/paper and tmp/sheaf/n8/closure. Many are field projections or doc
  references; they split into the following migration classes.

### Class A — old schema core (highest priority)
| file | objects | change |
|---|---|---|
| S1391C3LSourcePilotActual | SourcePilotRegionData, CompletionRootBlock, oldSourcePilotToCore, oldSourcePilotToCompletionRootBlock, oldSourcePilotOfCoreAndBlock, actualCompletionRootBlock_nonempty_iff | keep as legacy + add not_nonempty_CompletionRootBlock (negative theorem); stop using as inhabitant |
| S1408C3LSourcePilotConsumerActual | sourcePilotRegionDonorsOfLBlock, c3DonorConsumerOfLBlock, oldSourcePilotOfLBlock | mark old route blocked; migrate consumer to L record/core; do not require B |
| C3Actual | SourcePilotRegionDonors, sourcePilotRegionDataOfDonors | keep as old donor schema; add L analogue or deprecate |

### Class B — QPilot old C3 chain
Files: QPilotObjectActual (QPilotLineActual.C3 old), QPilotCanonicalConstruction,
QPilotIdentificationActual, QPilotIdentificationConstruction, OneColumnActual,
QPilotLineActualConstruction, Mzk1QPilotLineLActual (already L).
Change: replace C3 : SourcePilotRegionData by C3L : SourcePilotRegionDataL (or a common
core); keep C1/C2; use QPilotLineActualL and qPilotIdentificationActualL_nonempty_of_object.
The old QPilotIdentificationActual cannot be inhabited once CompletionRootBlock is empty.

### Class C — concrete old-donor assemblies
Files: ConcreteC3DonorActual, ConcreteC3DonorAssemblyActual, ConcreteC3RootCompletionActual,
ConcreteC3RootTensorActual, BaseCompletionRootsActual/Adapted, BaseRootKummer*,
BaseRootKummerObjectActual*, S342QVFamilyRootImpossibleActual.
Change: the completion-root construction parts become obsolete; retain S342's negative
theorem as the template; use concreteRootsAlgebraicClosure for L roots. Do not try to
transport completion roots.

### Class D — downstream C3 field consumers (C4-C9 and paper bridges)
~800 file occurrences; classes:
- consumers reading only core fields (p, place, q, thetaPacket, qUnit, tensor block):
  generalize over SourcePilotRegionCore and feed sourcePilotRegionLToCore L.C3L;
- consumers reading roots/roots'/kummerClass/rootChange: retype to the L record or
  algebraic-closure root systems; old completion types are empty;
- doc/quoted references: update names only.
Change type is mostly mechanical (field projection/typeclass parameter), not mathematical.

## 4. Migration worklist (file/theorem/change)

| # | file | key declaration | change | priority |
|---|---|---|---|---|
| 1 | S1391C3LSourcePilotActual | CompletionRootBlock, old data constructors | add negative theorem; mark old route legacy | P0 |
| 2 | S1408C3LSourcePilotConsumerActual | sourcePilotRegionDonorsOfLBlock, oldSourcePilotOfLBlock | migrate to L core without B; old route blocked | P0 |
| 3 | QPilotObjectActual | QPilotLineActual.C3 | C3 -> C3L or common core | P0 |
| 4 | QPilotCanonicalConstruction / QPilotIdentificationConstruction | object/identification constructors | use L line/object | P0 |
| 5 | QPilotIdentificationActual | C3 field/logKummer types | L analogue or restrict to L | P0 |
| 6 | OneColumnActual / QPilotLineActualConstruction | actual line/object over old C3 | L line/object | P0 |
| 7 | Mzk1QPilotLineLActual | QPilotLineActualL etc | compile (no olean yet) and use | P0 |
| 8 | C3Actual | SourcePilotRegionDonors/Data | keep legacy; add L analogue | P1 |
| 9 | ConcreteC3Donor* / Base*Root* | completion root constructions | obsolete; retain negative S342 | P1 |
| 10 | C4-C9 / paper C3 consumers | field projections | core generalization or L retype (bulk ~800 refs) | P1-P2 |

Estimate: core migration is 2 files (S1391/S1408) + 5 QPilot-chain files + 1 L line file;
Class C ~8 files; Class D bulk ~800 references across ~300 files, mostly mechanical.
No migration can make old completion roots exist; the negative theorem forces the L route.

## 5. Verdict

- Negative criterion: **unconditional** for every actual finite place/q candidate, by the
  all-n valuation argument; not merely non-square/Legendre. It is paper-level and should be
  formalized (exponent_pos + pow_self + Valued.v + integer arithmetic); no missing Mathlib
  fact expected.
- Old completion schema: impossible, not just missing. S1408 old route cannot be inhabited.
- L route: SourcePilotRegionDataL actual green; L paper q-pilot object green
  (OrigXiFPaperQPilotOfBoundary); L line/identification source exists (needs compile and
  C1/C2).
- Migration scale: ~2 core + 5 QPilot + 1 L + 8 concrete files; ~800 old-type references
  mostly mechanical.
