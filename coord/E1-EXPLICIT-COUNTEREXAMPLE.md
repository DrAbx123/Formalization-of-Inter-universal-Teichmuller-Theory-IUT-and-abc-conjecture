# E1-EXPLICIT-COUNTEREXAMPLE — explicit q candidate and bare E1 failure

Status: **GREEN LEAN CANDIDATE + paper-level gap statement**. The Lean file
tmp/sheaf/xif/paper/Mzk1E1ExplicitCounterexampleActual.lean compiles EXIT=0,
olean 22504 B, and the three exported axioms probes depend only on
[propext, Classical.choice, Quot.sound]. This is a parameterized explicit local
counterexample, not a fully constructed SourceDefinition31Data term.

## 1. Explicit q candidate

FinitePlaceQCandidate (LeanFormal/IUT/Foundations/NumberField/LocalQParameter.lean:39):
  q : Completion place; q_ne_zero; valuation_lt_one.

Constructor path:
- finitePlaceQCandidate_nonempty (LocalQParameter:111) chooses an irreducible
  uniformizer of the completed DVR, so its q has q ≠ 0 and v(q) < 1.
- explicitQCandidate place := Classical.choice (finitePlaceQCandidate_nonempty place)
  (Mzk1E1ExplicitCounterexampleActual.lean).
- exponent (LocalQParameter:67) = -Multiplicative.toAdd (WithZero.unzero v);
  exponent_pos (:71) gives 0 < exponent.

Lean theorem (compiled):
  explicitQCandidate_exponent_pos (place) : 0 < (explicitQCandidate place).exponent.
No concrete number field is fixed; the theorem is generic over any actual finite place.
For illustration, q=p in Q_p is a uniformizer, exponent 1; that numerical instance is not
needed for the formal result.

## 2. qSideContribution / localSignedLog relation

- ArithmeticQPilotLogVolume.localSignedLog (parameter) = Real.log ‖parameter.q‖; it is
  negative (localSignedLog_neg, :42).
- localLogMagnitude = -localSignedLog; positive (:46).
- Mzk1E1OrderActual.QSideContribution (signedLogQ) := -signedLogQ.
- Therefore for the explicit q candidate with signedLogQ := localSignedLog q:
    QSideContribution (localSignedLog q) = -localSignedLog q = localLogMagnitude q > 0.
Lean theorem:
  explicitQCandidate_qSide_ne_zero (place) :
    QSideContribution (localSignedLog (explicitQCandidate place)) ≠ 0.
- Mzk1E1OrderActual.E1PaperScaledHullForm qSide := qSide = 0, and
  e1_iff_qside_zero : E1PaperScaledHullForm qSide ↔ qSide = 0.
- Hence (compiled):
  bareE1_false_for_explicit_local_q (place) :
    ¬ E1PaperScaledHullForm
      (QSideContribution (localSignedLog (explicitQCandidate place))).
Thus the bare E1 equality fails for the explicit local q-side value, in the
parameterized form (any actual finite place). No full I / SourceDefinition31Data is needed
for this local statement.

## 3. Relation to actual sourceQPilotSignedLog

Definition (tmp/sheaf/xif/PaperQPilotObject.lean:66-74):
  sourceBadQAbsLog S = sum_b |Real.log (S.reduction.qParameter b)|
  sourceQPilotSignedLog S = -sourceBadQAbsLog S.
By sourceBadQAbsLog_nonneg/pos_of_nonempty:
- sourceQPilotSignedLog S ≤ 0;
- if S.badPlaces is nonempty and some |log q_b| ≠ 0, then sourceQPilotSignedLog S < 0,
  hence QSideContribution (sourceQPilotSignedLog S) ≠ 0 and bare E1 fails for S.

Missing to make this a full actual-D counterexample:
- a concrete SourceDefinition31Data l with nonempty badPlaces and qParameter whose
  log is nonzero (the source contract has arithmetic/selectedPlaces/badPlaces/reduction/
  torsion/orbicurve/sections/cusp plus five compatibility fields; no concrete term is
  constructed in the tree);
- or a concrete OriginalInput.initial source contract with the same data.
The minimal input list is exactly the SourceDefinition31Data fields:
arithmetic : InitialThetaArithmeticData l; selectedPlaces; badPlaces;
reduction : SourceReductionClause selectedPlaces badPlaces (with qParameter);
torsion : SourceTorsionClause l; orbicurve : SourceOrbicurveClause;
sections : SourceSectionClause; cusp : SourceCuspClause;
five arithmetic_*_compatibility props with proofs.
No term of this structure is available in the tree.

## 4. Verdict

- Explicit q candidate: **constructed** (Classical.choice of the DVR existence theorem),
  exponent > 0, generic over any finite place; Lean EXIT=0, olean 22504 B.
- Local q-side contribution is nonzero; bare E1PaperScaledHullForm fails for
  QSideContribution (localSignedLog q) by e1_iff_qside_zero; Lean theorem compiled and
  axiom-gated to the trio.
- Full actual SourceDefinition31Data counterexample: **not constructed**; gap is the
  source contract term. Once a term with a nonzero bad q log is supplied, the same argument
  proves sourceQPilotSignedLog ≠ 0 and bare E1 false for that S.
- The correct E1 interface remains the allocation form E1AllocationForm, not bare
  V_norm = V_hull.

## 5. Artifacts

- Lean: tmp/sheaf/xif/paper/Mzk1E1ExplicitCounterexampleActual.lean
  (olean 22504 B; EXIT=0; axioms [propext, Classical.choice, Quot.sound] on all three
  exported declarations).
- E1 interface file: tmp/sheaf/xif/paper/Mzk1E1OrderActual.lean (E1PaperScaledHullForm,
  QSideContribution, e1_iff_qside_zero, E1AllocationForm).
- Source scalar: tmp/sheaf/xif/PaperQPilotObject.lean:66-74.
