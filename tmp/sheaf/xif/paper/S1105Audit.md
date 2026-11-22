# S1105: audit of S1100/S1101/S1102/S1103

Date: 2026-10-30. Audit report.

## Existence / EXIT

* S1100: absent from tmp/sheaf/xif/paper (and all of tmp).
* S1101RationalBaseActual.lean: exists, local compile EXIT=1.
  Error at line 36: change pattern
    Ideal.absNorm (comap ...).maximalIdeal.asIdeal =
      Rat.HeightOneSpectrum.primesEquiv ...
  is not defeq to the target, which has coercions
  (Ideal.absNorm ... cast) and double-coerced primesEquiv val.
  Fix is cast/normalization in the statement, not a missing axiom.
* S1102PushforwardHullPositivityActual.lean: EXIT=0 (olean built).
* S1103Q1UGlobalWeightedActual.lean: EXIT=0 (olean built); S1086, its
  per-b input dependency, now also compiles EXIT=0.

## Axioms

S1102.s1102Hull_pos_fin_actual:
  [propext, Classical.choice, Quot.sound]
S1103.s1103WeightedGlobal_of_exact:
  [propext, Classical.choice, Quot.sound]
Exactly the allowed trio.

S1101 cannot be axiom-audited (EXIT=1); S1100 absent.

## Object correctness

S1102:
* object is rootStackPaperThetaHull (root-stack theta hull);
* measure is s1080PushforwardHaar;
* proves 0 < mu(hull) and mu(hull) < top;
* exact input S1102MeasurabilityInput = S1095ExactMinimum
  (embedding/region measurability).
This is the correct root-stack hull positivity/finiteness.

S1103:
* qPilot side is qPilotQ1ULogHaar, the canonical q[1u] Haar log;
* theta side is rootStackPaperThetaHullLog;
* proves weightedPaperV(q[1u] log) <= weightedPaperV(root hull log)
  from S1103PerBInequality = forall b, qPilotQ1ULogHaar b <=
  rootStackPaperThetaHullLog b.
This is the correct q[1u]/root-stack weighted-global reduction, and it does
NOT use s994VR as q.

S1101:
* target S1097RationalBase from S1101AbsNormNatGenerator
  (absNorm = primesEquiv.val for HeightOneSpectrum Z); mathematically the
  correct rational residue-base input, but not compiled due coercion mismatch.

## Remaining exact

* S1100 missing file.
* S1101 cast/coercion fix in change/statement.
* S1102 exact input S1095ExactMinimum.
* S1103 exact input S1103PerBInequality.
* S1086 exact measure/geometric inputs (q[1u] containment, embedding
  injective/measurable, region measurable, Haar equality, positivity and
  finiteness); S1086 compiles but its main theorem is conditional.

## Fake scan

grep sorry | axiom | True | PUnit | unsafe | admit:
S1101 0, S1102 0, S1103 0.

No fake; no paper claim beyond the conditional objects above.
