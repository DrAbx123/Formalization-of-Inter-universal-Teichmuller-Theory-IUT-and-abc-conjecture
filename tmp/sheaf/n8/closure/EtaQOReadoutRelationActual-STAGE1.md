# QO readout relation via Haar normalization

- Task: close QOReadoutRelationTarget using Haar uniqueness under normalization
  at O.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaQOReadoutRelationActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; two named sorries (exact gaps).

## Actual theorem

normalized_haar_agree_on_everywherePos: for two additive Haar measures on the
same locally compact additive group, if both are normalized at an open set O
(mu O = 1, mu' O = 1), then they agree on every everywhere-positive measurable
set.  Proof uses Mathlib
measure_isAddHaarMeasure_eq_smul_of_isOpen (scalar factor = 1) and
measure_isAddHaarMeasure_eq_smul_of_isEverywherePos.

## Exact gaps

- O_K := Integers (K X), O_Q := Integers (QCompletion X).
- NormalizationInputs := muK(O_K)=1 and muQ(O_Q)=1.  No production theorem
  normalizes these arbitrary Haar measures at O; named sorry.
- QOReadoutRelationViaNormalizationTarget := QOReadoutRelationTarget, named
  sorry.  Even with normalization, the canonical GlobalRssAtF measure and the
  multiradial QCompletion measure live on separately elaborated carriers; the
  common-carrier measure transport is the remaining exact input.

No arbitrary measure equality is assumed; the Haar lemma is actual and the
normalization/transport inputs are explicit gaps.