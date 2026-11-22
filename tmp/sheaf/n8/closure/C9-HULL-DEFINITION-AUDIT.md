# C9 hull/finite-phase audit (2026-10-23)

## Current C9 reduction

`C9Proof` reduces `QSigned <= ThetaSigned` to finite phase:
no positive log-degree point in `sourceHolomorphicHull`.

## Refutation of the hScaling premise under degree faithfulness

The finite-phase route uses `sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators`,
which requires:

- image points nonpositive (available from q<1 via `sourceImageLogDegree_nonpos_of_q_le_one`);
- scaling units nonpositive (`sourceScalingUnits_nonpos_obligation`).

But production proves:

`not_sourceScalingUnits_logDegree_nonpos_of_degreeFaithful`
: under pointwise degree faithfulness, the constant scaling of exponent 1 lies in
`sourceScalingUnits` and has positive log-degree = card(SourceVolumeIndex). Hence the
scaling-nonpositive premise is FALSE in the degree-faithful regime.

Therefore the current source value-monoid hull/scaling definition cannot deliver the
finite phase from degree-level data. The paper needs the ambient O-module/`1,circ U`
compactness input (a source construction), not a degree bound on these scalings.

## Target consequence

- C9 is NOT closed by the current finite-phase reduction.
- The current `sourceScalingUnits` definition is too broad for the paper hull.
- Either define the actual λO-hull/compactness region from source data, or keep the C9
  comparison as a named target gap; do not assert hScaling.

No N8 closure claimed.