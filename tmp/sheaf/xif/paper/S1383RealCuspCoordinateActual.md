# S1383: D8 real cusp coordinate — exact first field

Date: 2026-10-30. Lean EXIT=0. No q=1/5/log q use.

## Exact object

The paper cusp is S1330PaperCusp l S = Iut.OrbicurveBoundaryCusp S.cK.
A real epsilon requires

  S1383EpsilonMap l S = S1357EpsilonMap l S
    = S1330PaperCusp l S -> Real,

plus positivity, nonzero, cuspScaleOf, cuspScale positivity, epsilon*cuspScale
nonzero, and compatibility data.  S1357 already provides the conditional
constructor S1330CuspClauseOfRealCuspCoordinate; S1383 does not duplicate it.

## Actual constraints reused

* S1330ActualLogQ_ne_epsilon: actual q (log q < 0) cannot be the positive
  epsilon; q=1/5 is not substituted.
* S1330CuspRep_x_zero: every representative of the actual projective cusp
  point [0:1:0] has x = 0, so the x-coordinate is not a positive epsilon.

## Exact first field

  epsilonOf : S1330PaperCusp l S -> Real

with positivity/nonzero.  No actual epsilonOf is constructed from the actual
cusp object alone; the actual OrbicurveBoundaryCusp carries geometric
data/residue scheme, not a real coordinate.  No arbitrary real or q
substitution is added.

## Consumer

S1330CuspClauseOfRealCuspCoordinate / SourceCuspClause D8.  Exact missing
object: S1330RealCuspCoordinateMissing l S.

No weak Prop/Nonempty gate beyond the existing exact-required definition.
