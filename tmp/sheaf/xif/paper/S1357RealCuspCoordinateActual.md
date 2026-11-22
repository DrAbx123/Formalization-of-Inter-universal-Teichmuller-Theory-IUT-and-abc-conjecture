# S1357: D8 real cusp coordinate from actual cusp / exact first field

Date: 2026-10-30. Lean file EXIT=0. No q=1/5/log q use.

## Actual input

S1330 gives the faithful paper cusp

  S1330PaperCusp l S := Iut.OrbicurveBoundaryCusp S.cK,

the actual Gaussian projective cusp point [0:1:0], actual q=1/5, and proves
log q < 0 cannot be epsilon.  The projective point has x=z=0 and its Y
coordinate is only defined up to scaling, so it gives no canonical positive
real coordinate.

## S1357 result

File: tmp/sheaf/xif/paper/S1357RealCuspCoordinateActual.lean

* S1357PaperCusp := S1330PaperCusp (faithful cusp carrier);
* S1357EpsilonMap l S := S1357PaperCusp l S -> Real (first exact field type);
* s1357RealCuspCoordinateOfMap: actual conditional construction of
  S1330RealCuspCoordinate from
    epsilonOf, positivity, nonzero, cuspScaleOf, positivity of cuspScale,
    epsilon*cuspScale != 0, compatibility Prop + proof;
* s1357ActualQ_ne_epsilon / s1357CuspRep_x_zero reused from S1330;
* s1357RealCuspCoordinateRequired is the existing exact missing object
  Nonempty (S1330RealCuspCoordinate l S), not inhabited.

## Exact first field

A real coordinate on the paper cusp requires

  epsilonOf : S1357PaperCusp l S -> Real

with its positivity/nonzero data; then cuspScaleOf and compatibility.  This
is not the q-parameter: S1330 already proves q cannot be epsilon (q>0 with
log q<0, epsilon>0), and q=1/5 is not inserted.

No actual epsilonOf is constructed; the actual cusp point alone does not
provide one.  No arbitrary real/Classical.choice substitution.

## Consumer

SourceCuspClause / SourceDefinition31Data D8 CuspClause; conditional clause
is S1330CuspClauseOfRealCuspCoordinate.

EXIT=0 (Lean compiles); no weak Prop/Nonempty gate beyond the existing
S1330 exact-required definition.
