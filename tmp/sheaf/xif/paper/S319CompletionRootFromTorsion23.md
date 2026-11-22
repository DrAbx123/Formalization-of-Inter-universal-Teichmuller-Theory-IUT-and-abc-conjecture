# S319: completion 2l-th root from torsion23 data

Date: 2026-10-29. Completion carrier only; no L/transport/normalization.

## Actual source data inspected

* T.clauseC.torsion23_rational : Torsion23Rational T.arithmetic.curve.
  Torsion23Rational is AllNTorsionRational 6: every 6-torsion point over the
  algebraic closure descends to the base field.  It is not a Tate-parameter
  root statement.
* qVFamily T b is the actual SourceTateComparisonWitness parameter in
  Completion((nativeBadLift T).lift b); qVUnit T b is its unit form.
* The Tate comparison witnesses supply the q parameter, not an implication
  q_v = r^(2l).

## Recorded exact missing datum

MissingCompletionRootFromTorsion23 :=
  Torsion23Rational T.arithmetic.curve ->
    Nonempty (NatRootSystem (qVUnit T b)).

No inhabitant is constructed.  Conditional on it, twoLthRootData_of_missing
gives actual TwoLthRootData in the completion.  The source supplies the torsion
statement and qVFamily, but not this root implication.

No fake root/axiom/sorry/True/PUnit; no inequality.
