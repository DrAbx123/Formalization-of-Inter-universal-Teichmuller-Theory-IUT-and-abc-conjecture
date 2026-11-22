# Root existence gap (the real missing theorem)

## Paper fact

IUT I, around line 3707:

  q_v admits a 2l-th root in O^⊵(T_X^Kv).

The text says this follows from the 2-torsion assumption
(IUT I, Definition 3.1, (b)).

## Source-side fact

`SourceInitialThetaData` / `SourceClauseC` contains

  PuncturedEllipticCurve.Torsion23Rational X

which is `AllNTorsionRational X 6`.

This is only a rationality statement for 6-torsion points.  It is NOT by
itself a construction of a 2l-th root of the Tate parameter q_v.

## Missing implication

The required implication is:

  Torsion23Rational X  ->  exists r in Completion, r^(2l) = q_v.

or equivalently `NatRootSystem (qVUnit T b)` in
`TwoLthRootQVActual`.

`TwoLthRootQVActual` records exactly:

  TwoLRootExistenceGap := Nonempty (NatRootSystem (qVUnit T b))

and states that the tree does not construct it for a general q.

## Consequence

The L = rootNormedExtension tower is a workaround for this gap.  It is not
the paper carrier.  All results on L/rootTensorBlock/root-extension Haars
and root-extension lambda-O hulls are AUXILIARY and must not be used as the
paper Theta side.

The exact paper-level route requires one of:

1. construct `NatRootSystem (qVUnit T b)` from the actual 2-torsion / Tate
   comparison data (the paper's route);
2. or record an explicit source theorem
   `q_v_has_twoLth_root_in_completion` as missing, without fake.

There is no carrier/quotient/normalization shortcut that preserves the paper
object.

## Decisive counterexample (qside audit)

`BadPlaceHalfRootCriterionActual` proves

  padic_five_no_twoL_root : not exists r : Q_5, r^(2l) = 5.

So an arbitrary completion q with order 1 has NO 2l-th root.  The paper root
exists only because the actual q_v is forced to be a 2l-th power by the
2-torsion assumption; the current `qVFamily` / `TateCurveComparison` source
does NOT encode that divisibility/root property.

Therefore the completion root cannot be constructed from the current source.
`HalfRootInCompletion` remains an explicit input, and
`HalfRootCompletionGap := Nonempty (HalfRootInCompletion T b)` is unproved.

## Exact missing source theorem

One of the following must be actually constructed (not assumed):

  qVFamily_twoLPower : exists r : Completion place, r^(2l) = qVFamily q

or

  torsion23_rational -> Nonempty (HalfRootInCompletion T b).

Neither exists in the current tree.  Without it, the Theta values
q_v^(j^2)= (q_v^(1/2l))^(j^2) cannot be built on the completion carrier.

The L = rootNormedExtension construction remains a non-paper workaround.

## STATUS CORRECTION (S342)
completion root is IMPOSSIBLE for actual qVFamily (order coprime l), not a missing Kummer/Hensel input. Correct missing object: O^tri/root-stack carrier (S346 spec).
