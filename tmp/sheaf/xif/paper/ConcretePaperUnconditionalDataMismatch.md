# Concrete PaperUnconditionalData: hq/hcomp vs final normalized theorem

Scope: object-level audit. No Lean witness is fabricated.

## 1. The concrete constructor and its two inputs

`ConcretePaperUnconditionalDataUnconditionalActual.concretePaperUnconditionalDataUnconditional`
has type (schematically):

    (hq : ConcreteSourceQIdentification (I := I) (actualSignedC3 D))
    (hcomp : concreteSourceComparison
      (concreteQPilotObject I)
      (unconditionalHull I D nu))
    → PaperUnconditionalData ...

The two inputs are:

* `hq : ConcreteSourceQIdentification I C3`
  where `ConcreteSourceQIdentification I C3 :=`
  `sourceQPilotSignedLog I.initial = localSignedLog C3.q`;
* `hcomp : concreteSourceComparison O P`
  where `concreteSourceComparison O P :=`
  `P.procession.average ≤ -O.qPilotLogVolume`.

Both are propositions, not theorems. The constructor only packages them; it
does not prove them.

## 2. The final normalized theorem

`PaperXiFFinalActual.paperLevelXiF_actual` proves

    ActualPaperXiFTarget T

where the target is

    ∑ b, nativeBadLocalWeight b *
      (qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b))
      ≥ threshold side

and the Theta side is the normalized log of the actual root theta closure
hull with coefficient `qVFamNormalizedCoefficient T b / (2l)`. The exact
normalized target is proved through `PaperLevelXiFTargetBridgeActual`.

## 3. Why `hq` is not derivable

`hq` compares:

* `sourceQPilotSignedLog I.initial`, coming from the concrete q-pilot object
  scalar;
* `localSignedLog C3.q`, the local C3 completion log.

The final theorem has no `C3` object and no `localSignedLog C3.q`. Its q
scalar is the weighted normalized qVFamily coefficient
`qVFamNormalizedCoefficient`; the only bridge in the tree is
`QVFamNormalizedCoefficientBridgeActual`, which relates normalized c_norm to
`localLogMagnitude (qVFamily)` only through the exact norm-ratio gap, and that
is about qVFamily, not C3.q. There is no equality between
`sourceQPilotSignedLog I.initial` and `localSignedLog C3.q`, nor between either
and the final normalized q scalar.

Exact mismatch:

    ConcreteSourceQIdentification I C3
      := sourceQPilotSignedLog I.initial = localSignedLog C3.q
    final q scalar
      := - ∑ weight * c_norm * log p

These are three different scalar normalizations/objects. No implication from
the final theorem to `hq` exists.

## 4. Why `hcomp` is not derivable

`hcomp` compares the concrete signed hull's `procession.average` with
-concrete q scalar:

    P.procession.average ≤ -O.qPilotLogVolume
    where P = unconditionalHull (PaperSignedHull)
          O = concreteQPilotObject.

The final theorem has no `PaperSignedHull`; its Theta scalar is
`arithmeticTupleNormalizedLogVolume` on the tensor root closure hull, not
`P.procession.average`, and its q scalar is the normalized weighted qVFamily
coefficient, not `O.qPilotLogVolume`. The final target's inequality is between
those two normalized scalars, not between P.average and O.qPilotLogVolume.

There is no theorem identifying:

* `P.procession.average` with the root tensor normalized hull log;
* `O.qPilotLogVolume` with the normalized qVFamily weighted sum.

Exact mismatch:

    hcomp object: PaperSignedHull P + PaperQPilotObject O
    final theorem object: qVFamTensorBlock/rootThetaHull + qVFamily c_norm

## 5. Can a `PaperUnconditionalData` instance be constructed?

Only **conditionally**, by supplying `hq` and `hcomp` as exact inputs to
`concretePaperUnconditionalDataUnconditional`. The final theorem does not
provide either input. It also does not identify its normalized scalars with
the concrete O/P scalars, so it cannot close the paper-level target
`PaperXiFActualTarget` through `PaperUnconditionalData`.

A genuine construction would need the following actual bridge fields:

1. `O.qPilotLogVolume =` the final weighted normalized qVFamily scalar
   (or a chain to `localSignedLog C3.q`);
2. `P.procession.average =` the final root tensor normalized hull log
   (or the signed relation needed by `concreteSourceComparison`);
3. the concrete `ConcreteSourceQIdentification I C3`;
4. the concrete `concreteSourceComparison O P`.

None is present in the final normalized theorem.

## 6. Verdict

`concretePaperUnconditionalDataUnconditional` can only be instantiated
conditionally on `hq` and `hcomp`, which are exact input propositions. The
final actual qVFamily/root-hull theorem proves a different normalized scalar
inequality and does not imply either `hq` or `hcomp`. Therefore no
`PaperUnconditionalData` instance can be constructed from the final theorem
alone, and the paper-level target cannot be connected through this route
without the four bridge fields above. This is an exact object mismatch, not a
missing proof of a shared proposition.
