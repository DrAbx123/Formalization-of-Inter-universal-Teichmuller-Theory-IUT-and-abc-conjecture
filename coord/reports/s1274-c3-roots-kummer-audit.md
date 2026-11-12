# S1274: C3 roots / kummerClass actuality

Date: 2026-10-30.  Read: `ConcreteC3DonorActual.lean`,
`ConcreteC3DonorCompletionActual.lean`, `ConcreteC3RootTensorActual.lean`,
`ConcreteC3RootCompletionActual.lean`, `BaseCompletionRootsActual.lean`.
No tensorUnit/HDD/Ind work.

## Verdict

The concrete q_v/root donors do **not** construct the C3 `roots`, `roots'`,
`kummerClass`, `rootChange` fields of `SourcePilotRegionData`.  The actual
roots available are in the **algebraic closure** of the completion, while the
C3 fields live in the completion itself.

## Actual donor

`ConcreteC3RootTensorActual` constructs:

```text
concreteC3QUnit : (CommonPrimeCompletion K place)^x
concreteQUnitAlgebraicClosure :
  (AlgebraicClosure (CommonPrimeCompletion K place))^x
concreteRootsAlgebraicClosure :
  NatRootSystem (concreteQUnitAlgebraicClosure)
concreteRootsPrimeAlgebraicClosure :
  NatRootSystem (concreteQUnitAlgebraicClosure)
```

`ConcreteC3RootCompletionActual` packages the actual algebraic-closure roots and
root-change:

```text
concreteC3RootCompletionActual : ConcreteC3RootCompletionActual
  roots := concreteRootsAlgebraicClosure
  roots' := concreteRootsPrimeAlgebraicClosure
  rootChange := KummerClass.rootSystemDiff roots roots'
  rootChange_eq := rfl
```

with actual power laws and root-change component formula.  This is genuine
actual data, but its carrier is `ConcreteQAlgebraicClosure`, not the completion.

## Exact obstruction

`ConcreteC3RootTensorActual` records:

```text
ConcreteCompletionRootObstruction := Nonempty (NatRootSystem (concreteC3QUnit))
```

`ConcreteC3DonorActual` records:

```text
ConcreteRootSystemObstruction
ConcreteKummerClassObstruction
ConcreteRootChangeObstruction
```

`ConcreteC3DonorCompletionActual` records the tensor-landing obstruction
separately (not touched here).  C3 needs:

```text
roots : NatRootSystem qUnit
roots' : NatRootSystem qUnit
kummerClass : CyclotomicTower (CommonPrimeCompletion place)
rootChange : CyclotomicTower (CommonPrimeCompletion place)
rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
```

for `qUnit : (CommonPrimeCompletion place)^x` in the **completion**.  The donor
supplies roots in `AlgebraicClosure (CommonPrimeCompletion place)`, which is a
different unit type; no map

```text
NatRootSystem (unitToAlgClosed qUnit) -> NatRootSystem qUnit
```

exists, and the completion is not algebraically closed.  Similarly the actual
`rootChange` is a `CyclotomicTower` of the algebraic closure, not the completion.

## First exact field

```text
completionRoots : NatRootSystem (concreteC3QUnit place)
```

equivalently `ConcreteCompletionRootObstruction`; then `roots'`, then
`kummerClass`/`rootChange` in the completion and `rootChange_eq`.

## Compilation status of the donor chain

The donor chain is not locally compiled: `ConcreteC3DonorActual` has elaboration
errors (universe mismatch at `NatRootSystem (concreteQUnit ...)` and
`CyclotomicTower (CommonPrimeCompletion ...)`), so
`ConcreteC3RootTensorActual` and `ConcreteC3RootCompletionActual` have no oleans
in this tree.  I did not modify those files (tensorUnit/HDD/Ind belong to other
subagents).

## Consequence

```text
actual algebraic-closure roots/rootChange     yes (source constructs them)
C3 completion roots/roots'/kummerClass       no
transport alg-closure roots -> completion     absent
first exact field                              completionRoots
weak wrapper / fabricated root                none
```

No Lean was added; this is an exact-gap report until the completion root datum
is constructed.
