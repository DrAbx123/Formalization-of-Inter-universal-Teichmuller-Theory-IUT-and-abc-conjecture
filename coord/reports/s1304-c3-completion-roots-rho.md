# S1304: C3 completion roots + actual Galois action rho

Date: 2026-10-30.  Read: S1283 report, `ConcreteC3DonorActual`,
`ConcreteC3RootTensorActual`, `ConcreteC3RootCompletionActual`,
`NatRootSystem.lean`, `AlgebraicClosureRootSystem`.

## Verdict

S1283 only made the two files compile; it did not construct completion roots.
The actual roots in `ConcreteC3RootCompletionActual` live in
`AlgebraicClosure (CommonPrimeCompletion place)` and **cannot be used as**
`NatRootSystem (concreteC3QUnit place)` in the completion.  No actual Galois
action `rho` on a C3 root system is present in the tree.

## 1. What is actual

`ConcreteC3RootTensorActual` constructs:

```text
concreteC3QUnit : (CommonPrimeCompletion place)^x
concreteQUnitAlgebraicClosure :
  (AlgebraicClosure (CommonPrimeCompletion place))^x
concreteRootsAlgebraicClosure :
  NatRootSystem (concreteQUnitAlgebraicClosure)
concreteRootsPrimeAlgebraicClosure :
  NatRootSystem (concreteQUnitAlgebraicClosure)
```

`ConcreteC3RootCompletionActual` packages these with `rootChange_eq` and power
laws.  This is genuine actual data on the algebraic-closure carrier.

## 2. What is missing for the original C3 object

The C3 donor needs completion-unit roots:

```text
roots : NatRootSystem (concreteC3QUnit place)
roots' : NatRootSystem (concreteC3QUnit place)
```

where `concreteC3QUnit : (CommonPrimeCompletion place)^x` is the q unit in the
**completion**, not in its algebraic closure.  The exact obstruction is:

```text
ConcreteCompletionRootObstruction := Nonempty (NatRootSystem (concreteC3QUnit place))
```

The completion is not algebraically closed; no compatible family of n-th roots
in completion units is constructed.  There is no map

```text
NatRootSystem (unitToAlgClosed qUnit) -> NatRootSystem qUnit
```

so the algebraic-closure roots cannot be silently re-used.

## 3. Galois action rho

No declaration in the tree constructs an actual Galois action on a C3
`NatRootSystem` (neither completion nor algebraic-closure root system).  The
available `AlgEquiv`/`AbsoluteGaloisProfinite`/`galoisActionOnPoint` objects
act on fields/points/torsion; they are not an action on the `NatRootSystem`
root family.  In particular there is no:

```text
rho : Gal(L/K) →* MulAut (NatRootSystem ...)
```

or `rho` satisfying `root (σ n) = σ (root n)` and the compatibility laws.

If one chooses the algebraic-closure route, the first exact object is an actual
`rho` on `NatRootSystem (concreteQUnitAlgebraicClosure)`; this is a different
object from a completion root system and does not close C3.

## 4. First exact field

```text
completionRoots : NatRootSystem (concreteC3QUnit place)
```

then:

```text
completionRoots' : NatRootSystem (concreteC3QUnit place)
completionKummerClass / rootChange : CyclotomicTower (CommonPrimeCompletion place)
rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
actualRho : Galois action on the root system, with action laws
```

`actualRho` is not meaningful for the C3 object until the root carrier is the
original one (completion or explicitly specified algebraic closure); it cannot
be fabricated on algebraic-closure roots and then called the completion action.

## 5. Status

```text
ConcreteC3RootTensorActual          EXIT=0 (S1283)
ConcreteC3RootCompletionActual      EXIT=0 (S1283)
algebraic-closure roots             actual
completion roots                    absent
actual Galois action rho            absent
L roots used as completion roots    no
first exact field                   completionRoots
```

## 6. Recommendation

Stop at `completionRoots`; do not add another wrapper around the
algebraic-closure roots.  If the paper permits an algebraic-closure root carrier
with Galois action, state that object explicitly and construct `rho` on it; the
completion-root C3 field still remains a separate exact field.
