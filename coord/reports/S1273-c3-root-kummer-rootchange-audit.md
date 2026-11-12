# S1273: C3 donor root / kummer class / rootChange audit

Date: 2026-10-30. Report only; no ind1/2/3, tensorUnit, HDD lattice touched.

## 1. Actual source-level status

`ConcreteC3DonorActual.lean` currently does **not** compile:

```text
lake env lean ... ConcreteC3DonorActual.lean
EXIT=1
```

Errors:

- :71 `ConcreteRootSystemCarrier := NatRootSystem (concreteQUnit I place)` —
  `NatRootSystem` expects `Units.{0}` but `concreteQUnit` has `Units.{ua}`;
- :76/:85/:94 `ConcreteRootSystemCarrier` / `ConcreteKummerClassCarrier` /
  `ConcreteRootChangeCarrier` are not functions of `I`;
- :81/:90 `CyclotomicTower (CommonPrimeCompletion ...)` —
  `CommonPrimeCompletion` expects the base field in universe 0, but
  `I.initial.arithmetic.Fmod : Type ua`;
- :110 `ConcreteC3ActualFields I` has no `place` parameter;
- :121/:125/:129/:134 use `sorry` (warnings).

So none of the concrete root/Kummer/rootChange declarations is currently
kernel-closed; no actual construction can be cited from this file as-is.

## 2. First exact gap: universe of CommonPrimeCompletion/NatRootSystem

`CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place` requires
`K : Type` (universe 0), while `OriginalInput.{ua, 0, ...}` allows
`Fmod : Type ua`.  Likewise `NatRootSystem` is fixed to `Units.{0}` while
`concreteQUnit : Units.{ua}`.

The exact first required change is one of:

```lean
-- restrict to ua = 0, or
ULift (CommonPrimeCompletion (K := ...) place)
```

and the carrier definitions must take `I`/`place` explicitly:

```lean
def ConcreteRootSystemCarrier (I) (place) : Type :=
  NatRootSystem (concreteQUnit I place)
```

This is a type/universe gap, not a missing mathematical object.

## 3. After the universe fix: which fields are actually constructible?

### roots / roots'

Exact object:

```lean
ConcreteRootSystemCarrier = NatRootSystem (concreteQUnit I place)
```

The completion `CommonPrimeCompletion place` is not algebraically closed,
and the tree has no `NatRootSystem` in completion units.  The exact
obstruction remains:

```lean
ConcreteRootSystemObstruction := Nonempty (ConcreteRootSystemCarrier I place)
```

Actual alternative: in the algebraic closure L there is

```lean
concreteRootsAlgebraicClosure : NatRootSystem concreteQUnitAlgebraicClosure
concreteRootsPrimeAlgebraicClosure : NatRootSystem ...
```

but these are over `ConcreteQAlgebraicClosure`, not over the completion.
There is no transport of a completion `NatRootSystem` to/from L in the tree.

### kummerClass

Exact carrier:

```lean
ConcreteKummerClassCarrier = CyclotomicTower (CommonPrimeCompletion place)
```

`CyclotomicTower` has a trivial actual inhabitant `CyclotomicTower.one`
(KummerClass.lean:27), so the **type** is inhabited.  But `one` is the
trivial unit tower, not the source arithmetic Kummer class.  A nontrivial
actual class requires an actual Galois action and root system:

```lean
KummerClass.kummerClass (ρ : G →* (Mˣ ≃* Mˣ))
  (r : NatRootSystem value) (fixed : ...) (σ : G) : CyclotomicTower M
```

Neither `G/ρ/fixed` nor a completion root system is supplied by the concrete
C3 input.  Exact first nontrivial field: `NatRootSystem (concreteQUnit)` plus
an actual action/`fixed` datum.

### rootChange

Exact carrier: same `CyclotomicTower` over the completion.

Actual formula:

```lean
KummerClass.rootSystemDiff roots roots' : CyclotomicTower M
```

As in the algebraic-closure assembly:

```lean
rootChangeAlgClosure := KummerClass.rootSystemDiff
  concreteRootsAlgebraicClosure concreteRootsPrimeAlgebraicClosure
```

This actual algebraic-closure `rootChange` exists (type
`CyclotomicTower (ConcreteQAlgebraicClosure)`), but there is no completion
`rootChange`: the input `roots/roots'` in the completion are exactly missing.
The trivial `CyclotomicTower.one` is not the root difference and must not be
used as the donor value.

## 4. Actual constructible fields

Assuming only the universe/argument fixes above:

- `qUnit` actual (completion q unit);
- `qUnitAlgebraicClosure` actual;
- algebraic-closure `roots`, `roots'` actual;
- algebraic-closure `rootChange := rootSystemDiff roots roots'` actual;
- power laws for both algebraic-closure root systems actual;
- `rootChange.component n = roots'.root n / roots.root n` actual.

These are exactly the fields of `ConcreteC3RootCompletionActual` (once the
underlying `ConcreteC3DonorActual` universe errors and `sorry`s are fixed).

## 5. Exact missing fields for the completion donor

1. `NatRootSystem (concreteQUnit)` in the completion;
2. actual Galois group/action and fixed q-unit for `KummerClass.kummerClass`;
3. `CyclotomicTower` over the completion equal to the root-system difference
   of (1);
4. all three carrier definitions must be universe-compatible
   (`ua = 0` or `ULift`), and parameterized by `I`/`place`.

## 6. Conclusion

- No currently compiling actual `ConcreteRootSystem` / `ConcreteKummerClass` /
  `rootChange` over the completion.
- First exact gap is the universe mismatch (`CommonPrimeCompletion` at
  universe 0, `NatRootSystem` over `Units.{0}`) plus missing explicit
  `I`/`place` parameters; the file additionally contains `sorry`s.
- Semantically, completion roots and a nontrivial Kummer class remain exact;
  the actual algebraic-closure roots/rootChange exist but are over L, not the
  completion.
- `CyclotomicTower.one` is a trivial type inhabitation, not the source class;
  using it as rootChange/Kummer class would be fake.
- No ind1/2/3, tensorUnit, HDD lattice touched; report only, EXIT=0.
