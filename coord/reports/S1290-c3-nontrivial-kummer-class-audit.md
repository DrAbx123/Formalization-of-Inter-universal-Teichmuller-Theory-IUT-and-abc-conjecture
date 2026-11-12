# S1290: C3 nontrivial Kummer class — actual construction or exact gap

Date: 2026-10-30. Report only; roots/rootChange not modified.

## 1. What a Kummer class needs

`KummerClass.kummerClass` (KummerClass.lean:62):

```lean
def kummerClass
    (ρ : G →* (Mˣ ≃* Mˣ))
    (r : NatRootSystem value)
    (fixed : ∀ σ : G, ρ σ value = value)
    (σ : G) : CyclotomicTower M where
  component n := ρ σ (r.root n) / r.root n
  ...
```

So a nontrivial class requires:

1. an actual unit `value` and `NatRootSystem value`;
2. an actual group `G` and action `ρ` on `Mˣ`;
3. `fixed` for `value`;
4. a `σ : G` and `n` with `ρ σ (r.root n) ≠ r.root n`.

`CyclotomicTower.one` (KummerClass.lean:27) is the trivial unit tower; it is
type-inhabited but is exactly the class that must not be used as the C3 donor.

## 2. Concrete C3 data

`ConcreteC3DonorActual` supplies (at type level):

- `qUnit : (CommonPrimeCompletion place)ˣ`;
- `ConcreteKummerClassCarrier := CyclotomicTower (CommonPrimeCompletion place)`.

It does **not** supply:

- `NatRootSystem qUnit` in the completion;
- a Galois group/action `ρ` on completion units;
- a fixed-unit proof or a nontrivial `σ`.

`ConcreteC3RootTensorActual` / `ConcreteC3RootCompletionActual` construct
actual roots and `rootChange` over the algebraic closure L, not over the
completion:

```lean
concreteRootsAlgebraicClosure :
  NatRootSystem concreteQUnitAlgebraicClosure
rootChange := KummerClass.rootSystemDiff roots roots' : CyclotomicTower L
```

These are actual algebraic-closure objects, but they still do not give a
`kummerClass`: there is no actual `G`, `ρ`, `fixed`, or nontrivial `σ` on L
in the tree.

## 3. Can a nontrivial class be built from these?

Not currently.

From algebraic-closure roots one could in principle form

```lean
KummerClass.kummerClass ρ concreteRootsAlgebraicClosure fixed σ
```

but `ρ`/`fixed`/`σ` are exactly missing.  The generic construction is sound;
the obstruction is the actual Galois action and a nontrivial element.

Without a root system in the completion, the alternative

```lean
KummerClass.kummerClass ρ r fixed σ : CyclotomicTower (CommonPrimeCompletion place)
```

is impossible: `r : NatRootSystem qUnit` does not exist.

## 4. First exact fields (in order)

1. `NatRootSystem (concreteQUnit I place)` in the completion, or an actual
   transport of the algebraic-closure roots to the completion;
2. `G : Type` with `Group G` and an actual
   `ρ : G →* ((CommonPrimeCompletion place)ˣ ≃* (CommonPrimeCompletion place)ˣ)`
   (or the L-units analogue);
3. `fixed : ∀ σ, ρ σ (image of qUnit) = image of qUnit`;
4. an actual `σ : G` and `n : Nat` with
   `ρ σ (r.root n) ≠ r.root n`;
5. then `(KummerClass.kummerClass ρ r fixed σ).component n ≠ 1`, which is
   the nontriviality witness.

No current source field supplies (1), (2), or (4).

## 5. Notes on fakes

- `CyclotomicTower.one` is actual but trivial; it cannot be the C3 Kummer
  class or rootChange donor.
- `CyclotomicTower.mul` of `one` with `one` is still `one`.
- A tower with `component n = 1` for all n is exactly `one` by
  `CyclotomicTower.ext`; nontriviality requires some component ≠1, hence
  a nontrivial root action.

## 6. Conclusion

- No actual nontrivial concrete C3 `kummerClass` in the tree.
- Exact first fields: completion root system, actual Galois action `ρ`,
  fixed q-unit, and a nontrivial `σ`/root witness.
- The actual algebraic-closure roots/rootChange are necessary but not
  sufficient; they do not supply the action.
- No roots/rootChange modified; report only, EXIT=0.
