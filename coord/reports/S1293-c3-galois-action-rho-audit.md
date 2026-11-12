# S1293: C3 actual Galois action ρ for KummerClass

Date: 2026-10-30. Report only; roots/rootChange/kummerClass not modified.

## Requirement

`KummerClass.kummerClass` needs:

```lean
G : Type, [Group G]
ρ : G →* ((CommonPrimeCompletion place)ˣ ≃* (CommonPrimeCompletion place)ˣ)
fixed : ∀ σ, ρ σ qUnit = qUnit
σ : G
```

The requested target is an actual `G` and `ρ` on the **completion** units.

## What actually exists

`TateDeckAction.lean` constructs, for

```lean
sigma : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
          AlgebraicClosure (Completion place)
```

the actual unit equivalence

```lean
unitsAlgEquiv place sigma :
  (AlgebraicClosure (Completion place))ˣ ≃*
  (AlgebraicClosure (Completion place))ˣ
```

with:

- `unitsAlgEquiv_refl`;
- `unitsAlgEquiv_trans`;
- `unitsAlgEquiv_tateParameterUnit`: it fixes the image of the Tate q-unit.

So there is an actual Galois action **on the algebraic closure L**, not on the
completion itself.  Since `concreteQUnitAlgebraicClosure` is the image of the
completion q-unit in L, the fixed-unit law is available on L.

## Completion-unit obstruction

No construction in the tree gives:

```lean
G : Type
[Group G]
ρ : G →* MulAut (CommonPrimeCompletion place)ˣ
```

with a nontrivial action.  An `AlgEquiv` of
`AlgebraicClosure (Completion place)` over `Completion place` does not act on
`CommonPrimeCompletion place` itself: the completion is not algebraically
closed and is not the algebraic closure.  There is also no actual map
`G_L → MulAut (CommonPrimeCompletion place)ˣ` compatible with the L-action.

A trivial actual action exists (`G = PUnit`, `ρ = 1`), but it yields only
`CyclotomicTower.one`-type classes; it is not the source Galois action and
cannot produce a nontrivial Kummer class.

## Exact first fields

1. `G : Type` with `[Group G]`;
2. actual `ρ : G →* MulAut (CommonPrimeCompletion place)ˣ`;
3. actual `fixed : ∀ σ, ρ σ qUnit = qUnit`;
4. an actual nontrivial `σ : G` (and a root witness) for nontriviality.

None is supplied by `ConcreteC3DonorActual`, the completion/Galois tower
files, or theta data.  The only actual action is `unitsAlgEquiv` on L.

## Alternative on L

If KummerClass is allowed over L, the actual action is available:

```lean
G_L := AlgebraicClosure (Completion place) ≃ₐ[Completion place]
        AlgebraicClosure (Completion place)
ρ_L σ := unitsAlgEquiv place σ
```

and `fixed` follows from `unitsAlgEquiv_tateParameterUnit` (applied to the
completion q-unit image).  But this is **not** the requested completion-unit
action, and it still lacks a proved nontrivial `σ` acting nontrivially on the
roots.  `AlgEquiv.refl` and `unitsAlgEquiv_refl` only give the trivial element.

## Conclusion

- No actual nontrivial `G, ρ` on completion units.
- Actual available: `unitsAlgEquiv` Galois action on algebraic-closure units,
  including the fixed Tate q-unit law.
- Exact first field: an actual completion-unit action `ρ` (equivalently a
  source construction of a nontrivial automorphism of the completion units),
  followed by `fixed` and a nontrivial `σ`/root witness.
- No roots/rootChange/kummerClass modified; report only, EXIT=0.
