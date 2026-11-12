# S1244: which is the paper's source algorithm Choice?

Date: 2026-10-30. Report only; no source or theorem changed.

## Question

`ConcreteFiniteTheorem311.ProcessionChoice` versus `I.family.index` for
`I : OriginalInput l V`: which is the original paper's algorithm Choice?

## Evidence

### 1. ProcessionChoice is explicitly a finite model boundary

`ConcreteFiniteModel.lean` header (:1-10):

> A finite, source-oriented carrier for the three indeterminacy layers. ...
> the underlying arithmetic carrier is our proved Q(i)-at-5 C-stage packet,
> rather than an unconstrained toy proposition.  The finite model is
> deliberately recorded as a model boundary; it is not the source theorem
> about arbitrary Hodge theaters.

Its structure (:94-101):

```lean
structure ProcessionChoice (l : PrimeGeFive) where
  processionLabel : finiteLabel l
  tensorLabel : finiteLabel l
  upperSemiLevel : Nat
```

with the comment:

> The place, curve, Frobenioid, and theta packet are fixed to the proved
> C-stage carrier; only the three displayed indeterminacy coordinates vary.

So ProcessionChoice is a **concrete model carrier** with a fixed C-stage
packet, not a choice in an arbitrary initial Hodge-theater family.

### 2. The finite model is used only for the concrete input

`SourceProcessionBoundary.concreteInput` (and the `Concrete...` files) use
`ProcessionChoice`; the S1229 audit (:31-37) states:

> `concreteInput` uses the concrete finite model
> `ConcreteFiniteTheorem311.ProcessionChoice`, not an arbitrary
> `I.family.index`.  It is not a source-index connection for arbitrary
> `OriginalInput`.

No map or equivalence from `I.family.index` to `ProcessionChoice` exists in
the tree.  `ProcessionChoice` has `finiteLabel l = Fl l.value` labels, while
`I.family.index` is an arbitrary index type with only
`index_equiv : I.family.index ≃ Int × Int`; there is no canonical comparison.

### 3. I.family.index is the actual source family index

`OriginalInput` (SourceOriginalInput.lean:41-46):

```lean
structure OriginalInput (l : PrimeGeFive) (V : Type uv) where
  initial : SourceDefinition31Data l
  family : SourceHodgeTheaterFamily l V
  index_equiv : family.index ≃ SourceTheorem311Index
  arithmetic_alignment : ...
```

with `SourceTheorem311Index := Int × Int`.

The actual source choices are the Hodge theaters `I.family.theater i` for
`i : I.family.index`; the family is `Int × Int`-indexed and distinct:

- `theaterAt n m := I.family.theater (I.indexOf n m)`;
- `theaterAt_eq_iff` says different `(n,m)` are different theaters;
- `stripOfChoice i := I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2`
  (S1221/S1225) attaches the actual F-prime-strip to that choice.

Thus `I.family.index` is the actual index of the paper's initial Hodge-theater
choices for arbitrary `I`.  The paper's source choice is a choice of Hodge
theater in this family, not a ProcessionChoice tuple.

## Conclusion

- **Paper source algorithm Choice = `I.family.index`** (the actual
  `SourceHodgeTheaterFamily.index`, with `index_equiv ≃ Int × Int`).
- **`ProcessionChoice` is not the paper source Choice**; it is an explicitly
  labeled finite model/C-stage carrier (`processionLabel`, `tensorLabel`,
  `upperSemiLevel`) with the arithmetic packet fixed.  It is used by the
  concrete `concreteInput` path, not by the arbitrary-`OriginalInput` theorem.
- Caveat: `I.family.index` is the correct **Choice type**; it does not by
  itself supply the algorithm input/profile/route.  Those are separate
  fields to construct on `Choice = I.family.index`.
- No source/theorem changed; report only, EXIT=0.
