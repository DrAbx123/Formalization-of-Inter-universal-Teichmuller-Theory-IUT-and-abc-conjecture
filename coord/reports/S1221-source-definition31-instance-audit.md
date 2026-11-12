# S1221: SourceDefinition31Data instance / constructor audit

Date: 2026-10-30. Report only.

## 1. Structure

`SourceDefinition31Data` (SourceDefinition31Boundary.lean:619) requires:

```lean
arithmetic : InitialThetaArithmeticData l
selectedPlaces badPlaces : Type u
reduction : SourceReductionClause selectedPlaces badPlaces
torsion : SourceTorsionClause l
orbicurve : SourceOrbicurveClause
sections : SourceSectionClause
cusp : SourceCuspClause
five (Prop, proof) arithmetic-compatibility pairs
```

The structure has no inhabitant asserted anywhere in the tree.

## 2. Search for actual instance

`Example36SourceObjectBridge.SourceDefinition31DataCard` (:187):

```lean
def SourceDefinition31DataCard (l) : Prop :=
  ∀ A : InitialThetaArithmeticData.{0} l, Nonempty (SourceDefinition31Data.{0} l)
```

This is only a Prop card.  No theorem proves it.

`SourceDefinition31RootLemmas` header (:17-21) states explicitly:

> It does not construct a `SourceDefinition31Data` value from an arbitrary
> arithmetic curve: that construction is the source obligation being tracked.

## 3. Actual constructors (conditional)

### d11EntryData

`SourceDefinition31PlacePartition.lean:180`:

```lean
noncomputable def d11EntryData
    (P : SourcePlaceSelection A) [Fintype (Bad P)]
    (C : BadPlaceReductionCards P)
    (T : SourceTorsionClause l)
    (O : SourceOrbicurveClause)
    (Se : SourceSectionClause)
    (Cu : SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourceDefinition31Data l
```

Actual construction, but every clause is a hypothesis.

### StageConstructionTrace.toSource

`SourceDefinition31RootLemmas.lean:3807`:

```lean
def StageConstructionTrace.toSource : SourceDefinition31Data l
```

Actual conditional on a `StageConstructionTrace`, whose fields are exactly
the same D4-D9 clause data plus compatibility proofs.  No trace instance is
constructed.

`stage_d10_to_d11` reduces the universal construction to

```lean
∀ A, Nonempty (StageConstructionTrace l)
```

which is not proved.

### D4D9Supply

`SourceDefinition31D4D9Supply.lean` bundles the D4-D9 supplies and calls
`d11EntryData`; it also does not manufacture any field.

## 4. Exact first fields from InitialThetaArithmeticData

Given only `A : InitialThetaArithmeticData l`, the first missing field is:

```lean
P : SourcePlaceSelection A
[Fintype (Bad P)]
```

then, in order:

```lean
C : BadPlaceReductionCards P
T : SourceTorsionClause l
O : SourceOrbicurveClause
Se : SourceSectionClause
Cu : SourceCuspClause
redCompat/hredCompat ... cusCompat/hcusCompat
```

No theorem derives `P`, the bad set/partition, the reduction cards, the
torsion/orbicurve/section/cusp clauses, or the compatibility proofs from `A`
alone.  These are the source-side D3-D11 data, not functions of the
arithmetic curve A.

## 5. Conclusion

- No actual concrete instance of `SourceDefinition31Data` exists in the tree.
- Actual constructors: `d11EntryData` and `StageConstructionTrace.toSource`,
  both conditional on the full D3-D11 clause supply.
- Exact first fields from `A` alone: `SourcePlaceSelection A` + `Fintype (Bad P)`,
  followed by reduction/torsion/orbicurve/section/cusp clauses and five
  compatibility pairs.
- `SourceDefinition31DataCard` is unproved, and the root-lemma file explicitly
  disclaims constructing a value from an arbitrary arithmetic curve.
- No fake curve/instance; report only, EXIT=0.
