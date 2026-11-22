# S1243: W.3 bridge — ProcessionChoice/concreteInput to FPrimeStrip

Target: an actual map

```text
ProcessionChoice l → FPrimeStrip V   (or SourceFTimesMuPrimeStrip V)
```

or an exact first missing field.  No weak compatible/Prop wrapper.

## Search result

### actual maps on source families (not ProcessionChoice)

- `OriginalInput.fPrimeStripAt (n m : Int) : FPrimeStrip V`
  (`SourceH1H2Construction.lean:52`).
- S1225 / `SourceOutputPrimeStripInterpretation.stripOfChoice`
  (`Output/SourceOutputPrimeStripInterpretation.lean:150`):
  ```lean
  stripOfChoice (i : I.family.index) : FPrimeStrip V :=
    I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2
  ```
  This is actual, but its domain is `I.family.index`, not
  `ProcessionChoice l`.
- `I.fStageCapsule n : FStageCapsule I n` has
  `strip : Fin (n+1) → FPrimeStrip V`, again not `ProcessionChoice`.
- `SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt n m)` gives actual
  `SourceFTimesMuPrimeStrip V` at integer source indices, again not
  `ProcessionChoice`.

### ProcessionChoice

`ConcreteFiniteModel.ProcessionChoice l` is

```lean
structure ProcessionChoice (l : PrimeGeFive) where
  processionLabel : finiteLabel l   -- = ZMod l
  tensorLabel : finiteLabel l
  upperSemiLevel : Nat
```

with `ind1Act`, `ind2Act`, `ind3Lift` acting on the first two labels by
addition in `ZMod l`, not on `Int × Int` source indices.

### concreteInput

`SourceProcessionBoundary.Input.concreteInput l` has a `carrier.core :
Core Label Choice` with `Choice = ProcessionChoice l`, but no field or
theorem maps `Choice` to `FPrimeStrip V` or `SourceFTimesMuPrimeStrip V`.

## Exact first missing field

### Object

```text
processionChoiceStrip : ProcessionChoice l → FPrimeStrip V
```

or the ×μ version

```text
processionChoiceTimesMuStrip : ProcessionChoice l → SourceFTimesMuPrimeStrip V.
```

### Required compatibility

The map must intertwine the procession operations with the source links:

```text
processionChoiceStrip (ind1Act t c) related by an actual FPrimeStripEquiv
  to processionChoiceStrip c
```

and similarly for `ind2Act`/`ind3Lift`.

### Why no actual map is available

`ProcessionChoice` labels are `ZMod l`; `I.fPrimeStripAt` takes `Int × Int`.
There is a raw representative map
`(i.processionLabel.val : Int)`, but it is not compatible with `+` in
`ZMod l` (only modulo l), so it cannot satisfy the above compatibility.
No other choice-to-strip map exists in the tree.

## Consumer

`SourceMultiradialPresentationWiring` W.3: compatibility with
`OriginalInput.fPrimeStripAt` (`SourceMultiradialPresentationWiring.lean:57-64`,
also card note at :698).  The W.3 record itself cannot be stated without
`processionChoiceStrip`.

## Conclusion

Exact stop at `processionChoiceStrip`.  No weak wrapper, no representative-
based fake map.  This is the same obstruction recorded in W.3 and in
`SourceMultiradialIplLinkWiring` route (b).

Status: exact stop; no new Lean file, no compile claim.
