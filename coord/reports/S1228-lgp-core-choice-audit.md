# S1228: can the actual SourceLGPProcession / SourceProcessionBoundary.Input core
be instantiated on Choice = I.family.index?

Date: 2026-10-30. Report only. The source index is `I.family.index`.

## 1. SourceLGPProcession requirements

`SourceHodgeTheaterBridge.SourceLGPProcession` (lines 158-183) requires:

```lean
hodge : SourceHodgeTheaterSystem.{u, v, v} l
base : Choice
level : Choice → Nat
ind1 ind2 : Label → Choice → Choice
ind3 : Nat → Choice → Choice
all Core group laws
source_index : Choice → hodge.index
ind1_index : source_index (ind1 g c) = source_index c
ind2_index : source_index (ind2 g c) = source_index c
ind3_index : source_index (ind3 n c) = source_index c
```

`hodge : SourceHodgeTheaterSystem.{u, v, v} l` has:

```lean
source : SourceDefinition31Data.{u} l
index : Type v
theaterCarrier : Type v
theater : index → theaterCarrier
qParameter scale link permutation ...
```

## 2. Why Choice = I.family.index does not directly instantiate it

### (a) universe/type mismatch

`SourceLGPProcession` requires `hodge.index` and `hodge.theaterCarrier` to live
in the same universe `v` as `Choice`.

For `Choice := I.family.index`:

- `I.family.index : Type ui`;
- `HodgeTheater : Type (max ua uv upi umon)`.

These are not the same universe in general, so the actual family
`I.family.theater : I.family.index → HodgeTheater` cannot be inserted as
`hodge.theater : hodge.index → hodge.theaterCarrier` with
`hodge.index = Choice` and `hodge.theaterCarrier = HodgeTheater`.

One can choose `theaterCarrier := I.family.index` and `theater := id`, but then
the hodge system is not the actual Hodge-theater family; it is a degenerate
index-only system.

### (b) source_index

`source_index : Choice → hodge.index` is actual only in the degenerate choice
`hodge.index = Choice`, `source_index = id`.  With the actual Hodge family one
would need `source_index : I.family.index → hodge.index` and a proof that
ind1/ind2/ind3 preserve it.  No such map is defined in the tree.

### (c) ind1/ind2/ind3

`I.horizontalShift`, `I.verticalShift`, `I.translate` are actual index
operations, but `SourceLGPProcession` does not identify them with its
`ind1/ind2/ind3`; its fields are bare operations with group laws only.

`S1227.SourceCoreActual.sourceCore` supplies a `MultiradialKernel.Core` on
`Choice = I.family.index` via `I.translate` (actual group/level laws), but
it is **not** a `SourceLGPProcession`: it has no `hodge`, `source_index`, or
`ind*_index` fields.  It also has no proof that translate operations are the
paper's LGP ind operations (the source Hodge system only supplies links
between theaters, not ind1/ind2/ind3 acting on an index).

## 3. Degenerate constructor

`SourceProcessionFromContract.sourceLGPProcessionOfDefinition31Data`
(line 121) builds a `SourceLGPProcession` from a `SourceDefinition31Data` and
a base point:

```lean
hodge := canonicalSourceHodgeTheaterSystem S  -- identity index/theater
level := 0
ind1 := id, ind2 := id, ind3 := id
source_index := id
```

Its own docstring calls it degenerate: "carries no arithmetic content and is
not the paper's Hodge theater".  It can be instantiated with
`S = I.initial`, `Choice = I.family.index`, but this is exactly the identity
core, not the actual source core; using it would be identity/translation
pretending.

There is also the conditional `SourceRealizationLifting.hodge` from a
`SourceTheorem311Completion C`, which itself requires a `SourceDefinition31Data`
and a `SourceProcessionBoundary.Input` with q/scale/link data; no such C is
constructed from arbitrary I.

## 4. SourceProcessionBoundary.Input

`SourceProcessionBoundary.Input` (SourceProcessionBoundary.lean:33) requires:

```lean
theater : HodgeTheater
history : HodgeTheaterHistory ...
carrier : ParametricTheorem311.Carrier Label Choice
baseChoice : Choice
packetVolume : Choice → Real
target_q : Real
route_normal_form : ...
```

With `Choice = I.family.index`, the actual `carrier` is the first missing
structured field:

- `S1227` gives `sourceCore : Core Label Choice`;
- `Carrier` additionally needs
  `profile : Profile sourceCore`,
  `connector : Choice → Choice → List (RouteStep Label)` with
  `connector_horizontal`, `connector_target_same_level`, and
  `ind3_level_eq`.

No actual `Profile`/`connector` on `I.family.index` is constructed in the
tree, and no actual `HodgeTheaterHistory` from `I.family` is supplied.

First exact fields for `Input`:

1. `profile : Profile sourceCore`;
2. `connector` with its three laws;
3. `theater`/`history` with actual source provenance;
4. `packetVolume`/`target_q` identifications.

## 5. Conclusion

- No actual instantiation of `SourceLGPProcession` with
  `Choice = I.family.index` exists.
- The first exact type gaps are:
  1. `hodge : SourceHodgeTheaterSystem.{u,v,v}` with actual Hodge family:
     universe mismatch between `I.family.index` and `HodgeTheater`;
  2. `source_index : Choice → hodge.index` with actual family semantics;
  3. actual `ind1/ind2/ind3` identification with source operations
     (translate alone is not the LGP core);
  4. for `SourceProcessionBoundary.Input`: actual `profile`/`connector` and
     actual `HodgeTheaterHistory`.
- The only existing constructor is the explicitly degenerate identity
  procession; it is not an actual core.
- No wrapper or translation-pretender written; EXIT=0 report.
