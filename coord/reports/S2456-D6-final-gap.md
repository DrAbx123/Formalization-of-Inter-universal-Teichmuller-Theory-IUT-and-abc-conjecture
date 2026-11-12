# S2456: D6 final gap after S2424/S2431/S2433

Date: 2026-11-03. Layer O (D6(c) finite-etale input). No compilation was run
in this report; hashes are from the last serial verified builds.

## What is actual

### S2424 composition (representable composable pairs)

- `tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.lean`
  EXIT=0, source SHA256 `B220AB8E…122C7C`, olean SHA256 `55AC6B2A…39BB`,
  axioms trio.
- `tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.lean`
  EXIT=0, source SHA256 `9D1E1C28…D432EA1A`, olean SHA256
  `9574D3AE…DCE950`, axioms:
  `S2431CompositeMapIsoRequired_holds` and
  `S2431S2424CompositionRequired` both
  `propext, Classical.choice, Quot.sound`.

Closed:

```text
S2429CastComp
S2429CompositeMap
Mono (S2429CompositeMap H)
S2429CompositeMapIsoRequired H
S2424CompositionRequired H
```

for every composable pair of representable cover maps.

### Non-identity coherent example

- `tmp/sheaf/xif/paper/S2433NonidentityStrongRepresentable.lean`
  EXIT=0, source SHA256 `890178D5…E442852`, olean SHA256
  `9E7EED2E…58148FC8`, axioms trio.

Actual: `S2433Map` between terminal and fold coherent covers,
`S2403RepresentableCoverMap S2433Map`, `Mono S2433G0`,
`S2433G0_not_iso`, S2240/S2357 per-cover coherence/presentation/finite-etale
projection.

### Corrected geometric apex

- `tmp/sheaf/xif/paper/S2367CorrectedD6Actual.lean` (EXIT=0):
  strong-cover per-cover presentation from S2240/S2357 and the correct S2291
  geometric presentation; no false S2130 target.

## What is NOT actual

```text
S2086StackCancellation
S2089StackPresentationStatement
```

Neither is constructed.

### S2089 exact statement

```text
S2089StackPresentationStatement
  = forall f g,
      EtaleStackFiniteEtaleMorphism (f ; g) ->
      EtaleStackFiniteEtaleMorphism g ->
      forall T ptY,
        EtaleStackBaseChangePresentation f T ptY
```

plus `S2089StackPropertyStatement` (the presentation projection is finite and
etale). These give stack cancellation via
`S2089StackCancellationOfPresentation`.

### S2086 exact statement

```text
S2086StackCancellation
  = forall {X Y Z} (f : X.Hom Y) (g : Y.Hom Z),
      EtaleStackFiniteEtaleMorphism (f ; g) ->
      EtaleStackFiniteEtaleMorphism g ->
      EtaleStackFiniteEtaleMorphism f
```

This is exactly the missing input for
`S2086CospanGMapFiniteEtaleOfStackCancellation`.

## Why S2424/S2431/S2433 do not close arbitrary covers

- S2424 composition applies only to composable **representable** maps
  (`S2424ComposableRepresentable` with `S2403RepresentableCoverMap` fields).
- S2433 gives one non-identity representable example; it does not prove all
  cover maps are representable.
- S2400/S2403 exact missing remains: for an arbitrary
  `g : S1728CoverMap A B`, no source/target fiber representability, no
  `g.map = S1742StrongTransOfHom g0`, and no `Mono g0` is known.
- S2367 corrected apex supplies per-cover presentations for strong/coherent
  target covers. It does not supply the arbitrary f-presentation required by
  S2089; the S2291 weak cover has a genuine geometric presentation but not the
  global F^⊩/two-pullback property.

## Exact first missing / needed structure

To close either route, one must provide one of:

1. `S2089StackPresentationStatement` + `S2089StackPropertyStatement`;
2. `S2086StackCancellation` directly;
3. a theorem that every relevant cover map is representable and monic
   (`S2400RepresentableCoverMap` / `S2403RepresentableCoverMap`) with
   composition closure, which would let S2424/S2431 apply globally;
4. a corrected-apex supply for arbitrary weak covers with projection, 2-cell,
   and full 2-universal property.

None is available from the current tree; this is the honest D6 boundary.

## Rejected substitutions

- S2130ConcreteTwoPullback / S2185StrictConeIso / S2269 graph compatibility:
  false or unavailable; not used.
- terminal/point fiber and metadata signature: not used.
- conditional apex/handwave cancellation: not used.
- No new axiom/sorry/True/PUnit.

## Next executable step

Within the D6 scope, the least-coupled genuine subgoal remains:

```text
S2089StackPresentationStatement
```

from g-presentation and f;g-presentation, requiring a representability or
corrected-apex input that makes postcomposition cancellation work. S2424
composition and S2433 provide the representable cases but not the arbitrary
non-representable case.
