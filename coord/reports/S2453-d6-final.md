# S2453: D6 composite Mono/map iso FINAL STATUS (serial verified)

Date: 2026-11-03. Layer O (D6(c) finite-etale input). Lock released; all builds
below were serial `lake env lean -j1 -R 'D:/lean'`; no parallel compilation.

## 1. S2429 cast-composition + Mono

`tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.lean`

```text
EXIT=0
lines=116
source SHA256=B220AB8ED37AA8D2A7C103A3370475645DD5C9CB264D0824A1A5DFF121122C7C
olean SHA256=55AC6B2A2867B386F6FD5B283F8D297D55C7B750127A0ABA3E8836FBECE439BB
olean bytes=79528
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.olean
axioms:
  S2429CastComp_general -> propext, Classical.choice, Quot.sound
  S2429CompositeMap_mono -> propext, Classical.choice, Quot.sound
```

Actual:

- `S2429CastComp_general` / `S2429CastComp_holds`;
- `S2429MonoCastComp` / `S2429CompositeMap_mono`;
- `S2429CompositeMap H := H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)`;
- `S2424CompositeOfMapIso H h`, `S2424CompositionRequired_of_mapIso H h`.

The consumer signatures use the current two-argument form (H and map iso only);
Mono is provided internally. This resolves the stale subagent warning about a
three-argument consumer: the current S2429 and S2431 compile together.

## 2. S2431 composite map iso

`tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.lean`

```text
EXIT=0
lines=163
source SHA256=9D1E1C289BF344C6DE8B6EE6F6BF67856AC0A6A4CEC9A4F28A1330D0A432EA1A
olean SHA256=9574D3AEFCDC1AAC8A68AF91DD217A958569FFAD05F0D031D0E4DD6236DCE950
olean bytes=100080
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.olean
axioms:
  S2431CompositeMapIsoRequired_holds -> propext, Classical.choice, Quot.sound
  S2431S2424CompositionRequired -> propext, Classical.choice, Quot.sound
```

Actual:

- `S2431CastHomMidIso`: transport of the second map iso along the middle
  scheme equality, via `cases m` + proof irrelevance + `eqToIso`;
- `S2431StrongTransOfHomCompIso`: S1742 round trip + S2398 composition;
- `S2431CompositeMapIsoRequired_holds : S2429CompositeMapIsoRequired H`;
- `S2431S2424CompositionRequired : S2424CompositionRequired H`.

Therefore `S2424CompositionRequired` is **actual** for every composable pair
of representable cover maps.

## 3. S2433 non-identity coherent cover example

`tmp/sheaf/xif/paper/S2433NonidentityStrongRepresentable.lean`

```text
EXIT=0
lines=431
source SHA256=890178D59040C3B0CE9FA34B18D557148937FD7B5958B57FFBFA89B80E442852
olean SHA256=9E7EED2EB452EC72EE88B46D59785374030E24D39477265F096BD7C858148FC8
olean bytes=130512
axioms: propext, Classical.choice, Quot.sound
```

Actual non-identity example: terminal coherent cover to a fold coherent cover,
`S2433Representable : S2403RepresentableCoverMap S2433Map`, `Mono S2433G0`,
`S2433G0_not_iso`, S2240/S2357 per-cover presentation and finite-etale
projection.

## 4. What is closed

```text
S2429CastComp
S2429CompositeMap
Mono (S2429CompositeMap H)
S2429CompositeMapIsoRequired H
S2424CompositionRequired H   (representable composable pairs)
non-identity strong/coherent representable example
```

## 5. Exact remaining (not closed)

```text
S2086StackCancellation
S2089StackPresentationStatement
```

S2424 composition handles pairs of representable maps. It does not construct an
arbitrary f-presentation from g and f;g presentations, so arbitrary
(non-representable) cover maps still require stack cancellation or a corrected
apex supply.

The corrected geometric apex remains S2367 (strong per-cover actual); arbitrary
weak covers are not covered by S2424 composition.

## 6. Honesty

- No false S2130/S2185/S2269 target.
- No conditional/fake substitution in the closed statements; the only
  hypotheses are the actual input data H and its fields.
- Serial compilation only after lock release; no parallel builds.
- S2431 subagent's stale "three argument" observation is resolved by the
  current S2429 two-argument consumer; both were compiled serially EXIT=0.
