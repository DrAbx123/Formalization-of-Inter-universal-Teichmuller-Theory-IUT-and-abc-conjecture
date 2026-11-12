# D6 status after build incident (no further compiles)

Date: 2026-11-03. Layer O (D6(c) finite-etale input).

Build coordinator incident: Mathlib artifacts missing; per instruction no new
lake/lean compilation was started after the incident, and this report only
records the last successfully completed builds and their hashes.

## Actual closed in this branch

### S2429 cast-composition + Mono

`tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.lean`

```text
EXIT=0 (last clean compile before incident)
lines=116
SHA256=B220AB8ED37AA8D2A7C103A3370475645DD5C9CB264D0824A1A5DFF121122C7C
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.olean
```

Proved actual:

- `S2429CastComp_general` and `S2429CastComp_holds`;
- `S2429MonoCastComp` / `S2429CompositeMap_mono`;
- `S2429CompositeMap H`;
- conditional consumer `S2424CompositeOfMapIso` (map iso was then still open).

### S2431 composite map iso

`tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.lean`

```text
EXIT=0 (clean compile completed before incident)
lines=163
source SHA256=9D1E1C289BF344C6DE8B6EE6F6BF67856AC0A6A4CEC9A4F28A1330D0A432EA1A
olean SHA256=9574D3AEFCDC1AAC8A68AF91DD217A958569FFAD05F0D031D0E4DD6236DCE950
olean bytes=100080
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.olean
```

The file contains:

- `S2431CastHomMidIso` (transport of the second map_iso along middle equality);
- `S2431StrongTransOfHomCompIso` (S1742 round trip + S2398 composition);
- `S2431CompositeMapIsoRequired_holds : S2429CompositeMapIsoRequired H`;
- integration `S2431S2424CompositionRequired : S2424CompositionRequired H`.

Thus `S2424CompositionRequired` is actual for composable representable cover
maps, conditional only on the input H. The last compile of this file was
EXIT=0. The independent axiom probe was not completed after the build incident;
the subagent reported axioms `propext, Classical.choice, Quot.sound` but this
was not independently rerun in this session after the incident.

### S2433 non-identity coherent cover example

`tmp/sheaf/xif/paper/S2433NonidentityStrongRepresentable.lean`

```text
EXIT=0
lines=431
source SHA256=890178D59040C3B0CE9FA34B18D557148937FD7B5958B57FFBFA89B80E442852
olean SHA256=9E7EED2EB452EC72EE88B46D59785374030E24D39477265F096BD7C858148FC8
olean bytes=130512
axioms observed: propext, Classical.choice, Quot.sound
```

Actual content: `S2433Map` between the terminal coherent cover and a
non-identity fold coherent cover, `S2433Representable :
S2403RepresentableCoverMap S2433Map` with `g0 = S2433G0` (coproduct
inclusion), `Mono S2433G0`, `S2433G0_not_iso`, and S2240/S2357 per-cover
coherence/presentation/finite-etale projection.

## Still exact missing

- `S2086StackCancellation` / `S2089StackPresentationStatement` for arbitrary
  (non-representable) cover maps remain open.
- The corrected geometric apex remains S2367 (strong per-cover actual; general
  weak cover exact apex/stack cancellation open).
- Full S2086 ToA assembly needs the above; it is not claimed.

## Artifact integrity

No new compiles or lake builds were started after the incident notice. The
hashes above are from the last successful builds. If Mathlib artifacts are
restored, the immediate verification command is:

```text
lake env lean -j1 -R 'D:/lean' -o '.lake/build/lib/lean/tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.olean' 'tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.lean'
```

and then an axiom probe for `S2431CompositeMapIsoRequired_holds` and
`S2431S2424CompositionRequired`.
