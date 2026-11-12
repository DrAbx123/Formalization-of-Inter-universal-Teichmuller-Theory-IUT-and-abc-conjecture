# S2409: strong terminal cover representability example

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S1852CoherentCoverActual.lean`
  (`StrongCover`, `CoherentCover`, `S1852TerminalStrong`,
  `S1852TerminalCoherent`)
- `tmp/sheaf/xif/paper/S2403RepresentableExamplesActual.lean`
- `tmp/sheaf/xif/paper/S2400CoverRepresentableActual.lean`
- `tmp/sheaf/xif/paper/S2398HomOfStrongTransCompActual.lean`
- `tmp/sheaf/xif/paper/S1641CoverMapCompositionActual.lean`
- reports `S2403-representable-examples.md`, `S2400-cover-representable.md`

## Source object / domain / direction

- Source object: the identity cover map of the terminal strong cover
  `S1852TerminalStrong`.
- Domain: original O-layer D6(c); no S2130/S2185/S2269.
- Direction: construct a concrete strong-cover example of
  `S2403RepresentableCoverMap` (source/target fiber representable, map iso to
  S1742 representable map, monic).

## Deliverable

`tmp/sheaf/xif/paper/S2409StrongCoverRepresentableActual.lean`

```text
EXIT=0
olean=YES
lines=59
SHA256=500CAC6A756F15564FA14248B2BE90D4B20B85B69E91E9A14D7E2E5467565B19
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2409StrongCoverRepresentableActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT / PROVED (actual)

1. `S2409TerminalStrong_source_fiber`:
   `(StrongCover.cover S1852TerminalStrong).source.fiber =
    S1742YS S1726AffineOver` (rfl).
2. `S2409TerminalStrong_map`:
   the identity cover map is the identity strong transformation
   (S1641CoverMapId_map).
3. `S2409TerminalStrongRepresentable`:
   `S2403RepresentableCoverMap
     (S1641CoverMapId (StrongCover.cover S1852TerminalStrong))`.
   - sourceScheme = targetScheme = S1726AffineOver;
   - `g0 = 𝟙 S1726AffineOver`;
   - map iso via the S1742 round-trip iso;
   - `Mono g0` by instance.

So a concrete strong cover (the terminal/identity strong cover) has a
representable monic cover map.

## Exact first missing for general strong/coherent covers

For a general `Cs : StrongCover S1726Orbicurve` (or coherent), the current
data provide:

- `source : EtaleStackOverField S1726K` (arbitrary);
- `map : source.Hom S1726Orbicurve.stack`;
- a strong finite-etale structure, i.e. per-point strong presentations and
  finite-etale projections.

They do **not** provide:

```text
S2403RepresentableCoverMap (S1641CoverMapId (StrongCover.cover Cs))
```

i.e. source/target fiber representability, an iso/HEq of the map with
`S1742StrongTransOfHom g0`, and `Mono g0`. The strong terminal example is the
identity special case; the general exact first missing is the same
`S2400RepresentableCoverMap` / `S2403RepresentableCoverMap` condition.

No theorem in S1852/S2240/S2357 implies source representability or monicity of
the cover map. Strong/coherent presentations concern base changes, not the
global source stack representation.

## Weak/non-monic counterexample

No concrete non-representable or non-monic weak cover is produced. The S2291
path-cover identity is representable (S2403); its weak behavior is in the
two-pullback target, not representability. S1852's terminal strong cover is
also representable. General weak cover representability remains open/exact
missing, not refuted.

## Consumer

`S2409TerminalStrongRepresentable` gives an actual S2403 data point for the
terminal strong cover. For other covers, `S2400RepresentableCoverMap` remains
the exact condition needed before S2398 local cancellation and the S2380
presentation construction.

## Next executable subgoal

For a non-identity strong/coherent cover `Cs`, prove:

```text
source.fiber = S1742YS sourceScheme
map iso/HEq S1742StrongTransOfHom g0
Mono g0
```

or exhibit a non-representable/non-monic cover. No global cancellation is
assumed.

## Reports read

`coord/reports/S2403-representable-examples.md`,
`coord/reports/S2400-cover-representable.md`, and the S1852 strong/coherent
cover definitions.
