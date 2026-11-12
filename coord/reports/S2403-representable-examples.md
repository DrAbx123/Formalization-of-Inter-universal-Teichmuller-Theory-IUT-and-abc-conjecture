# S2403: identity path-cover representability example

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S2400CoverRepresentableActual.lean`
- `tmp/sheaf/xif/paper/S2398HomOfStrongTransCompActual.lean`
- `tmp/sheaf/xif/paper/S1641CoverMapCompositionActual.lean`
- `tmp/sheaf/xif/paper/S2291UniformGraphCompatActual.lean`
- `tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean`
- reports `S2400-cover-representable.md`, `S2398-hom-comp.md`

## Source object / domain / direction

- Source object: identity cover map `S1641CoverMapId S2291PathCover` and the
  S2291 path cover source.
- Domain: original O-layer D6(c); no S2130/S2185/S2269.
- Direction: exhibit an actual representable/monic map for a concrete cover
  (identity map), and isolate what remains for arbitrary weak covers.

## Deliverable

`tmp/sheaf/xif/paper/S2403RepresentableExamplesActual.lean`

```text
EXIT=0
olean=YES
lines=83
SHA256=6CF8A1AEC31EFA1A416676FE98E44FE2074B9E8B3D3569833680778E9B555C9A
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2403RepresentableExamplesActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT / PROVED (actual)

1. `S2403CastHom`: transport a stack hom along source/target fiber equalities
   to the representable S1742 model.
2. `S2403RepresentableCoverMap g`: source/target schemes, fiber equalities,
   `g0 : sourceScheme ⟶ targetScheme`, an iso
   `S2403CastHom ... g.map ≅ S1742StrongTransOfHom g0`, and `Mono g0`.
3. `S2403PathCover_source_fiber`:
   `S2291PathCover.source.fiber = S1742YS S1726AffineOver` (rfl).
4. `S2403PathCoverId_map`:
   `(S1641CoverMapId S2291PathCover).map = StrongTrans.id ...`.
5. `S2403PathCoverIdRepresentable`:
   the identity cover map of `S2291PathCover` is represented by
   `𝟙 S1726AffineOver` up to the S1742 round-trip iso, and that scheme map is
   monic.

This gives an actual representable/monic example at the S2291 datum.

## Exact remaining condition

For an arbitrary cover map `g : S1728CoverMap A B`:

```text
S2400RepresentableCoverMap g
```

i.e. source/target fibers are representable, `g.map` is (up to the S1742
round-trip iso / HEq in S2400) induced by `g0`, and `Mono g0`. The identity
path cover shows the condition is non-vacuous and actual for one important
cover; it does not prove it for all weak covers.

## Strong/coherent cover maps

S2240/S2357 supply per-cover presentations and finite-etale projections for
strong/coherent target covers, but they do not assert that the cover map itself
is representable by a monic scheme map. No such representability/monicity
theorem is currently derived from the S2240/S2357 data. This remains part of
the exact first missing.

## Weak-cover counterexample

No concrete non-representable/non-monic weak cover is produced. The S2291
path-cover identity is representable/monic; the weak behavior of S2291 is in
the two-pullback target, not in this local representability.

## Consumer

`S2403PathCoverIdRepresentable` can feed the local cancellation argument at the
S2291 datum (after transporting the S1742 iso to the exact equality used by
S2388/S2398). For arbitrary covers, `S2400RepresentableCoverMap g` is still the
exact obstruction.

## Next executable subgoal

Prove `S2400RepresentableCoverMap g` for:

1. other concrete covers with representable source/target (e.g. covers built
   from `S1726AffineOver`);
2. strong/coherent cover maps from S2240/S2357, if their underlying scheme maps
   are monic;
or isolate a concrete non-representable cover.

No global cancellation is assumed.

## Reports read

`coord/reports/S2400-cover-representable.md`,
`coord/reports/S2398-hom-comp.md`, and the S1641/S2291 definitions.
