# S2424: representable cover composition closure (exact missing)

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S2403RepresentableExamplesActual.lean`
- `tmp/sheaf/xif/paper/S2400CoverRepresentableActual.lean`
- `tmp/sheaf/xif/paper/S1641CoverMapCompositionActual.lean`
- `tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean`
- reports `S2403-representable-examples.md`, `S2400-cover-representable.md`

## Source object / domain / direction

- Source object: composition of two representable cover maps g1 : A -> B and
  g2 : B -> C.
- Domain: original O-layer D6(c); no S2130/S2185/S2269.
- Direction: construct a representable/monic composite map, or record the exact
  missing data.

## Deliverable

`tmp/sheaf/xif/paper/S2424CoverCompositionActual.lean`

```text
EXIT=0
olean=YES
lines=48
SHA256=16892C72FE3A474BBB0F2F564B4C59CC0CABC1D1ADE78BAD67C71A60B2364D1F
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2424CoverCompositionActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2424ComposableRepresentable g1 g2`:
   - `R1 : S2403RepresentableCoverMap g1`,
   - `R2 : S2403RepresentableCoverMap g2`,
   - `middle_eq : R1.targetScheme = R2.sourceScheme`.
2. `S2424CompositeRepresentable H`:
   - source/target schemes,
   - source/target fiber equalities,
   - `g0 : sourceScheme ⟶ targetScheme`,
   - `map_iso` from the cast composite map to `S1742StrongTransOfHom g0`,
   - `mono : Mono g0`.
3. `S2424CompositionRequired H := Nonempty (S2424CompositeRepresentable H)`.

No inhabitant is asserted.

## Exact missing for composition closure

```text
S2424CompositionRequired H
```

i.e. for every composable pair of representable cover maps with compatible
middle scheme, supply the composite `g0`, its iso to the S1742 representable
map, and `Mono g0`.

The source/target fiber equalities are directly inherited from R1 and R2; the
scheme-level composite should be
`R1.g0 ; (middle_eq ▸ R2.g0)`, and monicity would follow from monicity of both
factors once the dependent cast is handled. What is not yet assembled is the
map iso for the composite:

```text
Iso (cast composite g.map) (S1742StrongTransOfHom composite g0)
```

It requires composing the two S1742 round-trip isos and identifying
`vcomp (S1742StrongTransOfHom g1.g0) (S1742StrongTransOfHom g2.g0)` with
`S1742StrongTransOfHom (g1.g0 ; g2.g0)` (S2398 gives the underlying-hom
composition equation; the strong-transformation iso form still has to be
packaged).

## Strong non-identity example

No non-identity strong/coherent cover with representable monic map is
constructed here. The only actual examples are:

- S2291 path-cover identity (S2403);
- S1852 terminal strong cover identity (S2409).

General `StrongCover` sources/maps do not expose representability or monicity;
that remains the exact first missing `S2400RepresentableCoverMap`.

## What is not claimed

- No general composition closure theorem is claimed.
- No global cancellation or `S2086CospanGMapFiniteEtale` is assumed.
- No S2130/S2185/S2269 target is used.
- No non-identity strong cover example is fabricated.

## Consumer

An inhabitant of `S2424CompositionRequired H` would give a representable
composite cover map, feeding S2398 local cancellation / S2380 presentation.
Without it, composition of the known representable examples is not yet
assembled.

## Next executable subgoal

Prove `S2424CompositionRequired H` by:

1. defining the composite scheme map with the middle equality cast;
2. proving `Mono` of that composite from `Mono R1.g0` and `Mono R2.g0`;
3. composing the two map isos and using the S1742 composition/round-trip iso
   to obtain the composite map iso.

Then attempt a non-identity strong cover example.

## Reports read

`coord/reports/S2403-representable-examples.md`,
`coord/reports/S2400-cover-representable.md`, and the S1641/S1742 definitions.
