# S2400: cover-map representability / exact first missing

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S1728CoverCategoryActual.lean`
  (`S1728Cover`, `S1728CoverMap`, `S1728Paper`)
- `Iut/Foundations/Orbicurve.lean`
  (`OrbicurveFiniteEtaleCover`, `OrbicurveFiniteEtaleCoverMap`)
- `tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean`
- `tmp/sheaf/xif/paper/S2398HomOfStrongTransCompActual.lean`
- reports `S2398-hom-comp.md`, `S2388-postcomp-cancellation.md`

## Source object / domain / direction

- Source object: actual cover map `g : S1728CoverMap A B` and its underlying
  stack hom `g.map`.
- Domain: original O-layer D6(c); no S2130/S2185/S2269.
- Direction: verify whether `g.map` is representable by a monic scheme map, so
  that S2398 local cancellation applies.

## Definition audit

`S1728CoverMap` is an abbreviation for
`Iut.OrbicurveFiniteEtaleCoverMap A B`, whose fields are:

```text
map : A.source.Hom B.source
commutes : Iso (vcomp map B.map) A.map
```

There is **no** field:

- that `A.source` or `B.source` is representable;
- that `g.map` is `S1742StrongTransOfHom g0` for a scheme morphism `g0`;
- that `g0` is monic.

The covers themselves carry `source : EtaleStackOverField` and
`map : source.Hom X.stack` with finite etaleness; arbitrary finite-etale
covers need not have representable source/target.

## Deliverable

`tmp/sheaf/xif/paper/S2400CoverRepresentableActual.lean`

```text
EXIT=0
olean=YES
lines=40
SHA256=A53CFBA2154B6FE5CEDA81EB54EA3452E5C97E07A34BAE5E28821748ADF31FE6
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2400CoverRepresentableActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

`S2400RepresentableCoverMap g` records exactly:

```text
sourceScheme targetScheme : SchemeOverField S1726K
source_fiber_eq : A.source.fiber = S1742YS sourceScheme
target_fiber_eq : B.source.fiber = S1742YS targetScheme
g0 : sourceScheme ⟶ targetScheme
map_heq : HEq g.map (S1742StrongTransOfHom g0)
mono : Mono g0
```

and

```text
S2400RepresentableCoverMapRequired g := Nonempty (S2400RepresentableCoverMap g)
```

No inhabitant is asserted.

## Exact first missing

```text
S2400RepresentableCoverMapRequired g
  = exists sourceScheme targetScheme,
      A.source.fiber = S1742YS sourceScheme
      / B.source.fiber = S1742YS targetScheme
      / (g0 : sourceScheme ⟶ targetScheme)
      / HEq g.map (S1742StrongTransOfHom g0)
      / Mono g0
```

Only after this does S2398 give local postcomposition cancellation
(`S2398PostcompRequired`). The missing part is not the composition equation
(now actual) but the representability and monicity of the actual cover map.

## Why it cannot be derived from the current cover structure

- `OrbicurveFiniteEtaleCoverMap` only stores an arbitrary stack hom and a
  commuting triangle;
- `EtaleStackOverField` is a general category-valued etale stack; no field
  equates its fiber with `schemeRepresentableEtalePseudofunctor`;
- no theorem in the tree proves every finite-etale cover of the orbicurve has
  representable source/target, and no theorem proves `g0` monic;
- strong/coherent target covers supply per-cover presentations, not
  representable monic cover maps for arbitrary B.

No counterexample to representability/monicity is produced; the statement is
simply not available from the recorded data.

## Consumer

If `S2400RepresentableCoverMap g` holds, S2398 local cancellation applies
(under the exact HEq/representability identification), feeding the S2380
presentation construction and eventually the S2086 finite-etale input without
S2130/S2185/S2269. Otherwise the exact missing above is the obstruction.

## Next executable subgoal

Prove for the actual cover maps of interest:

```text
A.source.fiber = S1742YS sourceScheme
B.source.fiber = S1742YS targetScheme
g.map = S1742StrongTransOfHom g0
Mono g0
```

or isolate a concrete non-representable cover. No global cancellation is
assumed.

## Reports read

`coord/reports/S2398-hom-comp.md`,
`coord/reports/S2388-postcomp-cancellation.md`, and the S1728/Iut cover-map
definitions.
