# S2377: stack presentation construction / exact extra structure

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S2089StackCancellationActual.lean`
  (`S2089StackPresentationStatement`, `S2089StackPropertyStatement`,
  `S2089StackCancellationOfPresentation`)
- `tmp/sheaf/xif/paper/S2090StackCancellationObstructionActual.lean`
  (`S2090PostcompCancellation`)
- `tmp/sheaf/xif/paper/S2088GMapCancellationActual.lean`
- `tmp/sheaf/xif/paper/S2374StackCancellationActual.lean`
- reports `S2374-stack-cancellation.md`, `S2367-corrected-d6.md`

## Source object / domain / direction

- Source object: f's base-change presentation at an arbitrary point ptY, from
  a presentation of g at ptY ; g and of f ; g at ptY.
- Domain: original O-layer D6(c); no S2130/S2185/S2269.
- Direction: construct the presentation by cancelling postcomposition, with an
  explicit fixed-morphism cancellation input; otherwise record the exact
  missing structure.

## Deliverable

`tmp/sheaf/xif/paper/S2377StackPresentationActual.lean`

```text
EXIT=0
olean=YES
lines=68
SHA256=33C14400AAA9BCD41622A60B82B0B38E0EB9008B9A1CD3CB0FB9F6967CF756FE
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2377StackPresentationActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2377PostcompCancellationAt g`: fixed-morphism extra structure
   `cancel : Iso (a ; g) (b ; g) -> Iso a b`.
2. `S2377PostcompCancellation := S2090PostcompCancellation`: global form,
   false in general.
3. `S2377PostcompAtOfGlobal`: global -> fixed-morphism structure.
4. `S2377PresentationRequired := S2089StackPresentationStatement`.
5. `S2377PropertyRequired := S2089StackPropertyStatement`.
6. `S2377StackCancellationOfPresentation`: presentation + property ->
   `S2088StackCancellation`.
7. `S2377PresentationFirstMissing := Nonempty S2377PresentationRequired`,
   with definitional iff.

No inhabitant of the presentation statement is asserted; no postcomposition
cancellation is assumed globally.

## What could not be constructed

The actual f-presentation cannot be built from the recorded data alone:

- from g's presentation at `ptY ; g` and f;g's presentation at `ptY`, the
  natural construction requires cancelling postcomposition by g in the
  comparison 2-isomorphism;
- `S2090PostcompCancellation` is false in general (constant functors lose
  information), so this cancellation is not available for arbitrary stack
  morphisms;
- therefore f's base-change presentation and its finite-etale projection are
  not constructed.

## Exact first missing / needed extra structure

```text
S2089StackPresentationStatement
  = forall f g,
      EtaleStackFiniteEtaleMorphism (f ; g) ->
      EtaleStackFiniteEtaleMorphism g ->
      forall T ptY,
        EtaleStackBaseChangePresentation f T ptY
```

plus

```text
S2089StackPropertyStatement
  = the resulting projection is finite and etale
```

A sufficient extra input is fixed-morphism postcomposition cancellation
`S2377PostcompCancellationAt g` (or a representability/faithfulness or
corrected-apex condition that yields it). Global
`S2090PostcompCancellation` is not assumed and is false in general. Strong or
coherent target covers (S2240/S2357) do not by themselves supply the arbitrary
f presentation.

## Relation to S2374

This refines S2374: stack cancellation is exactly the presentation statement
plus finite-etale property, and the presentation statement needs the extra
postcomposition cancellation/representability. No false uniform apex,
S2130/S2185/S2269, or terminal/point/metadata substitution is used.

## Consumer

`S2377StackCancellationOfPresentation` -> S2088StackCancellation ->
S2086CospanGMapFiniteEtaleOfStackCancellation -> S2086 ToA assembly.

## Next executable subgoal

Construct an f-presentation at arbitrary ptY from:

1. g-presentation at `ptY ; g`;
2. f;g-presentation at ptY;
3. a fixed-morphism `S2377PostcompCancellationAt g` or a
   representability/faithfulness/corrected-apex theorem that implies it.

If none is available for arbitrary weak covers, record that as the exact
obstruction rather than assuming it.

## Reports read

`coord/reports/S2374-stack-cancellation.md`,
`coord/reports/S2367-corrected-d6.md`, and the S2088/S2089/S2090 definitions.
