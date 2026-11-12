# S2374: direct S2086 stack cancellation audit

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S2088GMapCancellationActual.lean`
  (`S2088_scheme_finiteEtale_cancel`, `S2088StackCancellation`)
- `tmp/sheaf/xif/paper/S2089StackCancellationActual.lean`
  (`S2089StackPresentationStatement`, `S2089StackPropertyStatement`,
  `S2089StackCancellationOfPresentation`)
- `tmp/sheaf/xif/paper/S2090StackCancellationObstructionActual.lean`
  (`S2090PostcompCancellation`)
- `tmp/sheaf/xif/paper/S2086ToAAssemblyActual.lean`
  (`S2086StackCancellation`, `S2086CospanGMapFiniteEtaleOfStackCancellation`)
- `tmp/sheaf/xif/paper/S2357CorrectedD6ApexActual.lean`
  (strong-cover per-cover presentation)
- reports `S2359-s2086-direct.md`, `S2367-corrected-d6.md`

## Source object / domain / direction

- Source object: `S2086StackCancellation`.
- Domain: original O-layer D6(c); no false S2130 target.
- Direction: prove stack cancellation directly or isolate the exact
  presentation/coherence input.

## Deliverable

`tmp/sheaf/xif/paper/S2374StackCancellationActual.lean`

```text
EXIT=0
olean=YES
lines=50
SHA256=BD953B1083C3D28D4E259645B4649C946934BA2EDE7EBB57811824073E71A091
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2374StackCancellationActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT (actual)

1. `S2374PresentationRequired := S2089StackPresentationStatement`:
   for f, g, finite-etale f;g and g, a base-change presentation of f at every
   test point.
2. `S2374PropertyRequired := S2089StackPropertyStatement`: the projection of
   that presentation is finite and etale.
3. `S2374StackCancellationOfPresentation`: presentation + property give
   `S2088StackCancellation`.
4. `S2374SchemeCancellation`: scheme-level cancellation actual via Mathlib
   `Etale.of_comp` and `IsFinite.of_comp`.
5. `S2374PostcompObstruction := S2090PostcompCancellation`.
6. `S2374StackCancellationFirstMissing := Nonempty S2374PresentationRequired`,
   with definitional iff.

No inhabitant of stack cancellation or its presentation statement is
asserted.

## Exact first missing

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
  = the projection of that presentation is finite and etale
```

No strong/coherent cover hypothesis is part of this first missing. The
strong-cover S2357 data supplies presentations for maps targeting a strong
cover, but not the presentation of an arbitrary f at arbitrary ptY required by
cancellation.

## Why the recorded data does not suffice

S2090 isolates the obstruction in the natural attempt: to build f's
presentation one must cancel postcomposition by g in a 2-isomorphism

```text
Iso (vcomp (vcomp xsrc f) g) (vcomp proj (vcomp ptY g))
  -> Iso (vcomp xsrc f) (vcomp proj ptY)
```

This postcomposition cancellation is false in general (S2090PostcompCancellation).
Therefore the presentation statement cannot be derived from the recorded
finite-etale fields alone; it needs a representability/faithfulness or
corrected-apex input. No such witness is fabricated.

The scheme-level cancellation (S2374SchemeCancellation) is actual, but it only
gives the finite-etale property once the scheme-level presentation is known; it
does not construct the stack base-change presentation.

## Relation to strong/coherent covers

S2357's strong-cover per-cover presentation and S2240 witnesses remain actual
for strong/coherent target covers. They do not eliminate the arbitrary f
presentation required by stack cancellation, so they are not a substitute for
`S2089StackPresentationStatement`.

## Consumer

`S2374StackCancellationOfPresentation` -> `S2088StackCancellation` ->
`S2086CospanGMapFiniteEtaleOfStackCancellation` -> S2086 ToA assembly,
without S2130/S2185/S2269 and without the false uniform apex.

## Next executable subgoal

Construct the presentation of f at an arbitrary point ptY from:

- a presentation of g at `ptY ; g`,
- a presentation of `f ; g`,
- a representability/faithfulness or corrected-apex input for g that permits
  postcomposition cancellation of the comparison 2-isomorphism.

## Rejected routes

- assuming `S2086StackCancellation`: not done;
- using false S2130ConcreteTwoPullback: not used;
- declaring `S2090PostcompCancellation`: not done;
- replacing cancellation by uniform `S2240ConeEssSurjAt`: not used.

## Reports read

`coord/reports/S2359-s2086-direct.md`,
`coord/reports/S2367-corrected-d6.md`, and the S2088/S2089/S2090 definitions
above.
