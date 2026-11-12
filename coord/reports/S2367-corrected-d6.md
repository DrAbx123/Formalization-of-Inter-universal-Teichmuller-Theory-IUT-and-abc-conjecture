# S2367: corrected D6 after review item 2

Date: 2026-11-03. Layer: **O** (D6(c) base-change finite-etale input).
No target change, no fake.

## Review D6 item 2 compliance

- S2185/S2269/S2130 are cut from this route.
- If the 3.12 cover source supplies a `StrongCover`, use the
  S2240/S2357 per-cover presentation and finite-etale projection.
- Otherwise the corrected geometric apex is the actual base-change
  presentation of `g.map` at the chosen point; at the S2291 weak-cover
  example this presentation exists (S2350PresentationAtDatum).
- Direct-route exact missing is `S2086StackCancellation` or a corrected-apex
  supply, **not** `forall B C, S2240ConeEssSurjAt B C`.

## Deliverable

`tmp/sheaf/xif/paper/S2367CorrectedD6Actual.lean`

```text
EXIT=0
olean=YES
lines=73
SHA256=88D2CB8C716B110F08929AEAE6BCCB92392864DFE6F66F46F8B9FA36BD6104A6
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2367CorrectedD6Actual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT (actual)

1. `S2367CorrectedApex f g T ptA :=
   EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA)`.
   This is the corrected geometric apex at a fixed point, not `S2130P`.
2. `S2367CorrectedApexOfStrongCover Cs B A f g T ptA`:
   the actual S2240/S2357 per-cover presentation from a strong target cover.
3. `S2367CorrectedApexOfStrongCover_finiteEtale`:
   its projection is finite and étale.
4. `S2367S2291Presentation`:
   at the S2291 weak-cover datum,
   `Nonempty (EtaleStackBaseChangePresentation S2291F.map S2291T
     (S2130PtC S2291F S2291T S2291PtA))`.
   This is the correct geometric presentation, not a two-pullback witness.
5. `S2367DirectFirstMissing := S2086StackCancellation`.
6. `S2367S2086CospanGMapFiniteEtaleOfCancellation`:
   stack cancellation gives the full S2086 finite-etale input without
   S2130/S2185/S2269.

## Strong-cover route

Given `Cs : StrongCover S1726Orbicurve`, for every source cover A, target
cover B, maps f/g targeting `StrongCover.cover Cs`, test scheme T and point
ptA, we obtain:

```text
S2367CorrectedApexOfStrongCover Cs B A f g T ptA :
  EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA)
```

and its projection is finite étale. This is the per-cover replacement supplied
by S2240/S2357, no uniform S2130 apex.

## S2291 example

At the same weak-cover example that refutes the S2130 uniform two-pullback
target, `S2367S2291Presentation` records the actual corrected geometric
presentation. The S2130 apex is empty, but the geometric presentation exists;
the two statements are different.

## Exact first missing

```text
S2086StackCancellation
  = forall {X Y Z : EtaleStackOverField S1726K} (f : X.Hom Y) (g : Y.Hom Z),
      EtaleStackFiniteEtaleMorphism (vcomp f g) ->
      EtaleStackFiniteEtaleMorphism g ->
      EtaleStackFiniteEtaleMorphism f
```

or, alternatively, a corrected-apex supply for all weak covers. The direct
route is not stated as `forall B C, S2240ConeEssSurjAt B C`, and no such
uniform cone-essential-surjectivity claim is used.

No inhabitant of stack cancellation is asserted.

## What is not used

- S2130ConcreteTwoPullback: false (S2350) and absent from the route.
- S2185StrictConeIso / S2269 graph compatibility: not used.
- terminal/point/metadata signatures: not used.
- uniform `S2240ConeEssSurjAt`: not used as the exact missing.

## Consumer

`S2367CorrectedApexOfStrongCover` + finite-etale projection gives the
per-cover D6(c) input for a strong target cover. For arbitrary weak targets,
`S2367S2086CospanGMapFiniteEtaleOfCancellation` needs
`S2086StackCancellation`; the alternative is a corrected-apex supply. Both
feed S2086 ToA assembly without the false S2130 target.

## Next executable subgoal

Prove `S2086StackCancellation`, or construct a corrected-apex supply for all
weak covers. A strong/coherent cover supply is the already-available per-cover
special case.

## Reports read

`coord/reports/S2357-corrected-d6-apex.md`,
`coord/reports/S2359-s2086-direct.md`, S2350 refutation report, and the
S2240/S2357 definitions above.
