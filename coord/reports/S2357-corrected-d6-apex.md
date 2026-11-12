# S2357: corrected D6 apex / per-cover strong-cover replacement

Date: 2026-11-03. Layer: **O** (D6(c) base-change / S2086 finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S2130ExplicitD6Actual.lean`
  (`S2130P`, `S2130ToSource`, `S2130Proj`, `S2130Commutes`,
  `S2130ConcreteTwoPullback`)
- `tmp/sheaf/xif/paper/S2291UniformGraphCompatActual.lean`
  (`S2291PathCover`, `S2291NotGraphCompatAll`, refutation datum)
- `tmp/sheaf/xif/paper/S2350D6AfterRefuteActual.lean`
  (`S2350NotConcreteTwoPullback`, `S2350IsEmpty`,
  `S2350PresentationAtDatum`)
- `tmp/sheaf/xif/paper/S2240StrictConeIsoActual.lean`
  (`S2240ConeEssSurjAt`, `S2240WitnessFor_strongCover`,
  `S2240HgFor_strongCover`, `S2240HgFor_strongCover_finiteEtale`)
- `tmp/sheaf/xif/paper/S2086ToAAssemblyActual.lean`
  (`S2086CospanGMapFiniteEtale`, `S2086BaseChangePullback`)
- report `coord/reports/S2310...` (if present) and S2350 audit.

## Source object / domain / direction

- Source object: S2130 recorded concrete base-change square and the S2086
  finite-etale input.
- Domain: original O-layer, D6(c) geometric half.
- Direction: audit which S2130 pieces are reusable after the false uniform
  apex; construct the per-cover strong-cover replacement and isolate its exact
  coherence obligation.

## Deliverable

`tmp/sheaf/xif/paper/S2357CorrectedD6ApexActual.lean`

```text
EXIT=0
olean=YES
lines=64
SHA256=39DD0B96CE32F4DCC07D3C511ECD10B32F678330F707BA410072536549DCFA44
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2357CorrectedD6ApexActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## S2130 reuse audit

1. `S2130ToSource`: uses
   `S2130P_fst_site` and `S2130PB.toSource`.
   Reusable only for an apex that carries a projection to `S2130PB` and the
   same source comparison; at the S2291 datum no such projection makes the
   recorded square a two-pullback.
2. `S2130Proj`: uses `S2130P_snd_site`.
   Reusable as the projection component only after a corrected apex with a
   projection to `T` is supplied.
3. `S2130Commutes`: built from `S2130CompositeHomEq` and the strict
   pullback condition of `S2130P`.  It proves the recorded square commutes,
   but does not make it a two-pullback; at S2291 the apex `S2130P` is empty,
   so this cannot be repaired by a graph/diagonal replacement while keeping the
   same recorded legs.
4. `S2130P_fst/snd` finite-etale facts remain reusable only conditionally on
   a corrected apex; they are not themselves the obstruction.
5. S2240 replaces the presentation comparisons by
   `S2240PhiSiteToSource/Proj`, `S2240GraphSiteToSource/Proj` and the
   strong/coherent-cover witness; those are the reusable pieces for a
   non-uniform route.

## BUILT (actual)

1. `S2357UniformApexImpossible : S2130ConcreteTwoPullback -> False`.
2. `S2357NoUniformApex : Not (Nonempty S2130ConcreteTwoPullback)`.
3. `S2357PerCoverCoherenceRequired B C := S2240ConeEssSurjAt B C`.
4. `S2357StrongCoverCoherence Cs B :
   S2357PerCoverCoherenceRequired B (StrongCover.cover Cs)`
   from `S2240ConeEssSurjAt_of_strongCover`.
5. `S2357StrongCoverPresentation Cs B A f g T ptA :
   EtaleStackBaseChangePresentation g.map T (S2130PtC f T ptA)`
   (S2240 strong-cover presentation).
6. `S2357StrongCoverPresentation_finiteEtale`:
   its projection is finite and etale.
7. `S2357CorrectedD6FirstMissing := ∀ B C, S2240ConeEssSurjAt B C`;
   no inhabitant asserted.

## Exact first missing

```text
S2357CorrectedD6FirstMissing
  = ∀ B C : S1728Cover, S2240ConeEssSurjAt B C
```

i.e. per-cover presentation cone essential surjectivity for every target
cover. Strong covers and coherent covers supply it
(`S2240ConeEssSurjAt_of_strongCover`, `S2240WitnessFor_coherent`); arbitrary
weak covers do not, as S2291/S2350 show.

The uniform replacement of `S2130P` by a graph/diagonal scheme cannot cover
arbitrary weak covers because `S2130ConcreteTwoPullback` is already empty at
the S2291 datum. The corrected route must be per-cover (S2240), with the
coherence obligation above or a chosen strong/coherent target family.

## Effect on D6(c) / S2086

The false uniform target `S2130ConcreteTwoPullback` is bypassed. For a fixed
strong target cover, S2240 gives an actual base-change presentation and finite
etale projection, which is the per-cover substitute for the
`S2086CospanGMapFiniteEtale` input. The global
`S2086CospanGMapFiniteEtale` (all target covers) is **not** obtained from this
route; its exact remaining input is the per-cover coherence above or a
strong/coherent cover supply. No uniform finite-etale claim is fabricated.

## Rejected routes

- graph/diagonal correction of `S2130P` retaining the recorded legs: refuted
  by S2350 (empty apex at S2291);
- using `S2130ConcreteTwoPullback`: false;
- declaring `S2240ConeEssSurjAt` for all covers: not available;
- terminal/point stack or metadata signature: irrelevant and not used.

## Consumer

`S2357StrongCoverPresentation` and
`S2357StrongCoverPresentation_finiteEtale` feed a per-cover D6(c)
finite-etale package for strong target covers; the uniform D6(c) consumer
requires `S2357CorrectedD6FirstMissing` or an equivalent strong/coherent
target supply.

## Reports read

`coord/reports/S2310...` (S2291/S2350 audit), S2240 strict-cone report, and
the S2130/S2086 definitions above.
