# P6 relaxed semantics audit — reference=region degenerates Theta/Values

- date: 2026-10-24
- scope: actual relaxed P6 readout / global relaxed readout / relaxed route
  obligations and their C9 destination.
- Lean changes: **none**. This is a semantic audit of the current tree.

## Files audited

- `tmp/sheaf/n8/closure/P6L.lean` — `ellOut` definition.
- `tmp/sheaf/n8/closure/P6AdmRedesign.lean` — `RelaxedP6Readout`,
  `relaxedP6Readout`.
- `tmp/sheaf/n8/closure/P6RelaxedReadoutActual.lean` —
  `RelaxedAdmFinite`, `relaxedFiniteEllOut`, `relaxedFiniteReadout`.
- `tmp/sheaf/n8/closure/P6RelaxedGlobalReadout.lean` —
  `ArchReadout`, `RelaxedGlobalReadout`, `missing_archReadout`.
- `tmp/sheaf/n8/closure/P6ArchReadoutActual.lean` —
  `archEllOut`, `archReadout`.
- `tmp/sheaf/n8/closure/P6RelaxedGlobalReadoutActual.lean` —
  `relaxedGlobalReadoutActual`.
- `tmp/sheaf/n8/closure/P6RelaxedGlobalNumerical.lean` —
  `NumericalGlobalReadout`, `numericalGlobalReadout`.
- `tmp/sheaf/n8/closure/P6RelaxedSourceRouteIntegration.lean` —
  `RelaxedRouteObligations`, `relaxedRouteActual`,
  `RelaxedC9PaperTarget`.
- `tmp/sheaf/n8/closure/P6RelaxedReadoutRouteIntegration.lean` —
  `relaxedP6ReadoutOfGlobal`, `relaxedRouteActualGlobal`.

## The formula

`P6L.lean:67` defines

```text
ellOut support weight dimension reference region
  = sum_{v in support} weight v *
      ( log (mu v (region v)) - log (mu v (reference v)) ) / dimension v.
```

Every actual relaxed construction uses the same set for `reference` and
`region`:

- `P6AdmRedesign.relaxedP6Readout` (lines 143-157): both are
  `fun v => Metric.ball 0 1`.
- `P6RelaxedReadoutActual.relaxedFiniteReadout` (lines 134-155): both are
  `fun v => unitSphereAt v`.
- `P6RelaxedGlobalReadout.archClosedBall` is used as both reference and region
  in `archAdm_closedBall`; `P6ArchReadoutActual.archReadout` uses the same
  `archClosedBall` for reference and region.
- `P6RelaxedGlobalClosed.archReadoutClosed` also uses `archUnitBall` twice.
- `P6RelaxedGlobalReadoutActual.relaxedGlobalReadoutActual` combines the above
  finite and archimedean components.

Therefore each summand is

```text
weight v * (log (mu v (S v)) - log (mu v (S v))) / dimension v = 0.
```

Hence:

1. `relaxedFiniteReadout.value = 0` for every native input satisfying the
   listed hypotheses.
2. `archReadout.value = 0` (in fact its support is `∅`).
3. `numericalGlobalReadout.value = finite.value + arch.value = 0`.
4. `RelaxedRouteObligations.Theta` is defined as `readout.value`; for
   `relaxedRouteActual` the readout is `P6AdmRedesign.relaxedP6Readout`, so
   `Theta = 0`.
5. `relaxedP6ReadoutOfGlobal` combines `combinedReference` and
   `combinedRegion`; with `G.finite.reference = G.finite.region` and the same
   `archClosedBall` on the archimedean branch, these functions are equal, so
   `ellOut = 0` again. Thus `relaxedRouteActualGlobal` has `Theta = 0`.

This is not a hidden numeric accident: it is forced by the identity
`reference = region` in all actual constructors. The earlier archimedean
"gap" is replaced by actual data, but the actual data is the same set twice.

## Values degeneracy

`C9QThetaValuesNamed.ValuesNamed` is the set of `P6Readout.ellOutValue`
images. Once the route readout has `value = 0`, every image is `0`; the
relaxed analogue therefore has

```text
Values = {0}   (for the actual relaxed readout)
```

if C9 is instantiated with the relaxed route. Consequences:

- `ValuesBounded` (`∀ z ∈ Values, z <= Theta`) becomes `0 <= 0`, i.e.
  trivial.
- Any statement that every actual value is bounded by `Theta` becomes
  vacuous, because the only value is the boundary point `0`.
- If a destination also asks `Q <= Theta`, it becomes `Q <= 0`; for a positive
  actual q-pilot scalar this is not the paper inequality, and may be false.
  It is not a legitimate strengthening/weakening of the paper comparison.

## Destination weakening

- `RelaxedRouteObligations` has exactly `chainA` and `readout`; its `Theta`
  is the relaxed readout value (zero for all actual constructors).
- `RelaxedC9PaperTarget` contains `route` and `jRange_eq : JRange = Set.univ`.
  It does **not** contain `q_le_theta`; the destination is already weakened by
  omission of the paper inequality, while its `Theta` is zero.
- `JRange = Set.univ` admits every source-allowed output, so the "range"
  condition is also vacuous.
- `NumericalGlobalReadout.value = 0` supplies a numerically concrete but
  semantically degenerate value.
- The old frozen `P6Readout` avoids this only by a.e. localLog=0 and was
  independently impossible at archimedean places; replacing it with
  `reference=region` makes `ellOut` zero instead of solving the readout.

**Verdict: the actual relaxed destination is semantically weakened /
degenerate.** The reference-relative relaxation removed the a.e.-zero log
condition but did not produce a distinct region with a nontrivial signed
readout. A zero `Theta` makes Values/Bounded/Q<=Theta trivial or false, not
paper-equivalent.

## Decisive correction requirements

The relaxation must be rebuilt with actual, distinct, positive-finite Haar
regions and a genuinely nonzero readout. Concretely, a corrected target must
provide:

1. **Different actual region**: for every supported place, an actual
   `region v` distinct from `reference v` (or at least
   `mu v (region v) != mu v (reference v)`), both measurable with
   `0 < mu v ... < top`. The finite and archimedean branches should not reuse
   the same ball/sphere.
2. **Nonzero readout**: the corrected `ellOut` must be computed from the
   distinct regions and must be accompanied by at least one of:
   - `value != 0`, and ideally an actual nonzero lower/upper bound;
   - a proof that the actual construction realizes the paper's `ell_out`
     (not merely the definitional formula).
3. **Nondegenerate Values**: `Values` must be the image of the corrected
   nonzero readout, not `{0}`; `ValuesBounded` must not reduce to
   `0 <= Theta`.
4. **Nonempty actual support**: the archimedean branch must use an actual
   nonempty support of infinite places with actual multiplicities; the current
   `archReadout.support = ∅` is another zero source.
5. **Non-vacuous destination**: the corrected C9 target must contain the
   actual `Q <= Theta` comparison (or its actual signed source form), and
   `JRange` must not be `Set.univ` unless that is independently shown to be
   the source-allowed range.
6. **No reference=region regression**: add a target-level condition
   `reference != region` (or `mu region != mu reference`) so a future
   constructor cannot satisfy the target by collapsing the two sets.

Until these are supplied, any C9/N8/C10 closure using
`P6RelaxedSourceRouteIntegration.relaxedC9PaperTarget_actual` or
`P6RelaxedGlobalNumerical.numericalGlobalReadout` is a zero-Theta/zero-Value
closure and must not be counted as the paper comparison.

## Status

- statement_compiles: not applicable (audit only).
- proof_body_checked: not applicable.
- kernel_closed: not applicable.
- target_accepted: no; this audit rejects the current relaxed readout semantics.
- production/tmp Lean files changed: none.
