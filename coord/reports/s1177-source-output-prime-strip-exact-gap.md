# S1177/S1180: SourceOutputPrimeStripInterpretation — exact first gap

Scope: only `SourceOutputPrimeStripInterpretation.lean`; no new weak Lean wrappers.
Read: `coord/reports/source-compute-integration-20261030.md`,
`coord/reports/supplement-gap-priorities-20261030.md`,
`SourceKummerEvaluationArrows.lean`, `SourceEvaluationUnitPortionConjugation.lean`,
`LocalIntegralUnitEvaluationImage.lean`, `SourceMultiradialPresentationWiring.lean`.

## Result

No actual `SourceOutputPrimeStripInterpretation` construction is available yet.
The first honest stop is the existing exact type

```text
Theorem311Source.SourceEvaluationUnitPortion G upper lower
```

for the actual non-self strips produced by a source run.  We did **not** add a
new Prop/Nonempty/True wrapper for it.

## Three deliverables and status

### 1. Actual evaluation input/output strips and evaluation data

Actual and reusable:

- `I.fPrimeStripAt n m` gives the actual source F-prime-strips.
- `I.fLinkAt n m n' m'` gives actual F-prime-strip source links.
- `AlgorithmInput C` / `runAlgorithm C input` give the actual source
  algorithm input and output target.
- `S1170RouteTraceAuditActual.routeTrace` records intermediate choices and proves
  `endpoint = runAlgorithm.target` (EXIT=0).

Not actual: the paper evaluation arrow.  The existing
`SourceEvaluationArrow G upper lower` requires two fields:

```text
stripIso : FPrimeStripEquiv upper lower
unitPortion : SourceEvaluationUnitPortion G upper lower
```

The only existing inhabitant `sourceEvaluationArrow_self` uses
`FPrimeStripEquiv.refl` and trivial actions; its own docstring says it is a
gate-only witness and not the paper evaluation isomorphism.  The generic
`fLinkAt` can supply a candidate `stripIso`, but it does not supply the Card EV
unit portion or the operation provenance.

### 2. upperEnv and adjacent Kummer square

The upperEnv target type is:

```text
SourceEvaluationArrow G (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
```

The adjacent Kummer square requires additionally:

```text
SourceKummerArrow G upperLeft lowerLeft
SourceKummerArrow G upperRight lowerRight
SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight
```

Each `SourceKummerArrow` itself requires a `SourceTimesMuKummerLayer G upper lower`,
whose field is

```text
kummer : ∀ v, TimesMuKummer.Isomorphism (sourceAction v) (targetAction v)
```

so the Kummer square is blocked before the square: the actual x-mu Kummer layer
at the source strips is not constructed.  The local comparison
`timesMuEvaluationComparison` in `LocalIntegralUnitEvaluationImage.lean` is an
actual local p-adic evaluation/Kummer isomorphism, but no bridge from
`FPrimeStrip.Mon v` to that local monoid is present.

### 3. forget relation and downstream consumers

Actual:

```text
routeTrace_endpoint_eq_runAlgorithm_target :
  (routeTrace carrier input.route input.source).endpoint
    = (runAlgorithm carrier input).target
```

so the forget relation can use the actual route endpoint.  Consumers:

- `iplAlgorithmicProvenanceCard` (SourceMultiradialIplLinkWiring.lean:190);
- Step-XI `ipl : Prop` slot (Contract.lean:37-40);
- APT site assemblies (APT.lean:370, :395);
- capsule/tensor consumer: `SourceCapsulePacketActualBridge`
  (S1169, exact bridge structure; no inhabitant asserted).

No downstream consumer can be fed yet because the first evaluation unit portion
and the x-mu Kummer layer are missing.

## Exact first gap

The first non-circular sublemma is:

```text
SourceEvaluationUnitPortion G upper lower
```

for the actual `upper`, `lower` F-prime-strips of the run, with:

- `sourceAction : ∀ v, G →* MulAut ((upper.Mon v)ˣ)`
- `targetAction : ∀ v, G →* MulAut ((lower.Mon v)ˣ)`
- `unitLayer : ∀ v, TimesMuQuotient ((upper.Mon v)ˣ) ≃*
    TimesMuQuotient ((lower.Mon v)ˣ)`
- `unitLayer_equivariant`

What is missing to construct it: the actual x-mu unit action on the source
strips and the actual Kummer isomorphism at each v, not an arbitrary
`FPrimeStripEquiv` from `fLinkAt`.  `SourceEvaluationUnitPortion.ofKummerLayer`
already reduces this to `SourceTimesMuKummerLayer G upper lower`; that layer is
the exact source obligation.

## Not done / not to do

- No new `compatible : Prop`, `isActual : Prop`, `Nonempty` gate, `True`, or
  `PUnit` construction.
- No wrapper that says "candidate square exists" after taking `hsq` as an
  assumption; S1168's candidate square is only a candidate-link path identity.
- No `Classical.choice` strip map.
- No arbitrary identification of `fLinkAt` with the actual evaluation arrow.

## Next minimal actual work

1. Construct `SourceTimesMuKummerLayer G upper lower` for the actual run strips
   by transporting the actual local `timesMuEvaluationComparison` to each
   `Mon v` (or record the exact missing transport if it does not exist).
2. From that layer, `SourceEvaluationUnitPortion.ofKummerLayer` gives the Card EV
   unit portion; combine with the candidate `fLinkAt` stripIso to get a
   `SourceEvaluationArrow`.
3. Prove the Kummer square and the operation provenance; only then attempt
   `SourceOutputPrimeStripInterpretation`.

Until step 1 is actual, no Lean file is written here.
