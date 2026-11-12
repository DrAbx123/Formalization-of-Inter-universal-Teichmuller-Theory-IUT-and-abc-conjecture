# S1159: SourceRun C m shape

Read for this report:
- `coord/reports/s1157-next-package-acceptance.md`
- `LeanFormal/IUT/IUTIII/Theorem311/ParametricCarrier.lean` (Carrier, AlgorithmInput,
  AlgorithmOutput, runAlgorithm, routeTarget, applyStep/applyRoute)
- `LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialPresentationWiring.lean`
  (SourceProcessionAutomorphismData, Ind2ActionData, sourcePresentationOfCarrier,
  sourceAlgorithmOfCarrier)
- `SourceMultiradialIplLinkWiring.lean:190` (iplAlgorithmicProvenanceCard)

Report only; no Lean file changed.

## 1. Real field shape

Parameter: a source carrier `C : ParametricTheorem311.Carrier Label Choice`,
the source `I`, the label parameter `n : Int`, groups `G₁, G₂`.

```text
structure SourceRun
    (C : ParametricTheorem311.Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData C G₁)
    (ind2Data : Ind2ActionData C autom G₂)
    (input : ParametricTheorem311.AlgorithmInput C) where
  output : ParametricTheorem311.AlgorithmOutput C input
  output_eq : output = ParametricTheorem311.runAlgorithm C input
  presentation : SourceTheorem311MultiradialPresentation G₁ I n Choice
  presentation_eq : presentation =
    sourcePresentationOfCarrier (I := I) (n := n) C autom input
  algorithm : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Choice
  algorithm_eq : algorithm =
    sourceAlgorithmOfCarrier (I := I) (n := n) C autom ind2Data input
```

This is the part that is **actual today**:

- `AlgorithmInput C` has real fields
  `source : Choice`, `route : List (RouteStep Label)`,
  `source_image_nonempty`.
- `runAlgorithm` is an actual `AlgorithmOutput C input`.
- `sourcePresentationOfCarrier` and `sourceAlgorithmOfCarrier` are actual
  definitions from W.1/W.4 data.
- All three equalities are `rfl`.

The fields proposed by the previous checklist map as follows.

| S1157 field | Real source | Status |
|---|---|---|
| input | `AlgorithmInput C` (`source`, `route`, nonempty image) | actual |
| legal choices | `input.route : List (RouteStep Label)` plus `input.source` | actual |
| operation outputs | `output.target = runAlgorithm C input .target` (final) | actual |
| intermediate outputs | a new `routeTrace : List Choice` over the route | constructible; not in tree as a named function |
| strip interpretation | no `Choice -> SourceFTimesMuPrimeStrip V` in tree | exact gap |
| forgetRun | `fun r => r.output.target` | actual |
| Q ≤ H / q membership | absent by type | required absence |

## 2. First constructible actual fields

The immediately constructible package is:

```text
input        := input
output       := runAlgorithm C input
forgetRun    := fun r => r.output.target
forgetRun_of_source_execution := rfl   -- output is runAlgorithm
```

and the presentation/algorithm records:

```text
presentation := sourcePresentationOfCarrier C autom input
algorithm    := sourceAlgorithmOfCarrier C autom ind2Data input
```

So a `SourceRun` carrying input, final operation output, presentation,
algorithm record, and `forgetRun` is **actual and constructible now**, with no
extra assumptions beyond the carrier, W.1, W.4, and the algorithm input.
The intermediate `routeTrace` is a short recursive definition over
`List (RouteStep Label)`; it is new auxiliary code, not a missing object.

## 3. Exact first gap: strip interpretation / diagram realization

The genuinely missing field is:

```text
stripOfChoice : Choice -> SourceFTimesMuPrimeStrip V
stripOfRun    : SourceRun ... -> SourceFTimesMuPrimeStrip V
diagramOfRun  : SourceRun ... -> Rem3102Diagram
```

No such functor exists in the tree.  The provenance card records three blocked
routes:
(a) direct functor from route operations/stages to `SourceFTimesMuPrimeStrip V`
    — no such functor and the reduced interface has no prime-strip object;
(b) through `FPrimeStripEquiv`/`canonicalLift` — no bridge
    `FPrimeStrip V -> Choice/Output` is modelled;
(c) through `SourcePolyIsoTransportLaws` O1-O4 — it takes transport data as
    fields and constructs no provenance.

Therefore the first exact gap is not "choose a strip arbitrarily"; it is:

```text
S1159OperationArrowRealization : Prop :=
  exists a realization of the four source arrows
    lowerEnv, verticalEnv, verticalGau, upperEnv
  from the actual operations of the run,
  compatible with stripOfRun/diagramOfRun,
  and with the square lowerEnv >> verticalGau = verticalEnv >> upperEnv.
```

No inhabitant is asserted.  `forgetRun` is not the gap: it is actual now.

## 4. What must not be put in SourceRun

- `Q <= H`, final q membership, full source comparison.
- A generic `compatible : Prop` / `isActual : Prop` field.
- An arbitrary `stripOfRun` chosen by `Classical.choice` from `Nonempty`.
- A pre-existing diagram with `commEnv` used as the proof of the square.
- Renamed `fLinkAt`/self-conjugation/`canonicalLift` pretending to be the
  actual evaluation arrow.
- `True`/`PUnit`/toy carriers to fill the strip field.

## 5. Acceptance for this package

Actual part:

```text
SourceRun C autom ind2Data input        -- actual record
forgetRun                              -- actual
forgetRun_of_source_execution          -- rfl
presentation/algorithm equations       -- rfl
```

Exact part:

```text
stripOfChoice / stripOfRun / diagramOfRun
operation-arrow realization + commEnv square
```

Acceptance when either:
- actual part compiles with no forbidden fields and the exact gap is stated as
  a `Prop` with no inhabitant; or
- a deterministic operation chain constructs the four arrows and their square,
  then the diagram and `iplLink` provenance follow.

## 6. Consumers

- `iplAlgorithmicProvenanceCard` (SourceMultiradialIplLinkWiring.lean:190).
- Step-XI `ipl : Prop` slot (Contract.lean:37-40).
- APT site assemblies (APT.lean:370, :395).
- `IUT-III.source-APT-transport-supply` (APT.lean:457), (IPL) half only.

## 7. Next executable step

1. Implement the actual `SourceRun` record and `forgetRun`/`routeTrace`
   (input, output, presentation, algorithm; no strip field).
2. State the exact `stripOfChoice`/operation-arrow realization Prop.
3. Only then attempt the specific square; do not fill it from a generic
   `commEnv` or an arbitrary strip choice.
