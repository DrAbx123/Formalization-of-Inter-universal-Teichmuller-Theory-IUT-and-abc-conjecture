# SourceOutputPrimeStripInterpretation: exact stop

Package: first joint of `coord/reports/source-compute-integration-20261030.md` §2.
Named consumer: `LeanFormal.IUT.Audit.iplAlgorithmicProvenanceCard`
(`SourceMultiradialIplLinkWiring.lean:190`).

## Verdict

No actual source evaluation construction exists in the current tree.  The only
available evaluation data is generic `fLinkAt` / self-conjugation:
`LogKummerCorrespondenceFromSource.actualIPLEvaluationArrow` is built from
`I.fLinkAt 0 0 1 0` and `selfEvaluationUnitPortion`, not from an algorithm
operation of the Theorem 3.11 construction.  Therefore this package stops at the
first source-evaluation sublemma; it does not define a weak `SourceRun`,
`compatible` Prop, `Nonempty` gate, or forget wrapper.

## 1. Input/output strips and existing evaluation data

Actual source strips (from `OriginalInput`):

```text
bottomEnv  = I.fPrimeStripAt 1 0
bottomGau  = I.fPrimeStripAt 1 1
topEnv     = I.fPrimeStripAt 0 0
topGau     = I.fPrimeStripAt 1 0
```

Existing candidate evaluation arrow:

```text
actualIPLEvaluationLink :
  FPrimeStripEquiv (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 1 0)
  := I.fLinkAt 0 0 1 0

actualIPLEvaluationUnit :
  SourceEvaluationUnitPortion ...
  := actualEvaluationUnitOf ... (I.fLinkAt 1 0 0 0) (I.fLinkAt 1 0 1 0)

actualIPLEvaluationArrow :
  SourceEvaluationArrow ...
  := sourceEvaluationArrowOfUnitPortion actualIPLEvaluationLink actualIPLEvaluationUnit
```

These are actual `FPrimeStripEquiv`/unit-portion data, but they are **not**
constructed from a source evaluation operation.  The existing links are generic
`fLinkAt`; renaming them as the algorithm evaluation is forbidden.

## 2. First unconstructed source evaluation sublemma

Exact missing statement:

```text
sourceEvaluationLink_generated :
  I.fLinkAt 0 0 1 0 =
    sourceEvaluationOperation (this run's evaluation operation)
```

Missing objects:

```text
run : SourceRun C m                 -- source-side run keeping actual data
evaluationOperation (run)          -- actual evaluation operation, not generic link
sourceEvaluationLink (evaluationOperation) :
  FPrimeStripEquiv (inputStrip run) (outputStrip run)
```

Current tree has no `SourceRun`, no evaluation operation, and no operation
whose output is an `FPrimeStripEquiv`.  This is the first gap; it precedes
`upperEnv` and the Kummer square.

## 3. upperEnv and adjacent Kummer square (exact target, not constructed)

Given the missing evaluation operation, the target upperEnv is:

```text
upperEnv : topEnv → topGau
upperEnv = toFullPolyIso (sourceEvaluationLink (evaluationOperation))
```

Adjacent square target (`SourceFTimesMuPrimeStripRem3102Diagram.commEnv`):

```text
lowerEnv ≫ₜ verticalGau = verticalEnv ≫ₜ upperEnv
```

Available actual arrows for the other three sides:

- `lowerEnv` candidate: `I.fLinkAt 1 0 1 1` (actual);
- `verticalEnv` candidate: `I.fLinkAt 1 0 0 0` (actual);
- `verticalGau` candidate: `I.fLinkAt 1 1 0 0` if present (exact check needed),
  otherwise the square is not even statable at this interface.

The square cannot be proved by `rfl`: the missing `upperEnv` is not the
composite of the other three sides.  Defining it as that composite and then
using `rfl` would be exactly the forbidden fake.

## 4. Forget relation and downstream consumers

Existing reduced output:

```text
ParametricTheorem311.runAlgorithm carrier input
  : AlgorithmOutput carrier input
target : Choice
```

Required forget relation (currently unstatable):

```text
forgetRun : SourceRun C m → Choice
forgetRun_of_source_execution :
  forgetRun (runSource C m input) = (runAlgorithm carrier input).target
```

Why unstatable: `SourceRun` would need a source-side run record, but the
current algorithm only carries `Choice`/`List RouteStep`; no `Choice →
FPrimeStrip V` map exists.  The first forget target already fails at the run's
initial source choice, before any operation.

Downstream consumers:

- `iplAlgorithmicProvenanceCard` (`SourceMultiradialIplLinkWiring.lean:190`)
  currently `status := pending`; it needs the operation-to-arrow realization.
- Step-XI contract `ipl : Prop` slot (`Contract.lean:37-40`);
- APT site assemblies (`APT.lean:370`, `:395`) use the `ipl` hypothesis;
- `IUT-III.source-APT-transport-supply` (`APT.lean:457`) consumes the (IPL)
  half.

## 5. Reusable actual donors (not enough)

- `ParametricCarrier.runAlgorithm`, `routeTarget`, `AlgorithmOutput`: actual,
  but only on `Choice`.
- `SourceMultiradialPresentationWiring.automorphism_runAlgorithm_target`: actual,
  but only at `Choice` level.
- `LogKummerCorrespondenceFromSource.actualIPLEvaluationArrow`: actual generic
  `fLinkAt` evaluation data, not source-operation provenance.
- `SourceFTimesMuPrimeStripRem3102Diagram`/`iplLink`: actual diagram/poly-iso
  composition, given eight strips and arrows.
- `SourceFTimesMuPrimeStripEquivalence.canonicalLift`: actual strip-level lift,
  but no bridge to `Choice`/output.

## 6. Exact minimum for reopening

```text
1. SourceRun on the source side, keeping input strip, operation chain, and
   output strip (not a Prop wrapper);
2. a map from the actual evaluation operation to
   FPrimeStripEquiv (inputStrip) (outputStrip);
3. the theorem that this source link equals the diagram's upperEnv;
4. the three adjacent arrows and commEnv square;
5. a forget map to Choice with proof it equals runAlgorithm.target.
```

No Lean file is delivered as an object because every available Lean encoding
would be a weak wrapper.  Exact stop: `sourceEvaluationLink_generated`.
