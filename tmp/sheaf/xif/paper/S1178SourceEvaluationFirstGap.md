# S1178: first missing source evaluation operation

Scope: only `sourceEvaluationLink_generated` (first gap).  No weak Lean.

## Search result

Executed searches under `LeanFormal/IUT` and `tmp/sheaf/xif/paper`:

```text
evaluationOperation       0 hits
sourceEvaluationLink      0 hits
EvaluationOperation       0 hits
```

Existing related declarations:

- `LogKummerCorrespondenceFromSource.actualIPLEvaluationLink`
  = `I.fLinkAt 0 0 1 0` (generic source strip link);
- `actualIPLEvaluationUnit` = conjugated self evaluation unit portion;
- `actualIPLEvaluationArrow` = `sourceEvaluationArrowOfUnitPortion` of the two;
- `SourceH1H2Construction.fLinkAt n m n' m'` = `I.primeStripLinkAt n m n' m'`
  (generic source link, not an algorithm operation);
- `SourceOutputWiring.sourceEvaluationBridgeOfVertical` = identity
  `EvaluationSystem Choice` / identity horizontal link (a wiring slot, not
  the source evaluation operation).

Conclusion: no actual `evaluationOperation` and no actual `sourceEvaluationLink`
exists in the tree.  The candidate arrow is generic `fLinkAt`; it cannot be
renamed to the algorithm evaluation.

## First exact gap

### Object

```text
evaluationOperation (run) :
  a source operation attached to one actual Theorem 3.11 algorithm run,
  whose evaluation data is a SourceEvaluationArrow
    (inputStrip run) (outputStrip run)
  with stripIso : FPrimeStripEquiv (inputStrip run) (outputStrip run)
  and unitPortion : SourceEvaluationUnitPortion ...
```

### Quantifier

```text
for every actual source input I : OriginalInput l V,
for every actual algorithm run (carrier, autom, ind2Data, input),
there is an evaluation operation of that run, not an arbitrary generic link.
```

Equivalently, first sublemma:

```text
sourceEvaluationLink_generated :
  I.fLinkAt 0 0 1 0 =
    (sourceEvaluationLink (evaluationOperation run)).stripIso
```

and the unit-portion compatibility:

```text
sourceEvaluationUnit_generated :
  actualIPLEvaluationUnit = (sourceEvaluationLink (evaluationOperation run)).unitPortion
```

Neither can be stated with current data because `SourceRun` /
`evaluationOperation` do not exist.

### Consumer

Direct consumer: `iplAlgorithmicProvenanceCard`
(`SourceMultiradialIplLinkWiring.lean:190`, status `pending`).
Through it: `upperEnv` of `SourceFTimesMuPrimeStripRem3102Diagram`
(`SourceFTimesMuPrimeStripPolyIsomorphism.lean:805`) and its `commEnv` square;
then `iplLink` (`:845`) and the Step-XI `ipl` slot
(`Contract.lean:37-40`), plus `APT.lean:370`, `:395`, and
`IUT-III.source-APT-transport-supply` (`APT.lean:457`).

## What is not the first gap

`SourceEvaluationArrow` and `SourceEvaluationUnitPortion` are actual structures
and are not missing.  `actualIPLEvaluationArrow` is an actual inhabitant of
`SourceEvaluationArrow`; its provenance is the gap, not its type.

`fLinkAt` is an actual `FPrimeStripEquiv`, but it is a source prime-strip link,
not an operation of the algorithm; using it as `upperEnv` would identify a
generic link with the algorithm evaluation, which the report explicitly forbids.

## Exact minimum

```text
1. actual source-side run record with input/output strips;
2. evaluationOperation of that run;
3. sourceEvaluationLink (evaluationOperation) : SourceEvaluationArrow;
4. proof its stripIso/unitPortion are the diagram upperEnv data;
5. then adjacent Kummer square lowerEnv ≫ verticalGau = verticalEnv ≫ upperEnv.
```

Status: exact stop.  No Lean file written, no `compatible`/`Nonempty` gate,
no compile claim.
