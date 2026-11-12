# S1179: evaluation / sourceEvaluationLink / upperEnv provenance audit

Date: 2026-10-30. Search scope: LeanFormal/IUT, plus the interpretation file.

## 1. Search result

| name | occurrences in LeanFormal |
|---|---|
| `evaluationOperation` | 0 |
| `sourceEvaluationLink` | 0 |
| `evaluationArrow` / `evaluation_arrow` | 0 |
| `upperEnv` | 23, all diagram fields/lemmas in SourceFTimesMuPrimeStripPolyIsomorphism plus the current SourceOutputPrimeStripInterpretation field |
| `AlgorithmicProvenance` | only the audit card `iplAlgorithmicProvenanceCard` |

No actual operation-level evaluation producer exists.

## 2. Actual declarations that can be reused

`SourceFTimesMuPrimeStripPolyIsomorphism.lean`

- `SourceFTimesMuPrimeStripRem3102Diagram.upperEnv` (field, :815);
- `iplLink` (:845), `lowerEnv_symm_verticalEnv_upperEnv` (:856), `iplLink` cancellation lemmas;
- `SourceFTimesMuPrimeStripEquivalence.canonicalLift` (:343);
- `SourceFTimesMuPrimeStripFullPolyIsomorphism.canonical_trans` (:675), `comp_assoc` (:627).

`SourceH1H2Construction.lean`

- `fPrimeStripAt` (:52), `fLinkAt` (:165).

`SourceKummerEvaluationArrows.lean`

- `SourceEvaluationArrow` (:290): fields `stripIso : FPrimeStripEquiv upper lower` and `unitPortion : SourceEvaluationUnitPortion`;
- `SourceEvaluationUnitPortion` (:249): per-place unit-layer isomorphism/equivariance;
- `SourceKummerEvaluationSquare` (:347): upper/lower horizontals, left/right Kummer arrows, `commutes`;
- `domainExpression_eq_codomainExpression` (:385) actual;
- `sourceEvaluationArrow_self` (:318): only the identity/trivial gate, not a source evaluation.

`SourceLinkFactorization` (:418) is the frozen IPL composite, conditional on supplied arrows.

## 3. Exact first gap

Target object:

  SourceEvaluationArrow G (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)

For the upperEnv of the first joint square.  Existing actual candidate:

  stripIso := I.fLinkAt 1 0 1 1  (an F-prime-strip link)

The exact missing data is the actual `SourceEvaluationUnitPortion` (Card EV)
for this strip iso, together with provenance that the strip iso is produced
by the selected source evaluation operation.

First precise source sublemma:

  SourceEvaluationUnitPortion G (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
  with source/target unit actions and per-place equivariant unit-layer
  isomorphism, induced by the actual source evaluation operation.

None of the fields is currently constructed: the tree has only
`sourceEvaluationArrow_self` with trivial actions and identity unit layer.

The adjacent Kummer square then additionally needs:

- left Kummer arrow `SourceKummerArrow G lowerLeft (I.fPrimeStripAt 1 0)`;
- right Kummer arrow `SourceKummerArrow G lowerRight (I.fPrimeStripAt 1 1)`;
- the conjugation law with the same upperEnv stripIso.

No actual source Kummer arrows are constructed; `SourceKummerEvaluationArrows`
only freezes the records.

## 4. Current SourceOutputPrimeStripInterpretation.lean

The current file (read at this audit) defines a structure with fields
`run`, `inputStrip`, `outputStrip`, `evaluation`, `square`, and a `Consumer`
Prop.  `evaluation` is a field, not constructed; `Consumer` restates the square
equality.  This is the kind of weak wrapper that must not be counted as
progress.  It does not construct the actual evaluation, does not identify
`pilot strips` with source strips, and does not connect to a SourceRun output.

Its only useful content is the exact residual type:

  SourceEvaluationArrow G inputStrip outputStrip

which is already the named gap above.  The file should not be cited as a
construction of upperEnv.

## 5. LogKummerCorrespondenceFromSource

Source: `tmp/sheaf/xif/paper/LogKummerCorrespondenceFromSource.lean`.
It composes supplied source links (Kummer/evaluation data) but does not
construct the algorithm operation or prove that an `fLinkAt` is the actual
evaluation.  It therefore does not close the provenance gap.

## 6. Verdict

- actual: fPrimeStripAt/fLinkAt; canonicalLift and full-poly category;
  SourceEvaluationArrow record; sourceEvaluationArrow_self gate only;
  SourceKummerEvaluationSquare record and its two-path equality; iplLink
  conditional on diagram data.
- exact first gap: actual `SourceEvaluationUnitPortion` for
  `I.fLinkAt 1 0 1 1`, with source-operation provenance, plus Kummer arrows
  for the adjacent square.
- no actual `SourceRun`/`evaluationOperation`; the current interpretation file
  is a wrapper and is not counted.

