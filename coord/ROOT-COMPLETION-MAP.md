# ROOT-COMPLETION-MAP — search for `rootNormedExtension → CommonPrimeCompletion` (A1062)

Status: read-only; no compile.  Resolves the obstruction in `Mzk1QRegionConstructActual`.

## 1. Direct search result

Searched `tmp/sheaf/xif/paper` and `LeanFormal` for
`rootNormedExtension`, `sourceRootField`, `rootBase`, `CommonPrimeCompletion`,
`sourceRoot`, and for ring/unit equivs between them.

**No declaration maps `rootNormedExtension` (or `sourceRootField`) to a
`CommonPrimeCompletion`.**  The only related equivalence is
`PaperRootExtensionEquivActual.rootExtensionEquivRingEquiv` (`:39`):
```lean
RootExtension (G := G) v ≃+* SourceAlgebraicClosure (G.place v).val
```
which is an identity on a **common algebraic closure**, not a map to a
completion.  Its `rootExtensionEquivUnits` (`:48`) maps units between
algebraic-closure carriers, not into `CommonPrimeCompletion`.

## 2. Types

- `sourceRootField T b := NormalizedCompletion (qVFamTensorPlace T b)`
  (`PaperThetaRootObstructionActual:41`);
  `qVFamTensorPlace T b` is a finite place of `T.arithmetic.F`
  (`QVFamTensorCoefficientActual:47`).
- `rootNormedAmbient := AlgebraicClosure (sourceRootField T b)`;
  `rootNormedExtension := IntermediateField.adjoin ... {rootNormedElement}`
  (`PaperRootCompletionTensorActual:54-60`).
- `rootNormedUnit : (rootNormedExtension T b)ˣ` (`:120`);
- `C3LogShellFiberL i := CommonPrimeCompletion (C3LogShellPlaceL i)`
  (`Mzk1C3LogShellTensorLActual:40`);
- `CommonPrimeCompletion place = NormalizedCompletion place.val`
  (`FinitePlaceCommonPrimeCompletion:20`).

So `sourceRootField` is a **base completion**, while `rootNormedExtension` is
a finite extension of it; the qroot is in the extension, not in the base
completion.  A ring hom `rootNormedExtension → CommonPrimeCompletion` would
require an embedding of the extension into the same completion, which is not
available from the C3 L record.

## 3. Possible compositions

- `sourceRootField ≃+* NormalizedCompletion (C3LogShellPlaceL i)`
  would identify the base completions, but it does **not** map `rootNormedUnit`
  (an extension element) into the completion.
- `PaperRootExtensionEquivActual` maps `RootExtension` to
  `SourceAlgebraicClosure`, and `rootExtensionNorm` uses the source norm;
  this is the algebraic-closure side, not `CommonPrimeCompletion`.
- `FinitePlaceCommonPrimeCompletion.commonPrimeCompletionRingEquiv`
  (`:63`) is only `CommonPrimeCompletion place ≃+* NormalizedCompletion place.val`
  (identity), not a root-extension map.

Thus no composition gives `rootNormedUnit → (CommonPrimeCompletion)ˣ`.

## 4. Minimal honest declarations

The qroot does **not** live in the C3 base completion; two honest routes:

### Route A: value-group/log-volume scaling (recommended)
Define the qroot action through its **order/log-volume**, not as a field unit:
```lean
-- root order from the actual root, e.g. localNormOrder or rootNormedLogVolume
noncomputable def qRootLogOrder (T : SourceNativeInitialThetaData l)
    (b : Bad (nativePlaceSelection T)) : ℝ :=
  localNormOrder (qVFamTensorP T b) (rootNormedElement T b)

-- a real-exponent scaling on the C3 log-shell region
def qPilotScaledRegion (alpha : ℝ) : Set (C3LogShellTensorBlockL C3L) :=
  {x | ∃ y ∈ actualC3LogShellTensorRegionL C3L, x = ... }
```
Then the Haar/log-volume scaling law is proved via the local norm, not via a
field unit.  This matches the actual role of qroot in `S3050Unit`/theta
scalings and avoids the extension/completion mismatch.

### Route B: base-change the C3 tensor block to the root extension
Replace the C3 fibers `CommonPrimeCompletion (C3LogShellPlaceL i)` by
completions of the root extension at places above them; this is a new
tensor-block construction (`C3LogShellTensorBlockL` base-changed to L), not
present.

Minimal declarations for Route B:
1. `rootExtension ≃+*` a completion of the extension;
2. a place map from C3 tensor indices to extension places;
3. base-changed tensor block and Haar measure;
4. region scaling by the root unit.

## 5. Verdict

- No existing map/equivalence from `rootNormedExtension` to
  `CommonPrimeCompletion`; `PaperRootExtensionEquivActual` only identifies
  algebraic-closure carriers.
- The obstruction is not merely a missing `def`: the qroot is an extension
  element, while C3 block fibers are **base** completions.  A ring/unit map
  would need a chosen embedding of the extension into the base completion
  (not available).
- Honest minimal path: use the **value-group/log-volume** of qroot (Route A)
  for a real scaling on the log-shell region; or base-change the tensor block
  to the root extension (Route B, a new construction).
- Therefore `Mzk1QRegionConstructActual`'s `e : Block ≃L Block` parameter is
  the correct honest fallback; it should be documented as a placeholder for
  Route A/B, not as a qroot field action.
