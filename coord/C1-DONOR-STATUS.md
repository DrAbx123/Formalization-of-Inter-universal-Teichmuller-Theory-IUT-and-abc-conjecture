# C1 donor conditional formalization: status (A962)

## State

Draft file `tmp/sheaf/xif/paper/Mzk1C1DonorConditionalActual.lean` is written but NOT
compiling (EXIT=1).  No conditional theorem has been claimed; the draft is not green and
must not be used as evidence.

## Structures read (source facts)

- `NativeC1PaperSource` (`tmp/sheaf/n8/closure/NativeC1PaperSource.lean:51`) has five fields:
  `X : N8NativeInput l`, `S : NativeSourceAssembly X.S`,
  `e : X.family.index ≃ SourceTheorem311Index`,
  `R : NativeImageRealizationSourceFields X`,
  `F : NativeFiberSourceFields X`;
  plus `donors : P6BridgeDonors P.X` (:78), `c1ActualData` (:87) and
  `sourceInputBindingOfNativeDonors` (:91).
- The primitive/positive-real-action content is exactly `R.posRealAction` and its
  `degree_of_q` compatibility (`NativeBindingRFActual:50-55`); the fiber comparison is
  `F.fiberMonEquiv` (`:67-71`).

## Precise first errors (in order)

1. `NativeImageRealizationSourceFields` is NOT unary: its type is
   `Theorem311Source.OriginalInput l (NativePlaces X.S) → Type` (an explicit `I` argument).
   Fixed by adding `I : OriginalInput l (NativePlaces X.S)` and using
   `NativeImageRealizationSourceFields X I`.
2. `NativeSourceAssembly` lives in namespace `LeanFormal.IUT.N8Closure.C1Actual`;
   `N8NativeInput` in `LeanFormal.IUT.N8Closure.NativeInput`;
   `NativeImageRealizationSourceFields`/`NativeFiberSourceFields` in
   `LeanFormal.IUT.N8Closure.NativeBindingRFActual`; `SourceTheorem311Index` in
   `LeanFormal.IUT.Theorem311Source.OriginalInput`.  Opens were added accordingly.
3. Remaining (current) error: the `F : NativeFiberSourceFields X I e` field application is
   still rejected (`Function expected at ...`), i.e. the parameter shape of
   `NativeFiberSourceFields` differs from (X, I, e) assumption; also the full name of the
   structure is `LeanFormal.IUT.N8Closure.NativeC1PaperSource.NativeC1PaperSource`
   (namespace equals structure name), which needs careful qualification.

## Conclusion

- The conditional construction is NOT formalized in this pass (stopped at the
  `NativeFiberSourceFields` parameter-shape / name-resolution blocker).
- No mathematical obstruction identified; only elaboration/parameter-order work remains.
- Next step: inspect `NativeFiberSourceFields` binder order (read its full declaration) and
  the exact section-variable list around `NativeC1PaperSource` structure (which `I` it
  binds), then qualify names with the full namespace
  `LeanFormal.IUT.N8Closure.NativeC1PaperSource`.
- No sorry/axiom added; the draft is unregistered (compiles not).
