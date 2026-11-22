# Root normalized-log equality: consumption audit

## 1. The equality target

RootNormalizedThetaHullActual.rootThetaHullNormalizedLog_eq_formula_of_gap proves

  rootThetaHullNormalizedLog mu = rootThetaHullFormulaLog

from the conditional gap data RootThetaHullNormalizationGap.

## 2. Consumer trace

No final xi-f consumer uses this equality.

- PaperXiFClosedActual.paperXiF_actual consumes
  globalQPilotLog and globalThetaHullLog, plus
  nativeQVPilotNormalizedSignedLogVolume. It does not import
  RootNormalizedThetaHullActual.
- PerBXiFScalarActual.paperXiF_root consumes globalRootLog and paperRootQ,
  not rootThetaHullNormalizedLog or rootThetaHullFormulaLog.
- PerBRootXiFScalarData packages globalRootLog, not the root hull normalized
  log equality.
- PaperLevelXiFTargetActual uses actualLocalHullLog directly via
  arithmeticTupleNormalizedLogVolume on the root hull region. Its target is an
  inequality ActualPaperXiFTarget, not an equality to rootThetaHullFormulaLog.
- RootTensorBlockLGapActual imports RootNormalizedThetaHullActual but does not
  use rootThetaHullNormalizedLog_eq_formula_of_gap; it only records the exact
  object-level gap for a tensor block over the algebraic closure.
- A repository-wide search finds no occurrence of
  rootThetaHullNormalizedLog_eq_formula_of_gap outside its defining file.

Therefore the equality target is not consumed by the final xi-f scalar. It is
an optional normalization identity, not a minimal dependency.

## 3. What final xi-f actually needs

The final scalar needs:

1. an actual root hull region on the per-b tensor block;
2. the actual normalized log-volume on that region
   (or the actual Haar measure);
3. a monotonicity comparison from an actual inclusion of regions, using
   arithmeticTupleNormalizedLogVolume_mono / Haar measure monotonicity;
4. the actual q-pilot scalar and the sign comparison.

It does not need the equality of that normalized log-volume with the
coefficient formula. The coefficient formula is a computational witness, not the
definition of the consumed scalar.

## 4. Minimal replacement

Delete the equality target and the equality-only gap fields:

- rootThetaHullNormalizedLog_eq_formula_of_gap;
- the equality part of RootThetaHullNormalizationGap
  (rootHull_eq_minimalRegion and scalingData) if only the equality uses them.

Keep or add only:

- rootThetaHull and rootThetaRegion as actual regions;
- a monotonicity theorem of the form
    arithmeticTupleNormalizedLogVolume_mono ... hsubset hpos hfin
  for the actual region inclusion;
- the actual Haar positivity/finiteness fields needed for that monotonicity;
- the actual formula rootThetaHullFormulaLog only as a separate computational
  scalar, not asserted equal to the normalized log.

## 5. Conclusion

The equality rootThetaHullNormalizedLog = rootThetaHullFormulaLog is not on the
final xi-f dependency path. Its removal is safe for the scalar target.
Use monotonicity of the actual normalized log-volume instead of proving the
equality. No fake equality or assumption is needed.
