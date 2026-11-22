# S992/S993: final integration corrected

Date: 2026-10-30. Corrected after S990/S991 and S980 status fixes.
Only inequality.

## Actual inputs

* S990FiniteCarrierPositivityFinitenessActual has olean and supplies
  s990QPilotImage_measure_pos / s990TensorRegionHull_measure_lt_top and
  S990HullFinitenessInput.
* S980QPilotImagePositivityActual compiles and supplies
  s980FinalLImage_measure_pos from S980FinalLImageInteriorExactInput.
* S991S983LinkInputsActual has olean and constructs the concrete
  PaperXiFSourceLink from S983 inputs (hC3, hQ).
* S979TensorRegionHullInequalityActual supplies the region-image inequality
  and final conditional Cor312 assembly.

S988 was not needed; no missing-file claim is made for S990/S991 or S980.

## s992S979Hypotheses

From per-b:
* S980FinalLImageInteriorExactInput T b (D b);
* S990HullFinitenessInput T b (D b);
proves S979TensorRegionHypotheses T D, filling positivity via S980 and
finiteness via S990/S981.

## Concrete link

s992ConcreteLink P C3 Oa hC3 hQ :=
  s991PaperXiFSourceLink P C3 Oa hC3 hQ.
s992ConcreteLink_actual records Nonempty (PaperXiFSourceLink ...).

## Final theorem

paperCor312_of_finiteCarrierExact:
  Oa, hC3, hQ (concrete S991 inputs) ->
  D -> hpos (S980) -> hfin (S990) ->
  explicit link : PaperXiFSourceLink O P C3 ->
  hlink -> finite links ->
  tensorRegionHullPaperWeightedInequality T D
    and Cor312Conclusion.

The explicit link may be the S991 concrete link; inequality part is S979/S962,
no equality/scaling route.
