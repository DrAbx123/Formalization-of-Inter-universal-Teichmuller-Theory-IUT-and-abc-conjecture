/-!
# S3171g: IV §1 ids (data only; registry frozen 14041, no registry edits)

Ids for lattice / mainline after the IV §1 display batch.

* INDEX.IUTIV.Thm110.display -> S3171IUTIVSection1DisplayActual:
  Thm110DisplayTerms, thm110Lhs/thm110Mid/thm110Rhs/thm110Cor312Gap,
  Thm110DisplayInputs, thm110_final_display, thm110DisplayClass,
  paperRouteResidualData_of_undilated, abcConjecture_of_undilated,
  thm110_display_and_abc_of_undilated.
* INDEX.IUTIV.Thm110.inputs -> S3171IUTIVSection1InputsActual.s3171InputMapping
  ((b)/(c) undilated <-> families <-> skeleton fields <-> display terms).
* INDEX.IUTIV.Thm110.uniform-height -> S3171UniformHeightConsumerActual:
  uniformHeightComparison_of_valuation_bound, undilatedHeightBound_of_valuation_bound,
  heightComparisonFamily_of_valuation_bound, s3171HeightAssetWitnesses
  (reuses production ABCHeightArithmeticWeightComparison + pinned Mathlib Height).
* INDEX.IUTIV.Thm110.FLT-support -> S3171FLTAssetSupportActual.s3171FLTAssets
  (6 adapted AG_FLT_* assets; RiemannRochRows/SerrePairing/SmoothProperCurveFiniteMapData PENDING, not counted).
* INDEX.IUTIV.Thm110.skeleton-align -> S3171SkeletonAlignActual.s3171SkeletonAlignment.
* INDEX.IUTIV.Thm110.step0 -> S3171Step0RecordActual.s3171Step0Record.
Reused (not re-proved): S3171IUTIVSection1StatementActual (statement/step table),
S3131PaperRouteHeight/RegionReductionActual, S3131PaperRouteSkeletonActual,
S3131PaperRouteFieldStatementsActual, Mathlib.NumberTheory.Height.NumberField via
ABCHeightArithmeticWeightComparison.
Honest classes: hCor312 (route (b)/(c) consumer) and hSlack (Step (v) paper
arithmetic) are explicit class-B inputs; display shape is statement-faithful.
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3171IdsActual

/-- IV §1 ids: (index id, declarations, file). -/
def s3171Ids : List (String × String × String) :=
  [ ("INDEX.IUTIV.Thm110.display",
      "Thm110DisplayTerms, thm110Lhs, thm110Mid, thm110Rhs, thm110Cor312Gap, Thm110DisplayInputs, thm110_final_display, thm110DisplayClass, paperRouteResidualData_of_undilated, abcConjecture_of_undilated, thm110_display_and_abc_of_undilated",
      "S3171IUTIVSection1DisplayActual.lean"),
    ("INDEX.IUTIV.Thm110.inputs", "s3171InputMapping", "S3171IUTIVSection1InputsActual.lean"),
    ("INDEX.IUTIV.Thm110.uniform-height",
      "uniformHeightComparison_of_valuation_bound, undilatedHeightBound_of_valuation_bound, heightComparisonFamily_of_valuation_bound, s3171HeightAssetWitnesses",
      "S3171UniformHeightConsumerActual.lean"),
    ("INDEX.IUTIV.Thm110.FLT-support", "s3171FLTAssets", "S3171FLTAssetSupportActual.lean"),
    ("INDEX.IUTIV.Thm110.skeleton-align", "s3171SkeletonAlignment", "S3171SkeletonAlignActual.lean"),
    ("INDEX.IUTIV.Thm110.step0", "s3171Step0Record", "S3171Step0RecordActual.lean") ]

end LeanFormal.IUT.XiFPaper.S3171IdsActual
