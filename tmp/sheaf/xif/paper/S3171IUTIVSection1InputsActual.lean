/-!
# S3171b: IV §1 inputs — (b)/(c) undilated interfaces and log-volume terms (data only)

Maps Theorem 1.10's inputs to the tree's existing (b)/(c) interfaces (naming
aligned with S3131PaperRouteSkeletonActual.PaperRouteResidualData and with the
existing S3171IUTIVSection1StatementActual step table).

* display terms (corpus l.1362-1385): 1/6 log(q); (1+20 d_mod/l)(log d_F + log f_F)
  + 20(e*_mod l + η_prm); the F_tpd middle term with 12/10; the Cor 3.12 gap
  ((1/6)(12/l²))log q.  Declarations: S3171IUTIVSection1DisplayActual
  (Thm110DisplayTerms / thm110Lhs / thm110Mid / thm110Rhs / thm110Cor312Gap).
* (b) -> S3131PaperRouteHeightReductionActual.UndilatedHeightBound
       = forall ABC triples: Height.logHeight1 (abcRationalPoint a c)
         <= (W.logVolume {point a b c}).toReal
  -> HeightComparisonFamily (provable reduction, heightComparisonFamily_of_undilated)
  = PaperRouteResidualData.height_comparison.
* (c) -> S3131PaperRouteRegionReductionActual.UndilatedRegionBound
       = exists D: (W.logVolume {point}).toReal <= arithmeticWeight + logVolume hull + D
  -> RegionVolumeFamily (provable reduction, regionVolumeFamily_of_undilated)
  = PaperRouteResidualData.region_volume_bound.
* log-volume terms: W.logVolume (IQHullLogVolumeInterface); (W.logVolume W.hull).toReal
  (thetaBound); Height.logHeight1 (Mathlib.NumberTheory.Height.NumberField).
* assembly: UndilatedHeightBound + UndilatedRegionBound => PaperRouteResidualData
  => ABCConjecture (S3171IUTIVSection1DisplayActual.paperRouteResidualData_of_undilated /
  abcConjecture_of_undilated; skeleton abcConjecture_of_paperRouteResiduals).
Statuses: (b) class B paper-input (uniform height comparison; H1 conditional
reduction support in S3171UniformHeightConsumerActual); (c) class B
(IV section2 / [GenEll] arithmetic strength); display derivation: hCor312 (route
consumer) + hSlack (Step (v) paper arithmetic).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3171IUTIVSection1InputsActual

/-- IV §1 input mapping row: (paper input, tree interface, status). -/
def s3171InputMapping : List (String × String × String) :=
  [ ("final display terms (1/6)log q; (1+20d/l)(log d_F+log f_F)+20(el+η)",
      "S3171IUTIVSection1DisplayActual.Thm110DisplayTerms/thm110Lhs/thm110Mid/thm110Rhs/thm110Cor312Gap",
      "statement faithful (corpus l.1362-1385)"),
    ("(b) undilated height comparison",
      "S3131PaperRouteHeightReductionActual.UndilatedHeightBound -> HeightComparisonFamily -> PaperRouteResidualData.height_comparison",
      "class B paper-input; reduction PROVED in tree"),
    ("(c) undilated region-volume bound",
      "S3131PaperRouteRegionReductionActual.UndilatedRegionBound -> RegionVolumeFamily -> PaperRouteResidualData.region_volume_bound",
      "class B paper-input; reduction PROVED in tree"),
    ("log-volume terms / thetaBound",
      "IQHullLogVolumeInterface.logVolume (W.hull / point regions); Height.logHeight1",
      "reuse (Cor312ComparisonRegionV2Actual, Mathlib NumberTheory.Height)"),
    ("assembly -> ABC",
      "PaperRouteResidualData -> abcConjecture_of_paperRouteResiduals (no card P)",
      "PROVED (conditional on (b)/(c))") ]

end LeanFormal.IUT.XiFPaper.S3171IUTIVSection1InputsActual
