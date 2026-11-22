/-!
# S3171f: STEP 0 deep-search record — IUT IV §1 batch (policy §7.10; data only)

Queries (tools/xif_deep_search.ps1):
  UndilatedHeightBound|UndilatedRegionBound|RiemannRochRows|SerrePairing|CechSectionsOfDivisor|SmoothProperCurveFiniteMapData|PaperRouteSkeleton|NumberTheory.Height
Hits: LeanFormal 4 (only RationalPointDictionary/ABCInvariantHeight/RationalLocalHeightDecomposition
importing Mathlib.NumberTheory.Height.NumberField) / tmp/sheaf/xif/paper 50.
Sections read: coord/PRIOR-ART-INDEX.md C (Theta side), D ((b)/(c)), E (paper cites), G (paper-level).
Corpus: IUT IV §1 "Log-volume Estimates" (l.38), Thm 1.10 at l.1255, final display
Step (v) at l.1362-1385 (1/6)log q <= (1+20d/l)(log d_Ftpd+log f_Ftpd)+20(el+eta)
<= (1+20d/l)(log d_F+log f_F)+20(el+eta), with C_Theta formula and "C_Theta >= -1".
Reuse decisions (no re-proof):
* (b) -> S3131PaperRouteHeightReductionActual.UndilatedHeightBound (+
  heightComparisonFamily_of_undilated proved).
* (c) -> S3131PaperRouteRegionReductionActual.UndilatedRegionBound (+
  regionVolumeFamily_of_undilated proved).
* skeleton -> S3131PaperRouteSkeletonActual.PaperRouteResidualData /
  abcConjecture_of_paperRouteResiduals.
* Thm 1.10 statement/step table already in S3171IUTIVSection1StatementActual (reuse;
  this batch adds the display theorem + (b) uniform height consumer).
* pinned Mathlib.NumberTheory.Height.NumberField -> production
  ABCHeightArithmeticWeightComparison.abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound
  (reused for (b) uniform height comparison).
* FLT prior art -> AG00bFLTAssetAuditActual (5 adapted modules) + AG_FLT_*.lean
  adapted copies; RiemannRochRows/SerrePairing/SmoothProperCurveFiniteMapData are
  PENDING adaptation (raw only) and NOT counted.
Pins: registry frozen 14041; no intermediate reopen.
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3171Step0RecordActual

/-- STEP 0 record: (query, hits, reuse/adapt decision). -/
def s3171Step0Record : List (String × String × String) :=
  [ ("UndilatedHeightBound|UndilatedRegionBound|PaperRouteSkeleton", "paper 50 hits; LeanFormal 0",
      "reuse S3131PaperRouteHeight/RegionReductionActual + S3131PaperRouteSkeletonActual"),
    ("RiemannRochRows|SerrePairing|CechSectionsOfDivisor|SmoothProperCurveFiniteMapData", "FLT raw only (tmp/external/flt-lean); 6 adapted AG_FLT_* present",
      "adapted: reuse future AG-03/04; pending: RiemannRochRows/SerrePairing/SmoothProperCurveFiniteMapData NOT counted"),
    ("NumberTheory.Height", "LeanFormal 4 (RationalPointDictionary/ABCInvariantHeight/RationalLocalHeightDecomposition); Mathlib pinned",
      "reuse ABCHeightArithmeticWeightComparison uniform valuation theorem for (b)"),
    ("IUT IV Thm 1.10 display (corpus l.1255/l.1362-1385)", "corpus", "new conditional display theorem S3171IUTIVSection1DisplayActual (exact shape)") ]

end LeanFormal.IUT.XiFPaper.S3171Step0RecordActual
