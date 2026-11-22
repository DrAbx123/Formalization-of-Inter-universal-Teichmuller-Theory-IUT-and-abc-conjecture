/-!
# S3171e: alignment with S3131PaperRouteSkeletonActual — (b)/(c) family naming (data only)

Naming alignment for the paper route (card P never assumed):

skeleton field                         tree family                         undilated interface
PaperRouteResidualData.point           pt : Nat -> Nat -> Nat -> X        (input)
PaperRouteResidualData.height_comparison
                                       HeightComparisonFamily W pt        UndilatedHeightBound W pt
PaperRouteResidualData.region_volume_bound
                                       RegionVolumeFamily W pt            UndilatedRegionBound W pt
(display) thm110Lhs/thm110Mid/thm110Rhs  Thm110DisplayTerms              hCor312 + hSlack (class B)

Provable reductions (already in tree):
* heightComparisonFamily_of_undilated : UndilatedHeightBound W pt -> HeightComparisonFamily W pt
* regionVolumeFamily_of_undilated     : UndilatedRegionBound W pt -> RegionVolumeFamily W pt
* paperRouteResidualData_of_undilated : both -> PaperRouteResidualData W
* abcConjecture_of_undilated          : both -> ABCConjecture (via skeleton, no card P)

(b) uniform height comparison support: S3171UniformHeightConsumerActual
(height undilated bound from the uniform valuation bound + volume domination;
reuses Mathlib NumberTheory.Height pins via production
ABCHeightArithmeticWeightComparison).
(c) remaining: weight <= theta (hull half free via CardAMPLThetaBoundSupply) +
hpoint/dictionary (records in PRIOR-ART-INDEX C/D/G).
Display: S3171IUTIVSection1DisplayActual.thm110_final_display (conditional).
Statuses: (b)/(c) are class-B analytic residual families; display derivation has
two explicit class-B inputs; nothing closed unconditionally.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3171SkeletonAlignActual

/-- Alignment rows: (skeleton name, tree family, status). -/
def s3171SkeletonAlignment : List (String × String × String) :=
  [ ("PaperRouteResidualData.point", "pt : Nat -> Nat -> Nat -> X", "input (class A)"),
    ("PaperRouteResidualData.height_comparison", "HeightComparisonFamily W pt", "(b) class B; from UndilatedHeightBound (proved reduction)"),
    ("PaperRouteResidualData.region_volume_bound", "RegionVolumeFamily W pt", "(c) class B; from UndilatedRegionBound (proved reduction)"),
    ("abcConjecture_of_paperRouteResiduals", "ABCConjecture from the two families", "PROVED conditional (paper-route skeleton; card P not assumed)"),
    ("Thm110DisplayTerms", "(1/6)log q <= (1+20d/l)(log d_F+log f_F)+20(el+eta)", "statement faithful; conditional on hCor312 + hSlack"),
    ("S3171UniformHeightConsumerActual", "(b) undilated + uniform valuation bound", "REUSED Mathlib height pins; no new proof") ]

end LeanFormal.IUT.XiFPaper.S3171SkeletonAlignActual
