import tmp.sheaf.xif.paper.Mzk1GeomCoreRRProvedBundleActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreChartBasicFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D green facts bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DGreenFactsActual

open AlgebraicCurve
open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual

universe u v

theorem dGreen_canonical_bound {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    (hex : ∃ ω : Ω[F⁄K], ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hex.choose_spec) ≤ 2 * (genus K F : ℤ) - 1 :=
  LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedBundleActual.rr_canonical_bound hex

def dGreenRows : List (String × String × String) :=
  [ ("canonical degree bound from RR bundle", "PROVED", "dGreen_canonical_bound"),
    ("chart basic facts", "PROVED", "consumed from Mzk1GeomCoreChartBasicFactsActual (DONE0)") ]

theorem dGreenRows_length : dGreenRows.length = 2 := rfl

#check dGreen_canonical_bound
#check dGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1DGreenFactsActual
end