import tmp.sheaf.xif.paper.Mzk1GeomCoreRRCanonicalDegreeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D RR canonical-degree green bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeGreenActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRCanonicalDegreeActual

universe u v

theorem rrCanonicalDegreeGreen_hdual {K F : Type*} [Field K] [IsAlgClosed K] [Infinite K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    (hdeg : Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2)
    (T : Finset (Place K F)) (hcard : 2 * (genus K F : ℤ) + 1 ≤ (T.card : ℤ)) :
    (∀ t ∈ T,
      (ell (canonicalDivisorOf hω - LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.punctureDivisor T) : ℤ) = 0 ∧
      (ell (canonicalDivisorOf hω - (LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.punctureDivisor T - Finsupp.single t (1 : ℤ))) : ℤ) = 0) :=
  hdual_of_canonical_degree hω hdeg T hcard

def rrCanonicalDegreeGreenRows : List (String × String × String) :=
  [ ("dual vanishing from 2g-2", "PROVED", "rrCanonicalDegreeGreen_hdual") ]

theorem rrCanonicalDegreeGreenRows_length : rrCanonicalDegreeGreenRows.length = 1 := rfl

#check rrCanonicalDegreeGreen_hdual
#check rrCanonicalDegreeGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeGreenActual
end