import tmp.sheaf.xif.paper.Mzk1GeomCoreRRCanonicalDegreeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D RR canonical degree consumer 2; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeConsumer2Actual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRCanonicalDegreeActual

universe u v

theorem rrCanonicalDegreeConsumer2_hdual {K F : Type*} [Field K] [IsAlgClosed K] [Infinite K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    (hdeg : Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2)
    (T : Finset (Place K F)) (hcard : 2 * (genus K F : ℤ) + 1 ≤ (T.card : ℤ)) :
    (∀ t ∈ T,
      (ell (canonicalDivisorOf hω - LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.punctureDivisor T) : ℤ) = 0) :=
  fun t ht => (hdual_of_canonical_degree hω hdeg T hcard t ht).1

def rrCanonicalDegreeConsumer2Rows : List (String × String × String) :=
  [ ("dual vanishing projection", "PROVED", "rrCanonicalDegreeConsumer2_hdual") ]

theorem rrCanonicalDegreeConsumer2Rows_length : rrCanonicalDegreeConsumer2Rows.length = 1 := rfl

#check rrCanonicalDegreeConsumer2_hdual
#check rrCanonicalDegreeConsumer2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeConsumer2Actual
end