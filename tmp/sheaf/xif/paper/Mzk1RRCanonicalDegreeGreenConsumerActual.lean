import tmp.sheaf.xif.paper.Mzk1RRCanonicalDegreeConsumer2Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # D RR canonical degree green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeGreenConsumerActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRCanonicalDegreeActual

universe u v

theorem rrCanonicalDegreeGreenConsumer_hdual {K F : Type*} [Field K] [IsAlgClosed K] [Infinite K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    (hdeg : Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2)
    (T : Finset (Place K F)) (hcard : 2 * (genus K F : ℤ) + 1 ≤ (T.card : ℤ)) :
    (∀ t ∈ T,
      (ell (canonicalDivisorOf hω - LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.punctureDivisor T) : ℤ) = 0) :=
  LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeConsumer2Actual.rrCanonicalDegreeConsumer2_hdual hω hdeg T hcard

def rrCanonicalDegreeGreenConsumerRows : List (String × String × String) :=
  [ ("dual vanishing", "PROVED", "rrCanonicalDegreeGreenConsumer_hdual") ]

theorem rrCanonicalDegreeGreenConsumerRows_length : rrCanonicalDegreeGreenConsumerRows.length = 1 := rfl

#check rrCanonicalDegreeGreenConsumer_hdual
#check rrCanonicalDegreeGreenConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRCanonicalDegreeGreenConsumerActual
end