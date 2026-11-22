import tmp.sheaf.xif.paper.Mzk1GeomCoreRRProvedBundleActual
import tmp.sheaf.xif.paper.Mzk1RRInterfaceBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # flt_core RR green consumer (green deps); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRGreenConsumerActual

open AlgebraicCurve

universe u v

theorem rrGreen_canonical_bound {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    (hex : ∃ ω : Ω[F⁄K], ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hex.choose_spec) ≤ 2 * (genus K F : ℤ) - 1 :=
  LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedBundleActual.rr_canonical_bound hex

theorem rrGreen_puncture_degree {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) :
    Divisor.degree (LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.punctureDivisor T) =
      (T.card : ℤ) :=
  LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.degree_punctureDivisor T

def rrGreenRows : List (String × String × String) :=
  [ ("canonical degree bound", "PROVED", "rrGreen_canonical_bound"),
    ("puncture degree", "PROVED", "rrGreen_puncture_degree"),
    ("RR statement + zero divisor", "PROVED", "consumed from Mzk1GeomCoreRRProvedBundleActual (DONE0)") ]

theorem rrGreenRows_length : rrGreenRows.length = 3 := rfl

#check rrGreen_canonical_bound
#check rrGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRGreenConsumerActual
end