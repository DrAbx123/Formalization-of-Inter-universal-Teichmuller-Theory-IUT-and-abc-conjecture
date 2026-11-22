import tmp.sheaf.xif.paper.Mzk1RRGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # flt_core RR green consumer bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRGreenConsumerBundleActualAdapted

open AlgebraicCurve

universe u v

theorem rrGreenConsumerBundle_canonical {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    (hex : ∃ ω : Ω[F⁄K], ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hex.choose_spec) ≤ 2 * (genus K F : ℤ) - 1 :=
  LeanFormal.IUT.XiFPaper.Mzk1RRGreenConsumerActual.rrGreen_canonical_bound hex

def rrGreenConsumerBundleRows : List (String × String × String) :=
  [ ("canonical bound", "PROVED", "rrGreenConsumerBundle_canonical") ]

theorem rrGreenConsumerBundleRows_length : rrGreenConsumerBundleRows.length = 1 := rfl

#check rrGreenConsumerBundle_canonical
#check rrGreenConsumerBundleRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRGreenConsumerBundleActualAdapted
end