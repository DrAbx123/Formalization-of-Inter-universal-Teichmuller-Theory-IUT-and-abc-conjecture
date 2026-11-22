import tmp.sheaf.xif.paper.Mzk1RRPunctureClusterRollupActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # flt_core RR puncture cluster consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRPunctureClusterConsumerActualAdapted

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRPunctureClusterRollupActual

universe u v

theorem rrPunctureClusterConsumer_bundle {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) :
    Divisor.degree (LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.punctureDivisor T) = (T.card : ℤ) :=
  rrPunctureClusterRollup_bundle T

def rrPunctureClusterConsumerRows : List (String × String × String) :=
  [ ("puncture degree", "PROVED", "rrPunctureClusterConsumer_bundle") ]

theorem rrPunctureClusterConsumerRows_length : rrPunctureClusterConsumerRows.length = 1 := rfl

#check rrPunctureClusterConsumer_bundle
#check rrPunctureClusterConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRPunctureClusterConsumerActualAdapted
end