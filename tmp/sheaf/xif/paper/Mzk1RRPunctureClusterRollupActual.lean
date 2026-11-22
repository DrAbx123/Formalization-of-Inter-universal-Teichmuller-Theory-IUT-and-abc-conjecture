import tmp.sheaf.xif.paper.Mzk1RRPunctureGreenConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # flt_core RR puncture cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRPunctureClusterRollupActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRPunctureGreenConsumerActual

universe u v

theorem rrPunctureClusterRollup_bundle {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) :
    Divisor.degree (LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.punctureDivisor T) = (T.card : ℤ) :=
  (rrPunctureGreen_bundle T).1

def rrPunctureClusterRollupRows : List (String × String × String) :=
  [ ("puncture degree", "PROVED", "rrPunctureClusterRollup_bundle") ]

theorem rrPunctureClusterRollupRows_length : rrPunctureClusterRollupRows.length = 1 := rfl

#check rrPunctureClusterRollup_bundle
#check rrPunctureClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRPunctureClusterRollupActual
end