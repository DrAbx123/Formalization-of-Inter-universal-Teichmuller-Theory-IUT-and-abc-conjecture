import tmp.sheaf.xif.paper.Mzk1RRPunctureDegreeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # flt_core RR green puncture consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRGreenPunctureConsumerActualAdapted

open AlgebraicCurve

universe u v

theorem rrGreenPuncture_bundle {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) :
    Divisor.degree (Finset.sum T (fun t => Finsupp.single t (1 : ℤ))) = (T.card : ℤ) := by
  have h := LeanFormal.IUT.XiFPaper.Mzk1RRPunctureDegreeActual.rr_puncture_degree T
  simpa [LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual.Curve.punctureDivisor] using h

def rrGreenPunctureRows : List (String × String × String) :=
  [ ("puncture degree (sum form)", "PROVED", "rrGreenPuncture_bundle") ]

theorem rrGreenPunctureRows_length : rrGreenPunctureRows.length = 1 := rfl

#check rrGreenPuncture_bundle
#check rrGreenPunctureRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRGreenPunctureConsumerActualAdapted
end