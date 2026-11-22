import tmp.sheaf.xif.paper.Mzk1RRPunctureDegreeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # flt_core RR puncture green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRPunctureGreenConsumerActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRPunctureDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

universe u v

theorem rrPunctureGreen_bundle {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) :
    Divisor.degree (Curve.punctureDivisor T) = (T.card : ℤ) ∧
      (∀ v : Place K F, v.deg = 1) :=
  ⟨rr_puncture_degree T, fun v => rr_place_degree_one v⟩

def rrPunctureGreenRows : List (String × String × String) :=
  [ ("puncture degree + place degree", "PROVED", "rrPunctureGreen_bundle") ]

theorem rrPunctureGreenRows_length : rrPunctureGreenRows.length = 1 := rfl

#check rrPunctureGreen_bundle
#check rrPunctureGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRPunctureGreenConsumerActual
end