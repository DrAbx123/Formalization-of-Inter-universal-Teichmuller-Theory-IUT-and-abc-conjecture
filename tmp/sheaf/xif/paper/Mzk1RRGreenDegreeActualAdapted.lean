import tmp.sheaf.xif.paper.Mzk1RRPunctureDegreeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # flt_core RR green degree bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRGreenDegreeActualAdapted

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

universe u v

theorem rrGreenDegree_puncture {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) :
    Divisor.degree (Curve.punctureDivisor T) = (T.card : ℤ) :=
  LeanFormal.IUT.XiFPaper.Mzk1RRPunctureDegreeActual.rr_puncture_degree T

theorem rrGreenDegree_place {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.deg = 1 :=
  LeanFormal.IUT.XiFPaper.Mzk1RRPunctureDegreeActual.rr_place_degree_one v

def rrGreenDegreeRows : List (String × String × String) :=
  [ ("puncture degree", "PROVED", "rrGreenDegree_puncture"),
    ("place degree one", "PROVED", "rrGreenDegree_place") ]

theorem rrGreenDegreeRows_length : rrGreenDegreeRows.length = 2 := rfl

#check rrGreenDegree_puncture
#check rrGreenDegreeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRGreenDegreeActualAdapted
end