import tmp.sheaf.xif.paper.Mzk1RRInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # flt_core RR negative-degree consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRNegativeDegreeConsumerActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

universe u v

theorem rr_neg_ell_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] {D : Divisor K F} (hD : Divisor.degree D < 0) :
    ell D = 0 := ell_eq_zero_of_degree_neg_interface hD

theorem rr_neg_ell_bundle {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] {D : Divisor K F} (hD : Divisor.degree D < 0) (v : Place K F) :
    ell D = 0 ∧ v.deg = 1 :=
  ⟨ell_eq_zero_of_degree_neg_interface hD, deg_eq_one_interface v⟩

def rrNegRows : List (String × String × String) :=
  [ ("negative-degree ell vanishing", "PROVED", "rr_neg_ell_zero"),
    ("negative-degree + place degree bundle", "PROVED", "rr_neg_ell_bundle") ]

theorem rrNegRows_length : rrNegRows.length = 2 := rfl

#check rr_neg_ell_bundle
#check rrNegRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRNegativeDegreeConsumerActual
end