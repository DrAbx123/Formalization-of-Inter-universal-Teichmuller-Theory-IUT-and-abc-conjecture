import tmp.sheaf.xif.paper.Mzk1RRInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: flt_core puncture-degree bundle (D evidence) -> Mzk1RRInterfaceActual.Curve.punctureDivisor/degree_punctureDivisor + degree_single_interface + deg_eq_one_interface -> PROVED bundle: puncture divisor degree = |T|, single divisor degree, place degree one. No named inputs beyond ported instances. No closure.

# Mzk1RRPunctureDegreeActual — flt_core puncture-degree bundle

PROVED: `rr_puncture_degree` (puncture divisor degree = |T|), `rr_single_degree`,
`rr_place_degree_one`.  Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRPunctureDegreeActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

universe u v

/-- **PROVED:** degree of the puncture divisor is |T|. -/
theorem rr_puncture_degree {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) :
    Divisor.degree (Curve.punctureDivisor T) = (T.card : ℤ) :=
  Curve.degree_punctureDivisor T

/-- **PROVED:** degree of a single-place divisor. -/
theorem rr_single_degree {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n * v.deg :=
  degree_single_interface v n

/-- **PROVED:** every place has degree one over an algebraically closed base. -/
theorem rr_place_degree_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.deg = 1 :=
  deg_eq_one_interface v

def rrPunctureRows : List (String × String × String) :=
  [ ("puncture divisor degree |T|", "PROVED", "rr_puncture_degree (Curve.degree_punctureDivisor)")
  , ("single divisor degree", "PROVED", "rr_single_degree")
  , ("place degree one", "PROVED", "rr_place_degree_one") ]

theorem rrPunctureRows_length : rrPunctureRows.length = 3 := rfl

#check rr_puncture_degree
#check rr_single_degree
#check rr_place_degree_one
#check rrPunctureRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRPunctureDegreeActual
end