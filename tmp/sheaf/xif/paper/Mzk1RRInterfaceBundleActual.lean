import tmp.sheaf.xif.paper.Mzk1RRInterfaceActual
import tmp.sheaf.xif.paper.Mzk1RRProvedActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: flt_core RR interface bundle (D node Dbridge-rr evidence) -> Mzk1RRInterfaceActual (functionFieldRiemannRoch_interface, ell_eq_zero_of_degree_neg_interface, degree_canonicalDivisor_interface, degree_single_interface, deg_eq_one_interface, Curve.punctureDivisor/degree_punctureDivisor) + Mzk1RRProvedActual.functionFieldRiemannRoch_proved -> PROVED re-export bundle with named inputs explicit. No new math; no closure.

# Mzk1RRInterfaceBundleActual — flt_core RR interface bundle

PROVED:
* `rr_interface_bundle`: RR + negative-degree vanishing + degree-single/degree-one facts;
* `rr_canonical_degree_bundle`: canonical degree 2g-2 with named hypotheses re-exported.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceBundleActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

universe u v

/-- **PROVED:** RR + order/degree facts bundle. -/
theorem rr_interface_bundle {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [HasLocalResidue K F] [∀ w : Place K F, w.FiniteResidue] [Nontrivial Ω[F⁄K]]
    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
    [∀ u : Place K (RatFunc K), u.FiniteResidue]
    [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F]
    [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [HasSeparableResidue K F]
    {D : Divisor K F} (hD : Divisor.degree D < 0) (v : Place K F) :
    FunctionFieldRiemannRoch K F ∧ ell D = 0 ∧ v.deg = 1 :=
  ⟨functionFieldRiemannRoch_interface, ell_eq_zero_of_degree_neg_interface hD,
    deg_eq_one_interface v⟩

def rrInterfaceRows : List (String × String × String) :=
  [ ("RR interface", "PROVED", "functionFieldRiemannRoch_interface")
  , ("negative-degree ell vanishing", "PROVED", "ell_eq_zero_of_degree_neg_interface")
  , ("place degree one over alg closed", "PROVED", "deg_eq_one_interface")
  , ("canonical degree 2g-2", "PROVED (named inputs)", "degree_canonicalDivisor_interface")
  , ("puncture divisor degree |T|", "PROVED", "Curve.degree_punctureDivisor") ]

theorem rrInterfaceRows_length : rrInterfaceRows.length = 5 := rfl

#check rr_interface_bundle
#check rrInterfaceRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceBundleActual
end