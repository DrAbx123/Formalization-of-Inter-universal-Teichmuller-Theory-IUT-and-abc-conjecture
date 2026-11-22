import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
import tmp.sheaf.xif.paper.S1491NormEDSNetActual
/-! # S1509: reduced invariant numerator and the exact missing identity
Defines the actual reduced invariant numerator from Mathlib's normEDS, complEDS₂
and S1410's complEDS₂Aux.  The defining identity
  reducedInvarNum b c d m = reducedInvarDenom b c d m * (d + b^4)
equivalently 2ω + a1 φψ + a3 ψ^3 = ψc, is not proved: it needs the
IsEllipticNet invariant cancellation theorems
  invarNum_normEDS_one_eq_reducedInvarNum_mul
  invarDenom_normEDS_one_eq_reducedInvarDenom_mul,
which are absent from Mathlib v4.32.2 (the S1491 net theorem supplies only
IsEllipticNet (normEDS ...)).  No fake identity. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
section ReducedInvarNum
variable {R : Type*} [CommRing R] (b c d : R) (m : ℤ)
/-- The actual reduced invariant numerator of a normalised EDS. -/
noncomputable def reducedInvarNum : R :=
  complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m
theorem reducedInvarNum_def :
    reducedInvarNum b c d m =
      complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * complEDS₂Aux b c d m :=
  rfl
end ReducedInvarNum
end WeierstrassCurve
#check WeierstrassCurve.reducedInvarDenom
end
