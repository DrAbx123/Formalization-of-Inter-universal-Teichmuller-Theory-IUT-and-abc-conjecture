/- U-L root actual: distinguished root order formula. -/
import tmp.sheaf.xif.paper.Mzk1P6RootParameterWeightActual
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual
open LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
namespace LeanFormal.IUT.XiFPaper.Mzk1ULRootActual
theorem uL_root_order {p : Nat} {K : Type*} [NormedField K]
    (X : DistinguishedScalarData p K) :
    ord (K := K) p (theta X.alpha X.j) =
      ((X.j : Real) ^ 2 / (2 * (X.l : Real))) * ord (K := K) p X.q :=
  distinguished_theta_order X
theorem uL_root_alpha_pow {p : Nat} {K : Type*} [NormedField K]
    (X : DistinguishedScalarData p K) :
    X.alpha ^ (2 * X.l) = X.q :=
  X.root_eq
#print axioms uL_root_order
#print axioms uL_root_alpha_pow
end LeanFormal.IUT.XiFPaper.Mzk1ULRootActual
end
