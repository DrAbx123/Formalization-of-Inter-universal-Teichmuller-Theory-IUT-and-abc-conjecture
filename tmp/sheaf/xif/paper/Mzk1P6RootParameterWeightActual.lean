/- P6 root parameter weight actual: ord(varpi)=j^2/(2l)*ord(q). -/
import tmp.sheaf.xif.paper.Mzk1BoxDistinguishedScalarActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
variable {p : Nat} {K : Type*} [NormedField K]
def rootParameterWeight (X : DistinguishedScalarData p K) : ℝ :=
  ((X.j : ℝ) ^ 2 / (2 * (X.l : ℝ))) * ord (K := K) p X.q
theorem rootParameterWeight_eq_ord_theta (X : DistinguishedScalarData p K) :
    ord (K := K) p (theta X.alpha X.j) = rootParameterWeight X :=
  distinguished_theta_order X
theorem rootParameterWeight_eq_ord_varpi (X : DistinguishedScalarData p K) :
    ord (K := K) p (theta X.alpha X.j) =
      ((X.j : ℝ) ^ 2 / (2 * (X.l : ℝ))) * ord (K := K) p X.q :=
  distinguished_theta_order X
theorem weighted_rootParameter_sum {ι : Type*} [Fintype ι]
    (X : DistinguishedScalarData p K) (w : ι → ℝ) :
    (∑ i : ι, w i * ord (K := K) p (theta X.alpha X.j)) =
      (∑ i : ι, w i) * rootParameterWeight X := by
  rw [← Finset.sum_mul]
  congr 1
  exact rootParameterWeight_eq_ord_theta X
#print axioms rootParameterWeight_eq_ord_theta
#print axioms weighted_rootParameter_sum
end LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
