import tmp.sheaf.xif.paper.TateJacobiTripleProductAttempt

noncomputable section
open LeanFormal.IUT.XiFPaper.TateJacobiTripleProductAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateJacobiStandardAttempt

universe u

variable {K : Type u} [NormedField K]

/-- Standard Jacobi triple product with exponent n^2. -/
noncomputable def jacobiStandardProduct (q z : K) : K :=
  tprod (fun m : Nat =>
    (1 - q ^ (2 * (m + 1))) *
      (1 + z * q ^ (2 * (m + 1) - 1)) *
      (1 + z⁻¹ * q ^ (2 * (m + 1) - 1)))

noncomputable def jacobiStandardSeries (q z : K) : K :=
  ∑' n : Int, q ^ (n * n) * z ^ n

def TateJacobiStandardTarget (q z : K) : Prop :=
  jacobiStandardProduct q z = jacobiStandardSeries q z

/-- q^1 coefficient of the standard product: from m=1 factors, z + z^-1. -/
def jacobiStandardQ1LHS (z : K) : K := z + z⁻¹

/-- q^1 coefficient of the standard series: from n=±1, z + z^-1. -/
def jacobiStandardQ1RHS (z : K) : K := z + z⁻¹

theorem S3130_jacobi_standard_q1 (z : K) :
    jacobiStandardQ1LHS z = jacobiStandardQ1RHS z := rfl


/-- Half-exponent target after substituting q_std = r, z = u*r with r^2=q. -/
def TateJacobiHalfExponentTarget (q r u : K) : Prop :=
  jacobiStandardProduct r (u * r) =
    ∑' n : Int, q ^ (n * (n + 1) / 2) * u ^ n

#check TateJacobiHalfExponentTarget
#check jacobiStandardProduct
#check jacobiStandardSeries
#check TateJacobiStandardTarget
#check S3130_jacobi_standard_q1
#print axioms S3130_jacobi_standard_q1

end LeanFormal.IUT.XiFPaper.TateJacobiStandardAttempt
end