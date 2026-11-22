import tmp.sheaf.xif.paper.TateThetaNormalizationAttempt

noncomputable section
open LeanFormal.IUT.XiFPaper.TateThetaNormalizationAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateJacobiTripleProductAttempt

universe u

variable {K : Type u} [NormedField K]

/-- Proposed Jacobi product with the requested plus signs. -/
noncomputable def tateJacobiProduct (q u : K) : K :=
  tprod (fun n : Nat =>
    (1 - q ^ (n + 1)) * (1 + q ^ (n + 1) * u) *
      (1 + q ^ (n + 1) * u⁻¹))

/-- Proposed Jacobi bilateral series with exponent n(n+1)/2. -/
noncomputable def tateJacobiSeries (q u : K) : K :=
  ∑' n : Int, q ^ (n * (n + 1) / 2) * u ^ n

def TateJacobiTripleProductTarget (q u : K) : Prop :=
  tateJacobiProduct q u = tateJacobiSeries q u

def jacobiQ1LHS (u : K) : K := u + u⁻¹ - 1
def jacobiQ1RHS (u : K) : K := u + u⁻¹ ^ 2

theorem S3129_jacobi_q1_false_at_two :
    jacobiQ1LHS (2 : Rat) ≠ jacobiQ1RHS (2 : Rat) := by
  norm_num [jacobiQ1LHS, jacobiQ1RHS]

#check tateJacobiProduct
#check tateJacobiSeries
#check TateJacobiTripleProductTarget
#check S3129_jacobi_q1_false_at_two
#print axioms S3129_jacobi_q1_false_at_two

end LeanFormal.IUT.XiFPaper.TateJacobiTripleProductAttempt
end