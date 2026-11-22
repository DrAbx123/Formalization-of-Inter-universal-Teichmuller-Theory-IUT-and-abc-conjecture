import tmp.sheaf.xif.paper.TateThetaOddEquationAttempt

noncomputable section
open LeanFormal.IUT.TateCurve
open LeanFormal.IUT.XiFPaper.TateThetaOddEquationAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateThetaOddCoefficientAttempt

universe u

variable {K : Type u} [Field K]

/-- q^0 coefficient of the odd coordinate: only the n=0 term of the kernel sum. -/
def oddIdentityQ0X (u : K) : K := u / (1 - u) ^ 2

/-- q^0 coefficient of the odd series: only the n=0 term of the kernel sum. -/
def oddIdentityQ0O (u : K) : K := u * (1 + u) / (1 - u) ^ 3

/-- The q^0 coefficient identity of the odd Weierstrass equation: the a4/a6 terms
vanish at q=0, leaving O^2 = 4 X^3 + X^2. -/
theorem S3128_oddIdentity_q0 (u : K) (hu : 1 - u ≠ 0) :
    oddIdentityQ0O u ^ 2 = 4 * oddIdentityQ0X u ^ 3 + oddIdentityQ0X u ^ 2 := by
  unfold oddIdentityQ0O oddIdentityQ0X
  field_simp [hu]
  ring

/-- Explicit analytic input boundary: the full odd identity is not derived from
kernel sums here; it is recorded as a named hypothesis for the conditional chain. -/
def TateThetaOddIdentityAnalyticInput (K : Type u) [NormedField K]
    [CharZero K] [CompleteSpace K] : Prop :=
  forall (q : K) (u : K), ‖q‖ < 1 -> TateThetaOddIdentityTarget q u


/-- Expected q^1 coefficient of the raw X series: n=1 gives u, n=-1 gives u^-1. -/
def oddIdentityQ1X (u : K) : K := u + u⁻¹

/-- Expected q^1 coefficient of the raw O series: n=1 gives u, n=-1 gives -u^-1. -/
def oddIdentityQ1O (u : K) : K := u - u⁻¹

/-- q^1 coefficient of O^2. -/
def oddIdentityQ1LHS (u : K) : K :=
  2 * oddIdentityQ0O u * oddIdentityQ1O u

/-- q^1 coefficient of 4X^3 + X^2 + 4 a4 X + 4 a6,
using a4 coefficient -5 and a6 coefficient -1. -/
def oddIdentityQ1RHS (u : K) : K :=
  12 * oddIdentityQ0X u ^ 2 * oddIdentityQ1X u +
    2 * oddIdentityQ0X u * oddIdentityQ1X u -
    20 * oddIdentityQ0X u - 4

/-- The q^1 coefficient identity fails at u = 2, so the raw-coordinate
odd identity cannot be the correct target. -/
theorem S3128_rawOddIdentity_q1_false_at_two :
    oddIdentityQ1LHS (2 : Rat) ≠ oddIdentityQ1RHS (2 : Rat) := by
  norm_num [oddIdentityQ1LHS, oddIdentityQ1RHS, oddIdentityQ0X,
    oddIdentityQ0O, oddIdentityQ1X, oddIdentityQ1O]

#check S3128_oddIdentity_q0
#check TateThetaOddIdentityAnalyticInput
#check TateThetaOddIdentityTarget
#print axioms S3128_oddIdentity_q0

end LeanFormal.IUT.XiFPaper.TateThetaOddCoefficientAttempt
end