/- B1 analytic h, batch 3b (kurt): AlgPoint instantiation of the coefficient bound.

For an algebraic point presented by its monic minimal polynomial over Q, after
base change to C the coefficients are bounded by 2 ^ deg, and roots of the
derivative of the base-changed polynomial are bounded by 1 + deg * 2 ^ deg,
whenever all complex roots lie in the unit disc.

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC registry: kurt-adapters-20261117 (1M heartbeats; Lead-approved list).
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiCauchyBound3Actual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2ProducerActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiB3AlgPointActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2ProducerActual

/-- The base change of an algebraic point's minimal polynomial to C. -/
noncomputable def algPointPoly (p : AlgPoint) : ℂ[X] :=
  p.minpoly.map (algebraMap ℚ ℂ)

/-- The base-changed polynomial is monic. -/
theorem algPointPoly_monic (p : AlgPoint) : (algPointPoly p).Monic :=
  p.monic.map _

/-- Coefficient bound for an AlgPoint whose complex conjugates lie in the unit disc. -/
theorem algPoint_coeff_bound (p : AlgPoint)
    (hroots : ∀ z ∈ (algPointPoly p).roots, ‖z‖ ≤ 1) (k : ℕ) :
    ‖(algPointPoly p).coeff k‖ ≤ (2 : ℝ) ^ p.deg :=
  (Mzk1G1PsiCauchyBound3Actual.coeff_norm_le_choose (algPointPoly p)
      (algPointPoly_monic p) hroots k).trans
    (Mzk1G1PsiCauchyBound3Actual.choose_le_two_pow p.deg k)

/-- Uniform coefficient bound for an AlgPoint with unit-disc conjugates. -/
theorem algPoint_coeff_bound_uniform (p : AlgPoint)
    (hroots : ∀ z ∈ (algPointPoly p).roots, ‖z‖ ≤ 1) :
    ∀ k, ‖(algPointPoly p).coeff k‖ ≤ (2 : ℝ) ^ p.deg :=
  fun k => algPoint_coeff_bound p hroots k

/-- Roots of the derivative of the base-changed minimal polynomial are bounded by
1 + deg * 2 ^ deg (unit-disc case). -/
theorem algPoint_derivative_root_bound (p : AlgPoint)
    (hroots : ∀ z ∈ (algPointPoly p).roots, ‖z‖ ≤ 1) {z : ℂ}
    (hz : (algPointPoly p).derivative.IsRoot z) (hd : 1 ≤ p.deg) :
    ‖z‖ ≤ 1 + (p.deg : ℝ) * 2 ^ p.deg :=
  Mzk1G1PsiCauchyBound3Actual.derivative_root_bound_choose (algPointPoly p)
    (algPointPoly_monic p) hroots hz hd

/-- The explicit B(d_0) bound used by the M2 analytic recursion for unit-disc
Algebraic points: 1 + deg * 2 ^ deg bounds the critical points. -/
noncomputable def psiB (d : ℕ) : ℝ := 1 + (d : ℝ) * 2 ^ d

/-- The B(d_0) bound is positive. -/
theorem psiB_pos (d : ℕ) : 0 < psiB d := by
  unfold psiB
  positivity

#print axioms algPointPoly_monic
#print axioms algPoint_coeff_bound
#print axioms algPoint_derivative_root_bound
#print axioms psiB_pos

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiB3AlgPointActual
end