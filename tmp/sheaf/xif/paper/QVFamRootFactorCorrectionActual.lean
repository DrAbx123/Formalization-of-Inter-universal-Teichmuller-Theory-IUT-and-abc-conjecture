import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.TwoLthRootKummerActual

/-!
# 2l-th root factor correction for qVFamily tensor coefficients

IUT I, Example 3.2, (iv), and IUT II, Introduction, pp.2-3:

  q_v is the classical q-parameter;
  q_v^(1/2l) is the chosen 2l-th root;
  the theta values at l-torsion points are, up to a 2l-th root of unity,
  q_v^(j^2 / 2l).

The value qVFamily T b is the classical q parameter (order = qVFamily.order).
Therefore the paper-level root coefficient is

  c_b^(root) = order(qVFamily T b) / (2l),

not order(qVFamily T b).  The old QVFamTensorCoefficientActual coefficient

  c_b = order(qVFamily T b)

is the coefficient of the classical q, not of the 2l-th root theta value.  The
old theta tensor coefficient j^2 * order(q) is therefore too large by 2l when
used as the theta-value coefficient.

This file constructs the corrected actual coefficients and exact comparison
with the old ones.  No inequality is asserted and the old file is not edited.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual 2l-th root coefficient of the classical q parameter:
order(q) / (2l). -/
noncomputable def qVFamPaperRootCoefficient : Real :=
  ((qVFamily T b).order : Real) / (2 * l.value : Real)

/-- The corrected paper-level theta tensor coefficient:
j^2 * order(q) / (2l). -/
noncomputable def qVFamPaperThetaTensorCoefficient
    (j : SignedLabel l.value) : Real :=
  ((gaussExponent j.1).toNat : Real) * qVFamPaperRootCoefficient T b

/-- The old qVFamily coefficient is 2l times the corrected root coefficient. -/
theorem qVFamTensorCoefficient_eq_twoL_mul_rootCoefficient :
    qVFamTensorCoefficient T b =
      (2 * l.value : Real) * qVFamPaperRootCoefficient T b := by
  unfold qVFamTensorCoefficient qVFamPaperRootCoefficient
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  exact (mul_div_cancel₀ ((qVFamily T b).order : Real) htwo).symm

/-- The old theta tensor coefficient is 2l times the corrected paper
coefficient. -/
theorem qVFamThetaTensorCoefficient_eq_twoL_mul_rootCoefficient
    (j : SignedLabel l.value) :
    (fun _ : qVFamTensorV =>
      ((gaussExponent j.1).toNat : Real) * qVFamTensorCoefficient T b) =
      fun _ : qVFamTensorV =>
        (2 * l.value : Real) * qVFamPaperThetaTensorCoefficient T b j := by
  funext _
  unfold qVFamPaperThetaTensorCoefficient
  rw [qVFamTensorCoefficient_eq_twoL_mul_rootCoefficient]
  ring

/-- Exact integrality condition for the root valuation: the classical order is
divisible by 2l. -/
def qVFamRootOrderIntegral : Prop :=
  (2 * l.value) ∣ (qVFamily T b).order

/-- Under the integrality condition, the root coefficient is an actual natural
quotient. -/
noncomputable def qVFamRootOrderNat
    (h : qVFamRootOrderIntegral (l := l) T b) : Nat :=
  (qVFamily T b).order / (2 * l.value)

/-- The actual 2l-th root theta value in the algebraic closure, with the
corrected exponent j^2. -/
noncomputable def qVFamPaperThetaValueRoot
    (j : SignedLabel l.value) :
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  (hodgeTwoLthRoot T b) ^ (gaussExponent j.1).toNat

/-- The corrected paper theta value is the root raised to j^2; its tensor
coefficient is the root coefficient times j^2, not the classical order. -/
theorem qVFamPaperThetaValueRoot_formula
    (j : SignedLabel l.value) :
    qVFamPaperThetaValueRoot T b j =
      (hodgeTwoLthRoot T b) ^ (gaussExponent j.1).toNat :=
  rfl

end LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual

end
