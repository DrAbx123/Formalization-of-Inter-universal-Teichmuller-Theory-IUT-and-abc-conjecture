import tmp.sheaf.xif.paper.S1592DblZSmulPolyActual
import tmp.sheaf.xif.paper.S1577CuspPsiEvalActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1592DblZSmulPolyActual
def smulField (n : ℤ) : Fin 3 → Field := polyToField ∘ smulPoly n
def pointedCurve : WeierstrassCurve Field := curvePoly.map polyToField
@[simp] theorem smulField_apply (n : ℤ) (i : Fin 3) :
    smulField n i = polyToField (smulPoly n i) := rfl
theorem dblZ_smulField (n : ℤ) :
    WeierstrassCurve.Jacobian.dblZ pointedCurve.toAffine (smulField n) =
      polyToField (curve.ψ (2 * n)) := by
  rw [show smulField n = polyToField ∘ smulPoly n from rfl]
  change (curvePoly.toAffine.toJacobian.map polyToField).dblZ
      (polyToField ∘ smulPoly n) = polyToField (curve.ψ (2 * n))
  rw [WeierstrassCurve.Jacobian.map_dblZ]
  exact congrArg polyToField (s1592DblZSmulPoly n)
theorem addZ_smulField (m n : ℤ) :
    WeierstrassCurve.Jacobian.addZ (smulField m) (smulField n) =
      polyToField (curve.ψ (n + m) * curve.ψ (n - m)) := by
  change WeierstrassCurve.Jacobian.addZ
      (polyToField ∘ smulPoly m) (polyToField ∘ smulPoly n) =
      polyToField (curve.ψ (n + m) * curve.ψ (n - m))
  rw [WeierstrassCurve.Jacobian.map_addZ polyToField (smulPoly m) (smulPoly n)]
  exact congrArg polyToField (s1592AddZSmulPoly m n)
def S1593DblXYZSmulFieldRequired : Prop :=
  ∀ n : ℤ,
    WeierstrassCurve.Jacobian.dblXYZ (pointedCurve.toJacobian) (smulField n) =
      smulField (2 * n)
def S1593AddXYZSmulFieldRequired : Prop :=
  ∀ m n : ℤ,
    WeierstrassCurve.Jacobian.addXYZ (pointedCurve.toJacobian) (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m)
def S1593NonsingularSmulField : Prop :=
  ∀ n : ℤ, (pointedCurve.toJacobian).Nonsingular (smulField n)
end LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
end
