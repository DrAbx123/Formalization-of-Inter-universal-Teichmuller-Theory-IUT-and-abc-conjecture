import tmp.sheaf.xif.paper.S1483MulByIntOnFunctionFieldActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

/-! # S1534: generic point to Jacobian point, and the omega/ZSMul bridge

S1467/S1483 provide genericPoint/omega/psi/mulByIntX/Y/EquationMulByInt.
Mathlib v4.32.2 provides `WeierstrassCurve.Affine.Point.toJacobian`; this file
exposes the actual conversion of the generic point and restates the S1481
OmegaZSMulBridge on the rebased layer, without importing S1430 and without
duplicating Isogeny/genericX.

`EquationMulByInt` is proved from the exact coordinate-match field, which is
the next missing bridge: the Jacobian ZSMul representative gives the affine
coordinates `(mulByIntX, mulByIntY)`.  No inhabitant of that field is asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1534GenericPointJacobianActual

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open TauCeti.Isogeny

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The actual affine generic point as a Jacobian point. -/
noncomputable def s1534GenericPointJacobian :
    (W⁄W.FunctionField).toJacobian.Point :=
  (genericPoint W).toJacobian

@[simp] theorem s1534GenericPointJacobian_point :
    (s1534GenericPointJacobian W).point = (genericPoint W).toJacobian.point := rfl

/-- The Jacobian generic point lifts back to the affine generic point. -/
@[simp] theorem s1534GenericPointJacobian_toAffineLift :
    (s1534GenericPointJacobian W).toAffineLift = genericPoint W := by
  letI := Classical.decEq F
  change (WeierstrassCurve.Jacobian.Point.toAffineLift
      (W := W⁄W.FunctionField) (s1534GenericPointJacobian W)) = genericPoint W
  rw [s1534GenericPointJacobian, WeierstrassCurve.Affine.Point.toJacobian]
  exact (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv
    (W⁄W.FunctionField)).right_inv (genericPoint W)

/-- Restatement of S1481's OmegaZSMulBridge on the S1467/S1483 layer. -/
def S1534OmegaZSMulBridge (n : ℤ) : Prop :=
  ∃ (Y : W.FunctionField)
    (h : (W⁄W.FunctionField).Nonsingular (genericX W) (genericY W)),
    Y = omegaFunctionField W n ∧
    (n • s1534GenericPointJacobian W).point =
      ⟦![((W.Φ n).map (algebraMap F W.FunctionField)).eval (genericX W), Y,
        psiFunctionField W n]⟧

/-- The exact next missing bridge: the Jacobian representative's affine
coordinates are exactly `(mulByIntX, mulByIntY)` at the generic point. -/
def S1534AffineCoordinatesMatch (n : ℤ) : Prop :=
  ∃ h : (W⁄W.FunctionField).Nonsingular (mulByIntX W n) (mulByIntY W n),
    n • genericPoint W =
      (WeierstrassCurve.Affine.Point.some (mulByIntX W n) (mulByIntY W n) h)

/-- From the exact coordinate match, the target equation follows: the affine
point `n • genericPoint` has nonsingular coordinates `(mulByIntX, mulByIntY)`. -/
theorem equationMulByInt_of_affineCoordinatesMatch {n : ℤ}
    (h : S1534AffineCoordinatesMatch W n) : EquationMulByInt W n := by
  rcases h with ⟨hns, _⟩
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mpr hns

#check s1534GenericPointJacobian
#check S1534OmegaZSMulBridge
#check S1534AffineCoordinatesMatch
#check equationMulByInt_of_affineCoordinatesMatch

end LeanFormal.IUT.XiFPaper.S1534GenericPointJacobianActual
end
