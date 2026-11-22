import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1469IsogenyBasicActual

open Polynomial WeierstrassCurve.Affine

variable {F : Type*} [Field F]
variable {W1 W2 : WeierstrassCurve.Affine F}

abbrev CoordinatePullback (W1 W2 : WeierstrassCurve.Affine F) : Type _ :=
  W2.CoordinateRing →ₐ[F] W1.FunctionField

def MapsInfinity (pullback : CoordinatePullback W1 W2) : Prop :=
  letI := pullback.toRingHom.toAlgebra
  ∀ x : W1.CoordinateRing,
    algebraMap W1.CoordinateRing W1.FunctionField x ∈
      integralClosure W2.CoordinateRing W1.FunctionField

structure Isogeny (W1 W2 : WeierstrassCurve.Affine F) where
  pullback : CoordinatePullback W1 W2
  mapsInfinity : MapsInfinity pullback
  fieldPullback : W2.FunctionField →ₐ[F] W1.FunctionField
  fieldPullback_algebraMap : ∀ x : W2.CoordinateRing,
    fieldPullback (algebraMap W2.CoordinateRing W2.FunctionField x) = pullback x
  degree : Nat

end LeanFormal.IUT.XiFPaper.S1469IsogenyBasicActual

end
