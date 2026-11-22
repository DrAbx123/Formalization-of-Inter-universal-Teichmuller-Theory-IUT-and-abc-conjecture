import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
set_option backward.isDefEq.respectTransparency false
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
namespace Probe6
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
example (W : WeierstrassCurve k) :
    ((W⁄K)⁄(AlgebraicClosure K)) = (W⁄(AlgebraicClosure K)) := by
  change (W⁄K).map ((IsScalarTower.toAlgHom k K (AlgebraicClosure K) : K →ₐ[k] AlgebraicClosure K) : K →+* AlgebraicClosure K) = W⁄(AlgebraicClosure K)
  rw [WeierstrassCurve.Affine.map_baseChange]
example (W : WeierstrassCurve k)
    (P : ((W⁄K)⁄(AlgebraicClosure K)).Point) :
    True := by
  classical
  have hcurve : ((W⁄K)⁄(AlgebraicClosure K)) = (W⁄(AlgebraicClosure K)) := by
    change (W⁄K).map ((IsScalarTower.toAlgHom k K (AlgebraicClosure K) : K →ₐ[k] AlgebraicClosure K) : K →+* AlgebraicClosure K) = W⁄(AlgebraicClosure K)
    rw [WeierstrassCurve.Affine.map_baseChange]
  let P' : (W⁄(AlgebraicClosure K)).Point := hcurve ▸ P
  have hP' : P' = P' := rfl
  trivial
end Probe6
