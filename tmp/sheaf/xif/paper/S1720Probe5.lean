import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
set_option backward.isDefEq.respectTransparency false
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
namespace Probe5
variable (K : Type) [Field K] [DecidableEq (AlgebraicClosure K)] (W : WeierstrassCurve K)
example (P : (W.baseChange (AlgebraicClosure K)).toAffine.Point) : (6 : ℤ) • P = 0 := by
  sorry
example (P : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (e : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (6 : ℤ) • (Affine.Point.map (W' := W.toAffine) (e.symm : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) P) = 0 := by
  rw [← AddMonoidHom.map_zsmul]
  sorry
end Probe5
