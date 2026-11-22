import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
set_option backward.isDefEq.respectTransparency false
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
namespace Probe9
variable {k K : Type*} [Field k] [Field K] [Algebra k K] [DecidableEq k] [DecidableEq K]
  [DecidableEq (AlgebraicClosure k)] [DecidableEq (AlgebraicClosure K)]
example (W : WeierstrassCurve k) (Q : W.toAffine.Point)
    (hcurve : ((W⁄K)⁄(AlgebraicClosure K)) = (W⁄(AlgebraicClosure K))) :
    (hcurve ▸ Affine.Point.baseChange (W' := W) K (AlgebraicClosure K)
        (Affine.Point.baseChange (W' := W) k K Q)) =
      Affine.Point.baseChange (W' := W) k (AlgebraicClosure K) Q := by
  classical
  dsimp only
  cases hcurve
  rw [Affine.Point.baseChange, Affine.Point.baseChange, Affine.Point.baseChange, Affine.Point.map_map]
  congr 1
  ext x
  simp
end Probe9
