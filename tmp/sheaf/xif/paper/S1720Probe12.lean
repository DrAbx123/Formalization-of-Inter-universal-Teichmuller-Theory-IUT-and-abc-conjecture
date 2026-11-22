import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
set_option backward.isDefEq.respectTransparency false
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
namespace Probe12
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
example (W : WeierstrassCurve k) (Q : W.toAffine.Point) :
    True := by
  classical
  let _ := Affine.Point.baseChange (W' := W) k K Q
  trivial
end Probe12
