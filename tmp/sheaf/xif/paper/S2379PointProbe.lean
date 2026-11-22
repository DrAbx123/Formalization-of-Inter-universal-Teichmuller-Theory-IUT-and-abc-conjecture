import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual
import tmp.sheaf.xif.paper.S2376ThreeRootsActual
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
open WeierstrassCurve Polynomial

namespace TestPointRoots

universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

example :
    (W.map (algebraMap R (AlgebraicClosure R))).twoTorsionPolynomial =
      Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial := by
  ext <;> simp [WeierstrassCurve.twoTorsionPolynomial, WeierstrassCurve.map,
    Cubic.map, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

end TestPointRoots
