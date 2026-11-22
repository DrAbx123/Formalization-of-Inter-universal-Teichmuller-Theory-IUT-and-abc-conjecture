
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
open WeierstrassCurve

namespace S2223Probe

variable {F : Type*} [Field F]
variable (W : WeierstrassCurve F)

example (L : Type*) [Field L] [Algebra F L] :
    (W.baseChange L).twoTorsionPolynomial =
      (W.twoTorsionPolynomial).map (algebraMap F L) := by
  ext <;>
    simp only [Cubic.map, WeierstrassCurve.twoTorsionPolynomial, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      map_ofNat, map_add, map_mul, map_pow]
  all_goals ring

end S2223Probe
end
