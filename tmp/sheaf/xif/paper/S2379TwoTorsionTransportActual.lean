import tmp.sheaf.xif.paper.S2376ThreeRootsActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

-- S2379: root membership -> eval=0 on the base-changed curve.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2379TwoTorsionTransportActual

open WeierstrassCurve

universe u

variable {R : Type u} [Field R] [Nontrivial R]
variable (W : WeierstrassCurve R) [W.IsElliptic]

theorem S2379TwoTorsionPolynomial_map :
    (W.map (algebraMap R (AlgebraicClosure R))).twoTorsionPolynomial =
      Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial := by
  ext <;> simp [WeierstrassCurve.twoTorsionPolynomial, Cubic.map,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆]

#check S2379TwoTorsionPolynomial_map
#check Cubic.mem_roots_iff
#check S2353_equation
#check S2354Point
#check S2358_two_nsmul

end LeanFormal.IUT.XiFPaper.S2379TwoTorsionTransportActual

end
