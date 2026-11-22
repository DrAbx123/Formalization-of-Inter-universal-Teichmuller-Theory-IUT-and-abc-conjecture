import tmp.sheaf.xif.paper.S2385TwoTorsionTransportActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2389RootEvalActual

open WeierstrassCurve
universe u
variable {R : Type u} [Field R] [Nontrivial R]
variable (W : WeierstrassCurve R) [W.IsElliptic]

theorem S2389TwoTorsionPolynomial_map :
    (W.map (algebraMap R (AlgebraicClosure R))).twoTorsionPolynomial =
      Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial := by
  ext <;>
    simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.map, WeierstrassCurve.map,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
      map_ofNat, map_add, map_mul, map_pow]


#print axioms S2389TwoTorsionPolynomial_map

end LeanFormal.IUT.XiFPaper.S2389RootEvalActual
end