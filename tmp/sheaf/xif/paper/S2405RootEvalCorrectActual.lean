import tmp.sheaf.xif.paper.S2389RootEvalActual
import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual
import Mathlib.Algebra.CubicDiscriminant

noncomputable section
open WeierstrassCurve Polynomial

namespace LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual

universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

/-- Root membership in the base-changed 2-division polynomial gives the vanishing of its evaluation. -/
theorem S2405_eval_zero_of_mem (x : AlgebraicClosure R)
    (hx : x ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots) :
    (W.map (algebraMap R (AlgebraicClosure R))).twoTorsionPolynomial.toPoly.eval x = 0 := by
  rw [LeanFormal.IUT.XiFPaper.S2389RootEvalActual.S2389TwoTorsionPolynomial_map]
  rw [Cubic.roots] at hx
  have hroot : (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).toPoly.IsRoot x := by
    exact (Polynomial.mem_roots'.mp hx).2
  rwa [Polynomial.IsRoot.def] at hroot

#print axioms S2405_eval_zero_of_mem

end LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual
