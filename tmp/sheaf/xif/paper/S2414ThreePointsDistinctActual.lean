import tmp.sheaf.xif.paper.S2412ThreePointsTransportActual

noncomputable section
open WeierstrassCurve Polynomial
open WeierstrassCurve.Affine
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual
open LeanFormal.IUT.XiFPaper.S2411PointBuildActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual

namespace LeanFormal.IUT.XiFPaper.S2414ThreePointsDistinctActual

universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

section
local instance : DecidableEq (AlgebraicClosure R) := Classical.decEq _
local instance : (S2411WK W).toAffine.IsElliptic := inferInstance
local instance : AddCommGroup (S2411WK W).toAffine.Point := inferInstance

/-- The base-changed 2-torsion point is nonzero. -/
theorem S2414_point_ne_zero (h2' : (2 : AlgebraicClosure R) ≠ 0)
    (x : AlgebraicClosure R)
    (hx : x ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots) :
    S2354Point (S2411WK W) h2' x (S2405_eval_zero_of_mem W x hx) ≠ 0 := by
  change Point.some x (S2337Y (S2411WK W) x) _ ≠ 0
  exact Point.some_ne_zero _

/-- Distinct 2-division roots give distinct base-changed 2-torsion points. -/
theorem S2414_point_ne (h2' : (2 : AlgebraicClosure R) ≠ 0)
    (x y : AlgebraicClosure R)
    (hx : x ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots)
    (hy : y ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots)
    (hxy : x ≠ y) :
    S2354Point (S2411WK W) h2' x (S2405_eval_zero_of_mem W x hx) ≠
      S2354Point (S2411WK W) h2' y (S2405_eval_zero_of_mem W y hy) := by
  intro h
  apply hxy
  change Point.some x (S2337Y (S2411WK W) x) _ =
    Point.some y (S2337Y (S2411WK W) y) _ at h
  injection h with hx' _

#print axioms S2414_point_ne_zero
#print axioms S2414_point_ne

end
end LeanFormal.IUT.XiFPaper.S2414ThreePointsDistinctActual
