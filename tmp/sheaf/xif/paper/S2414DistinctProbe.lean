import tmp.sheaf.xif.paper.S2412ThreePointsTransportActual

noncomputable section
open WeierstrassCurve Polynomial
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual
open LeanFormal.IUT.XiFPaper.S2411PointBuildActual

namespace TestDistinct
universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

section
local instance : DecidableEq (AlgebraicClosure R) := Classical.decEq _
local instance : (S2411WK W).toAffine.IsElliptic := inferInstance
local instance : AddCommGroup (S2411WK W).toAffine.Point := inferInstance

variable (h2 : (2 : R) ≠ 0) (x y : AlgebraicClosure R)
  (hx : x ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots)
  (hy : y ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots)

example (hxy : x ≠ y) :
    S2354Point (S2411WK W) (by
      rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
      exact fun h => h2 ((map_eq_zero_iff _ (algebraMap R _).injective).mp h)) x
      (S2405_eval_zero_of_mem W x hx) ≠
    S2354Point (S2411WK W) (by
      rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
      exact fun h => h2 ((map_eq_zero_iff _ (algebraMap R _).injective).mp h)) y
      (S2405_eval_zero_of_mem W y hy) := by
  intro h
  apply hxy
  simpa [S2354Point, Point.mk] using (Point.some.injEq.mp h).1

example :
    S2354Point (S2411WK W) (by
      rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
      exact fun h => h2 ((map_eq_zero_iff _ (algebraMap R _).injective).mp h)) x
      (S2405_eval_zero_of_mem W x hx) ≠ 0 := by
  change Point.some x (S2337Y (S2411WK W) x) _ ≠ 0
  exact Point.some_ne_zero _

end
end TestDistinct
