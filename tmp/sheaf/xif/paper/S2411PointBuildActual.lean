import tmp.sheaf.xif.paper.S2405RootEvalCorrectActual
import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
open WeierstrassCurve Polynomial
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual

namespace LeanFormal.IUT.XiFPaper.S2411PointBuildActual

universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

noncomputable abbrev S2411WK (W : WeierstrassCurve R) : WeierstrassCurve (AlgebraicClosure R) :=
  W.map (algebraMap R (AlgebraicClosure R))

section
local instance : DecidableEq (AlgebraicClosure R) := Classical.decEq _
local instance : (S2411WK W).toAffine.IsElliptic := inferInstance
local instance : AddCommGroup (S2411WK W).toAffine.Point := inferInstance

/-- A 2-division root gives a base-changed affine 2-torsion point. -/
theorem S2411_two_torsion_point (h2 : (2 : R) ≠ 0) (x : AlgebraicClosure R)
    (hx : x ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots) :
    (2 : Nat) • S2354Point (S2411WK W) (by
      rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
      exact fun h => h2 ((map_eq_zero_iff _ (algebraMap R _).injective).mp h)) x
      (S2405_eval_zero_of_mem W x hx) = 0 := by
  have h2' : (2 : AlgebraicClosure R) ≠ 0 := by
    rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
    exact fun h => h2 ((map_eq_zero_iff _ (algebraMap R _).injective).mp h)
  exact @S2358_two_nsmul (AlgebraicClosure R) _ (Classical.decEq _) (S2411WK W) inferInstance h2' x
    (S2405_eval_zero_of_mem W x hx)

#print axioms S2411_two_torsion_point

end
end LeanFormal.IUT.XiFPaper.S2411PointBuildActual
