import tmp.sheaf.xif.paper.S2405RootEvalCorrectActual
import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
open WeierstrassCurve Polynomial
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual

namespace TestPointBuild3
universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

noncomputable abbrev WK (W : WeierstrassCurve R) : WeierstrassCurve (AlgebraicClosure R) :=
  W.map (algebraMap R (AlgebraicClosure R))

theorem point_build (h2 : (2 : R) ≠ 0) (x : AlgebraicClosure R)
    (hx : x ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots) :
    (2 : Nat) • S2354Point (WK W) (by
      rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
      exact fun h => h2 ((map_eq_zero_iff _ (algebraMap_injective R _)).mp h)) x
      (S2405_eval_zero_of_mem W x hx) = 0 := by
  letI : DecidableEq (AlgebraicClosure R) := Classical.decEq _
  haveI : (WK W).toAffine.IsElliptic := inferInstance
  letI : AddCommGroup (WK W).toAffine.Point := inferInstance
  have h2' : (2 : AlgebraicClosure R) ≠ 0 := by
    rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
    exact fun h => h2 ((map_eq_zero_iff _ (algebraMap_injective R _)).mp h)
  exact @S2358_two_nsmul (AlgebraicClosure R) _ (Classical.decEq _) (WK W) inferInstance h2' x
    (S2405_eval_zero_of_mem W x hx)

end TestPointBuild3
