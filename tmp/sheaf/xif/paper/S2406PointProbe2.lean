import tmp.sheaf.xif.paper.S2405RootEvalCorrectActual
import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
open WeierstrassCurve Polynomial
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual

namespace TestPointBuild2
universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

theorem point_build (h2 : (2 : R) ≠ 0) (x : AlgebraicClosure R)
    (hx : x ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots) :
    let WK := W.map (algebraMap R (AlgebraicClosure R))
    (2 : Nat) • S2354Point WK (map_ne_zero (algebraMap R (AlgebraicClosure R)) h2) x
      (S2405_eval_zero_of_mem W x hx) = 0 := by
  letI : DecidableEq (AlgebraicClosure R) := Classical.decEq _
  let WK := W.map (algebraMap R (AlgebraicClosure R))
  haveI : WK.toAffine.IsElliptic := inferInstance
  letI : AddCommGroup WK.toAffine.Point := inferInstance
  exact S2358_two_nsmul WK (map_ne_zero (algebraMap R (AlgebraicClosure R)) h2) x
    (S2405_eval_zero_of_mem W x hx)

end TestPointBuild2
