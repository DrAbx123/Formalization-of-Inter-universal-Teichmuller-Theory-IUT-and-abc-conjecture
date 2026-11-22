import tmp.sheaf.xif.paper.S2411PointBuildActual
import tmp.sheaf.xif.paper.S2376ThreeRootsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2412ThreePointsTransportActual

open WeierstrassCurve Polynomial
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2376ThreeRootsActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual
open LeanFormal.IUT.XiFPaper.S2411PointBuildActual

universe u
variable {R : Type u} [Field R] (W : WeierstrassCurve R) [W.toAffine.IsElliptic]

section
local instance : DecidableEq (AlgebraicClosure R) := Classical.decEq _
local instance : (S2411WK W).toAffine.IsElliptic := inferInstance
local instance : AddCommGroup (S2411WK W).toAffine.Point := inferInstance

theorem S2412ThreePoints (h2 : (2 : R) ≠ 0) :
    ∃ P1 P2 P3 : (S2411WK W).toAffine.Point,
      (2 : Nat) • P1 = 0 ∧ (2 : Nat) • P2 = 0 ∧ (2 : Nat) • P3 = 0 := by
  obtain ⟨x, y, z, _hxy, _hxz, _hyz, hx, hy, hz⟩ := S2376ThreeDistinctRoots W h2
  refine ⟨S2354Point (S2411WK W) (by
      rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
      exact fun h => h2 ((map_eq_zero_iff _ (algebraMap R _).injective).mp h)) x
      (S2405_eval_zero_of_mem W x hx),
    S2354Point (S2411WK W) (by
      rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
      exact fun h => h2 ((map_eq_zero_iff _ (algebraMap R _).injective).mp h)) y
      (S2405_eval_zero_of_mem W y hy),
    S2354Point (S2411WK W) (by
      rw [show (2 : AlgebraicClosure R) = algebraMap R (AlgebraicClosure R) 2 from (map_ofNat _ 2).symm]
      exact fun h => h2 ((map_eq_zero_iff _ (algebraMap R _).injective).mp h)) z
      (S2405_eval_zero_of_mem W z hz), ?_, ?_, ?_⟩
  · exact S2411_two_torsion_point W h2 x hx
  · exact S2411_two_torsion_point W h2 y hy
  · exact S2411_two_torsion_point W h2 z hz

#print axioms S2412ThreePoints

end
end LeanFormal.IUT.XiFPaper.S2412ThreePointsTransportActual
end