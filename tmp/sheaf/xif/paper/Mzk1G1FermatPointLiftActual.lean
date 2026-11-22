import tmp.sheaf.xif.paper.Mzk1G1FermatCurveProjActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPointLiftActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveProjActual
/-- Projectivize an affine Fermat solution. -/
def fermatLift (x y : ℚ) : Fin 3 → ℚ := ![x, y, 1]
theorem fermatLift_mem (n : Nat) (x y : ℚ) (h : x ^ n + y ^ n = 1) :
    fermatLift x y ∈ projFermatCurve n := by
  constructor
  · simp [fermatLift, h]
  · intro hzero
    have h2 := congrFun hzero 2
    simp [fermatLift] at h2
#print axioms fermatLift_mem
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPointLiftActual
end