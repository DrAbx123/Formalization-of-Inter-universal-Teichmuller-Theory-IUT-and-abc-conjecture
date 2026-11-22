import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffStableAtActual

universe u

theorem thetaQExponent_nat_succ_ne (N : Nat) :
    thetaQExponent ((N + 1 : Nat) : Int) ≠ thetaQExponent (N : Int) := by
  unfold thetaQExponent
  have h : (0 : Rat) <= (N : Rat) := by positivity
  nlinarith

theorem etaleThetaSymmetricTrunc_coeff_stable_at_own (K : Type u) [Field K] (N : Nat) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K (N + 1)).coeff
        (thetaQExponent (N : Int)) =
      (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K N).coeff
        (thetaQExponent (N : Int)) := by
  apply LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_coeff_stable
  exact (thetaQExponent_nat_succ_ne N).symm

#check etaleThetaSymmetricTrunc_coeff_stable_at_own

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffStableAtActual
