import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffCoeffAtActual

universe u

theorem thetaPairTerm_coeff_at (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem etaleThetaSymmetricTrunc_diff_exact (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N =
      thetaPairTerm K (N + 1 : Int) := by
  rw [etaleThetaSymmetricTrunc_succ]
  exact add_sub_cancel_left _ _

theorem etaleThetaSymmetricTrunc_diff_coeff_at (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).coeff
        (thetaQExponent (N + 1 : Int)) =
      HahnSeries.single (thetaUExponent (N + 1 : Int)) ((-1 : K) ^ (N + 1 : Int)) +
        HahnSeries.single (thetaUExponent (-(N + 1 : Int) - 1))
          ((-1 : K) ^ (-(N + 1 : Int) - 1)) := by
  rw [etaleThetaSymmetricTrunc_diff_exact]
  exact thetaPairTerm_coeff_at K (N + 1 : Int)

#check etaleThetaSymmetricTrunc_diff_coeff_at

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncDiffCoeffAtActual
