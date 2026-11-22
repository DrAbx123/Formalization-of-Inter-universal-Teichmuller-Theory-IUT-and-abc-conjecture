import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtCoeffZeroActual

universe u

theorem thetaCoeffAt_eq_local (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_coeff_eq_zero_of_ne (K : Type u) [Field K] (n : Int) (x : Int)
    (h1 : x ≠ thetaUExponent n) (h2 : x ≠ thetaUExponent (-n - 1)) :
    (thetaCoeffAt K n).coeff x = 0 := by
  rw [thetaCoeffAt_eq_local]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, h1, h2, h2.symm]

#check thetaCoeffAt_coeff_eq_zero_of_ne

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtCoeffZeroActual
