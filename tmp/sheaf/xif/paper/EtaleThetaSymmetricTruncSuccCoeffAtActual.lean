import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccCoeffAtActual

universe u

theorem thetaPairTerm_coeff_at (K : Type u) [Field K] (n : Int) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
    LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem etaleThetaSymmetricTrunc_succ_coeff_at (K : Type u) [Field K] (N : Nat) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K (N + 1)).coeff
        (thetaQExponent (N + 1 : Int)) =
      (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K N).coeff
          (thetaQExponent (N + 1 : Int)) +
        (HahnSeries.single (thetaUExponent (N + 1 : Int)) ((-1 : K) ^ (N + 1 : Int)) +
          HahnSeries.single (thetaUExponent (-(N + 1 : Int) - 1))
            ((-1 : K) ^ (-(N + 1 : Int) - 1))) := by
  rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_succ,
    HahnSeries.coeff_add, thetaPairTerm_coeff_at]

#check etaleThetaSymmetricTrunc_succ_coeff_at

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccCoeffAtActual
