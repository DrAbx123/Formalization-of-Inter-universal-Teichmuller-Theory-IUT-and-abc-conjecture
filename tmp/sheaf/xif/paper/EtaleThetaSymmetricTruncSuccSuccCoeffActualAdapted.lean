import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccSuccCoeffActualAdapted

universe u

theorem etaleThetaSymmetricTrunc_succ_succ (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 2) =
      etaleThetaSymmetricTrunc K N + thetaPairTerm K (N + 1 : Int) +
        thetaPairTerm K (N + 2 : Int) := by
  rw [show N + 2 = (N + 1) + 1 by ring]
  rw [etaleThetaSymmetricTrunc_succ, etaleThetaSymmetricTrunc_succ]
  abel

theorem etaleThetaSymmetricTrunc_succ_succ_coeff (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) :
    (etaleThetaSymmetricTrunc K (N + 2)).coeff e =
      (etaleThetaSymmetricTrunc K N).coeff e +
        (thetaPairTerm K (N + 1 : Int)).coeff e +
          (thetaPairTerm K (N + 2 : Int)).coeff e := by
  rw [etaleThetaSymmetricTrunc_succ_succ, HahnSeries.coeff_add, HahnSeries.coeff_add]

#check etaleThetaSymmetricTrunc_succ_succ_coeff

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccSuccCoeffActualAdapted
