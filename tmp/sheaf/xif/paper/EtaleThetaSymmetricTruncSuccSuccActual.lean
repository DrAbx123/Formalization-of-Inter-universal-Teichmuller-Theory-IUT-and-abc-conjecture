import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccSuccActual

universe u

theorem etaleThetaSymmetricTrunc_succ_succ (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 2) =
      etaleThetaSymmetricTrunc K N + thetaPairTerm K (N + 1 : Int) +
        thetaPairTerm K (N + 2 : Int) := by
  rw [show N + 2 = (N + 1) + 1 by ring]
  rw [etaleThetaSymmetricTrunc_succ, etaleThetaSymmetricTrunc_succ]
  abel

#check etaleThetaSymmetricTrunc_succ_succ

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccSuccActual
