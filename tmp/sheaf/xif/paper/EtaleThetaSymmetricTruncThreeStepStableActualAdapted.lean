import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncThreeStepStableActualAdapted

universe u

theorem etaleThetaSymmetricTrunc_succ_three (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 3) =
      ((etaleThetaSymmetricTrunc K N + thetaPairTerm K (N + 1 : Int)) +
        thetaPairTerm K (N + 2 : Int)) + thetaPairTerm K (N + 3 : Int) := by
  rw [show N + 3 = ((N + 1) + 1) + 1 by ring]
  rw [etaleThetaSymmetricTrunc_succ, etaleThetaSymmetricTrunc_succ,
    etaleThetaSymmetricTrunc_succ]

theorem thetaPairTerm_coeff_eq_zero (K : Type u) [Field K] (n : Int) (e : HalfInt)
    (h : e ≠ thetaQExponent n) :
    (thetaPairTerm K n).coeff e = 0 := by
  by_contra hc
  have hmem : e ∈ (thetaPairTerm K n).support := (HahnSeries.mem_support _ _).2 hc
  have hsingle := thetaPairTerm_support K n hmem
  exact h (Set.mem_singleton_iff.mp hsingle)

theorem etaleThetaSymmetricTrunc_three_step_stable (K : Type u) [Field K]
    (N : Nat) (e : HalfInt)
    (h1 : e ≠ thetaQExponent (N + 1 : Int))
    (h2 : e ≠ thetaQExponent (N + 2 : Int))
    (h3 : e ≠ thetaQExponent (N + 3 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 3)).coeff e =
      (etaleThetaSymmetricTrunc K N).coeff e := by
  rw [etaleThetaSymmetricTrunc_succ_three, HahnSeries.coeff_add, HahnSeries.coeff_add,
    HahnSeries.coeff_add,
    thetaPairTerm_coeff_eq_zero K (N + 1 : Int) e h1,
    thetaPairTerm_coeff_eq_zero K (N + 2 : Int) e h2,
    thetaPairTerm_coeff_eq_zero K (N + 3 : Int) e h3]
  abel

#check etaleThetaSymmetricTrunc_three_step_stable

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncThreeStepStableActualAdapted
