import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffTwoAllActual

universe u

theorem thetaQExponent_two : thetaQExponent 2 = 3 := by
  unfold thetaQExponent
  norm_num

theorem thetaQExponent_ge_six {k : Nat} (hk : 3 <= k) :
    (6 : Rat) <= thetaQExponent (k : Int) := by
  unfold thetaQExponent
  have hk' : (3 : Rat) <= (k : Rat) := by exact_mod_cast hk
  nlinarith

theorem thetaQExponent_nat_ne_two {k : Nat} (hk : 3 <= k) :
    thetaQExponent (k : Int) ≠ thetaQExponent 2 := by
  have h6 := thetaQExponent_ge_six hk
  rw [thetaQExponent_two]
  linarith

theorem etaleThetaSymmetricTrunc_two_coeff_two (K : Type u) [Field K] :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K 2).coeff
        (thetaQExponent 2) =
      HahnSeries.single (thetaUExponent 2) (1 : K) +
        HahnSeries.single (thetaUExponent (-3)) (-1 : K) := by
  rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_succ K 1,
    HahnSeries.coeff_add]
  have htr : (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K 1).coeff (thetaQExponent 2) = 0 := by
    rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_succ K 0,
      HahnSeries.coeff_add]
    have hp0 : (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm K 0).coeff (thetaQExponent 2) = 0 := by
      unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
        LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
      have hne : thetaQExponent 0 ≠ thetaQExponent 2 := by unfold thetaQExponent; norm_num
      have hne2 : thetaQExponent (-1) ≠ thetaQExponent 2 := by unfold thetaQExponent; norm_num
      simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne, hne2]
    have hp1 : (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm K 1).coeff (thetaQExponent 2) = 0 := by
      unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
        LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
      have hne : thetaQExponent 1 ≠ thetaQExponent 2 := by unfold thetaQExponent; norm_num
      have hne2 : thetaQExponent (-2) ≠ thetaQExponent 2 := by unfold thetaQExponent; norm_num
      simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne, hne2]
    rw [hp0, hp1, add_zero]
  rw [htr, zero_add]
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
    LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, thetaQExponent, thetaUExponent]
  norm_num

theorem etaleThetaSymmetricTrunc_coeff_two_all (K : Type u) [Field K]
    (N : Nat) (hN : 2 <= N) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K N).coeff
        (thetaQExponent 2) =
      HahnSeries.single (thetaUExponent 2) (1 : K) +
        HahnSeries.single (thetaUExponent (-3)) (-1 : K) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hN1 : N < 2
      · interval_cases N
        exact etaleThetaSymmetricTrunc_two_coeff_two K
      · have hN2 : 2 <= N := by omega
        rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_coeff_stable K N]
        · exact ih hN2
        · have hk : 3 <= N + 1 := by omega
          exact thetaQExponent_nat_ne_two hk

#check etaleThetaSymmetricTrunc_coeff_two_all

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffTwoAllActual
