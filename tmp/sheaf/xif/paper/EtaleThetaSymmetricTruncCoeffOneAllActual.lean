import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffOneAllActual

universe u

theorem thetaQExponent_one : thetaQExponent 1 = 1 := by
  unfold thetaQExponent
  norm_num

theorem thetaQExponent_ge_three {k : Nat} (hk : 2 <= k) :
    (3 : Rat) <= thetaQExponent (k : Int) := by
  unfold thetaQExponent
  have hk' : (2 : Rat) <= (k : Rat) := by exact_mod_cast hk
  nlinarith

theorem thetaQExponent_nat_ne_one {k : Nat} (hk : 2 <= k) :
    thetaQExponent (k : Int) ≠ thetaQExponent 1 := by
  have h3 := thetaQExponent_ge_three hk
  rw [thetaQExponent_one]
  linarith

theorem etaleThetaSymmetricTrunc_one_coeff_one (K : Type u) [Field K] :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K 1).coeff
        (thetaQExponent 1) =
      HahnSeries.single (thetaUExponent 1) (-1 : K) +
        HahnSeries.single (thetaUExponent (-2)) (1 : K) := by
  rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_succ K 0,
    HahnSeries.coeff_add]
  have h0 : (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm K 0).coeff (thetaQExponent 1) = 0 := by
    unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
      LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
    have hne : thetaQExponent 0 ≠ thetaQExponent 1 := by
      unfold thetaQExponent; norm_num
    have hne2 : thetaQExponent (-1) ≠ thetaQExponent 1 := by
      unfold thetaQExponent; norm_num
    simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne, hne2]
  rw [h0, zero_add]
  unfold LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaPairTerm
    LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, thetaQExponent, thetaUExponent]
  norm_num

theorem etaleThetaSymmetricTrunc_coeff_one_all (K : Type u) [Field K]
    (N : Nat) (hN : 1 <= N) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K N).coeff
        (thetaQExponent 1) =
      HahnSeries.single (thetaUExponent 1) (-1 : K) +
        HahnSeries.single (thetaUExponent (-2)) (1 : K) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        exact etaleThetaSymmetricTrunc_one_coeff_one K
      · have hN1 : 1 <= N := by omega
        rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_coeff_stable K N]
        · exact ih hN1
        · have hk : 2 <= N + 1 := by omega
          exact thetaQExponent_nat_ne_one hk

#check etaleThetaSymmetricTrunc_coeff_one_all

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffOneAllActual
