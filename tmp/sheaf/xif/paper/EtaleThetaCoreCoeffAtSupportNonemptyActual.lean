import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportNonemptyActual

universe u

theorem thetaCoeffAt_eq_local (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_coeff_u_ne_zero (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent n) ≠ 0 := by
  rw [thetaCoeffAt_eq_local]
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  rw [HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single]
  simp [hne]
  exact zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)

theorem thetaCoeffAt_mem_support_u (K : Type u) [Field K] (n : Int) :
    thetaUExponent n ∈ (thetaCoeffAt K n).support :=
  (HahnSeries.mem_support _ _).2 (thetaCoeffAt_coeff_u_ne_zero K n)

theorem thetaCoeffAt_support_nonempty (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support.Nonempty :=
  ⟨thetaUExponent n, thetaCoeffAt_mem_support_u K n⟩

#check thetaCoeffAt_support_nonempty

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportNonemptyActual
