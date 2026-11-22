import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtEqIffActualAdapted

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

noncomputable def thetaCoeffAt (K : Type u) [Field K] (n : Int) :
    HahnSeries Int K :=
  (thetaPairTerm K n).coeff (thetaQExponent n)

theorem thetaCoeffAt_eq (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_coeff_u (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent n) = (-1 : K) ^ n := by
  rw [thetaCoeffAt_eq]
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem thetaCoeffAt_coeff_zero_of_ne (K : Type u) [Field K]
    (n m : Int) (h1 : thetaUExponent n ≠ thetaUExponent m)
    (h2 : thetaUExponent n ≠ thetaUExponent (-m - 1)) :
    (thetaCoeffAt K m).coeff (thetaUExponent n) = 0 := by
  rw [thetaCoeffAt_eq]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, h1, h2]

/-- The core theta coefficient determines n up to the theta involution n -> -n-1. -/
theorem thetaCoeffAt_eq_iff (K : Type u) [Field K] (n m : Int) :
    thetaCoeffAt K n = thetaCoeffAt K m ↔ n = m ∨ n + m = -1 := by
  constructor
  · intro h
    have hc := congrArg (fun s : HahnSeries Int K => s.coeff (thetaUExponent n)) h
    rw [thetaCoeffAt_coeff_u] at hc
    by_cases h1 : thetaUExponent n = thetaUExponent m
    · left; unfold thetaUExponent at h1; omega
    · by_cases h2 : thetaUExponent n = -thetaUExponent m
      · right; unfold thetaUExponent at h2; omega
      · exfalso
        have h2' : thetaUExponent n ≠ thetaUExponent (-m - 1) := by
          intro hh
          apply h2
          rw [hh, thetaUExponent_neg_succ]
        have hz := thetaCoeffAt_coeff_zero_of_ne K n m h1 h2'
        rw [hz] at hc
        exact (zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)) hc
  · rintro (rfl | h)
    · rfl
    · have h' : m = -n - 1 := by omega
      subst m
      unfold thetaCoeffAt
      rw [thetaQExponent_neg_succ]
      unfold thetaPairTerm
      rw [show (-(-n - 1) - 1 : Int) = n by ring]
      rw [add_comm]

#check thetaCoeffAt_eq_iff

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtEqIffActualAdapted
