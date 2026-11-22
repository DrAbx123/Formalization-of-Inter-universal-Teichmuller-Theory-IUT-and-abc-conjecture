import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffGeneralActualAdapted

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def etaleThetaTruncOneSided (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaTermEx K (k : Int))

theorem thetaQExponent_injective_nonneg {a b : Int}
    (ha : 0 <= a) (hb : 0 <= b) (h : thetaQExponent a = thetaQExponent b) :
    a = b := by
  have hfac : ((a : Rat) - (b : Rat)) * ((a : Rat) + (b : Rat) + 1) = 0 := by
    unfold thetaQExponent at h
    nlinarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact_mod_cast (sub_eq_zero.mp h1)
  · exfalso
    have h2' : (a : Rat) + (b : Rat) + 1 = 0 := h2
    have ha' : (0 : Rat) <= a := by exact_mod_cast ha
    have hb' : (0 : Rat) <= b := by exact_mod_cast hb
    linarith

theorem etaleThetaTruncOneSided_coeff_general (K : Type u) [Field K] (n : Nat) :
    (etaleThetaTruncOneSided K (n + 1)).coeff (thetaQExponent (n : Int)) =
      HahnSeries.single (thetaUExponent (n : Int)) ((-1 : K) ^ (n : Int)) := by
  rw [etaleThetaTruncOneSided, HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single n]
  · simp [thetaTermEx, HahnSeries.coeff_single]
  · intro k hk hkn
    have hk' : (k : Nat) <= n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hne : thetaQExponent (k : Int) ≠ thetaQExponent (n : Int) := by
      intro h
      have hEq : (k : Int) = (n : Int) := thetaQExponent_injective_nonneg
        (by positivity) (by positivity) h
      exact hkn (by omega)
    simp [thetaTermEx, HahnSeries.coeff_single, hne]
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

#check etaleThetaTruncOneSided_coeff_general

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffGeneralActualAdapted
