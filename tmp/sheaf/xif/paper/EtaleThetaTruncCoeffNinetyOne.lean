import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffNinetyOne

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

theorem thetaPairTerm_coeff (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaPairTerm_coeff_ne (K : Type u) [Field K] (n : Int) (e : HalfInt)
    (h : thetaQExponent n ≠ e) :
    (thetaPairTerm K n).coeff e = 0 := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [thetaTermEx, HahnSeries.coeff_add, HahnSeries.coeff_single, h]

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

noncomputable def etaleThetaSymmetricTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaPairTerm K (k : Int))

/-- General symmetric theta coefficient; replaces per-index coefficients. -/
theorem etaleThetaSymmetricTrunc_coeff_general (K : Type u) [Field K]
    (N n : Nat) (hN : n <= N) :
    (etaleThetaSymmetricTrunc K N).coeff (thetaQExponent (n : Int)) =
      HahnSeries.single (thetaUExponent (n : Int)) ((-1 : K) ^ (n : Int)) +
        HahnSeries.single (thetaUExponent (-(n : Int) - 1))
          ((-1 : K) ^ (-(n : Int) - 1)) := by
  rw [etaleThetaSymmetricTrunc, HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single n]
  · exact thetaPairTerm_coeff K (n : Int)
  · intro k hk hkn
    have hne : thetaQExponent (k : Int) ≠ thetaQExponent (n : Int) := by
      intro h
      have hEq : (k : Int) = (n : Int) := thetaQExponent_injective_nonneg
        (by positivity) (by positivity) h
      exact hkn (by omega)
    exact thetaPairTerm_coeff_ne K (k : Int) (thetaQExponent (n : Int)) hne
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

#check etaleThetaSymmetricTrunc_coeff_general

end LeanFormal.IUT.XiFPaper.EtaleThetaTruncCoeffNinetyOne
