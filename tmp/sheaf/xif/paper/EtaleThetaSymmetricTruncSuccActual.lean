import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

noncomputable def etaleThetaSymmetricTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaPairTerm K (k : Int))

theorem etaleThetaSymmetricTrunc_succ (K : Type u) [Field K] (N : Nat) :
    etaleThetaSymmetricTrunc K (N + 1) =
      etaleThetaSymmetricTrunc K N + thetaPairTerm K (N + 1 : Int) := by
  simp [etaleThetaSymmetricTrunc, Finset.sum_range_succ]

theorem thetaPairTerm_support (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).support ⊆ ({thetaQExponent n} : Set HalfInt) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset h)
  · exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset h)

theorem etaleThetaSymmetricTrunc_diff_support (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).support ⊆
      ({thetaQExponent (N + 1 : Int)} : Set HalfInt) := by
  rw [etaleThetaSymmetricTrunc_succ]
  rw [add_sub_cancel_left]
  exact thetaPairTerm_support K (N + 1 : Int)

theorem etaleThetaSymmetricTrunc_diff_coeff_eq_zero (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) (h : e ≠ thetaQExponent (N + 1 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).coeff e = 0 := by
  have hsub := etaleThetaSymmetricTrunc_diff_support K N
  have hnot : e ∉ (etaleThetaSymmetricTrunc K (N + 1) - etaleThetaSymmetricTrunc K N).support := by
    intro hmem
    exact h (Set.mem_singleton_iff.mp (hsub hmem))
  by_contra hc
  exact hnot ((HahnSeries.mem_support _ _).2 hc)

#check etaleThetaSymmetricTrunc_succ
theorem etaleThetaSymmetricTrunc_coeff_stable (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) (h : e ≠ thetaQExponent (N + 1 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 1)).coeff e =
      (etaleThetaSymmetricTrunc K N).coeff e := by
  have hz := etaleThetaSymmetricTrunc_diff_coeff_eq_zero K N e h
  rw [HahnSeries.coeff_sub] at hz
  exact sub_eq_zero.mp hz

#check etaleThetaSymmetricTrunc_diff_coeff_eq_zero
#check etaleThetaSymmetricTrunc_coeff_stable
#check etaleThetaSymmetricTrunc_diff_support

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
