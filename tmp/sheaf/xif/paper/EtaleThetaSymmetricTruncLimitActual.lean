import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual

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
  rw [etaleThetaSymmetricTrunc_succ, add_sub_cancel_left]
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

theorem etaleThetaSymmetricTrunc_coeff_stable (K : Type u) [Field K]
    (N : Nat) (e : HalfInt) (h : e ≠ thetaQExponent (N + 1 : Int)) :
    (etaleThetaSymmetricTrunc K (N + 1)).coeff e =
      (etaleThetaSymmetricTrunc K N).coeff e := by
  have hz := etaleThetaSymmetricTrunc_diff_coeff_eq_zero K N e h
  rw [HahnSeries.coeff_sub] at hz
  exact sub_eq_zero.mp hz

theorem thetaQExponent_nat_ge (N : Nat) :
    ((N : Rat) + 1) <= thetaQExponent (N + 1 : Int) := by
  unfold thetaQExponent
  push_cast
  have hN : (0 : Rat) <= (N : Rat) := by positivity
  have h2 : (2 : Rat) <= (N : Rat) + 2 := by linarith
  have hm : ((N : Rat) + 1) * 2 <= ((N : Rat) + 1) * ((N : Rat) + 2) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith

theorem thetaQExponent_unbounded (e : HalfInt) :
    exists N : Nat, e < thetaQExponent (N + 1 : Int) := by
  obtain ⟨N, hN⟩ := exists_nat_gt e
  refine ⟨N, ?_⟩
  have hle := thetaQExponent_nat_ge N
  have hN' : e < (N : Rat) := hN
  have hN'' : (N : Rat) < (N : Rat) + 1 := by linarith
  exact lt_of_lt_of_le (lt_trans hN' hN'') hle

theorem thetaQExponent_nat_mono {a b : Nat} (h : a <= b) :
    thetaQExponent (a + 1 : Int) <= thetaQExponent (b + 1 : Int) := by
  unfold thetaQExponent
  push_cast
  have hab : (a : Rat) <= (b : Rat) := by exact_mod_cast h
  have h0 : (0 : Rat) <= (b : Rat) - (a : Rat) := by linarith
  have h1 : (0 : Rat) <= (a : Rat) + (b : Rat) + 3 := by linarith
  nlinarith [mul_nonneg h0 h1]

theorem etaleThetaSymmetricTrunc_coeff_eventually_stable (K : Type u) [Field K]
    (e : HalfInt) :
    exists N0 : Nat, forall N : Nat, N0 <= N ->
      (etaleThetaSymmetricTrunc K (N + 1)).coeff e =
        (etaleThetaSymmetricTrunc K N).coeff e := by
  obtain ⟨N0, hN0⟩ := thetaQExponent_unbounded e
  refine ⟨N0, ?_⟩
  intro N hN
  have hmono := thetaQExponent_nat_mono hN
  have hlt : e < thetaQExponent (N + 1 : Int) := lt_of_lt_of_le hN0 hmono
  exact etaleThetaSymmetricTrunc_coeff_stable K N e (ne_of_lt hlt)

/-- Stabilized coefficient of the symmetric theta truncation at half-integer e. -/
noncomputable def etaleThetaSymmetricCoeffLimit (K : Type u) [Field K] (e : HalfInt) :
    HahnSeries Int K :=
  (etaleThetaSymmetricTrunc K
    (Classical.choose (etaleThetaSymmetricTrunc_coeff_eventually_stable K e))).coeff e

theorem etaleThetaSymmetricCoeffLimit_spec (K : Type u) [Field K] (e : HalfInt) :
    forall N : Nat,
      Classical.choose (etaleThetaSymmetricTrunc_coeff_eventually_stable K e) <= N ->
      (etaleThetaSymmetricTrunc K (N + 1)).coeff e =
        (etaleThetaSymmetricTrunc K N).coeff e :=
  Classical.choose_spec (etaleThetaSymmetricTrunc_coeff_eventually_stable K e)


end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual

end
