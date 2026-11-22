import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncLimitActual

noncomputable section
open scoped BigOperators

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual

universe u

theorem thetaQExponent_nat_ne_zero (N : Nat) :
    thetaQExponent (N + 1 : Int) ≠ 0 := by
  intro h
  have hge := thetaQExponent_nat_ge N
  rw [h] at hge
  have hN : (0 : Rat) <= (N : Rat) := by positivity
  linarith

theorem etaleThetaSymmetricTrunc_coeff_zero_all (K : Type u) [Field K] (N : Nat) :
    (etaleThetaSymmetricTrunc K N).coeff (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  induction N with
  | zero =>
      simp [etaleThetaSymmetricTrunc, thetaPairTerm, thetaTermEx,
        thetaQExponent, thetaUExponent]
  | succ N ih =>
      rw [etaleThetaSymmetricTrunc_succ, HahnSeries.coeff_add, ih]
      have hz : (thetaPairTerm K (N + 1 : Int)).coeff (0 : HalfInt) = 0 := by
        have hne : thetaQExponent (N + 1 : Int) ≠ 0 := thetaQExponent_nat_ne_zero N
        unfold thetaPairTerm thetaTermEx
        rw [thetaQExponent_neg_succ]
        simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne, hne.symm]
      rw [hz, add_zero]

theorem etaleThetaSymmetricCoeffLimit_zero (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  unfold etaleThetaSymmetricCoeffLimit
  exact etaleThetaSymmetricTrunc_coeff_zero_all K _

theorem etaleThetaSymmetricCoeffLimit_zero_ne_zero (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) ≠ 0 := by
  rw [etaleThetaSymmetricCoeffLimit_zero]
  intro h
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (1 : Int)) h
  have hne : (1 : Int) ≠ -1 := by norm_num
  simp [thetaUExponent, HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc

theorem etaleThetaSymmetricCoeffLimit_zero_eq_pair (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) =
      (thetaPairTerm K 0).coeff (thetaQExponent 0) := by
  rw [etaleThetaSymmetricCoeffLimit_zero]
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, thetaQExponent, thetaUExponent]

/-- Core theta coefficient at exponent thetaQExponent n. -/
noncomputable def thetaCoeffAt (K : Type u) [Field K] (n : Int) : HahnSeries Int K :=
  (thetaPairTerm K n).coeff (thetaQExponent n)

theorem etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) = thetaCoeffAt K 0 :=
  etaleThetaSymmetricCoeffLimit_zero_eq_pair K

theorem thetaCoeffAt_pair_minimal (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K (-n - 1) = thetaCoeffAt K n := by
  unfold thetaCoeffAt
  rw [thetaQExponent_neg_succ]
  unfold thetaPairTerm
  rw [show (-(-n - 1) - 1 : Int) = n by ring]
  rw [add_comm]

theorem thetaCoeffAt_ne_zero_minimal (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n ≠ 0 := by
  intro h
  unfold thetaCoeffAt thetaPairTerm thetaTermEx at h
  rw [show thetaQExponent (-n - 1) = thetaQExponent n by exact thetaQExponent_neg_succ n] at h
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent
    omega
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (thetaUExponent n)) h
  simp [thetaTermEx, HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc
  exact (zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)) hc

theorem thetaCoeffAt_eq_minimal (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_support_subset_minimal (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support ⊆
      ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) := by
  rw [thetaCoeffAt_eq_minimal]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · left; exact HahnSeries.support_single_subset h
  · right; exact HahnSeries.support_single_subset h

theorem thetaCoeffAt_coeff_u_ne_zero_minimal (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent n) ≠ 0 := by
  rw [thetaCoeffAt_eq_minimal]
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  rw [HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single]
  simp [hne]
  exact zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)

theorem thetaCoeffAt_coeff_neg_u_ne_zero_minimal (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent (-n - 1)) ≠ 0 := by
  rw [thetaCoeffAt_eq_minimal]
  have hne : thetaUExponent (-n - 1) ≠ thetaUExponent n := by
    unfold thetaUExponent; omega
  rw [HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single]
  simp [hne]
  exact zpow_ne_zero (-n - 1) (by norm_num : (-1 : K) ≠ 0)

theorem thetaCoeffAt_support_exact_minimal (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support =
      ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) := by
  apply Set.Subset.antisymm (thetaCoeffAt_support_subset_minimal K n)
  intro x hx
  rcases hx with h | h
  · subst x
    exact (HahnSeries.mem_support _ _).2 (thetaCoeffAt_coeff_u_ne_zero_minimal K n)
  · subst x
    exact (HahnSeries.mem_support _ _).2 (thetaCoeffAt_coeff_neg_u_ne_zero_minimal K n)

theorem thetaCoeffAt_support_encard_minimal (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support.encard = 2 := by
  rw [thetaCoeffAt_support_exact_minimal]
  apply Set.encard_pair
  unfold thetaUExponent
  omega

theorem etaleThetaSymmetricCoeffLimit_zero_support_encard (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.encard = 2 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt]
  exact thetaCoeffAt_support_encard_minimal K 0

theorem etaleThetaSymmetricCoeffLimit_zero_support_eq (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support = ({1, -1} : Set Int) := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt,
    thetaCoeffAt_support_exact_minimal]
  unfold thetaUExponent
  norm_num

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_one (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff (1 : Int) = 1 := by
  rw [etaleThetaSymmetricCoeffLimit_zero]
  have hne : (1 : Int) ≠ -1 := by norm_num
  simp [thetaUExponent, HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_neg_one (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff (-1 : Int) = -1 := by
  rw [etaleThetaSymmetricCoeffLimit_zero]
  have hne : (-1 : Int) ≠ 1 := by norm_num
  simp [thetaUExponent, HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem thetaCoeffAt_zero_coeff_one (K : Type u) [Field K] :
    (thetaCoeffAt K 0).coeff (1 : Int) = 1 := by
  rw [thetaCoeffAt_eq_minimal]
  have hne : (1 : Int) ≠ -1 := by norm_num
  simp [thetaUExponent, HahnSeries.coeff_add, HahnSeries.coeff_single, hne, zpow_zero]

theorem thetaCoeffAt_zero_coeff_neg_one (K : Type u) [Field K] :
    (thetaCoeffAt K 0).coeff (-1 : Int) = -1 := by
  rw [thetaCoeffAt_eq_minimal]
  have hne : (-1 : Int) ≠ 1 := by norm_num
  simp [thetaUExponent, HahnSeries.coeff_add, HahnSeries.coeff_single, hne, zpow_zero]

theorem thetaCoeffAt_zero_support_eq (K : Type u) [Field K] :
    (thetaCoeffAt K 0).support = ({1, -1} : Set Int) := by
  rw [thetaCoeffAt_support_exact_minimal]
  unfold thetaUExponent
  norm_num

theorem thetaCoeffAt_coeff_u_value_minimal (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent n) = (-1 : K) ^ n := by
  rw [thetaCoeffAt_eq_minimal]
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent; omega
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem thetaCoeffAt_coeff_neg_u_value_minimal (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent (-n - 1)) = (-1 : K) ^ (-n - 1) := by
  rw [thetaCoeffAt_eq_minimal]
  have hne : thetaUExponent (-n - 1) ≠ thetaUExponent n := by
    unfold thetaUExponent; omega
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem thetaCoeffAt_zero_value_minimal (K : Type u) [Field K] :
    thetaCoeffAt K 0 =
      HahnSeries.single (1 : Int) (1 : K) +
        HahnSeries.single (-1 : Int) (-1 : K) := by
  rw [thetaCoeffAt_eq_minimal]
  unfold thetaUExponent
  norm_num

theorem etaleThetaSymmetricCoeffLimit_zero_value_minimal (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) =
      HahnSeries.single (1 : Int) (1 : K) +
        HahnSeries.single (-1 : Int) (-1 : K) := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt,
    thetaCoeffAt_zero_value_minimal]

theorem thetaCoeffAt_zero_support_encard (K : Type u) [Field K] :
    (thetaCoeffAt K 0).support.encard = 2 := by
  rw [thetaCoeffAt_zero_support_eq]
  apply Set.encard_pair
  norm_num

theorem thetaCoeffAt_zero_ne_zero_minimal (K : Type u) [Field K] :
    thetaCoeffAt K 0 ≠ 0 :=
  thetaCoeffAt_ne_zero_minimal K 0

theorem etaleThetaSymmetricCoeffLimit_zero_ne_zero_minimal (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) ≠ 0 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt]
  exact thetaCoeffAt_zero_ne_zero_minimal K

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_eq_thetaCoeffAt
    (K : Type u) [Field K] (x : Int) :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff x =
      (thetaCoeffAt K 0).coeff x := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt]

theorem etaleThetaSymmetricCoeffLimit_zero_support_eq_thetaCoeffAt
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support =
      (thetaCoeffAt K 0).support := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt]

theorem thetaCoeffAt_zero_support_nonempty (K : Type u) [Field K] :
    (thetaCoeffAt K 0).support.Nonempty := by
  refine ⟨(1 : Int), ?_⟩
  rw [thetaCoeffAt_zero_support_eq]
  simp

theorem etaleThetaSymmetricCoeffLimit_zero_support_nonempty (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.Nonempty := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_thetaCoeffAt]
  exact thetaCoeffAt_zero_support_nonempty K

theorem etaleThetaSymmetricCoeffLimit_zero_support_finite (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.Finite := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq]
  exact (Set.finite_singleton (-1 : Int)).insert 1

theorem thetaCoeffAt_zero_support_finite (K : Type u) [Field K] :
    (thetaCoeffAt K 0).support.Finite := by
  rw [thetaCoeffAt_zero_support_eq]
  exact (Set.finite_singleton (-1 : Int)).insert 1

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_eq_zero_of_ne
    (K : Type u) [Field K] (x : Int) (h1 : x ≠ 1) (h2 : x ≠ -1) :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff x = 0 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_value_minimal]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, h1, h2]

theorem thetaCoeffAt_zero_coeff_eq_zero_of_ne (K : Type u) [Field K]
    (x : Int) (h1 : x ≠ 1) (h2 : x ≠ -1) :
    (thetaCoeffAt K 0).coeff x = 0 := by
  rw [thetaCoeffAt_zero_value_minimal]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, h1, h2]

theorem etaleThetaSymmetricCoeffLimit_zero_support_eq_pair (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support =
      ((thetaPairTerm K 0).coeff (thetaQExponent 0)).support := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_pair]

theorem thetaPairTerm_zero_coeff_support_eq (K : Type u) [Field K] :
    ((thetaPairTerm K 0).coeff (thetaQExponent 0)).support = ({1, -1} : Set Int) :=
  thetaCoeffAt_zero_support_eq K

theorem thetaPairTerm_zero_coeff_value (K : Type u) [Field K] :
    (thetaPairTerm K 0).coeff (thetaQExponent 0) =
      HahnSeries.single (1 : Int) (1 : K) +
        HahnSeries.single (-1 : Int) (-1 : K) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, thetaUExponent]

theorem thetaPairTerm_zero_coeff_ne_zero (K : Type u) [Field K] :
    (thetaPairTerm K 0).coeff (thetaQExponent 0) ≠ 0 := by
  rw [thetaPairTerm_zero_coeff_value]
  intro h
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (1 : Int)) h
  have hne : (1 : Int) ≠ -1 := by norm_num
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc

theorem thetaPairTerm_zero_coeff_support_nonempty (K : Type u) [Field K] :
    ((thetaPairTerm K 0).coeff (thetaQExponent 0)).support.Nonempty := by
  rw [thetaPairTerm_zero_coeff_support_eq]
  exact ⟨(1 : Int), by simp⟩

theorem etaleThetaSymmetricCoeffLimit_zero_support_nonempty_via_pair
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.Nonempty := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_pair]
  exact thetaPairTerm_zero_coeff_support_nonempty K

theorem thetaPairTerm_zero_coeff_support_finite (K : Type u) [Field K] :
    ((thetaPairTerm K 0).coeff (thetaQExponent 0)).support.Finite := by
  rw [thetaPairTerm_zero_coeff_support_eq]
  exact (Set.finite_singleton (-1 : Int)).insert 1

theorem etaleThetaSymmetricCoeffLimit_zero_support_finite_via_pair
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.Finite := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_pair]
  exact thetaPairTerm_zero_coeff_support_finite K

theorem thetaPairTerm_zero_coeff_support_encard (K : Type u) [Field K] :
    ((thetaPairTerm K 0).coeff (thetaQExponent 0)).support.encard = 2 := by
  rw [thetaPairTerm_zero_coeff_support_eq]
  apply Set.encard_pair
  norm_num

theorem etaleThetaSymmetricCoeffLimit_zero_support_encard_via_pair
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.encard = 2 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_pair]
  exact thetaPairTerm_zero_coeff_support_encard K

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual

end
